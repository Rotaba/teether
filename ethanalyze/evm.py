import copy
import logging
import numbers
from binascii import hexlify
from collections import defaultdict

from z3 import z3, z3util

import utils
from .disassembly import disass
from .memory import UninitializedRead
from .z3_extra_util import add_suffix
from .z3_extra_util import get_vars_non_recursive


class LazyProgram(object):
    def __init__(self, code):
        self.code = code
        self.ins = dict()

    def __disass__(self, i):
        for ins in disass(self.code, i):
            self.ins[ins.addr] = ins

    def __contains__(self, i):
        if i in self.ins:
            return True
        self.__disass__(i)
        return i in self.ins

    def __getitem__(self, i):
        if i in self:
            return self.ins[i]
        raise KeyError()


class ExternalData(Exception):
    pass


class SymbolicError(Exception):
    pass


class IntractablePath(Exception):
    pass


class vm_exception(Exception):
    pass


class Stack(list):
    def __init__(self, *args):
        super(Stack, self).__init__(*args)

    def push(self, v):
        self.append(v)

    def append(self, v):
        if concrete(v):
            v %= 2 ** 256
        super(Stack, self).append(v)


class Memory(object):
    def __init__(self, *args):
        self.memory = bytearray(*args)
        self._check_initialized = False
        self.initialized = set()

    def __getitem__(self, index):
        if isinstance(index, slice):
            initialized = all(i in self.initialized for i in xrange(index.start or 0, index.stop, index.step or 1))
        else:
            initialized = index in self.initialized
        if not self._check_initialized or initialized:
            return self.memory[index]
        else:
            raise UninitializedRead(index)

    def __setitem__(self, index, v):
        if isinstance(index, slice):
            for i in xrange(index.start or 0, index.stop, index.step or 1):
                self.initialized.add(i)
        else:
            self.initialized.add(index)
        self.memory[index] = v

    def set_enforcing(self, enforcing=True):
        self._check_initialized = enforcing

    def extend(self, start, size):
        if len(self.memory) < start + size:
            self.memory += bytearray(start + size - len(self.memory))

    def __len__(self):
        return len(self.memory)


class SymbolicMemory(object):
    def __init__(self):
        self.memory = z3.K(z3.BitVecSort(256), z3.BitVecVal(0, 8))

    def __getitem__(self, index):
        if isinstance(index, slice):
            if index.stop is None:
                raise ValueError("Need upper memory address!")
            if (index.start is not None and not concrete(index.start)) or not concrete(index.stop):
                raise SymbolicError("Use mem.read for symbolic range reads")
            r = []
            for i in xrange(index.start or 0, index.stop, index.step or 1):
                r.append(self[i])
            return r
        else:
            v = z3.simplify(self.memory[index])
            if z3.is_bv_value(v):
                return v.as_long()
            else:
                return v

    def __setitem__(self, index, v):
        if isinstance(index, slice):
            if index.stop is None:
                raise ValueError("Need upper memory address!")
            if (index.start is not None and not concrete(index.start)) or not concrete(index.stop):
                raise SymbolicError("Use mem.write for symbolic range writes")
            for j, i in enumerate(xrange(index.start or 0, index.stop, index.step or 1)):
                self[i] = v[j]
        else:
            if isinstance(v, basestring):
                v = ord(v)

            if concrete(v):
                old_v = self[index]
                if not concrete(old_v) or old_v != v:
                    self.memory = z3.Store(self.memory, index, v)
            else:
                self.memory = z3.Store(self.memory, index, v)

    def read(self, start, size):
        if concrete(start) and concrete(size):
            return self[start:start + size]
        elif concrete(size):
            return [self[start + i] for i in xrange(size)]
        else:
            sym_mem = SymbolicMemory()
            sym_mem.memory = self.memory
            return SymRead(sym_mem, start, size)
            # raise SymbolicError("Read of symbolic length")

    def write(self, start, size, val):
        if not concrete(size):
            raise SymbolicError("Write of symbolic length")
        if len(val) != size:
            raise ValueError("value does not match length")
        if concrete(start) and concrete(size):
            self[start:start + size] = val
        else:  # by now we know that size is concrete
            for i in xrange(size):
                self[start + i] = val[i]

    def set_enforcing(self, enforcing=True):
        pass

    def extend(self, start, size):
        pass

    def translate(self, level, extra_subst):
        new_memory = copy.copy(self)
        new_memory.memory = add_suffix(self.memory, level, extra_subst)
        return new_memory


class SymRead(object):
    def __init__(self, memory, start, size):
        self.memory = memory
        self.start = start
        if not concrete(start):
            self.start = z3.simplify(self.start)
        self.size = size
        if not concrete(size):
            self.size = z3.simplify(self.size)

    def translate(self, level, extra_subst):
        new_symread = copy.copy(self)
        new_symread.memory = self.memory.translate(level, extra_subst)
        if not concrete(self.start):
            new_symread.start = add_suffix(self.start, level, extra_subst)
        if not concrete(self.size):
            new_symread.size = add_suffix(self.size, level, extra_subst)
        return new_symread


class SymbolicStorage(object):
    def __init__(self):
        self.storage = z3.Array('STORAGE', z3.BitVecSort(256), z3.BitVecSort(256))
        self.history = [self.storage]

    def __getitem__(self, index):
        return self.storage[index]

    def __setitem__(self, index, v):
        self.storage = z3.Store(self.storage, index, v)
        self.history.append(self.storage)

    def translate(self, level, extra_subst):
        new_storage = copy.copy(self)
        new_storage.storage = add_suffix(self.storage, level, extra_subst)
        new_storage.history = [add_suffix(h, level, extra_subst) for h in self.history]
        return new_storage


class AbstractEVMState(object):
    def __init__(self, code=None):
        self.code = code or bytearray()
        self.pc = 0
        self.stack = Stack()
        self.memory = None
        self.trace = list()
        self.gas = None


class EVMState(AbstractEVMState):
    def __init__(self, code=None, gas=0):
        super(EVMState, self).__init__(code)
        self.memory = Memory()
        self.gas = gas


class SymbolicEVMState(AbstractEVMState):
    def __init__(self, code=None):
        super(SymbolicEVMState, self).__init__(code)
        self.memory = SymbolicMemory()
        self.storage = SymbolicStorage()
        self.gas = z3.BitVec('GAS', 256)

    def translate(self, level, extra_subst):
        new_state = copy.copy(self)
        new_state.memory = self.memory.translate(level, extra_subst)
        new_state.storage = self.storage.translate(level, extra_subst)
        new_state.stack = [s if concrete(s) else add_suffix(s, level, extra_subst) for s in self.stack]
        new_state.gas = add_suffix(self.gas, level, extra_subst)
        return new_state

    def rebase(self, storage):
        subst = [(self.storage.history[0], storage)]
        new_state = copy.copy(self)
        new_state.memory = self.memory.rebase(subst)
        new_state.storage = self.storage.rebase(subst)
        new_state.stack = [s if concrete(s) else z3.substitute(s, subst) for s in self.stack]
        return new_state


class Context(object):
    def __init__(self):
        self.address = 0
        self.balance = dict()
        self.origin = 0
        self.caller = 0
        self.callvalue = 0
        self.calldata = []
        self.gasprice = 0
        self.coinbase = 0
        self.timestamp = 0
        self.number = 0
        self.difficulty = 0
        self.gaslimit = 0
        self.storage = defaultdict(int)


def run(program, state=None, code=None, ctx=None, check_initialized=False, trace=False):
    ctx = ctx or Context()
    state = state or EVMState(code)
    state.memory.set_enforcing(check_initialized)
    while state.pc in program:
        if trace:
            state.trace.append(state.pc)
        ins = program[state.pc]
        opcode = ins.op
        op = ins.name
        stk = state.stack
        mem = state.memory
        # Valid operations
        # Pushes first because they are very frequent
        if 0x60 <= opcode <= 0x7f:
            stk.append(int(hexlify(ins.arg), 16))
            state.pc += opcode - 0x5f  # Move 1 byte forward for 0x60, up to 32 bytes for 0x7f
        # Arithmetic
        elif opcode < 0x10:
            if op == 'STOP':
                state.success = True
                return state
            elif op == 'ADD':
                stk.append(stk.pop() + stk.pop())
            elif op == 'SUB':
                stk.append(stk.pop() - stk.pop())
            elif op == 'MUL':
                stk.append(stk.pop() * stk.pop())
            elif op == 'DIV':
                s0, s1 = stk.pop(), stk.pop()
                stk.append(0 if s1 == 0 else s0 // s1)
            elif op == 'MOD':
                s0, s1 = stk.pop(), stk.pop()
                stk.append(0 if s1 == 0 else s0 % s1)
            elif op == 'SDIV':
                s0, s1 = utils.to_signed(stk.pop()), utils.to_signed(stk.pop())
                stk.append(0 if s1 == 0 else abs(s0) // abs(s1) *
                                             (-1 if s0 * s1 < 0 else 1))
            elif op == 'SMOD':
                s0, s1 = utils.to_signed(stk.pop()), utils.to_signed(stk.pop())
                stk.append(0 if s1 == 0 else abs(s0) % abs(s1) *
                                             (-1 if s0 < 0 else 1))
            elif op == 'ADDMOD':
                s0, s1, s2 = stk.pop(), stk.pop(), stk.pop()
                stk.append((s0 + s1) % s2 if s2 else 0)
            elif op == 'MULMOD':
                s0, s1, s2 = stk.pop(), stk.pop(), stk.pop()
                stk.append((s0 * s1) % s2 if s2 else 0)
            elif op == 'EXP':
                base, exponent = stk.pop(), stk.pop()
                stk.append(pow(base, exponent, utils.TT256))
            elif op == 'SIGNEXTEND':
                s0, s1 = stk.pop(), stk.pop()
                if s0 <= 31:
                    testbit = s0 * 8 + 7
                    if s1 & (1 << testbit):
                        stk.append(s1 | (utils.TT256 - (1 << testbit)))
                    else:
                        stk.append(s1 & ((1 << testbit) - 1))
                else:
                    stk.append(s1)
        # Comparisons
        elif opcode < 0x20:
            if op == 'LT':
                stk.append(1 if stk.pop() < stk.pop() else 0)
            elif op == 'GT':
                stk.append(1 if stk.pop() > stk.pop() else 0)
            elif op == 'SLT':
                s0, s1 = utils.to_signed(stk.pop()), utils.to_signed(stk.pop())
                stk.append(1 if s0 < s1 else 0)
            elif op == 'SGT':
                s0, s1 = utils.to_signed(stk.pop()), utils.to_signed(stk.pop())
                stk.append(1 if s0 > s1 else 0)
            elif op == 'EQ':
                stk.append(1 if stk.pop() == stk.pop() else 0)
            elif op == 'ISZERO':
                stk.append(0 if stk.pop() else 1)
            elif op == 'AND':
                stk.append(stk.pop() & stk.pop())
            elif op == 'OR':
                stk.append(stk.pop() | stk.pop())
            elif op == 'XOR':
                stk.append(stk.pop() ^ stk.pop())
            elif op == 'NOT':
                stk.append(utils.TT256M1 - stk.pop())
            elif op == 'BYTE':
                s0, s1 = stk.pop(), stk.pop()
                if s0 >= 32:
                    stk.append(0)
                else:
                    stk.append((s1 // 256 ** (31 - s0)) % 256)
        # SHA3 and environment info
        elif opcode < 0x40:
            if op == 'SHA3':
                s0, s1 = stk.pop(), stk.pop()
                mem.extend(s0, s1)
                data = utils.bytearray_to_bytestr(mem[s0: s0 + s1])
                stk.append(utils.big_endian_to_int(utils.sha3(data)))
            elif op == 'ADDRESS':
                stk.append(ctx.address)
            elif op == 'BALANCE':
                s0 = stk.pop()
                if s0 not in ctx.balance:
                    raise ExternalData('BALANCE')
                stk.append(ctx.balance[s0])
            elif op == 'ORIGIN':
                stk.append(ctx.origin)
            elif op == 'CALLER':
                stk.append(ctx.caller)
            elif op == 'CALLVALUE':
                stk.append(ctx.callvalue)
            elif op == 'CALLDATALOAD':
                s0 = stk.pop()
                stk.append(utils.bytearray_to_int(ctx.calldata[s0:s0 + 32]))
            elif op == 'CALLDATASIZE':
                stk.append(len(ctx.calldata))
            elif op == 'CALLDATACOPY':
                mstart, dstart, size = stk.pop(), stk.pop(), stk.pop()
                mem.extend(mstart, size)
                for i in range(size):
                    if dstart + i < len(ctx.calldata):
                        mem[mstart + i] = ord(ctx.calldata[dstart + i])
                    else:
                        mem[mstart + i] = 0
            elif op == 'CODESIZE':
                stk.append(len(state.code))
            elif op == 'CODECOPY':
                mstart, dstart, size = stk.pop(), stk.pop(), stk.pop()
                mem.extend(mstart, size)
                for i in range(size):
                    if dstart + i < len(state.code):
                        mem[mstart + i] = ord(state.code[dstart + i])
                    else:
                        mem[mstart + i] = 0
            elif op == 'RETURNDATACOPY':
                raise ExternalData('RETURNDATACOPY')
            elif op == 'RETURNDATASIZE':
                raise ExternalData('RETURNDATASIZE')
            elif op == 'GASPRICE':
                stk.append(ctx.gasprice)
            elif op == 'EXTCODESIZE':
                raise ExternalData('EXTCODESIZE')
            elif op == 'EXTCODECOPY':
                raise ExternalData('EXTCODECOPY')
        # Block info
        elif opcode < 0x50:
            if op == 'BLOCKHASH':
                raise ExternalData('BLOCKHASH')
            elif op == 'COINBASE':
                stk.append(ctx.coinbase)
            elif op == 'TIMESTAMP':
                stk.append(ctx.timestamp)
            elif op == 'NUMBER':
                stk.append(ctx.number)
            elif op == 'DIFFICULTY':
                stk.append(ctx.difficulty)
            elif op == 'GASLIMIT':
                stk.append(ctx.gaslimit)
        # VM state manipulations
        elif opcode < 0x60:
            if op == 'POP':
                stk.pop()
            elif op == 'MLOAD':
                s0 = stk.pop()
                mem.extend(s0, 32)
                stk.append(utils.bytes_to_int(mem[s0: s0 + 32]))
            elif op == 'MSTORE':
                s0, s1 = stk.pop(), stk.pop()
                mem.extend(s0, 32)
                mem[s0: s0 + 32] = utils.encode_int32(s1)
            elif op == 'MSTORE8':
                s0, s1 = stk.pop(), stk.pop()
                mem.extend(s0, 1)
                mem[s0] = s1 % 256
            elif op == 'SLOAD':
                s0 = stk.pop()
                stk.append(ctx.storage[s0])
            elif op == 'SSTORE':
                s0, s1 = stk.pop(), stk.pop()
                ctx.storage[s0] = s1
            elif op == 'JUMP':
                state.pc = stk.pop()
                if state.pc >= len(state.code) or not program[state.pc].name == 'JUMPDEST':
                    raise vm_exception('BAD JUMPDEST')
                continue
            elif op == 'JUMPI':
                s0, s1 = stk.pop(), stk.pop()
                if s1:
                    state.pc = s0
                    if state.pc >= len(state.code) or not program[state.pc].name == 'JUMPDEST':
                        raise vm_exception('BAD JUMPDEST')
                    continue
            elif op == 'PC':
                stk.append(state.pc - 1)
            elif op == 'MSIZE':
                stk.append(len(mem))
            elif op == 'GAS':
                stk.append(state.gas)
        # DUPn (eg. DUP1: a b c -> a b c c, DUP3: a b c -> a b c a)
        elif op[:3] == 'DUP':
            stk.append(stk[0x7f - opcode])  # 0x7f - opcode is a negative number, -1 for 0x80 ... -16 for 0x8f
        # SWAPn (eg. SWAP1: a b c d -> a b d c, SWAP3: a b c d -> d b c a)
        elif op[:4] == 'SWAP':
            # 0x8e - opcode is a negative number, -2 for 0x90 ... -17 for 0x9f
            stk[-1], stk[0x8e - opcode] = stk[0x8e - opcode], stk[-1]
        # Logs (aka "events")
        elif op[:3] == 'LOG':
            """
            0xa0 ... 0xa4, 32/64/96/128/160 + len(data) gas
            a. Opcodes LOG0...LOG4 are added, takes 2-6 stack arguments
                    MEMSTART MEMSZ (TOPIC1) (TOPIC2) (TOPIC3) (TOPIC4)
            b. Logs are kept track of during tx execution exactly the same way as suicides
               (except as an ordered list, not a set).
               Each log is in the form [address, [topic1, ... ], data] where:
               * address is what the ADDRESS opcode would output
               * data is mem[MEMSTART: MEMSTART + MEMSZ]
               * topics are as provided by the opcode
            c. The ordered list of logs in the transaction are expressed as [log0, log1, ..., logN].
            """
            depth = int(op[3:])
            mstart, msz = stk.pop(), stk.pop()
            topics = [stk.pop() for _ in range(depth)]
            mem.extend(mstart, msz)
            # Ignore external effects...
        # Create a new contract
        elif op == 'CREATE':
            raise ExternalData('CREATE')
        # Calls
        elif op in ('CALL', 'CALLCODE', 'DELEGATECALL', 'STATICCALL'):
            raise ExternalData(op)
        # Return opcode
        elif op == 'RETURN':
            s0, s1 = stk.pop(), stk.pop()
            mem.extend(s0, s1)
            state.success = True
            return state
        # Revert opcode (Metropolis)
        elif op == 'REVERT':
            s0, s1 = stk.pop(), stk.pop()
            mem.extend(s0, s1)
            return state
        # SUICIDE opcode (also called SELFDESTRUCT)
        elif op == 'SUICIDE':
            raise ExternalData('SUICIDE')

        state.pc += 1

    state.success = True
    return state


def concrete(v):
    return isinstance(v, numbers.Number)


def ctx_or_symbolic(v, ctx):
    return ctx.get(v, z3.BitVec('%s' % v, 256))


def is_false(cond):
    s = z3.Solver()
    s.add(cond)
    return s.check() == z3.unsat


def is_true(cond):
    # NOTE: This differs from `not is_false(cond)`, which corresponds to "may be true"
    return is_false(z3.Not(cond))


def addr(expr):
    return expr & (2 ** 160 - 1)


def run_symbolic(program, path, code=None, state=None, ctx=None, inclusive=False):
    # MAX_CALLDATA_SIZE = 512
    MAX_CALLDATA_SIZE = 256

    state = state or SymbolicEVMState(code=code)
    storage = state.storage
    constraints = []
    sha_constraints = dict()
    ctx = ctx or dict()
    ctx['CODESIZE-ADDRESS'] = len(code)
    calldata = z3.Array('CALLDATA', z3.BitVecSort(256), z3.BitVecSort(8))
    instruction_count = 0
    while state.pc in program:
        state.trace.append(state.pc)
        instruction_count += 1
        if not path and inclusive:
            state.success = True
            return SymbolicResult(state, constraints, sha_constraints)
        if state.pc == path[0]:
            path = path[1:]
            if not path and not inclusive:
                state.success = True
                return SymbolicResult(state, constraints, sha_constraints)

        ins = program[state.pc]
        opcode = ins.op
        op = ins.name
        stk = state.stack
        mem = state.memory
        state.gas -= ins.gas
        # Valid operations
        # Pushes first because they are very frequent
        if 0x60 <= opcode <= 0x7f:
            stk.append(int(hexlify(ins.arg), 16))
            state.pc += opcode - 0x5f  # Move 1 byte forward for 0x60, up to 32 bytes for 0x7f
        # Arithmetic
        elif opcode < 0x10:
            if op == 'STOP':
                if path:
                    raise IntractablePath()
                state.success = True
                return SymbolicResult(state, constraints, sha_constraints)
            elif op == 'ADD':
                stk.append(stk.pop() + stk.pop())
            elif op == 'SUB':
                stk.append(stk.pop() - stk.pop())
            elif op == 'MUL':
                stk.append(stk.pop() * stk.pop())
            elif op == 'DIV':
                s0, s1 = stk.pop(), stk.pop()
                if concrete(s1):
                    stk.append(0 if s1 == 0 else s0 / s1 if concrete(s0) else z3.UDiv(s0, s1))
                else:
                    stk.append(z3.If(s1 == 0, z3.BitVecVal(0, 256), z3.UDiv(s0, s1)))
            elif op == 'MOD':
                s0, s1 = stk.pop(), stk.pop()
                if concrete(s1):
                    stk.append(0 if s1 == 0 else s0 % s1)
                else:
                    stk.append(z3.If(s1 == 0, z3.BitVecVal(0, 256), z3.URem(s0, s1)))
            elif op == 'SDIV':
                s0, s1 = stk.pop(), stk.pop()
                if concrete(s0) and concrete(s1):
                    s0, s1 = utils.to_signed(s0), utils.to_signed(s1)
                    stk.append(0 if s1 == 0 else abs(s0) // abs(s1) *
                                                 (-1 if s0 * s1 < 0 else 1))
                elif concrete(s1):
                    stk.append(0 if s1 == 0 else s0 / s1)
                else:
                    stk.append(z3.If(s1 == 0, z3.BitVecVal(0, 256), s0 / s1))
            elif op == 'SMOD':
                s0, s1 = stk.pop(), stk.pop()
                if concrete(s0) and concrete(s1):
                    s0, s1 = utils.to_signed(s0), utils.to_signed(s1)
                    stk.append(0 if s1 == 0 else abs(s0) % abs(s1) *
                                                 (-1 if s0 < 0 else 1))
                elif concrete(s1):
                    stk.append(0 if s1 == 0 else z3.SRem(s0, s1))
                else:
                    stk.append(z3.If(s1 == 0, z3.BitVecVal(0, 256), z3.SRem(s0, s1)))
            elif op == 'ADDMOD':
                s0, s1, s2 = stk.pop(), stk.pop(), stk.pop()
                if concrete(s2):
                    stk.append((s0 + s1) % s2 if s2 else 0)
                else:
                    stk.append(z3.If(s2 == 0, z3.BitVecVal(0, 256), z3.URem((s0 + s1), s2)))
            elif op == 'MULMOD':
                s0, s1, s2 = stk.pop(), stk.pop(), stk.pop()
                if concrete(s2):
                    stk.append((s0 * s1) % s2 if s2 else 0)
                else:
                    stk.append(z3.If(s2 == 0, z3.BitVecVal(0, 256), z3.URem((s0 * s1), s2)))
            elif op == 'EXP':
                base, exponent = stk.pop(), stk.pop()
                if concrete(base) and concrete(exponent):
                    stk.append(pow(base, exponent, utils.TT256))
                else:
                    if concrete(base) and utils.is_pow2(base):
                        l2 = utils.log2(base)
                        stk.append(1 << (l2 * exponent))
                    else:
                        raise SymbolicError('exponentiation with symbolic exponent currently not supported :-/')
            elif op == 'SIGNEXTEND':
                s0, s1 = stk.pop(), stk.pop()
                if concrete(s0) and concrete(s1):
                    if s0 <= 31:
                        testbit = s0 * 8 + 7
                        if s1 & (1 << testbit):
                            stk.append(s1 | (utils.TT256 - (1 << testbit)))
                        else:
                            stk.append(s1 & ((1 << testbit) - 1))
                    else:
                        stk.append(s1)
                elif concrete(s0):
                    if s0 <= 31:
                        oldwidth = (s0 + 1) * 8
                        stk.append(z3.SignExt(256 - oldwidth, s1))
                    else:
                        stk.append(s1)
                else:
                    raise SymbolicError('symbolic bitwidth for signextension is currently not supported')
        # Comparisons
        elif opcode < 0x20:
            if op == 'LT':
                s0, s1 = stk.pop(), stk.pop()
                if concrete(s0) and concrete(s1):
                    stk.append(1 if s0 < s1 else 0)
                else:
                    stk.append(z3.If(z3.ULT(s0, s1), z3.BitVecVal(1, 256), z3.BitVecVal(0, 256)))
            elif op == 'GT':
                s0, s1 = stk.pop(), stk.pop()
                if concrete(s0) and concrete(s1):
                    stk.append(1 if s0 > s1 else 0)
                else:
                    stk.append(z3.If(z3.UGT(s0, s1), z3.BitVecVal(1, 256), z3.BitVecVal(0, 256)))
            elif op == 'SLT':
                s0, s1 = stk.pop(), stk.pop()
                if concrete(s0) and concrete(s1):
                    s0, s1 = utils.to_signed(s0), utils.to_signed(s1)
                    stk.append(1 if s0 < s1 else 0)
                else:
                    stk.append(z3.If(s0 < s1, z3.BitVecVal(1, 256), z3.BitVecVal(0, 256)))
            elif op == 'SGT':
                s0, s1 = stk.pop(), stk.pop()
                if concrete(s0) and concrete(s1):
                    s0, s1 = utils.to_signed(s0), utils.to_signed(s1)
                    stk.append(1 if s0 > s1 else 0)
                else:
                    stk.append(z3.If(s0 > s1, z3.BitVecVal(1, 256), z3.BitVecVal(0, 256)))
            elif op == 'EQ':
                s0, s1 = stk.pop(), stk.pop()
                if concrete(s0) and concrete(s1):
                    stk.append(1 if s0 == s1 else 0)
                else:
                    stk.append(z3.If(s0 == s1, z3.BitVecVal(1, 256), z3.BitVecVal(0, 256)))
            elif op == 'ISZERO':
                s0 = stk.pop()
                if concrete(s0):
                    stk.append(1 if s0 == 0 else 0)
                else:
                    stk.append(z3.If(s0 == 0, z3.BitVecVal(1, 256), z3.BitVecVal(0, 256)))
            elif op == 'AND':
                stk.append(stk.pop() & stk.pop())
            elif op == 'OR':
                stk.append(stk.pop() | stk.pop())
            elif op == 'XOR':
                stk.append(stk.pop() ^ stk.pop())
            elif op == 'NOT':
                stk.append(~stk.pop())
            elif op == 'BYTE':
                s0, s1 = stk.pop(), stk.pop()
                if concrete(s0):
                    if s0 >= 32:
                        stk.append(0)
                    else:
                        if concrete(s1):
                            stk.append((s1 // 256 ** (31 - s0)) % 256)
                        else:
                            v = z3.simplify(z3.Extract((31 - s0) * 8 + 7, (31 - s0) * 8, s1))
                            if z3.is_bv_value(v):
                                stk.append(v.as_long())
                            else:
                                stk.append(z3.ZeroExt(256 - 32, v))
                else:
                    raise SymbolicError('symbolic byte-index not supported')
        # SHA3 and environment info
        elif opcode < 0x40:
            if op == 'SHA3':
                s0, s1 = stk.pop(), stk.pop()
                mem.extend(s0, s1)
                mm = mem.read(s0, s1)
                if not isinstance(mm, SymRead) and all(concrete(m) for m in mm):
                    data = utils.bytearray_to_bytestr(mm)
                    stk.append(utils.big_endian_to_int(utils.sha3(data)))
                else:
                    if not isinstance(mm, SymRead):
                        sha_data = z3.simplify(z3.Concat([m if z3.is_expr(m) else z3.BitVecVal(m, 8) for m in mm]))
                        for k, v in sha_constraints.iteritems():
                            if isinstance(v, SymRead):
                                continue
                            if v.size() == sha_data.size() and is_true(v == sha_data):
                                sha = k
                                break
                        else:
                            sha = z3.BitVec('SHA3_%x' % instruction_count, 256)
                            sha_constraints[sha] = sha_data
                    else:
                        sha_data = mm
                        sha = z3.BitVec('SHA3_%x' % instruction_count, 256)
                        sha_constraints[sha] = sha_data
                    stk.append(sha)
                    # raise SymbolicError('symbolic computation of SHA3 not supported')
            elif op == 'ADDRESS':
                stk.append(ctx_or_symbolic('ADDRESS', ctx))
            elif op == 'BALANCE':
                s0 = stk.pop()
                if concrete(s0):
                    stk.append(ctx_or_symbolic('BALANCE-%x' % s0, ctx))
                elif is_true(s0 == addr(ctx_or_symbolic('ADDRESS', ctx))):
                    stk.append(ctx_or_symbolic('BALANCE-ADDRESS', ctx))
                elif is_true(s0 == addr(ctx_or_symbolic('CALLER', ctx))):
                    stk.append(ctx_or_symbolic('BALANCE-CALLER', ctx))
                else:
                    raise SymbolicError('balance of symbolic address (%s)' % str(z3.simplify(s0)))
            elif op == 'ORIGIN':
                stk.append(ctx_or_symbolic('ORIGIN', ctx))
            elif op == 'CALLER':
                stk.append(ctx_or_symbolic('CALLER', ctx))
            elif op == 'CALLVALUE':
                stk.append(ctx_or_symbolic('CALLVALUE', ctx))
            elif op == 'CALLDATALOAD':
                s0 = stk.pop()
                if not concrete(s0):
                    constraints.append(z3.ULT(s0, MAX_CALLDATA_SIZE))
                stk.append(z3.Concat([calldata[s0 + i] for i in xrange(32)]))
            elif op == 'CALLDATASIZE':
                stk.append(z3.BitVec('CALLDATASIZE', 256))
            elif op == 'CALLDATACOPY':
                mstart, dstart, size = stk.pop(), stk.pop(), stk.pop()
                if not concrete(dstart):
                    constraints.append(z3.ULT(dstart, MAX_CALLDATA_SIZE))
                if concrete(size):
                    for i in xrange(size):
                        mem[mstart + i] = calldata[dstart + i]
                else:
                    calldatasize = z3.BitVec('CALLDATASIZE', 256)
                    constraints.append(z3.UGE(calldatasize, dstart + size))
                    constraints.append(z3.ULT(size, MAX_CALLDATA_SIZE))
                    for i in xrange(MAX_CALLDATA_SIZE):
                        mem[mstart + i] = z3.If(size < i, mem[mstart + i], calldata[dstart + i])
            elif op == 'CODESIZE':
                stk.append(len(state.code))
            elif op == 'CODECOPY':
                mstart, dstart, size = stk.pop(), stk.pop(), stk.pop()
                if concrete(mstart) and concrete(dstart) and concrete(size):
                    mem.extend(mstart, size)
                    for i in range(size):
                        if dstart + i < len(state.code):
                            mem[mstart + i] = ord(state.code[dstart + i])
                        else:
                            mem[mstart + i] = 0
                else:
                    raise SymbolicError('Symbolic code index @ %s' % ins)
            elif op == 'RETURNDATACOPY':
                raise ExternalData('RETURNDATACOPY')
            elif op == 'RETURNDATASIZE':
                raise ExternalData('RETURNDATASIZE')
            elif op == 'GASPRICE':
                stk.append(ctx_or_symbolic('GASPRICE', ctx))
            elif op == 'EXTCODESIZE':
                s0 = stk.pop()
                if concrete(s0):
                    stk.append(ctx_or_symbolic('CODESIZE-%x' % s0, ctx))
                elif is_true(s0 == addr(ctx_or_symbolic('ADDRESS', ctx))):
                    stk.append(ctx_or_symbolic('CODESIZE-ADDRESS', ctx))
                elif is_true(s0 == addr(ctx_or_symbolic('CALLER', ctx))):
                    stk.append(ctx_or_symbolic('CODESIZE-CALLER', ctx))
                else:
                    raise SymbolicError('codesize of symblic address')
            elif op == 'EXTCODECOPY':
                raise ExternalData('EXTCODECOPY')
        # Block info
        elif opcode < 0x50:
            if op == 'BLOCKHASH':
                s0 = stk.pop()
                if not concrete(s0):
                    raise SymbolicError('symbolic blockhash index')
                stk.append(ctx_or_symbolic('BLOCKHASH[%d]' % s0))
            elif op == 'COINBASE':
                stk.append(ctx_or_symbolic('COINBASE', ctx))
            elif op == 'TIMESTAMP':
                stk.append(ctx_or_symbolic('TIMESTAMP', ctx))
            elif op == 'NUMBER':
                stk.append(ctx_or_symbolic('NUMBER', ctx))
            elif op == 'DIFFICULTY':
                stk.append(ctx_or_symbolic('DIFFICULTY', ctx))
            elif op == 'GASLIMIT':
                stk.append(ctx_or_symbolic('GASLIMIT', ctx))
        # VM state manipulations
        elif opcode < 0x60:
            if op == 'POP':
                stk.pop()
            elif op == 'MLOAD':
                s0 = stk.pop()
                mem.extend(s0, 32)
                mm = [mem[s0 + i] for i in xrange(32)]
                if all(concrete(m) for m in mm):
                    stk.append(utils.bytes_to_int(mem.read(s0, 32)))
                else:
                    v = z3.simplify(z3.Concat([m if not concrete(m) else z3.BitVecVal(m, 8) for m in mm]))
                    if z3.is_bv_value(v):
                        stk.append(v.as_long())
                    else:
                        stk.append(v)
            elif op == 'MSTORE':
                s0, s1 = stk.pop(), stk.pop()
                mem.extend(s0, 32)
                if concrete(s1):
                    mem.write(s0, 32, utils.encode_int32(s1))
                else:
                    for i in xrange(32):
                        m = z3.simplify(z3.Extract((31 - i) * 8 + 7, (31 - i) * 8, s1))
                        if z3.is_bv_value(m):
                            mem[s0 + i] = m.as_long()
                        else:
                            mem[s0 + i] = m
            elif op == 'MSTORE8':
                s0, s1 = stk.pop(), stk.pop()
                mem.extend(s0, 1)
                mem[s0] = s1 % 256
            elif op == 'SLOAD':
                s0 = stk.pop()

                v = z3.simplify(storage[s0])
                if z3.is_bv_value(v):
                    stk.append(v.as_long())
                else:
                    stk.append(v)
            elif op == 'SSTORE':
                s0, s1 = stk.pop(), stk.pop()
                storage[s0] = s1
            elif op == 'JUMP':
                s0 = stk.pop()
                if not concrete(s0):
                    raise SymbolicError('Symbolic jump target')
                state.pc = s0
                if state.pc >= len(state.code) or not program[state.pc].name == 'JUMPDEST':
                    raise vm_exception('BAD JUMPDEST')
                continue
            elif op == 'JUMPI':
                s0, s1 = stk.pop(), stk.pop()
                if concrete(s1):
                    if s1:
                        if not concrete(s0):
                            raise SymbolicError('Symbolic jump target')
                        state.pc = s0
                        if state.pc >= len(state.code) or not program[state.pc].name == 'JUMPDEST':
                            raise vm_exception('BAD JUMPDEST')
                        continue
                else:
                    next_target = path[0]
                    if state.pc + 1 == next_target:
                        constraints.append(s1 == 0)
                    elif concrete(s0) and s0 == next_target:
                        constraints.append(s1 != 0)
                        state.pc = s0
                        if state.pc >= len(state.code) or not program[state.pc].name == 'JUMPDEST':
                            raise vm_exception('BAD JUMPDEST')
                        continue
                    elif not concrete(s0):
                        raise SymbolicError('Symbolic jump target')
                    else:
                        raise IntractablePath()

            elif op == 'PC':
                stk.append(state.pc - 1)
            elif op == 'MSIZE':
                stk.append(len(mem))
            elif op == 'GAS':
                stk.append(z3.BitVec('GAS_%x' % instruction_count, 256))
        # DUPn (eg. DUP1: a b c -> a b c c, DUP3: a b c -> a b c a)
        elif op[:3] == 'DUP':
            stk.append(stk[0x7f - opcode])  # 0x7f - opcode is a negative number, -1 for 0x80 ... -16 for 0x8f
        # SWAPn (eg. SWAP1: a b c d -> a b d c, SWAP3: a b c d -> d b c a)
        elif op[:4] == 'SWAP':
            # 0x8e - opcode is a negative number, -2 for 0x90 ... -17 for 0x9f
            stk[-1], stk[0x8e - opcode] = stk[0x8e - opcode], stk[-1]
        # Logs (aka "events")
        elif op[:3] == 'LOG':
            """
            0xa0 ... 0xa4, 32/64/96/128/160 + len(data) gas
            a. Opcodes LOG0...LOG4 are added, takes 2-6 stack arguments
                    MEMSTART MEMSZ (TOPIC1) (TOPIC2) (TOPIC3) (TOPIC4)
            b. Logs are kept track of during tx execution exactly the same way as suicides
               (except as an ordered list, not a set).
               Each log is in the form [address, [topic1, ... ], data] where:
               * address is what the ADDRESS opcode would output
               * data is mem[MEMSTART: MEMSTART + MEMSZ]
               * topics are as provided by the opcode
            c. The ordered list of logs in the transaction are expressed as [log0, log1, ..., logN].
            """
            depth = int(op[3:])
            mstart, msz = stk.pop(), stk.pop()
            topics = [stk.pop() for _ in range(depth)]
            mem.extend(mstart, msz)
            # Ignore external effects...
        # Create a new contract
        elif op == 'CREATE':
            s0, s1, s2 = stk.pop(), stk.pop(), stk.pop()
            stk.append(addr(z3.BitVec('EXT_CREATE_%d' % instruction_count, 256)))
        # Calls
        elif op in ('CALL', 'CALLCODE', 'DELEGATECALL', 'STATICCALL'):
            if op in ('CALL', 'CALLCODE'):
                s0, s1, s2, s3, s4, s5, s6 = stk.pop(), stk.pop(), stk.pop(), stk.pop(), stk.pop(), stk.pop(), stk.pop()
            elif op == 'DELEGATECALL':
                s0, s1, s3, s4, s5, s6 = stk.pop(), stk.pop(), stk.pop(), stk.pop(), stk.pop(), stk.pop(), stk.pop()
                s2 = ctx_or_symbolic('CALLVALUE', ctx)
            elif op == 'STATICCALL':
                s0, s1, s3, s4, s5, s6 = stk.pop(), stk.pop(), stk.pop(), stk.pop(), stk.pop(), stk.pop(), stk.pop()
                s2 = 0

            if not concrete(s6):
                raise SymbolicError("Symbolic return-buffer length in %s", op)

            ostart = s5 if concrete(s5) else z3.simplify(s5)
            olen = s6

            if concrete(s1) and s1 == 4:
                logging.info("Calling precompiled identity contract")
                istart = s3 if concrete(s3) else z3.simplify(s3)
                for i in xrange(olen):
                    mem[ostart+i] = mem[istart+i]
                else:
                    raise SymbolicError("Precompiled contract %d not implemented", s1)
            else:
                for i in xrange(olen):
                    mem[ostart+i] = z3.BitVec('EXT_%d_%d'%(instruction_count, i))

            # assume call succeeded
            stk.append(1)
        elif op == 'RETURN':
            s0, s1 = stk.pop(), stk.pop()
            if concrete(s0) and concrete(s1):
                mem.extend(s0, s1)
            state.success = True
            if path:
                raise IntractablePath()
            return SymbolicResult(state, constraints, sha_constraints)
        # Revert opcode (Metropolis)
        elif op == 'REVERT':
            s0, s1 = stk.pop(), stk.pop()
            if not concrete(s0) or not concrete(s1):
                raise SymbolicError('symbolic memory index')
            mem.extend(s0, s1)
            if path:
                raise IntractablePath()
            return SymbolicResult(state, constraints, sha_constraints)
        # SUICIDE opcode (also called SELFDESTRUCT)
        elif op == 'SUICIDE':
            s0 = stk.pop()
            state.success = True
            if path:
                raise IntractablePath()
            return SymbolicResult(state, constraints, sha_constraints)

        state.pc += 1

    if path:
        raise IntractablePath()
    state.success = True
    return SymbolicResult(state, constraints, sha_constraints)


class SymbolicResult(object):
    def __init__(self, state, constraints, sha_constraints):
        self.state = state
        self.constraints = constraints
        self.sha_constraints = sha_constraints
        self.calls = 1

    def simplify(self):
        self.constraints = [z3.simplify(c) for c in self.constraints]
        self.sha_constraints = {sha: z3.simplify(sha_value) for sha, sha_value in self.sha_constraints.items()}

    def translate(self, level, storage_base):
        subst = [(self.state.storage.history[0], storage_base)]
        new_state = self.state.translate(level, subst)
        new_constraints = [add_suffix(c, level, subst) for c in self.constraints]
        new_sha_constraints = {add_suffix(sha, level, subst): (
            add_suffix(sha_value, level, subst) if not isinstance(sha_value, SymRead) else sha_value.translate(level,
                                                                                                               subst))
            for
            sha, sha_value in self.sha_constraints.items()}
        return SymbolicResult(new_state, new_constraints, new_sha_constraints)


class CombinedSymbolicResult(object):
    def __init__(self):
        self.results = []
        self._constraints = None
        self._sha_constraints = None
        self._states = None
        self.calls = 0

    def _reset(self):
        self._constraints = None
        self._sha_constraints = None
        self._states = None

    def _combine(self):
        storage_base = z3.K(z3.BitVecSort(256), z3.BitVecVal(0, 256))
        translated_results = []
        for i, result in enumerate(self.results):
            tr = result.translate(i, storage_base)
            storage_base = tr.state.storage.storage
            translated_results.append(tr)

        self._states = [tr.state for tr in translated_results]
        self._constraints = [c for tr in translated_results for c in tr.constraints]
        self._sha_constraints = {sha: sha_value for tr in translated_results for sha, sha_value in
                                 tr.sha_constraints.items()}

    def prepend(self, result):
        self.calls += 1
        self.results = [result] + self.results
        self._reset()

    @property
    def constraints(self):
        if self._constraints is None:
            self._combine()
        return self._constraints

    @property
    def sha_constraints(self):
        if self._sha_constraints is None:
            self._combine()
        return self._sha_constraints

    @property
    def states(self):
        if not self._states:
            self._combine()
        return self._states

    @property
    def state(self):
        return self.states[-1]

    def simplify(self):
        self._sha_constraints = {sha: (z3.simplify(sha_value) if not isinstance(sha_value, SymRead) else sha_value) for
                                 sha, sha_value in self.sha_constraints.items()}
        sha_ids = {e.get_id() for e in self.sha_constraints.keys()}
        self._constraints = [simplify_non_const_hashes(c, sha_ids) for c in self.constraints]


def simplify_non_const_hashes(expr, sha_ids):
    while True:
        expr = z3.simplify(expr, expand_select_store=True)
        sha_subst = get_sha_subst_non_recursive(expr, sha_ids)
        # sha_subst = get_sha_subst(expr, sha_ids)
        if not sha_subst:
            break
        expr = z3.substitute(expr, [(s, z3.BoolVal(False)) for s in sha_subst])
    return expr


def is_simple_expr(expr):
    '''
        True if expr does not contain an If, Store, or Select statement
    :param expr: the expression to check
    :return: True, iff expr does not contain If, Store, or Select
    '''

    if expr.decl().kind() in {z3.Z3_OP_ITE, z3.Z3_OP_SELECT, z3.Z3_OP_STORE}:
        return False
    else:
        return all(is_simple_expr(c) for c in expr.children())


def ast_eq(e1, e2, simplified=False):
    if not simplified:
        e1 = z3.simplify(e1)
        e2 = z3.simplify(e2)
    if e1.sort() != e2.sort():
        return False
    if e1.decl().kind() != e2.decl().kind():
        return False
    if z3util.is_expr_val(e1) and z3util.is_expr_val(e2):
        return e1.as_long() == e2.as_long()
    return all(ast_eq(c1, c2, True) for c1, c2 in zip(e1.children(), e2.children()))


def get_sha_subst(f, sha_ids, rs=None):
    if rs is None:
        f = z3.simplify(f, expand_select_store=True)
        rs = set()

    if f.decl().kind() == z3.Z3_OP_EQ and all(is_simple_expr(c) for c in f.children()):
        l, r = f.children()
        lvars, rvars = [{v.get_id() for v in get_vars_non_recursive(e, True)} for e in (l, r)]

        sha_left = bool(lvars & sha_ids)
        sha_right = bool(rvars & sha_ids)

        if sha_left and sha_right:
            # both sides use a sha-expression
            # => can be equal only if ASTs are equal
            if ast_eq(l, r):
                return rs
            else:
                return rs | {f}

        elif sha_left ^ sha_right:
            # only one side uses a sha-expression
            # => assume not equal (e.g. SHA == 5 seems unlikely)
            return rs | {f}

        else:
            # no side uses a sha-expression
            return rs

    else:

        # If we are not at at ==
        # recure to children
        for f_ in f.children():
            rs = get_sha_subst(f_, sha_ids, rs)

        return set(rs)


def get_sha_subst_non_recursive(f, sha_ids):
    todo = [z3.simplify(f, expand_select_store=True)]
    rs = set()
    seen = set()
    while todo:
        expr = todo.pop()
        if expr.get_id() in seen:
            continue
        seen.add(expr.get_id())
        if expr.decl().kind() == z3.Z3_OP_EQ and all(is_simple_expr(c) for c in expr.children()):
            l, r = expr.children()
            lvars, rvars = [{v.get_id() for v in get_vars_non_recursive(e, True)} for e in (l, r)]

            sha_left = bool(lvars & sha_ids)
            sha_right = bool(rvars & sha_ids)

            if sha_left and sha_right:
                # both sides use a sha-expression
                # => can be equal only if ASTs are equal
                if not ast_eq(l, r):
                    rs.add(expr)

            elif sha_left ^ sha_right:
                # only one side uses a sha-expression
                # => assume not equal (e.g. SHA == 5 seems unlikely)
                rs.add(expr)

        else:
            todo.extend(expr.children())

    return rs
