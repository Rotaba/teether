import datetime
import logging
import numbers
from binascii import hexlify
from collections import defaultdict

from z3 import z3, z3util

import utils
from .disassembly import disass
from .memory import UninitializedRead
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
        self.write_count = 0
        self.read_count = 0

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
            self.read_count += 1
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
            self.write_count += 1
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


class SymRead(object):
    def __init__(self, memory, start, size):
        self.memory = memory
        self.start = start
        if not concrete(start):
            self.start = z3.simplify(self.start)
        self.size = size
        if not concrete(size):
            self.size = z3.simplify(self.size)

    def translate(self, new_xid):
        sym_mem_mem = translate(self.memory.memory, new_xid)
        sym_mem = SymbolicMemory()
        sym_mem.memory = sym_mem_mem
        new_symread = SymRead(sym_mem, 0, 0)
        new_symread.start = self.start if concrete(self.start) else translate(self.start, new_xid)
        new_symread.size = self.size if concrete(self.size) else translate(self.size, new_xid)
        return new_symread


class SymbolicStorage(object):
    def __init__(self, xid):
        self.base = z3.Array('STORAGE_%d' % xid, z3.BitVecSort(256), z3.BitVecSort(256))
        self.storage = self.base

    def __getitem__(self, index):
        return self.storage[index]

    def __setitem__(self, index, v):
        self.storage = z3.Store(self.storage, index, v)

    def copy(self, new_xid):
        new_storage = SymbolicStorage(new_xid)
        new_storage.base = translate(self.base, new_xid)
        new_storage.storage = translate(self.storage, new_xid)
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
    def __init__(self, xid, code=None):
        super(SymbolicEVMState, self).__init__(code)
        self.memory = SymbolicMemory()
        self.storage = SymbolicStorage(xid)
        self.gas = z3.BitVec('GAS_%d' % xid, 256)
        self.start_balance = z3.BitVec('BALANCE_%d' % xid, 256)
        self.balance = self.start_balance

    def copy(self, new_xid):
        # Make a superficial copy of this state.
        # Effectively, only the storage is copied,
        # as this is sufficient to prepend a
        # result with this state to another call
        new_storage = self.storage.copy(new_xid)
        new_state = SymbolicEVMState(new_xid)
        new_state.storage = new_storage
        new_state.pc = self.pc
        new_state.trace = list(self.trace)
        new_state.start_balance = translate(self.start_balance, new_xid)
        new_state.balance = translate(self.balance, new_xid)
        return new_state


class LazySubstituteState(object):
    def __init__(self, state, substitutions):
        self._state = state
        self._substitutions = list(substitutions)
        self.memory = LazySubstituteMemory(self._state.memory, substitutions)
        self.stack = LazySubstituteStack(self._state.stack, substitutions)
        self.code = self._state.code
        self.pc = self._state.pc
        self.trace = self._state.trace


class LazySubstituteMemory(object):
    def __init__(self, memory, substitutions):
        self._memory = memory
        self._substitutions = substitutions

    def __getitem__(self, index):
        raise NotImplemented()


class LazySubstituteStack(object):
    def __init__(self, stack, substitutions):
        self._stack = stack
        self._substitutions = substitutions

    def __getitem__(self, index):
        r = self._stack[index]
        if isinstance(index, slice):
            return [x if concrete(x) else z3.substitute(x, self._substitutions) for x in r]
        else:
            return r if concrete(r) else z3.substitute(r, self._substitutions)


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


def ctx_or_symbolic(v, ctx, xid):
    return ctx.get(v, z3.BitVec('%s_%d' % (v, xid), 256))


def is_false(cond):
    s = z3.SolverFor("QF_ABV")
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
    if "xid" not in run_symbolic.__dict__:
        run_symbolic.xid = 0
    else:
        run_symbolic.xid += 1
    xid = run_symbolic.xid

    state = state or SymbolicEVMState(xid=xid, code=code)
    storage = state.storage
    constraints = []
    sha_constraints = dict()
    ctx = ctx or dict()
    min_timestamp = (datetime.datetime.now() - datetime.datetime(1970, 1, 1)).total_seconds()
    # make sure we can exploit it in the foreseable future
    max_timestamp = (datetime.datetime(2020, 1, 1) - datetime.datetime(1970, 1, 1)).total_seconds()
    ctx['CODESIZE-ADDRESS'] = len(code)
    calldata = z3.Array('CALLDATA_%d' % xid, z3.BitVecSort(256), z3.BitVecSort(8))
    instruction_count = 0
    state.balance += ctx_or_symbolic('CALLVALUE', ctx, xid)
    while state.pc in program:
        state.trace.append(state.pc)
        instruction_count += 1
        if not path and inclusive:
            state.success = True
            return SymbolicResult(xid, state, constraints, sha_constraints)
        if state.pc == path[0]:
            path = path[1:]
            if not path and not inclusive:
                state.success = True
                return SymbolicResult(xid, state, constraints, sha_constraints)

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
                return SymbolicResult(xid, state, constraints, sha_constraints)
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
                            sha = z3.BitVec('SHA3_%x_%d' % (instruction_count, xid), 256)
                            sha_constraints[sha] = sha_data
                    else:
                        sha_data = mm
                        sha = z3.BitVec('SHA3_%x_%d' % (instruction_count, xid), 256)
                        sha_constraints[sha] = sha_data
                    stk.append(sha)
                    # raise SymbolicError('symbolic computation of SHA3 not supported')
            elif op == 'ADDRESS':
                stk.append(ctx_or_symbolic('ADDRESS', ctx, xid))
            elif op == 'BALANCE':
                s0 = stk.pop()
                if concrete(s0):
                    stk.append(ctx_or_symbolic('BALANCE-%x' % s0, ctx, xid))
                elif is_true(s0 == addr(ctx_or_symbolic('ADDRESS', ctx, xid))):
                    stk.append(state.balance)
                elif is_true(s0 == addr(ctx_or_symbolic('CALLER', ctx, xid))):
                    stk.append(ctx_or_symbolic('BALANCE-CALLER', ctx, xid))
                else:
                    raise SymbolicError('balance of symbolic address (%s)' % str(z3.simplify(s0)))
            elif op == 'ORIGIN':
                stk.append(ctx_or_symbolic('ORIGIN', ctx, xid))
            elif op == 'CALLER':
                stk.append(ctx_or_symbolic('CALLER', ctx, xid))
            elif op == 'CALLVALUE':
                stk.append(ctx_or_symbolic('CALLVALUE', ctx, xid))
            elif op == 'CALLDATALOAD':
                s0 = stk.pop()
                if not concrete(s0):
                    constraints.append(z3.ULT(s0, MAX_CALLDATA_SIZE))
                stk.append(z3.Concat([calldata[s0 + i] for i in xrange(32)]))
            elif op == 'CALLDATASIZE':
                stk.append(z3.BitVec('CALLDATASIZE_%d' % xid, 256))
            elif op == 'CALLDATACOPY':
                mstart, dstart, size = stk.pop(), stk.pop(), stk.pop()
                if not concrete(dstart):
                    constraints.append(z3.ULT(dstart, MAX_CALLDATA_SIZE))
                if concrete(size):
                    for i in xrange(size):
                        mem[mstart + i] = calldata[dstart + i]
                else:
                    calldatasize = z3.BitVec('CALLDATASIZE_%d' % xid, 256)
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
                stk.append(ctx_or_symbolic('GASPRICE', ctx, xid))
            elif op == 'EXTCODESIZE':
                s0 = stk.pop()
                if concrete(s0):
                    stk.append(ctx_or_symbolic('CODESIZE-%x' % s0, ctx, xid))
                elif is_true(s0 == addr(ctx_or_symbolic('ADDRESS', ctx, xid))):
                    stk.append(ctx_or_symbolic('CODESIZE-ADDRESS', ctx, xid))
                elif is_true(s0 == addr(ctx_or_symbolic('CALLER', ctx, xid))):
                    stk.append(ctx_or_symbolic('CODESIZE-CALLER', ctx, xid))
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
                stk.append(ctx_or_symbolic('BLOCKHASH[%d]' % s0, xid))
            elif op == 'COINBASE':
                stk.append(ctx_or_symbolic('COINBASE', ctx, xid))
            elif op == 'TIMESTAMP':
                ts = ctx_or_symbolic('TIMESTAMP', ctx, xid)
                if not concrete(ts):
                    constraints.append(z3.UGE(ts, min_timestamp))
                    constraints.append(z3.ULE(ts, max_timestamp))
                stk.append(ts)
            elif op == 'NUMBER':
                stk.append(ctx_or_symbolic('NUMBER', ctx, xid))
            elif op == 'DIFFICULTY':
                stk.append(ctx_or_symbolic('DIFFICULTY', ctx, xid))
            elif op == 'GASLIMIT':
                stk.append(ctx_or_symbolic('GASLIMIT', ctx, xid))
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
                        if not (concrete(s0) and s0 == next_target):
                            constraints.append(s1 == 0)
                    elif concrete(s0) and s0 == next_target:
                        if state.pc + 1 != next_target:
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
            constraints.append(z3.UGE(state.balance, s0))
            state.balance -= s0
            stk.append(addr(z3.BitVec('EXT_CREATE_%d_%d' % (instruction_count, xid), 256)))
        # Calls
        elif op in ('CALL', 'CALLCODE', 'DELEGATECALL', 'STATICCALL'):
            if op in ('CALL', 'CALLCODE'):
                s0, s1, s2, s3, s4, s5, s6 = stk.pop(), stk.pop(), stk.pop(), stk.pop(), stk.pop(), stk.pop(), stk.pop()
                if op == 'CALL':
                    constraints.append(z3.UGE(state.balance, s2))
                    state.balance -= s2
            elif op == 'DELEGATECALL':
                s0, s1, s3, s4, s5, s6 = stk.pop(), stk.pop(), stk.pop(), stk.pop(), stk.pop(), stk.pop(), stk.pop()
                s2 = ctx_or_symbolic('CALLVALUE', ctx, xid)
            elif op == 'STATICCALL':
                s0, s1, s3, s4, s5, s6 = stk.pop(), stk.pop(), stk.pop(), stk.pop(), stk.pop(), stk.pop(), stk.pop()
                s2 = 0

            if not concrete(s6):
                raise SymbolicError("Symbolic return-buffer length in %s", op)

            ostart = s5 if concrete(s5) else z3.simplify(s5)
            olen = s6 if concrete(s6) else z3.simplify(s6)

            if concrete(s1) and s1 == 4:
                logging.info("Calling precompiled identity contract")
                istart = s3 if concrete(s3) else z3.simplify(s3)
                for i in xrange(olen):
                    mem[ostart + i] = mem[istart + i]
                else:
                    raise SymbolicError("Precompiled contract %d not implemented", s1)
            else:
                for i in xrange(olen):
                    mem[ostart + i] = z3.BitVec('EXT_%d_%d_%d' % (instruction_count, i, xid), 8)

            # assume call succeeded
            stk.append(1)
        elif op == 'RETURN':
            s0, s1 = stk.pop(), stk.pop()
            if concrete(s0) and concrete(s1):
                mem.extend(s0, s1)
            state.success = True
            if path:
                raise IntractablePath()
            return SymbolicResult(xid, state, constraints, sha_constraints)
        # Revert opcode (Metropolis)
        elif op == 'REVERT':
            s0, s1 = stk.pop(), stk.pop()
            if not concrete(s0) or not concrete(s1):
                raise SymbolicError('symbolic memory index')
            mem.extend(s0, s1)
            if path:
                raise IntractablePath()
            return SymbolicResult(xid, state, constraints, sha_constraints)
        # SUICIDE opcode (also called SELFDESTRUCT)
        elif op == 'SUICIDE':
            s0 = stk.pop()
            state.success = True
            if path:
                raise IntractablePath()
            return SymbolicResult(xid, state, constraints, sha_constraints)

        state.pc += 1

    if path:
        raise IntractablePath()
    state.success = True
    return SymbolicResult(xid, state, constraints, sha_constraints)


class SymbolicResult(object):
    def __init__(self, xid, state, constraints, sha_constraints):
        self.xid = xid
        self.state = state
        self.constraints = constraints
        self.sha_constraints = sha_constraints
        self.calls = 1
        self._simplified = False

    def simplify(self):
        if self._simplified:
            return
        self.constraints = [z3.simplify(c) for c in self.constraints]
        self.sha_constraints = {sha: z3.simplify(sha_value) if not isinstance(sha_value, SymRead) else sha_value for
                                sha, sha_value in self.sha_constraints.items()}
        self._simplified = True

    def copy(self):
        if "xid" not in run_symbolic.__dict__:
            run_symbolic.xid = 0
        else:
            run_symbolic.xid += 1
        new_xid = run_symbolic.xid

        self.simplify()

        new_constraints = [translate(c, new_xid) for c in self.constraints]
        new_sha_constraints = {translate(sha, new_xid): translate(sha_value, new_xid) if not isinstance(sha_value,
                                                                                                        SymRead) else sha_value.translate(
            new_xid) for sha, sha_value in
                               self.sha_constraints.items()}
        new_state = self.state.copy(new_xid)

        return SymbolicResult(new_xid, new_state, new_constraints, new_sha_constraints)


class CombinedSymbolicResult(object):
    def __init__(self):
        self.results = []
        self._constraints = None
        self._sha_constraints = None
        self._storage_constraints = None
        self._states = None
        self._idx_dict = None
        self.calls = 0

    def _reset(self):
        self._constraints = None
        self._sha_constraints = None
        self._states = None

    def _combine(self, storage=dict(), initial_balance=None):
        extra_subst = []

        storage_base = z3.K(z3.BitVecSort(256), z3.BitVecVal(0, 256))
        for k, v in storage.iteritems():
            storage_base = z3.Store(storage_base, k, v)
        for result in self.results:
            extra_subst.append((result.state.storage.base, storage_base))
            storage_base = z3.substitute(result.state.storage.storage, extra_subst)

        extra_constraints = []
        if initial_balance is not None:
            balance_base = z3.BitVecVal(initial_balance, 256)
            for result in self.results:
                extra_subst.append((result.state.start_balance, balance_base))
                balance_base = z3.substitute(result.state.balance, extra_subst)

        self._states = [LazySubstituteState(r.state, extra_subst) for r in self.results]
        self._constraints = [z3.substitute(c, extra_subst) for r in self.results for c in
                             r.constraints] + extra_constraints
        self._sha_constraints = {
            sha: z3.substitute(sha_value, extra_subst) if not isinstance(sha_value, SymRead) else sha_value for r in
            self.results for sha, sha_value in r.sha_constraints.iteritems()}

        self._idx_dict = {r.xid: i for i, r in enumerate(self.results)}

    def prepend(self, result):
        self.calls += 1
        self.results = [result] + self.results
        self._reset()

    @property
    def idx_dict(self):
        if self._idx_dict is None:
            self._combine()
        return self._idx_dict

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
    def storage_constraints(self):
        if self._storage_constraints is None:
            self._combine()
        return self._storage_constraints

    @property
    def states(self):
        if not self._states:
            self._combine()
        return self._states

    @property
    def state(self):
        return self.states[-1]

    def simplify(self):
        self._constraints = [z3.simplify(c) for c in self.constraints]
        self._sha_constraints = {sha: (z3.simplify(sha_value) if not isinstance(sha_value, SymRead) else sha_value) for
                                 sha, sha_value in self.sha_constraints.items()}


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
    import timeit
    start = timeit.default_timer()
    todo = [z3.simplify(f, expand_select_store=True)]
    rs = set()
    seen = set()
    subexprcount = 0
    while todo:
        expr = todo.pop()
        subexprcount += 1
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

    end = timeit.default_timer()
    # logging.info("get_sha_subst_non_recursive took %d microseconds (%d subexpressions)", (end-start)*1000000.0, subexprcount)
    return rs


def translate(expr, xid):
    substitutions = dict()

    def raw(s):
        return '_'.join(s.split('_')[:-1])

    for v in get_vars_non_recursive(expr):
        if v not in substitutions:
            v_name = raw(v.decl().name())
            if v.sort_kind() == z3.Z3_INT_SORT:
                substitutions[v] = z3.Int('%s_%d' % (v_name, xid))
            elif v.sort_kind() == z3.Z3_BOOL_SORT:
                substitutions[v] = z3.Bool('%s_%d' % (v_name, xid))
            elif v.sort_kind() == z3.Z3_BV_SORT:
                substitutions[v] = z3.BitVec('%s_%d' % (v_name, xid), v.size())
            elif v.sort_kind() == z3.Z3_ARRAY_SORT:
                substitutions[v] = z3.Array('%s_%d' % (v_name, xid), v.domain(), v.range())
            else:
                raise Exception('CANNOT CONVERT %s (%d)' % (v, v.sort_kind()))
    subst = substitutions.items()
    return z3.substitute(expr, subst)
