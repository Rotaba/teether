import datetime
import logging
import numbers
from binascii import hexlify
from collections import defaultdict

import itertools
from z3 import z3, z3util

import utils

from .disassembly import disass
from .memory import UninitializedRead
from .z3_extra_util import get_vars_non_recursive

#ROMAN
# from .opcodes import opcodes, has_address_in_ins
# from binascii import unhexlify
# from project import Project
# from ...advanced_combined_call_exploit import combined_getSymbolicResults
# from teether import advanced_combined_call_exploit
# from teether.advanced_combined_call_exploit import combined_getSymbolicResults

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
    def __init__(self, trace=[], remainingpath=[]):
        self.trace = tuple(trace)
        self.remainingpath = tuple(remainingpath)


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
    #R:
    def carbon_copy(self):
        return list.copy()


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
        self.accesses = list()

    def __getitem__(self, index):
        self.accesses.append(('read', index if concrete(index) else z3.simplify(index)))
        return self.storage[index]

    def __setitem__(self, index, v):
        self.accesses.append(('write', index if concrete(index) else z3.simplify(index)))
        self.storage = z3.Store(self.storage, index, v)

    @property
    def reads(self):
        return [a for t,a in self.accesses if t=='read']

    @property
    def writes(self):
        return [a for t,a in self.accesses if t == 'write']

    @property
    def all(self):
        return [a for t,a in self.accesses]

    def copy(self, new_xid):
        new_storage = SymbolicStorage(new_xid)
        new_storage.base = translate(self.base, new_xid)
        new_storage.storage = translate(self.storage, new_xid)
        new_storage.accesses = [(t, a if concrete(a) else translate(a, new_xid)) for t,a in self.accesses]
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
        self.callee_addr = None
        self.call_args = None
        # self.shared_data = None
        self.input_value = None
        self.return_value = None

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
        self.balance = z3.substitute(state.balance, substitutions)


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
                #why extend memory? it's a SLOAD - we take a value from stack not put it in
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
                stk.append(state.pc)
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

#R:
def symb_read_from_mem(constraints, memory, symb_value, symb_ptr, symb_size, name):
    if concrete(symb_ptr) and concrete(symb_size):
        if (symb_ptr == 0 and symb_size == 0):  # just a fallback function
            # logging.info("@@@@@_EVM: %s: symb_ptr and symb_size are ZERO? they're %s and %s\n" % (name, symb_ptr, symb_size))
            # symb_to = None
            return
        logging.info("_EVM: %s: concrete(symb_ptr) and concrete(symb_size)" % name)
        for i in xrange(symb_size):
            symb_value = z3.Store(symb_value, i, z3.Select(memory, symb_ptr+i))

    # s3 and/or s4 are Symoblic
    elif not concrete(symb_ptr) and not concrete(symb_size):
        logging.info(
            "@@@@@@@_EVM: %s: not concrete(symb_ptr) and not concrete(symb_size) they're %s and %s\n" % (name, symb_ptr, symb_size))
    elif not concrete(symb_ptr):
        logging.info(
            "@$@$@$@$@_EVM: %s: not concrete(symb_ptr) it's %s\n" % (name, symb_ptr))
        # for i in xrange(symb_size):
        #     symb_value = z3.Store(symb_value, i, z3.Select(memory, symb_ptr+i))
    elif not concrete(symb_size):
        logging.info(
            "_EVM: %s: not concrete(symb_size) it's %s\n" % (name, symb_size))
        # solution = try_to_solve(constraints, symb_size)
        # if (solution != None):
        #     for i in xrange(solution.as_long()):
        #         symb_to = z3.Store(symb_to, i, z3.Select(mem_from, symb_ptr + i))
        #     logging.info(
        #             "_EVM: %s: try_to_solve result is %s\n" % (name, solution))
        # else:
        #     logging.info(
        #             "@$@$@$@$@_EVM: %s: can't solve constrains - ABORT\n" % name )
        #     return
    else:
        logging.info(
            "@@@@#$%#&^*(^*^%@#$@@@_EVM: %s: SANITY CHECK FAILED: something is wrong\n\n\n" % name)
    # return symb_to
# R:
def symb_write_to_target(constraints, symb_value, write_target, symb_ptr, symb_size, name):
    if concrete(symb_ptr) and concrete(symb_size):
        if (symb_ptr == 0 and symb_size == 0):  # just a fallback function
            # logging.info("@@@@@_EVM: %s: symb_ptr and symb_size are ZERO? they're %s and %s\n" % (name, symb_ptr, symb_size))
            # symb_to = None
            return
        logging.info("_EVM: %s: concrete(symb_ptr) and concrete(symb_size)" % name)
        for i in xrange(symb_size):
            write_target = z3.Store(write_target, symb_ptr+i, z3.Select(symb_value, i))

    # s3 and/or s4 are Symoblic
    elif not concrete(symb_ptr) and not concrete(symb_size):
        logging.info(
            "@@@@@@@_EVM: %s: not concrete(symb_ptr) and not concrete(symb_size) they're %s and %s\n" % (name, symb_ptr, symb_size))
        for i in xrange(symb_size):
            write_target = z3.Store(write_target, symb_ptr+i, z3.Select(symb_value, i))
    elif not concrete(symb_ptr):
        logging.info(
            "@$@$@$@$@_EVM: %s: not concrete(symb_ptr) it's %s\n" % (name, symb_ptr))
    elif not concrete(symb_size):
        logging.info(
            "@$@$@$@$@_EVM: %s: not concrete(symb_size) it's %s\n" % (name, symb_size))
        # solution = try_to_solve(constraints, symb_size)
        # if (solution != None):
        #     for i in xrange(solution.as_long()):
        #         mem_to = z3.Store(mem_to, symb_ptr + i, z3.Select(symb_from, i))
        #     logging.info(
        #             "_EVM: %s: try_to_solve result is %s\n" % (name, solution))
        # else:
        #     logging.info(
        #             "@$@$@$@$@_EVM: %s: can't solve constrains - ABORT\n" % (name))
        #     return

    else:
        logging.info(
            "@@@@#$%#&^*(^*^%@#$@@@_EVM: %s: SANITY CHECK FAILED: something is wrong\n\n\n" % name)
    # return mem_to

def try_to_solve(constrains, target):
    s = z3.SolverFor("QF_ABV")
    constraints_of_target = []
    if (len(constrains) == 0):
        logging.info(
            "_EVM: can't try_to_solve because there are no constraints" % target)
        return None
    for i in constrains:
        if (str(target) in str(i)):
            constraints_of_target.append(i)
    s.add(constraints_of_target)
    if s.check() != z3.sat:
        # raise IntractablePath("CHECK", "MODEL")
        logging.info(
            "@@@@#$%#&^*(^*^%@#$@@@_EVM: can't resolve the symbolic target" % target)
        return None
    else:  # check is validand there are no sha3 constrains
        m = s.model()
        if (m[target] != None):
            return m[target]
        else:
            logging.info(
                "#!@#!@!@#_EVM: Solved constrains but it's a TypeNone target = %s" % target)


# EVM func for symbolic execution
def run_symbolic(program, path, code=None, state=None, ctx=None, inclusive=False, term_on_DC=False, storage_index=None):
    # MAX_CALLDATA_SIZE = 512
    MAX_CALLDATA_SIZE = 256
    if "xid" not in run_symbolic.__dict__:
        run_symbolic.xid = 0
    elif (state): #meaning there's a state import; we can reuse the xid
        pass #dont increment xid; it's still the same call
    else:
        run_symbolic.xid += 1
    xid = run_symbolic.xid
    #init stuff for SymbolicResult class later on
    state = state or SymbolicEVMState(xid=xid, code=code)
    storage = state.storage
    constraints = []
    sha_constraints = dict()
    #??? context?
    ctx = ctx or dict()
    initial_path = path
    min_timestamp = (datetime.datetime.now() - datetime.datetime(1970, 1, 1)).total_seconds()
    # make sure we can exploit it in the foreseable future
    max_timestamp = (datetime.datetime(2020, 1, 1) - datetime.datetime(1970, 1, 1)).total_seconds()
    ctx['CODESIZE-ADDRESS'] = len(code)
    # Fixed-size elements, such as
    # the call value or the callers address are modelled using
    # fixed-size bitvector expressions, variable-length elements,
    # such as the call data, the memory, and the storage
    # are modeled using Z3s array expressions.
    calldata = z3.Array('CALLDATA_%d' % xid, z3.BitVecSort(256), z3.BitVecSort(8))
    calldatasize = z3.BitVec('CALLDATASIZE_%d' % xid, 256)

    instruction_count = 0
    state.balance += ctx_or_symbolic('CALLVALUE', ctx, xid)

    #INPUT_ RETURN ARGS check
    if (state.call_args != None):
        # check if this is run on callee
        if (state.callee_addr == 1):
            calldata = z3.Array('calleeCALLDATA_%d' % xid, z3.BitVecSort(256), z3.BitVecSort(8))
            calldatasize = z3.BitVec('calleeCALLDATASIZE_%d' % xid, 256)
            if (state.input_value != None): #sanity check
                #memory declaration looks like this; self.memory = z3.K(z3.BitVecSort(256), z3.BitVecVal(0, 8))
                #input_value comes from memory -> r_return.state.input_value = (mem[s3: s3 + s4])
                s3 = state.call_args[3]
                s4 = state.call_args[4]
                # def conc_symb_read_write(symb_from, symb_to, symb_ptr, symb_size, name):
                #althoguh this is not a read form mem; I can reuse this code with ptr = 0
                symb_write_to_target(constraints, state.input_value, calldata, 0, s4, "callee:input_value_into_calldata")

            else: #(state.call_args != None and state.callee_addr == 1)
                # R: save it to state
                logging.info("_EVM: callee: start exec on callee but NO state.INPUT_value!")

        # check if this is run on TAIL
        elif(state.callee_addr != 1): #-> # TAIL # TAIL # TAIL # TAIL # TAIL # TAIL # TAIL # TAIL # TAIL # TAIL # TAIL # TAIL # TAIL

            return_ptr = state.call_args[5]
            return_size = state.call_args[6]
            if (state.return_value != None): #i.e. theres a return and WE ACTUALLY ASKED FOR IT! -> size >0
                symb_write_to_target(constraints, state.return_value, state.memory.memory, return_ptr, return_size, "CALLER:return_value_into_memory")
            else:
                logging.info("_EVM: CALLER: tail but NO state.RETURN_value present - is this a return-less path?")
        else: #sanity check
            logging.info("!@#!@#!@!#!@#!@#!@#!@#_EVM: there's ARGS but addr is not set?!@!#!@#!#!")

    #back to normal exec
    while state.pc in program:
        state.trace.append(state.pc)
        instruction_count += 1

        #<-- original return IFs location

        ins = program[state.pc]
        opcode = ins.op
        op = ins.name
        stk = state.stack
        mem = state.memory
        state.gas -= ins.gas


        #1) premature return: if path is NOT empty AND inclusive -> then return SymbolicResult
        if (not path) and inclusive:
            logging.info("_EVM: premature termination on %s because of 1: if (not path) and inclusive): " % op)
            state.success = True
            return SymbolicResult(xid, state, constraints, sha_constraints, initial_path, path)

        #2) premature return: if PC points to top op in path, then remove top op from path
        if state.pc == path[0]: #track path progression; if PC points at BB_index; then throw index out of path
            path = path[1:] #exclude first element from path -> mark that we arrived at this BB
            #if after we updated path it's empty and we're not running inclusive; -> then return SymbolicResult
            if (not path) and not inclusive:
                logging.info("_EVM: premature termination on %s because of 2: (if after PC update path's empty and NOT inclusive" % op)
                state.success = True
                return SymbolicResult(xid, state, constraints, sha_constraints, initial_path, path)


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
                logging.info("_EVM: legit termination becasue of STOP")
                #prepend_adddr_stoage_state_chnge_check
                if (storage_index and not state.callee_addr): # if s_i was set; but we didn't bump into a SSTORe with the ight index -> then we don't have an addr set
                        return None  # no SSTORE found that altered the requested addr
                return SymbolicResult(xid, state, constraints, sha_constraints, initial_path, path)
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
                constraints.append(z3.UGE(calldatasize, s0+32))
                if not concrete(s0):
                    constraints.append(z3.ULT(s0, MAX_CALLDATA_SIZE))
                stk.append(z3.Concat([calldata[s0 + i] for i in xrange(32)]))
            elif op == 'CALLDATASIZE':
                stk.append(calldatasize)
            elif op == 'CALLDATACOPY':
                mstart, dstart, size = stk.pop(), stk.pop(), stk.pop()
                constraints.append(z3.UGE(calldatasize, dstart + size))
                if not concrete(dstart):
                    constraints.append(z3.ULT(dstart, MAX_CALLDATA_SIZE))
                if concrete(size):
                    for i in xrange(size):
                        mem[mstart + i] = calldata[dstart + i]
                else:
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
                # logging.info("*S* SLOAD value %s from slot %d" % (storage[s0], s0))
                # todo this would result in pushing concrete values; i.e. if default is 0 it would be pushed!
                #R: added the and (v.as_long() != 0) to avoid pushing a zero t ostack' better push the stroage symbolic and figure its value later!
                if z3.is_bv_value(v):
                    stk.append(v.as_long())
                else:
                    stk.append(v)
            elif op == 'SSTORE':
                s0, s1 = stk.pop(), stk.pop()
                storage[s0] = s1
                if (storage_index == s0): #if SSTORE laters the requested index; set index to flagvalue that would be checked on return
                    storage_index = float('inf')
                    #we also set the value to current state; becasue we expect this value to be an addess
                    state.callee_addr = s1
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
                next_target = path[0]
                if concrete(s1):
                    if s1:
                        if not concrete(s0):
                            raise SymbolicError('Symbolic jump target')
                        if s0 != next_target and state.pc + 1 == next_target:
                            raise IntractablePath(state.trace, path)
                        state.pc = s0
                        if state.pc >= len(state.code) or not program[state.pc].name == 'JUMPDEST':
                            raise vm_exception('BAD JUMPDEST')
                        continue
                    else:
                        if concrete(s0):
                            if state.pc + 1 != next_target and s0 == next_target:
                                raise IntractablePath(state.trace, path)
                else:
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
                        raise IntractablePath(state.trace, path)

            elif op == 'PC':
                stk.append(state.pc)
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
                s0, s1, s3, s4, s5, s6 = stk.pop(), stk.pop(), stk.pop(), stk.pop(), stk.pop(), stk.pop()
                #DG doesn't have a value argument like CALL has
                # s2 = ctx_or_symbolic('CALLVALUE', ctx, xid)
                s2 = None #to keep the same template for all calls
                #first part of CALLER exec should terminate on DC
                if(term_on_DC):
                    #we append input value and size Tupel to the end of the contrains to be used later on on combine
                    # mem.extend(s4, s3)
                    # input_value = utils.bytes_to_int(mem[s3: s3 + s4])
                    # constraints.append((input_value, s3))
                    r_return = SymbolicResult(xid, state, constraints, sha_constraints,initial_path, path)
                    # save addr for combined_exploit()
                    r_return.state.callee_addr = s1
                    r_return.state.call_args = (s0, s1, s2, s3, s4, s5, s6)



                    r_return.state.input_value = z3.K(z3.BitVecSort(256), z3.BitVecVal(0, 8))
                    symb_read_from_mem(constraints, state.memory.memory, r_return.state.input_value, s3, s4,
                                         "term_on_DC:memory_into_input_value")
                    # if concrete(s3) and concrete(s4):
                    #     #memory DEF;self.memory = z3.K(z3.BitVecSort(256), z3.BitVecVal(0, 8))
                    #     #new symb  impl
                    #     # storage_base = z3.K(z3.BitVecSort(256), z3.BitVecVal(0, 256))  # init a Z3 object
                    #     # # populate the object with the given storage
                    #     # for k, v in storage.iteritems():
                    #     #     # J:
                    #     #     storage_base = z3.Store(storage_base, k,
                    #     #                             v)  # z3 array representation - store v on index k at storage_base
                    #     #
                    #
                    #     i_v = z3.K(z3.BitVecSort(256), z3.BitVecVal(0, 8))
                    #     for i in range(0,s4): #store memoryslice into i_v
                    #         i_v = z3.Store(i_v, i, z3.Select(mem.memory, s3+i))
                    #
                    #     r_return.state.input_value = i_v
                    #     #old concrete impl
                    #     # r_return.state.input_value = (mem[s3: s3 + s4])
                    #     logging.info("_EVM:term_on_DC: premature termination because of DELEGATECALL - saved input_value")
                    # # else: # s3 and/or s4 are Symoblic
                    # elif not concrete(s3) and not concrete(s4):
                    #     logging.info("@@@@@@@_EVM:term_on_DC: CAN'T save input_value in return_r beacsue s3 AND s4 are NOT concrete\n")
                    # elif not concrete(s3):
                    #     logging.info(
                    #         "@$@$@$@$@_EVM:term_on_DC: CAN'T save input_value in return_r beacsue s3=PTR is NOT concrete\n")
                    # elif not concrete(s4):
                    #     logging.info(
                    #         "@$@$@$@$@_EVM:term_on_DC: CAN'T save input_value in return_r beacsue s4=SIZE is NOT concrete\n")
                    # else:
                    #     logging.info(
                    #         "@@@@#$%#&^*(^*^%@#$@@@_EVM:term_on_DC: SANITY CHECK FAILED: something is wrong\n\n\n")

                    return r_return
                else:
                    #continue exec, leave succsesful 1 on stack as return value
                    stk.append(1)
            elif op == 'STATICCALL':
                s0, s1, s3, s4, s5, s6 = stk.pop(), stk.pop(), stk.pop(), stk.pop(), stk.pop(), stk.pop()
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

            stk.append(z3.BitVec('CALLRESULT_%d_%d'%(instruction_count, xid), 256))
        elif op == 'RETURN':
            s0, s1 = stk.pop(), stk.pop()
            # 	return memory[offset:offset+length]
            if concrete(s0) and concrete(s1):
                mem.extend(s0, s1)
            state.success = True
            if path:
                raise IntractablePath(state.trace, path)
            # prepend_adddr_stoage_state_chnge_check
            if (storage_index and not state.callee_addr):  # if s_i was set; but we didn't bump into a SSTORe with the ight index -> then we don't have an addr set
                logging.info(
                    "_EVM: &&&&&callee: # if s_i was set; but we didn't bump into a SSTORe with the ight index -> then we don't have an addr set")
                return None  # no SSTORE found that altered the requested addr

            r_return = SymbolicResult(xid, state, constraints, sha_constraints, initial_path, path)
            if (state.callee_addr == 1): #it's callee
                # if concrete(s0) and concrete(s1):
                # #     r_return.state.return_value = (mem[s0: s0 + s1])
                # #     logging.info("_EVM: callee: legit termination because of RETURN ; saved RETURN_value: %s ..." % str(mem[s0: s0 + s1])[:10])
                # # else:
                # #     logging.info("$$$$$$$$$$$$$_EVM: Can't save a return_value! becasue it's symbolic? %s ... $$$$$$$$$$$$$$$$$$" % str(mem[s0: s0 + s1])[:10])
                #

                r_return.state.return_value = z3.K(z3.BitVecSort(256), z3.BitVecVal(0, 8))
                symb_read_from_mem(constraints, state.memory.memory, r_return.state.return_value, s0, s1,
                                 "callee: RETURN :memory_into_return_value")

            #         for i in range(0, s1):  # store memoryslice into i_v
            #             r_v = z3.Store(r_v, i, z3.Select(mem.memory, s0 + i))
            #
            #         r_return.state.return_value = r_v
            #         # old concrete impl
            #         # r_return.state.return_value = (mem[s3: s3 + s4])
            #         logging.info("_EVM:term_on_DC: premature termination because of RETURN ; saved RETURN_value")
            #     # else:  # s3 and/or s4 are Symoblic
            #     elif not concrete(s0) and not concrete(s1):
            #         logging.info(
            #             "@@@@@@@_EVM:RETURN: CAN'T save return_value in return_r beacsue s0 AND s1 are NOT concrete\n")
            #     elif not concrete(s0):
            #         logging.info(
            #             "@$@$@$@$@_EVM:RETURN: CAN'T save return_value in return_r beacsue s0=PTR is NOT concrete\n")
            #     elif not concrete(s1):
            #         logging.info(
            #             "@$@$@$@$@_EVM:RETURN: CAN'T save return_value in return_r beacsue s1=SIZE is NOT concrete\n")
            #     else:
            #         logging.info(
            #             "@@@@#$%#&^*(^*^%@#$@@@_EVM:term_on_DC: SANITY CHECK FAILED: something is wrong\n\n\n")
            # else:
            #     logging.info("_EVM: CALLER: legit termination because of RETURN")

            return r_return


            # if (state.callee_addr == 1 and ): #it's a callee returning to CALLER
            #     if concrete(utils.bytes_to_int(mem[s0: s0 + s1])):
            #         r_return.state.return_value = utils.bytes_to_int(mem[s0: s0 + s1])
            #     else:
            #         #TODO symbolic return values :|
            #         logging.info("_EVM: mem[s0: s0 + s1] for return_value is NOT concrete!!! can't pass it along!")
            # logging.info("_EVM: legit return becasue of RETURN")
            # return r_return

        # Revert opcode (Metropolis)
        elif op == 'REVERT':
            s0, s1 = stk.pop(), stk.pop()
            if not concrete(s0) or not concrete(s1):
                raise SymbolicError('symbolic memory index')
            mem.extend(s0, s1)
            if path:
                raise IntractablePath(state.trace, path)
            logging.info("_EVM: $$$$$$$$$$$$ REVERT!!! this will roll back all changes and then terminate")
            return SymbolicResult(xid, state, constraints, sha_constraints, initial_path, path)
        # SUICIDE opcode (also called SELFDESTRUCT)
        elif op == 'SUICIDE':
            s0 = stk.pop()
            state.success = True
            if path:
                raise IntractablePath(state.trace, path)
            logging.info("_EVM: s0=addr POP-ed, legit termination because of a SUICIDE - this should terminates the whole execution!")
            return SymbolicResult(xid, state, constraints, sha_constraints, initial_path, path)

        state.pc += 1

        #END OF WHILE LOOP

    if path:
        raise 1(state.trace, path)
    state.success = True
    logging.info("_EVM: Illegal termination! - end of EVM whole loop!!!!")
    logging.info("_EVM: Illegal termination! - end of EVM whole loop!!!!")
    logging.info("_EVM: Illegal termination! - end of EVM whole loop!!!!")
    return SymbolicResult(xid, state, constraints, sha_constraints, initial_path, path)


class SymbolicResult(object):
    def __init__(self, xid, state, constraints, sha_constraints, initial_path, path_left):
        self.xid = xid
        self.state = state
        self.constraints = constraints
        self.sha_constraints = sha_constraints
        #the number of calls needed? i.e. 3 in the paper?
        self.calls = 1
        self._simplified = False
        self.storage_info = StorageInfo(self)
        self.initial_path = initial_path
        # R: we're adding a path to keep track of head-tail to avoid sticking the wrong head on the wrong tail!
        self.path_left = path_left




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
        new_initial_path = self.initial_path
        #R:
        new_path_left = self.path_left

        return SymbolicResult(new_xid, new_state, new_constraints, new_sha_constraints, new_initial_path, new_path_left)

    def may_read_from(self, other):
        return self.storage_info.may_read_from(other.storage_info)



class CombinedSymbolicResult(object):
    # encapsulates contract and VM state after executing multiple transactions (n state-changing + 1 critical).
    def __init__(self):
        self.results = []
        self._constraints = None
        self._sha_constraints = None
        self._states = None
        self._idx_dict = None
        self.calls = 0

    def _reset(self):
        self._constraints = None
        self._sha_constraints = None
        self._states = None

    def _combine(self, storage=dict(), initial_balance=None):
        # _combine does the main work in alpha-renaming etc

        # UPDATE storage
        extra_subst = []
        storage_base = z3.K(z3.BitVecSort(256), z3.BitVecVal(0, 256))         #init a Z3 object
        #populate the object with the given storage
        for k, v in storage.iteritems():
            #J:
            storage_base = z3.Store(storage_base, k, v) #z3 array representation - store v on index k at storage_base
            #logging.info("evm.CombinedSymbolicResult.combine(); " + z3.Select(storage_base,k) )
        #go over the given results starting with first in chronological order
        for result in self.results:
            extra_subst.append((result.state.storage.base, storage_base)) #
            #Substitute every occurrence of storage in the expression with extra_subst. = ALPHA RENAMING
            storage_base = z3.substitute(result.state.storage.storage, extra_subst)

        #UPDATE balance
        if initial_balance is not None:
            balance_base = z3.BitVecVal(initial_balance, 256)
        else:
            balance_base = None
        for result in self.results:
            if balance_base is not None: # if initial_balance is not None, then we need to adjust
                extra_subst.append((result.state.start_balance, balance_base))
                balance_base = z3.substitute(result.state.balance, extra_subst)
            else: #if initial_balance IS None, thne take from result
                balance_base = result.state.balance

        #now...
        extra_constraints = []
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

    def merge_results(self, storage=dict(), initial_balance=None):
        # merge should be able to concatanate head_callee_tail into one SR that represents the whole exec results of the whole call

        # UPDATE storage
        extra_subst = []
        storage_base = z3.K(z3.BitVecSort(256), z3.BitVecVal(0, 256))         #init a Z3 object
        #populate the object with the given storage
        for k, v in storage.iteritems():
            #J:
            storage_base = z3.Store(storage_base, k, v) #z3 array representation - store v on index k at storage_base
            #logging.info("evm.CombinedSymbolicResult.combine(); " + z3.Select(storage_base,k) )
        #go over the given results starting with first in chronological order
        for result in self.results:
            extra_subst.append((result.state.storage.base, storage_base)) #
            #Substitute every occurrence of storage in the expression with extra_subst. = ALPHA RENAMING
            storage_base = z3.substitute(result.state.storage.storage, extra_subst)

        #UPDATE balance
        balance_base = None
        if initial_balance is not None:
            balance_base = z3.BitVecVal(initial_balance, 256)
        else:
            balance_base = None
        for result in self.results:
            if balance_base is not None: # if initial_balance is not None, then we need to adjust
                extra_subst.append((result.state.start_balance, balance_base))
                balance_base = z3.substitute(result.state.balance, extra_subst)
            else: #if initial_balance IS None, thne take from result
                balance_base = result.state.balance

        # R: stack constrains and storage_info for a "choeseive" execution result
        for result in self.results[:-1]:
            #append to last result all constrains from begining to end-1
            self.results[-1].constraints[:0] = (result.constraints) #[:0] used as a prepend-extend!!!
            #merge storage_info
            self.results[-1].storage_info.si_merge(result.storage_info)

        #R:
        r_r = self.results[-1]
        ret_result = SymbolicResult(r_r.xid, r_r.state, r_r.constraints, r_r.sha_constraints, r_r.initial_path, r_r.path_left)
        # todo add the storage and balance from above;
        # ret_result.state.balance = balance_base
        # ret_result.state.storage = storage_base

        # if (self.results[-1].state.callee_addr == 1):#WORNG: WE ACTUALLY WANT STACK FROM CALLEE!!!!
        #     ret_result.state.stack = self.results[-2].state.stack #if it's the calle; we dont actually want it's stack - reather the stack form head
        #there's a sanity check on attmet_exploit that checks for the top element on stack to see if CC actually happens on Attacker addr; so we need ot keep latest stack as result
        # ret_result.state.stack = self.results[-1].state.stack
        # ret_result.storage_info = self.results[-1].storage_info

        return ret_result

    def merge_prepend(self, result):
        # self.calls += 1
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
    def states(self):
        if not self._states:
            self._combine()
        return self._states

    @property
    def state(self):
        return self.states[-1]

    def simplify(self):
        self._constraints = [z3.simplify(c) for c in self.constraints]
        #R: rewrite above line to debbug
        # ret_list = []
        # for c in self.constraints:
        #     z_simp = z3.simplify(c)
        #     ret_list.append(z_simp)
        # self._constraints = ret_list
        #back to J
        self._sha_constraints = {sha: (z3.simplify(sha_value) if not isinstance(sha_value, SymRead) else sha_value) for
                                 sha, sha_value in self.sha_constraints.items()}


class StorageInfo(object):
    def __init__(self, result):
        self.result = result
        self._vars = dict()
        self.concrete_reads = set()
        self.concrete_writes = set()
        self.symbolic_reads = set()
        self.symbolic_writes = set()
        self.symbolic_hash_reads = set()
        self.symbolic_hash_writes = set()
        for addr in set(result.state.storage.reads):
            if concrete(addr):
                self.concrete_reads.add(addr)
            else:
                x_vars = get_vars_non_recursive(addr, True)
                self._vars[addr] = x_vars
                if set(x_vars) & set(result.sha_constraints.keys()):
                    self.symbolic_hash_reads.add(addr)
                else:
                    self.symbolic_reads.add(addr)
        for addr in set(result.state.storage.writes):
            if concrete(addr):
                self.concrete_writes.add(addr)
            else:
                x_vars = get_vars_non_recursive(addr, True)
                self._vars[addr] = x_vars
                if set(x_vars) & set(result.sha_constraints.keys()):
                    self.symbolic_hash_writes.add(addr)
                else:
                    self.symbolic_writes.add(addr)

    def may_read_from(self, other):
        #30.01.19; example
        # if not caller_DC_r.may_read_from(suicide_r):
        if not self.symbolic_reads and not other.symbolic_writes:
            # no side has a non-hash-based symbolic access
            # => only concrete accesses can intersect
            # (or hash-based accesses, which we will check later)
            if self.concrete_reads & other.concrete_writes:
                return True
        else:
            # at least one side has a non-hash-based symbolic access
            # => if there is at least one concrete or symbolic access
            # on the other side, the two could be equal
            # (otherwise we have to look at hash-based accesses, see below)
            if ((self.symbolic_reads or self.concrete_reads or self.symbolic_hash_reads) and
                (other.symbolic_writes or other.concrete_writes or other.symbolic_hash_writes)):
                return True

        if self.symbolic_hash_reads and other.symbolic_hash_writes:
            for a,b in itertools.product(self.symbolic_hash_reads, other.symbolic_hash_writes):
                if not ast_eq(a,b):
                    continue
                hash_a = list(self._vars[a] & set(self.result.sha_constraints.keys()))
                hash_b = list(other._vars[b] & set(other.result.sha_constraints.keys()))
                if len(hash_a) != 1 or len(hash_b) != 1:
                    # multiple hashes on either side
                    # => assume they could be equal
                    return True
                # only one hash on either side
                # => check whether these two can actually be equal
                d_a = self.result.sha_constraints[hash_a[0]]
                d_b = other.result.sha_constraints[hash_b[0]]
                if isinstance(d_a, SymRead) or isinstance(d_b, SymRead):
                    return True
                if d_a.size() == d_b.size():
                    return True

        # at this point, we have checked every possible combination
        # => no luck this time
        return False

    def si_merge(self,other_storage_info):
        # |= works as as self.self = self.set.union(other.set)
        self.concrete_reads |= other_storage_info.concrete_reads
        self.concrete_writes |= other_storage_info.concrete_writes
        self.symbolic_reads |= other_storage_info.symbolic_reads
        self.symbolic_writes |= other_storage_info.symbolic_writes
        self.symbolic_hash_reads |= other_storage_info.symbolic_hash_reads
        self.symbolic_hash_writes |= other_storage_info.symbolic_hash_writes

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
