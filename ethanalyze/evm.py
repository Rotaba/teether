import numbers
from binascii import hexlify

from z3 import z3, is_false, is_true

from .memory import UninitializedRead
import utils


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
        self.memory = z3.Array('memory', z3.BitVecSort(256), z3.BitVecSort(8))

    def __getitem__(self, index):
        if isinstance(index, slice):
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
            for j, i in enumerate(xrange(index.start or 0, index.stop, index.step or 1)):
                self[i] = v[j]
        else:
            if concrete(v):
                self.memory = z3.Store(self.memory, index, v)
            elif isinstance(v, basestring):
                self.memory = z3.Store(self.memory, index, ord(v))
            else:
                self.memory = z3.Store(self.memory, index, v)

    def set_enforcing(self, enforcing=True):
        pass

    def extend(self, start, size):
        pass


class SymbolicStorage(object):
    def __init__(self):
        self.storage = z3.Array('STORAGE', z3.BitVecSort(256), z3.BitVecSort(256))
        self.history = [self.storage]

    def __getitem__(self, index):
        return self.storage[index]

    def __setitem__(self, index, v):
        self.storage = z3.Store(self.storage, index, v)
        self.history.append(self.storage)


class AbstractEVMState(object):
    def __init__(self, code=None):
        self.code = code or bytearray()
        self.pc = 0
        self.stack = Stack()
        self.memory = None
        self.trace = list()


class EVMState(AbstractEVMState):
    def __init__(self, code=None):
        super(EVMState, self).__init__(code)
        self.memory = Memory()


class SymbolicEVMState(AbstractEVMState):
    def __init__(self, code=None):
        super(SymbolicEVMState, self).__init__(code)
        self.memory = SymbolicMemory()
        self.storage = SymbolicStorage()
        self.initial_storage = self.storage


def run(program, state=None, code=None, check_initialized=False):
    state = state or EVMState(code)
    state.memory.set_enforcing(check_initialized)
    while state.pc in program:
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
                data = bytearray_to_bytestr(mem[s0: s0 + s1])
                stk.append(big_endian_to_int(sha3(data)))
            elif op == 'ADDRESS':
                raise ExternalData('ADDRESS')
            elif op == 'BALANCE':
                raise ExternalData('BALANCE')
            elif op == 'ORIGIN':
                raise ExternalData('ORIGIN')
            elif op == 'CALLER':
                raise ExternalData('CALLER')
            elif op == 'CALLVALUE':
                raise ExternalData('CALLVALUE')
            elif op == 'CALLDATALOAD':
                raise ExternalData('CALLDATALOAD')
            elif op == 'CALLDATASIZE':
                raise ExternalData('CALLDATASIZE')
            elif op == 'CALLDATACOPY':
                raise ExternalData('CALLDATACOPY')
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
                raise ExternalData('GASPRICE')
            elif op == 'EXTCODESIZE':
                raise ExternalData('EXTCODESIZE')
            elif op == 'EXTCODECOPY':
                raise ExternalData('EXTCODECOPY')
        # Block info
        elif opcode < 0x50:
            if op == 'BLOCKHASH':
                raise ExternalData('BLOCKHASH')
            elif op == 'COINBASE':
                raise ExternalData('COINBASE')
            elif op == 'TIMESTAMP':
                raise ExternalData('TIMESTAMP')
            elif op == 'NUMBER':
                raise ExternalData('NUMBER')
            elif op == 'DIFFICULTY':
                raise ExternalData('DIFFICULTY')
            elif op == 'GASLIMIT':
                raise ExternalData('GASLIMIT')
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
                raise ExternalData('SLOAD')
            elif op == 'SSTORE':
                raise ExternalData('SSTORE')
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
                raise ExternalData('GAS')
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


def run_symbolic(program, path, code=None, state=None, ctx=None):
    state = state or SymbolicEVMState(code=code)
    storage = state.storage
    constraints = []
    sha_constraints = dict()
    ctx = ctx or dict()
    calldata = z3.Array('CALLDATA', z3.BitVecSort(256), z3.BitVecSort(8))
    instruction_count = 0
    while state.pc in program:
        state.trace.append(state.pc)
        instruction_count += 1
        if state.pc == path[0]:
            path = path[1:]
            if not path:
                state.success = True
                return (state, constraints, sha_constraints)

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
                if path:
                    raise IntractablePath()
                state.success = True
                return (state, constraints, sha_constraints)
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
                if not concrete(s0) or not concrete(s1):
                    stk.append(z3.BitVec('SHA3_%x' % instruction_count, 256))
                    # raise SymbolicError('symbolic computation of SHA3 not supported')
                mem.extend(s0, s1)
                mm = mem[s0: s0 + s1]
                if all(concrete(m) for m in mm):
                    data = utils.bytearray_to_bytestr(mm)
                    stk.append(utils.big_endian_to_int(utils.sha3(data)))
                else:
                    sha_data = z3.simplify(z3.Concat([m if z3.is_expr(m) else z3.BitVecVal(m, 8) for m in mm]))
                    for k, v in sha_constraints.iteritems():
                        if v.size() == sha_data.size() and is_true(v == sha_data):
                            sha = k
                            break
                    else:
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
                elif is_true(s0 == ctx_or_symbolic('ADDRESS', ctx)):
                    stk.append(ctx_or_symbolic('BALANCE-ADDRESS', ctx))
                elif is_true(s0 == ctx_or_symbolic('CALLER', ctx)):
                    stk.append(ctx_or_symbolic('BALANCE-CALLER', ctx))
                else:
                    raise SymbolicError('balance of symblic address')
            elif op == 'ORIGIN':
                stk.append(ctx_or_symbolic('ORIGIN', ctx))
            elif op == 'CALLER':
                stk.append(ctx_or_symbolic('CALLER', ctx))
            elif op == 'CALLVALUE':
                stk.append(ctx_or_symbolic('CALLVALUE', ctx))
            elif op == 'CALLDATALOAD':
                s0 = stk.pop()
                stk.append(z3.Concat([calldata[s0 + i] for i in xrange(32)]))
            elif op == 'CALLDATASIZE':
                stk.append(z3.BitVec('CALLDATASIZE', 256))
            elif op == 'CALLDATACOPY':
                mstart, dstart, size = stk.pop(), stk.pop(), stk.pop()
                if concrete(size):
                    for i in xrange(size):
                        mem[mstart + i] = calldata[dstart + i]
                else:
                    raise SymbolicError('Symbolic memory size @ %s' % ins)
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
                    raise SymbolicError('Symbolic memory index @ %s' % ins)
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
                elif is_true(s0 == ctx_or_symbolic('ADDRESS', ctx)):
                    stk.append(ctx_or_symbolic('CODESIZE-ADDRESS', ctx))
                elif is_true(s0 == ctx_or_symbolic('CALLER', ctx)):
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
                    stk.append(utils.bytes_to_int(mem[s0: s0 + 32]))
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
                    mem[s0: s0 + 32] = utils.encode_int32(s1)
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
            raise ExternalData('CREATE')
        # Calls
        elif op in ('CALL', 'CALLCODE', 'DELEGATECALL', 'STATICCALL'):
            raise ExternalData(op)
        # Return opcode
        elif op == 'RETURN':
            s0, s1 = stk.pop(), stk.pop()
            if not concrete(s0) or not concrete(s1):
                raise SymbolicError('symbolic memory index')
            mem.extend(s0, s1)
            state.success = True
            if path:
                raise IntractablePath()
            return (state, constraints, sha_constraints)
        # Revert opcode (Metropolis)
        elif op == 'REVERT':
            s0, s1 = stk.pop(), stk.pop()
            if not concrete(s0) or not concrete(s1):
                raise SymbolicError('symbolic memory index')
            mem.extend(s0, s1)
            if path:
                raise IntractablePath()
            return (state, constraints, sha_constraints)
        # SUICIDE opcode (also called SELFDESTRUCT)
        elif op == 'SUICIDE':
            raise ExternalData('SUICIDE')

        state.pc += 1

    if path:
        raise IntractablePath()
    state.success = True
    return (state, constraints, sha_constraints)