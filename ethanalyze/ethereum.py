# coding: utf-8

from z3 import *
from binascii import hexlify, unhexlify
from collections import defaultdict, deque
import numbers
import logging
import utils
from intrange import Range
from opcodes import *


class Instruction(object):
    def __init__(self, addr, op, arg=None):
        opinfo = opcodes[op]
        len = (op - 0x5f) + 1 if 0x60 <= op <= 0x7f else 1
        self.addr = addr
        self.next_addr = self.addr + len
        self.op = op
        self.name = opinfo[0]
        self.arg = arg
        self.ins = opinfo[1]
        self.outs = opinfo[2]
        self.delta = self.outs - self.ins
        self.bb = None

    def __str__(self):
        return '(%5d) %4x:\t%02x\t-%d +%d = %d\t%s%s' % (
            self.addr, self.addr, self.op, self.ins, self.outs, self.delta, self.name,
            '(%d) %s' % (int(hexlify(self.arg), 16), '\t%s' % hexlify(self.arg)) if self.arg else '')

    def __repr__(self):
        return str(self)


class BB(object):
    def __init__(self, ins):
        self.ins = ins
        for i in ins:
            i.bb = self
        self.start = self.ins[0].addr
        self.pred = set()
        self.succ = set()
        self.succ_addrs = set()
        self.jump_resolved = False

    def _find_jump_target(self):
        if len(self.ins) >= 2 and 0x60 <= self.ins[-2].op <= 0x71:
            self.jump_resolved = True
            return int(hexlify(self.ins[-2].arg), 16)
        else:
            return None

    def get_succ_addrs_full(self):
        new_succ_addrs = set()
        if not self.jump_resolved:
            bs = backward_slice(self.ins[-1], [0])
            for b in bs:
                if 0x60 <= b[-1].op <= 0x7f:
                    succ_addr = int(hexlify(b[-1].arg), 16)
                    if not succ_addr in self.succ_addrs:
                        self.succ_addrs.add(succ_addr)
                        new_succ_addrs.add(succ_addr)
                else:
                    p = slice_to_program(b)
                    try:
                        succ_addr = run(p, check_initialized=True).stack.pop()
                        if not succ_addr in self.succ_addrs:
                            self.succ_addrs.add(succ_addr)
                            new_succ_addrs.add(succ_addr)
                    except ExternalData as e:
                        # logging.exception('WARNING, COULD NOT EXECUTE SLICE', repr(e))
                        pass
                    except UninitializedRead as e:
                        # logging.exception('WARNING, COULD NOT EXECUTE SLICE', repr(e))
                        pass
        return (self.succ_addrs, new_succ_addrs)

    def get_succ_addrs(self):
        if self.ins[-1].op in (0x56, 0x57):
            jump_target = self._find_jump_target()
            if jump_target:
                self.succ_addrs.add(jump_target)
        else:
            self.jump_resolved = True
        if self.ins[-1].op not in (0x00, 0x56, 0xf3, 0xfd, 0xfe, 0xff):
            fallthrough = self.ins[-1].next_addr
            if fallthrough:
                self.succ_addrs.add(fallthrough)
        return self.succ_addrs

    def __str__(self):
        s = 'BB @ %x' % self.start
        if self.pred:
            s += '\n'
            s += '\n'.join('%x ->' % pred.start for pred in self.pred)
        s += '\n'
        s += '\n'.join(str(ins) for ins in self.ins)
        if self.succ:
            s += '\n'
            s += '\n'.join(' -> %x' % succ.start for succ in self.succ)
        return s

    def __repr__(self):
        return str(self)


class CFG(object):
    def __init__(self, bbs, fix_xrefs=True):
        self.bbs = sorted(bbs, key=lambda bb: bb.start)
        self._bb_at = {bb.start: bb for bb in self.bbs}
        if fix_xrefs:
            self._xrefs()

    def _xrefs(self):
        self._easy_xrefs()
        self._hard_xrefs()

    def _easy_xrefs(self):
        for pred in self.bbs:
            for succ_addr in pred.get_succ_addrs():
                if succ_addr and succ_addr in self._bb_at:
                    succ = self._bb_at[succ_addr]
                    pred.succ.add(succ)
                    succ.pred.add(pred)

    def _hard_xrefs(self):
        new_link = True
        links = set()
        while new_link:
            new_link = False
            for pred in self.bbs:
                if not pred.jump_resolved:
                    # only interested in jump-target
                    succ_addrs, new_succ_addrs = pred.get_succ_addrs_full()
                    for succ_addr in new_succ_addrs:
                        if not succ_addr in self._bb_at:
                            logging.warn(
                                'WARNING, NO BB @ %x (possible successor of BB @ %x)' % (succ_addr, pred.start))
                            continue
                        succ = self._bb_at[succ_addr]
                        pred.succ.add(succ)
                        succ.pred.add(pred)
                        if not (pred.start, succ.start) in links:
                            new_link = True
                            links.add((pred.start, succ.start))

    def __str__(self):
        return '\n\n'.join(str(bb) for bb in self.bbs)


class InconsistentRange(Exception):
    pass


class IllegalInstruction(Exception):
    pass


class ArgumentTooShort(Exception):
    pass


class ExternalData(Exception):
    pass


class UninitializedRead(Exception):
    def __init__(self, index, *args):
        super(UninitializedRead, self).__init__(*args)
        if isinstance(index, slice):
            self.start = index.start or 0
            self.end = index.stop
        else:
            self.start = index
            self.end = index + 1

    def __repr__(self):
        return '%s from: %d to %d' % (super(UninitializedRead, self).__repr__(), self.start, self.end)

    def __str__(self):
        return '%s from: %d to %d' % (super(UninitializedRead, self).__repr__(), self.start, self.end)


class SymbolicError(Exception):
    pass


class IntractablePath(Exception):
    pass


class vm_exception(Exception):
    pass


def disass(code, i=0):
    while i < len(code):
        loc = i
        op = ord(code[i])
        arg = None
        inslen = 1
        if not op in opcodes:
            break
            # raise IllegalInstruction('%02x at %d'%(op, i))
        if 0x60 <= op <= 0x7f:
            arglen = op - 0x5f
            inslen += arglen
            arg = code[i + 1:i + 1 + arglen]
            if len(arg) < arglen:
                raise ArgumentTooShort
            i += arglen
        i += 1
        yield Instruction(loc, op, arg)
        # End basic block on STOP, JUMP, JUMPI, RETURN, REVERT, RAISE, or if the following instruction is a JUMPDEST
        if op in (0x00, 0x56, 0x57, 0xf3, 0xfd, 0xfe) or (i < len(code) and ord(code[i]) == 0x5b):
            break


def filter_ins(cfg, names):
    if isinstance(names, basestring):
        names = [names]
    return [ins for bb in cfg.bbs for ins in bb.ins if ins.name in names]


def generate_BBs(code):
    fallthrough_locs = [i + 1 for i, c in enumerate(code) if ord(c) == 0x57]
    jumpdest_locs = [i for i, c in enumerate(code) if ord(c) == 0x5b]
    leader_candidates = {0} | set(fallthrough_locs) | set(jumpdest_locs)
    for l in sorted(leader_candidates):
        try:
            instructions = list(disass(code, l))
            if instructions:
                yield BB(instructions)
        except:
            continue


def generate_BBs_recursive(code):
    resolve_later = []
    bbs = dict()
    todo = deque([(None, 0)])
    while True:
        if not todo:
            new_links = False
            for bb in resolve_later:
                _, new_succs = bb.get_succ_addrs_full()
                for s in new_succs:
                    new_links = True
                    todo.append((bb.start, s))
            if not new_links:
                break
        p, i = todo.popleft()
        pred = bbs[p] if not p is None else None

        if i in bbs:
            bb = bbs[i]
        else:
            # logging.info(hex(i))
            if i >= len(code):
                # logging.info('Jumptarget outside of code???')
                # logging.info(p, i)
                continue

            if pred and i != pred.ins[-1].next_addr and ord(code[i]) != 0x5b:
                # logging.info('WARNING, ILLEGAL JUMP-TARGET %x for BB @ %x'%(i, pred.start))
                continue

            instructions = list(disass(code, i))
            if not instructions:
                continue

            bb = BB(instructions)
            bbs[bb.start] = bb
            for s in bb.get_succ_addrs():
                # logging.info('Link from %x to %x', bb.start, s)
                todo.append((bb.start, s))
            if not bb.jump_resolved:
                resolve_later.append(bb)

        if pred:
            if p != pred.start or i != bb.start:
                logging.info('WEIRD SHIT')
                logging.info('p=%x, i=%x, pred=%x, bb=%x' % (p, i, pred.start, bb.start))
                pass
            bb.pred.add(pred)
            pred.succ.add(bb)

    return bbs.values()


def slice_to_program(s):
    pc = 0
    program = {}
    for ins in s:
        program[pc] = ins
        pc += ins.next_addr - ins.addr
    return program


def backward_slice(ins, taint_args=None, memory_info=None):
    def adjust_stack(backward_slice, stack_delta):
        if stack_delta > 0:
            backward_slice.extend(Instruction(0x0, 0x63, '\xde\xad\xc0\xde') for i in xrange(abs(stack_delta)))
        elif stack_delta < 0:
            backward_slice.extend(Instruction(0x0, 0x50) for i in xrange(abs(stack_delta)))

    startins = ins
    if ins.ins == 0:
        return []
    if taint_args:
        taintmap = set((ins.ins - 1) - i for i in taint_args)
    else:
        taintmap = set(xrange(ins.ins))
    if memory_info and ins in memory_info:
        memory_taint = memory_info[ins].reads
    else:
        memory_taint = Range()
    stacksize = ins.ins
    backward_slice = []
    todo = deque()
    stack_delta = 0
    stack_underflow = 0
    bb = ins.bb
    idx = bb.ins.index(ins)
    loops = defaultdict(int)
    todo.append((stacksize, stack_delta, taintmap, backward_slice, bb.ins[:idx], bb.pred, loops))
    results = []
    limit = 100000
    loop_limit = 2
    while todo and limit > 0:
        limit -= 1
        stacksize, stack_delta, taintmap, backward_slice, instructions, preds, loops = todo.popleft()
        for ins in instructions[::-1]:
            ##logging.info(ins)
            ##logging.info('\t%d | %d | %s'%(stacksize, stack_delta, ', '.join(map(str,sorted(taintmap)))))
            slice_candidate = False
            if taintmap and stacksize - ins.outs <= max(taintmap):
                slice_candidate = True
            if memory_info and ins in memory_info and memory_info[ins].writes & memory_taint:
                slice_candidate = True
            if slice_candidate:
                add_to_slice = False
                if 0x80 <= ins.op <= 0x8f:  # Special handling for DUP
                    if stacksize - 1 in taintmap:
                        add_to_slice = True
                        in_idx = ins.op - 0x7f
                        taintmap.remove(stacksize - 1)
                        taintmap.add((stacksize - 1) - in_idx)
                elif 0x90 <= ins.op <= 0x9f:  # Special handling for SWAP
                    in_idx = ins.op - 0x8f
                    if stacksize - 1 in taintmap or (stacksize - 1) - in_idx in taintmap:
                        add_to_slice = True
                        if stacksize - 1 in taintmap and (stacksize - 1) - in_idx in taintmap:
                            # both tainted => taint does not change
                            pass
                        elif stacksize - 1 in taintmap:
                            taintmap.remove(stacksize - 1)
                            taintmap.add((stacksize - 1) - in_idx)
                        elif (stacksize - 1) - in_idx in taintmap:
                            taintmap.remove((stacksize - 1) - in_idx)
                            taintmap.add(stacksize - 1)
                else:  # assume entire stack is affected otherwise
                    add_to_slice = True
                    taintmap -= set(xrange(stacksize - ins.outs, stacksize))
                    taintmap |= set(xrange(stacksize - ins.outs, stacksize - ins.delta))

                if add_to_slice:
                    adjust_stack(backward_slice, stack_delta)
                    stack_delta = -ins.delta
                    backward_slice.append(ins)
                    stack_underflow = min(stack_underflow, stacksize - ins.outs)
                    if memory_info and ins in memory_info:
                        ins_info = memory_info[ins]
                        memory_taint = memory_taint - ins_info.writes + ins_info.reads

            stacksize -= ins.delta
            # no taint left? then our job here is done
            if not taintmap and not memory_taint:
                if stack_underflow < 0:
                    adjust_stack(backward_slice, -stack_underflow)
                if stacksize > 0:
                    adjust_stack(backward_slice, stacksize)
                results.append(backward_slice[::-1])
                break

            if taintmap and stacksize < max(taintmap):
                # logging.info('GRAAAAAA')
                pass
            stack_delta += ins.delta

        else:
            if not preds:
                # logging.info('WARNING, missing predecessor for current slice (%x)'%(startins.addr))
                if ins:
                    # logging.info('Last checked address: %x'%ins.addr)
                    pass
                    # logging.info('Slice so far:')
                    # logging.info('\n'.join('\t%s'%i for i in backward_slice[::-1]))
                    # logging.info('')
            for p in preds:
                if loops[p] < loop_limit:
                    new_loops = defaultdict(int, loops)
                    new_loops[p] += 1
                    todo.append((stacksize, stack_delta, set(taintmap), list(backward_slice), p.ins, p.pred, new_loops))
    return results


class MemoryInfo(object):
    def __init__(self, reads, writes):
        self.reads = reads
        self.writes = writes


def get_memory_info(ins, code, memory_infos=None):
    targets = []

    read = False
    write = False

    if ins.name in memory_reads:
        read = True
        read_offset_info, read_size_info = memory_reads[ins.name]
        if read_offset_info < 0:
            targets.append(-1 - read_offset_info)
        if read_size_info < 0:
            targets.append(-1 - read_size_info)
    if ins.name in memory_writes:
        write = True
        write_offset_info, write_size_info = memory_writes[ins.name]
        if write_offset_info < 0:
            targets.append(-1 - write_offset_info)
        if write_size_info < 0:
            targets.append(-1 - write_size_info)

    if not read and not write:
        return None

    bs = backward_slice(ins, targets, memory_infos)

    read_range = None
    write_range = None
    for b in bs:
        try:
            state = run(slice_to_program(b), EVMState(code=code), check_initialized=True)
        except UninitializedRead as e:
            raise e
        except ExternalData as e:
            raise e
        if read:
            read_offset = state.stack[read_offset_info] if read_offset_info < 0 else read_offset_info
            read_size = state.stack[read_size_info] if read_size_info < 0 else read_size_info
            new_range = Range(read_offset, read_offset + read_size)
            if read_range is None:
                read_range = new_range
            elif read_range != new_range:
                raise InconsistentRange()
        if write:
            write_offset = state.stack[write_offset_info] if write_offset_info < 0 else write_offset_info
            write_size = state.stack[write_size_info] if write_size_info < 0 else write_size_info
            new_range = Range(write_offset, write_offset + write_size)
            if write_range is None:
                write_range = new_range
            elif write_range != new_range:
                raise InconsistentRange()
    return MemoryInfo(read_range or Range(), write_range or Range())


def resolve_all_memory(cfg, code):
    # logging.info(to_dot(cfg))
    memory_infos = dict()
    resolve_later = deque(
        ins for bb in cfg.bbs for ins in bb.ins if ins.name in memory_reads or ins.name in memory_writes)
    todo = deque()
    progress = True
    while todo or (progress and resolve_later):
        if not todo:
            todo = resolve_later
            resolve_later = deque()
            progress = False
        ins = todo.popleft()
        try:
            mi = get_memory_info(ins, code, memory_infos)
            if mi:
                progress = True
                memory_infos[ins] = mi
        except Exception as e:
            resolve_later.append(ins)
    return memory_infos


def extract_contract_code(code, fname=''):
    icfg = CFG(generate_BBs_recursive(code), fix_xrefs=True)
    from datetime import datetime
    with open('./cfg%s-%s.dot' % (
                '-' + fname if fname else fname, str(datetime.now()).replace(' ', '-').replace(':', '')),
              'w') as outfile:
        outfile.write(to_dot(icfg))
    returns = filter_ins(icfg, 'RETURN')
    memory_infos = resolve_all_memory(icfg, code)
    for r in returns:
        if not r in memory_infos:
            continue
        rmi = memory_infos[r].reads
        if len(rmi.points) != 2:
            continue
        (start, _), (stop, _) = rmi.points
        bs = backward_slice(r, memory_info=memory_infos)
        for b in bs:
            try:
                state = run(slice_to_program(b), EVMState(code=code))
                return str(state.memory[start:stop])
            except:
                pass
    return None


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
            ##logging.info('Slice was %s, initialized = %s'%(index, 'Yes' if initialized else 'No'))
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
        # logging.info('Read from symbolic memory at position',index)
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
        # logging.info('Write to symbolic memory at position',index,'value',repr(v))
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


def run(program, state=None, check_initialized=False):
    ##logging.info('='*32)
    ##logging.info('Running program')
    ##logging.info('='*32)
    state = state or EVMState()
    state.memory.set_enforcing(check_initialized)
    while state.pc in program:
        ins = program[state.pc]
        opcode = ins.op
        op = ins.name
        stk = state.stack
        mem = state.memory
        ##logging.info('PC: (%d) %x'%(state.pc, state.pc))
        ##logging.info(ins)
        ##logging.info('Stack:', '\n\t'.join(str(i) for i in stk))
        ##logging.info('')
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
            topics = [stk.pop() for x in range(depth)]
            mem.extend(mstart, msz)
            data = bytearray_to_bytestr(mem[mstart: mstart + msz])
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


def printstack(code):
    stacksize = 0
    for i, ins in enumerate(code):
        # logging.info('%3d\tStacksize:%3d\t%s'%(i, stacksize, ins))
        stacksize += ins.delta


def to_dot(cfg):
    s = 'digraph g {\n'
    s += '\tsplines=ortho;\n'
    s += '\tnode[fontname="courier"];\n'
    for bb in sorted(cfg.bbs, key=lambda x: x.start):
        s += '\t%d [shape=box,label=<<b>%x</b>:<br align="left"/>%s<br align="left"/>>];\n' % (bb.start, bb.start,
                                                                                               '<br align="left"/>'.join(
                                                                                                   '%4x: %02x %s %s' % (
                                                                                                       ins.addr, ins.op,
                                                                                                       ins.name,
                                                                                                       hexlify(
                                                                                                           ins.arg) if ins.arg else '')
                                                                                                   for ins in bb.ins))
    s += '\n'
    for bb in sorted(cfg.bbs, key=lambda x: x.start):
        for succ in sorted(bb.succ, key=lambda x: x.start):
            s += '\t%d -> %d;\n' % (bb.start, succ.start)
    s += '}'
    return s


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
    ##logging.info('='*32)
    ##logging.info('Running program')
    ##logging.info('='*32\)

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
        ##logging.info('PC: %x'%state.pc)
        if state.pc == path[0]:
            ##logging.info('Reached %x, still to go: %s'%(path[0], ', '.join('%x'%i for i in path[1:])))
            path = path[1:]
            if not path:
                state.success = True
                return (state, constraints, sha_constraints)

        ins = program[state.pc]
        opcode = ins.op
        op = ins.name
        stk = state.stack
        mem = state.memory
        # logging.info('PC: (%d) %x'%(state.pc, state.pc))
        # logging.info(ins)
        # logging.info('Stack:', '\n\t'.join(str(i) for i in stk))
        # logging.info('')
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
                if isinstance(s2, numers.Number):
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
                            sha_name = k
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
            topics = [stk.pop() for x in range(depth)]
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


def get_paths(ins, loop_limit=1):
    path = [ins.addr, ins.bb.start]
    loops = defaultdict(int)
    pred = ins.bb.pred
    todo = list()  # deque() for BFS
    todo.append((path, loops, pred))
    while todo:
        path, loops, pred = todo.pop()
        if path[-1] == 0:
            yield path[::-1]
        for p in pred:
            if loops[p] < loop_limit:
                new_path = path + [p.start]
                new_pred = p.pred
                new_loops = defaultdict(int, loops)
                new_loops[p] += 1
                todo.append((new_path, new_loops, new_pred))


def get_successful_paths_from(path, cfg, loop_limit=1):
    loops = defaultdict(int)
    bbs = [cfg._bb_at[p] for p in path if p in cfg._bb_at]
    for bb in bbs:
        loops[bb] = 1
    todo = deque()
    todo.appendleft((path, loops, bbs[-1].succ))
    while todo:
        path, loop, succ = todo.pop()
        for s in succ:
            if loops[s] < loop_limit:
                new_path = path + [s.start]
                if s.ins[-1].name in ('STOP', 'RETURN'):
                    yield new_path + [s.ins[-1].addr]
                else:
                    new_loops = defaultdict(int, loops)
                    new_loops[s] += 1
                    todo.appendleft((new_path, new_loops, s.succ))


def cfg_to_program(cfg):
    return {ins.addr: ins for bb in cfg.bbs for ins in bb.ins}


def array_to_array(array_model, length=0):
    l = array_model.as_list()
    entries, else_value = l[:-1], l[-1]
    length = max(max(e[0].as_long() for e in entries) + 1, length)
    arr = [else_value.as_long()] * length
    for e in entries:
        arr[e[0].as_long()] = e[1].as_long()
    return arr


def get_level(name):
    try:
        if '_' in name:
            return int(name[name.rfind('_') + 1:])
        else:
            return int(name)
    except:
        return 0


def model_to_calls(model):
    calls = defaultdict(dict)
    for v in model:
        name = v.name()
        if name.startswith('CALLDATA'):
            call_index = get_level(name[9:])
            calls[call_index]['payload'] = ''.join(map(chr, array_to_array(model[v])))
        elif name.startswith('CALLVALUE'):
            call_index = get_level(name[10:])
            calls[call_index]['value'] = model[v].as_long()
        elif name.startswith('CALLER'):
            call_index = get_level(name[7:])
            calls[call_index]['caller'] = model[v].as_long()
        else:
            logging.warning('CANNOT CONVERT %s', name)
            #            call[name] = model[v].as_long()

    return [v for k, v in sorted(calls.iteritems(), reverse=True)]


def to_bytes(v):
    s = (v.size() / 8) * 2
    fmt = '%%0%dx' % s
    v_str = fmt % (v.as_long())
    return unhexlify(v_str)


def get_vars(f, rs=set()):
    '''
    shameless copy of z3util.get_vars,
    but returning select-operations as well.
    E.g. 
    x = z3.Array('x', z3.IntSort(), z3.IntSort())
    get_vars(x[5])
    will return x[5] instead of x
    '''
    if not rs:
        f = simplify(f)

    if f.decl().kind() == Z3_OP_SELECT:
        arr, idx = f.children()
        if is_const(arr):
            if z3util.is_expr_val(idx):
                return rs | {f}
            else:
                return rs | {f, idx}
    if is_const(f):
        if z3util.is_expr_val(f):
            return rs
        else:  # variable
            return rs | {f}

    else:
        for f_ in f.children():
            rs = get_vars(f_, rs)

        return set(rs)


def add_suffix(expr, level=0):
    substitutions = dict()
    for v in z3.z3util.get_vars(expr):
        if v.sort_kind() == z3.Z3_INT_SORT:
            substitutions[v] = z3.Int('%s_%d' % (v.decl().name(), level))
        elif v.sort_kind() == z3.Z3_BOOL_SORT:
            substitutions[v] = z3.Bool('%s_%d' % (v.decl().name(), level))
        elif v.sort_kind() == z3.Z3_BV_SORT:
            substitutions[v] = z3.BitVec('%s_%d' % (v.decl().name(), level), v.size())
        elif v.sort_kind() == z3.Z3_ARRAY_SORT:
            substitutions[v] = z3.Array('%s_%d' % (v.decl().name(), level), v.domain(), v.range())
        else:
            raise Exception('CANNOT CONVERT %s (%d)' % (v, v.sort_kind()))
    return z3.substitute(expr, substitutions.items())


def check_and_model(constraints, sha_constraints):
    if not sha_constraints:
        sol = z3.Solver()
        sol.add(constraints)
        if sol.check() != z3.sat:
            raise IntractablePath()
        return sol.model()

    unresolved = set(sha_constraints.keys())
    sol = z3.Solver()
    todo = constraints
    while todo:
        new_todo = []
        for c in todo:
            if any(x in unresolved for x in get_vars(c)):
                new_todo.append(c)
            else:
                sol.add(c)
        unresolved_vars = set(v for c in new_todo for v in get_vars(c))
        if sol.check() != z3.sat:
            raise IntractablePath()
        m = sol.model()
        for u in set(unresolved):
            c = sha_constraints[u]
            if any(x in unresolved_vars for x in get_vars(c)):
                continue
            v = m.eval(c)
            logging.debug("Hashing %s", hexlify(to_bytes(v)))
            if z3util.is_expr_val(v):
                sha = utils.big_endian_to_int(utils.sha3(to_bytes(v)))
                sol.add(c == v)
                sol.add(u == sha)
                unresolved.remove(u)
        todo = new_todo
    if sol.check() != z3.sat:
        raise IntractablePath()
    return sol.model()


def trivial_call_exploit(code, target_addr, target_amount, amount_check='='):
    cfg = CFG(generate_BBs(code))
    call_ins = filter_ins(cfg, 'CALL')
    if not call_ins:
        logging.info('No CALL instructions')
        return
    logging.info('Found %d CALL instructions' % len(call_ins))
    prg = cfg_to_program(cfg)
    for call in call_ins:
        # Find slices where the second argument to CALL (destination) is possibly influenced by user-controlled data
        interesting_slices = [bs for bs in backward_slice(call, [1]) if any(
            ins.name in ['ORIGIN', 'CALLER', 'CALLVALUE', 'CALLDATALOAD', 'CALLDATASIZE', 'CALLDATACOPY', 'EXTCODESIZE',
                         'EXTCODECOPY', 'MLOAD', 'SLOAD'] for ins in bs)]
        # Check if ins.bb is set, as slices include padding instructions (PUSH, POP)
        interesting_sub_paths = [[ins.bb.start for ins in bs if ins.bb] for bs in interesting_slices]
        path_count = 0
        pruned = 0
        for path in get_paths(call):
            path_count += 1
            # If this path is NOT a superset of an interesting slice, skip it
            if not any(all(loc in path for loc in sub_path) for sub_path in interesting_sub_paths):
                pruned += 1
                continue
            try:
                state, constraints, sha_constraints = run_symbolic(prg, path, code)

                addr = state.stack[-2]
                amount = state.stack[-3]

                if not concrete(addr):
                    constraints.append(z3.Extract(159, 0, addr) == target_addr)
                else:
                    if addr != target_addr:
                        continue
                if amount_check == '+':
                    constraints.append(amount <= target_amount)
                elif amount_check == '-':
                    constraints.append(amount >= target_amount)
                else:
                    constraints.append(amount == target_amount)

                model = check_and_model(constraints, sha_constraints)

                logging.info('So far checked %d paths (%d pruned)' % (path_count, pruned))
                return model_to_calls(model), constraints, model
            except Exception as e:
                logging.exception('Failed path due to %s', repr(e))
                pass
    logging.info('Checked %d paths (%d pruned)' % (path_count, pruned))
    logging.info('Could not exploit any CALL')
    return


def dependency_summary(constraints, sha_constraints, detailed=False):
    if detailed:
        _get_vars = get_vars
    else:
        _get_vars = z3util.get_vars
    all_dependencies = set(x for c in constraints if z3.is_expr(c) for x in _get_vars(z3.simplify(c)))
    changed = True
    while changed:
        changed = False
        for x in set(all_dependencies):
            if x in sha_constraints:
                changed = True
                all_dependencies.discard(x)
                all_dependencies.update(_get_vars(z3.simplify(sha_constraints[x])))
    return all_dependencies


def call_constraints(code):
    cfg = CFG(generate_BBs(code))
    call_ins = filter_ins(cfg, 'CALL')
    if not call_ins:
        logging.info('No CALL instructions')
        return
    logging.info('Found %d CALL instructions' % len(call_ins))
    prg = cfg_to_program(cfg)
    for call in call_ins:
        # Find slices where the second argument to CALL (destination) is possibly influenced by user-controlled data
        interesting_slices = [bs for bs in backward_slice(call, [1]) if any(
            ins.name in ['ORIGIN', 'CALLER', 'CALLVALUE', 'CALLDATALOAD', 'CALLDATASIZE', 'CALLDATACOPY', 'EXTCODESIZE',
                         'EXTCODECOPY', 'MLOAD', 'SLOAD'] for ins in bs)]
        # Check if ins.bb is set, as slices include padding instructions (PUSH, POP)
        interesting_sub_paths = [[ins.bb.start for ins in bs if ins.bb] for bs in interesting_slices]
        path_count = 0
        pruned = 0
        for path in get_paths(call):
            path_count += 1
            # If this path is NOT a superset of an interesting slice, skip it
            if not any(all(loc in path for loc in sub_path) for sub_path in interesting_sub_paths):
                pruned += 1
                continue
            try:
                state, constraints, sha_constraints = run_symbolic(prg, path, code)
            except IntractablePath:
                continue
            except Exception as e:
                logging.exception('Failed path due to %s', e)
                continue
            if len(state.stack) < 3:
                logging.error('Stack underflow??')
                continue
            target = state.stack[-2]
            amount = state.stack[-3]
            if not concrete(target):
                target = z3.simplify(z3.Extract(159, 0, target))
            if not concrete(amount):
                amount = z3.simplify(amount)
            yield call, path, target, amount, state, list(z3.simplify(c) for c in constraints), {k: z3.simplify(v) for
                                                                                                 k, v in
                                                                                                 sha_constraints.items()}
            # yield call, path, target, amount, list(z3.simplify(c) for c in constraints), {k:type(v) for k,v in sha_constraints.items()}


def store_constraints(code):
    cfg = CFG(generate_BBs(code))
    store_ins = filter_ins(cfg, 'SSTORE')
    if not store_ins:
        logging.info('No STORE instructions')
        return
    logging.info('Found %d STORE instructions' % len(store_ins))
    prg = cfg_to_program(cfg)
    for store in store_ins:
        # Find slices where the second argument to STORE (value) is possibly influenced by user-controlled data
        interesting_slices = [bs for bs in backward_slice(store, [1]) if any(
            ins.name in ['ORIGIN', 'CALLER', 'CALLVALUE', 'CALLDATALOAD', 'CALLDATASIZE', 'CALLDATACOPY', 'EXTCODESIZE',
                         'EXTCODECOPY', 'MLOAD', 'SLOAD'] for ins in bs)]
        # Check if ins.bb is set, as slices include padding instructions (PUSH, POP)
        interesting_sub_paths = [[ins.bb.start for ins in bs if ins.bb] for bs in interesting_slices]
        path_count = 0
        pruned = 0
        for path in get_paths(store):
            path_count += 1
            # If this path is NOT a superset of an interesting slice, skip it
            if not any(all(loc in path for loc in sub_path) for sub_path in interesting_sub_paths):
                pruned += 1
                continue
            try:
                state, constraints, sha_constraints = run_symbolic(prg, path, code)
            except IntractablePath:
                continue
            except Exception as e:
                logging.exception('Failed path due to %s', e)
                continue
            if len(state.stack) < 2:
                logging.error('Stack underflow?? Trace: %s', ', '.join('%x' % i for i in state.trace))
                continue
            address = state.stack[-1]
            value = state.stack[-2]
            if not concrete(address):
                address = z3.simplify(address)
            if not concrete(value):
                value = z3.simplify(value)
            yield store, path, address, value, state, list(z3.simplify(c) for c in constraints), {k: z3.simplify(v) for
                                                                                                  k, v in
                                                                                                  sha_constraints.items()}
