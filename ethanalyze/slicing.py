import logging
from collections import deque, defaultdict

from ethanalyze.opcodes import potentially_user_controlled
from .cfg import Instruction
from .intrange import Range


def slice_to_program(s):
    pc = 0
    program = {}
    for ins in s:
        program[pc] = ins
        pc += ins.next_addr - ins.addr
    return program


def adjust_stack(backward_slice, stack_delta):
    if stack_delta > 0:
        backward_slice.extend(Instruction(0x0, 0x63, '\xde\xad\xc0\xde') for _ in xrange(abs(stack_delta)))
    elif stack_delta < 0:
        backward_slice.extend(Instruction(0x0, 0x50) for _ in xrange(abs(stack_delta)))


class SlicingState(object):
    def __init__(self, stacksize, stack_underflow, stack_delta, taintmap, memory_taint, backward_slice, instructions,
                 preds, loops):
        self.stacksize = stacksize
        self.stack_underflow = stack_underflow
        self.stack_delta = stack_delta
        self.taintmap = frozenset(taintmap)
        self.memory_taint = memory_taint
        self.backward_slice = tuple(backward_slice)
        self.instructions = tuple(instructions)
        self.preds = preds
        self.loops = loops

    def __hash__(self):
        return sum(a * b for a, b in zip((23, 29, 31, 37, 41), (self.stacksize, self.stack_delta, hash(self.taintmap),
                                                                hash(self.instructions), hash(self.backward_slice))))

    def __eq__(self, other):
        return (self.stacksize == other.stacksize and
                self.stack_delta == other.stack_delta and
                self.taintmap == other.taintmap and
                self.memory_taint == other.memory_taint and
                self.backward_slice == other.backward_slice and
                self.instructions == other.instructions)

    def __str__(self):
        return 'Stacksize: %d, Underflow: %d, Delta: %d, Map: %s' % (
            self.stacksize, self.stack_underflow, self.stack_delta, self.taintmap)


def advance_slice(state, memory_info, loop_limit):
    new_results = []
    new_todo = []
    stacksize = state.stacksize
    stack_underflow = state.stack_underflow
    stack_delta = state.stack_delta
    taintmap = set(state.taintmap)
    memory_taint = state.memory_taint
    backward_slice = list(state.backward_slice)
    instructions = state.instructions
    preds = state.preds
    loops = state.loops

    for ins in instructions[::-1]:
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
            stack_adjust = stacksize - stack_underflow
            if stack_adjust > 0:
                adjust_stack(backward_slice, stack_adjust)
            new_results.append(backward_slice[::-1])
            break

        if taintmap and stacksize < max(taintmap):
            pass
        stack_delta += ins.delta

    # still taint left? trace further
    else:
        for p in preds:
            if loops[p] < loop_limit:
                new_loops = defaultdict(int, loops)
                new_loops[p] += 1
                new_todo.append(
                    SlicingState(stacksize, stack_underflow, stack_delta, set(taintmap), memory_taint,
                                 list(backward_slice), p.ins,
                                 p.pred, new_loops))
    return new_results, new_todo


def backward_slice(ins, taint_args=None, memory_info=None, loop_limit=2):
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
    stack_underflow = 0
    stack_delta = 0
    bb = ins.bb
    idx = bb.ins.index(ins)
    loops = defaultdict(int)
    todo.append(
        SlicingState(stacksize, stack_underflow, stack_delta, taintmap, memory_taint, backward_slice, bb.ins[:idx],
                     bb.pred, loops))
    results = []
    cache = set()
    taintcache = set()
    while todo:
        state = todo.popleft()
        if state in cache:
            continue
        cache.add(state)
        if (state.taintmap, state.memory_taint) not in taintcache:
            taintcache.add((state.taintmap, state.memory_taint))
        logging.debug('Cachesize: %d\tTaint-Cachesize: %d\t(slicing %x, currently at %x)', len(cache), len(taintcache), ins.addr, state.instructions[-1].addr)
        logging.debug('Current state: %s', state)
        new_results, new_todo = advance_slice(state, memory_info, loop_limit)
        results.extend(new_results)
        todo.extend(new_todo)

    return results


def interesting_slices(instruction, args=None):
    return [bs for bs in backward_slice(instruction, args) if any(
        ins.name in potentially_user_controlled for ins in bs)]
