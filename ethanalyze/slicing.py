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
                 bb, loops, must_visit):
        self.stacksize = stacksize
        self.stack_underflow = stack_underflow
        self.stack_delta = stack_delta
        self.taintmap = frozenset(taintmap)
        self.memory_taint = memory_taint
        self.backward_slice = tuple(backward_slice)
        self.instructions = tuple(instructions)
        self.bb = bb
        self.loops = loops
        self.must_visit = frozenset(must_visit)

    def __hash__(self):
        return sum(
            a * b for a, b in zip((23, 29, 31, 37, 41, 43), (self.stacksize, self.stack_delta, hash(self.taintmap),
                                                             hash(self.instructions), hash(self.backward_slice),
                                                             hash(self.must_visit))))

    def __eq__(self, other):
        return (self.stacksize == other.stacksize and
                self.stack_delta == other.stack_delta and
                self.taintmap == other.taintmap and
                self.memory_taint == other.memory_taint and
                self.backward_slice == other.backward_slice and
                self.instructions == other.instructions and
                self.must_visit == other.must_visit)

    def __str__(self):
        return 'At: %x, Stacksize: %d, Underflow: %d, Delta: %d, Map: %s, Slice: %s, Must-Visit: %s, Hash: %x' % (
            self.instructions[-1].addr, self.stacksize, self.stack_underflow, self.stack_delta, self.taintmap,
            ','.join('%x' % i.addr for i in self.backward_slice),
            ','.join('%x' % x for x in self.must_visit), hash(self))


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
    bb = state.bb
    loops = state.loops
    must_visit = state.must_visit

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
        for p in bb.pred:

            if not loops[p] < loop_limit:
                continue

            new_must_visits = []
            for path in bb.pred_paths[p]:
                new_must_visit = (must_visit | set(path)) - {p.start}
                if not new_must_visit.issubset(p.ancestors):
                    continue
                new_must_visits.append(new_must_visit)

            for new_must_visit in minimize(new_must_visits):
                new_loops = defaultdict(int, loops)
                new_loops[p] += 1
                new_todo.append(
                    SlicingState(stacksize, stack_underflow, stack_delta, set(taintmap), memory_taint,
                                 list(backward_slice), p.ins,
                                 p, new_loops, new_must_visit))
    return new_results, new_todo


def minimize(sets):
    todo = sorted(sets, key=len)
    results = []
    while todo:
        test_set = todo[0]
        results.append(test_set)
        todo = [t for t in todo[1:] if not test_set.issubset(t)]
    return results


def backward_slice(ins, taint_args=None, memory_info=None, loop_limit=1, must_visits=[set()]):
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
    for must_visit in minimize(must_visits):
        todo.append(
            SlicingState(stacksize, stack_underflow, stack_delta, taintmap, memory_taint, backward_slice, bb.ins[:idx],
                         bb, loops, must_visit))
    results = []
    cache = set()
    while todo:
        state = todo.popleft()
        # if this BB can be reached via multiple paths, check if we want to cache it
        # or whether another path already reached it with the same state
        if len(bb.succ) > 1:
            if state in cache:
                logging.debug('CACHE HIT')
                continue
            cache.add(state)
        logging.debug('Cachesize: %d\t(slicing %x, currently at %x)', len(cache), ins.addr, state.instructions[-1].addr)
        logging.debug('Current state: %s', state)
        new_results, new_todo = advance_slice(state, memory_info, loop_limit)
        results.extend(new_results)
        todo.extend(new_todo)

    return results


def interesting_slices(instruction, args=None):
    return [bs for bs in backward_slice(instruction, args) if any(
        ins.name in potentially_user_controlled for ins in bs)]
