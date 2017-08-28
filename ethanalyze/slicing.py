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


def backward_slice(ins, taint_args=None, memory_info=None):
    def adjust_stack(backward_slice, stack_delta):
        if stack_delta > 0:
            backward_slice.extend(Instruction(0x0, 0x63, '\xde\xad\xc0\xde') for _ in xrange(abs(stack_delta)))
        elif stack_delta < 0:
            backward_slice.extend(Instruction(0x0, 0x50) for _ in xrange(abs(stack_delta)))

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
                pass
            stack_delta += ins.delta

        else:
            for p in preds:
                if loops[p] < loop_limit:
                    new_loops = defaultdict(int, loops)
                    new_loops[p] += 1
                    todo.append((stacksize, stack_delta, set(taintmap), list(backward_slice), p.ins, p.pred, new_loops))
    return results


def interesting_slices(instruction, args=None):
    return [bs for bs in backward_slice(instruction, args) if any(
        ins.name in potentially_user_controlled for ins in bs)]