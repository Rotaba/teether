import logging
from collections import deque

from .cfg import Instruction, BB
from .opcodes import opcodes


class ArgumentTooShort(Exception):
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