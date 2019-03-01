import logging
from collections import deque

from .cfg import Instruction, BB
from .opcodes import opcodes


from binascii import unhexlify, hexlify
# import json
#
# from collections import defaultdict
# from z3 import z3
#
# from ethanalyze.constraints import model_to_calls, check_model_and_resolve
# from ethanalyze.evm import concrete, CombinedSymbolicResult, IntractablePath
# from project import Project

class ArgumentTooShort(Exception):
    pass

#dissasamble and yield on Instruction(object) iterable on is valid
def disass(code, i=0):
    while i < len(code):
        loc = i
        op = ord(code[i])
        arg = None #init to none from last iteration
        inslen = 1 #inst length?
        if not op in opcodes: #sanity check if an existing EVM opcode
            break
            # raise IllegalInstruction('%02x at %d'%(op, i))

        #ROMAN
        if op == 0xf4: #
            # logging.info('***found a DELEGATECALL - hold my beer, I\'m going in!')
            # callee_code_path = "../teether-contracts/e_selfdest.contract.code"
            # with open(callee_code_path) as infile:
            #     inbuffer = infile.read().rstrip()
            # callee_code = unhexlify(inbuffer)
            # callee_p = Project(code)
            # logging.info('***loaded calle code into callee_project')


            pass

        if 0x60 <= op <= 0x7f: # PUSH1..PUSH32 #if its a PUSH
            arglen = op - 0x5f #calc X in PUSHX
            inslen += arglen
            arg = code[i + 1:i + 1 + arglen] #calc arguemnt of this opcode
            if len(arg) < arglen: #sanity check arg is really that long as X in PUSHX
                raise ArgumentTooShort
            i += arglen #jump OVER the arguments to be pushed to the stack - we know they're not opcodes
        i += 1 #iterate to index of next opcode
        yield Instruction(loc, op, arg) #add
        # End basic block on STOP, JUMP, JUMPI, RETURN, REVERT, RAISE, or if the following instruction is a JUMPDEST
        if op in (0x00, 0x56, 0x57, 0xf3, 0xfd, 0xfe, 0xff) or (i < len(code) and ord(code[i]) == 0x5b):
            break

#used for cfg init in Project class
# To address this, TE E THER uses backward slicing to
# iteratively reconstruct the CFG. Initially, the CFG con-
# tains only trivial edges, i.e., those matching the above
# pattern as well as fall-through cases for JUMPI. All other
# JUMP and JUMPI instructions are marked as unresolved.
def generate_BBs(code):
    #fallthrough_locs are exit points of a block
    fallthrough_locs = [i + 1 for i, c in enumerate(code) if ord(c) == 0x57] #JUMPI
    # jumpdest_locs are entry points ("leader")
    jumpdest_locs = [i for i, c in enumerate(code) if ord(c) == 0x5b] #JUMPDEST
    #PPOE is a leader, as well as jump dest, but why FT_locs is in the set?
    leader_candidates = {0} | set(fallthrough_locs) | set(jumpdest_locs) # BITWISE OR over? sets of integers?
    for l in sorted(leader_candidates):
        try:
            instructions = list(disass(code, l))
            if instructions: #condition; if Instruction(object) is created, then;
                yield BB(instructions) #create BB objects
        except: #Q: wouldn't the yield loop cont anyway?
            continue

# Reconstructing a control flow graph from EVM byte-
# code is a non-trivial task. This is due to the fact that the
# EVM only provides control flow instructions with indi-
# rect jumps. Both the conditional JUMPI and the uncondi-
# tional JUMP read the jump target from the top-most stack
# element.To address this, TE E THER uses backward slicing to
# iteratively reconstruct the CFG. Initially, the CFG con-
# tains only trivial edges, i.e., those matching the above
# pattern as well as fall-through cases for JUMPI. All other
# JUMP and JUMPI instructions are marked as unresolved.
# Next, an unresolved JUMP or JUMPI is selected and the
# set of (path-sensitive) backward slices of its jump target
# is computed.
def generate_BBs_recursive(code):
    resolve_later = []
    bbs = dict() #the BasicBlocksDict using bb.start as key to whole bb - return value
    todo = deque([(None, 0)]) #init deque with tupel
    valid_jump_targets = [ i for i,c in enumerate(code) if (ord(c) == 0x5b) ] #save index(es/i/?) of JUMPDEST inst in code
    while True: #until everything is "resolved"
        # when _todo is empty
        if not todo:
            new_links = False
            for bb in resolve_later: #check for
                _, new_succs = bb.get_succ_addrs_full(valid_jump_targets)
                for s in new_succs:
                    new_links = True
                    todo.append((bb.start, s))
            if not new_links:
                break #break out of while loop - finished resolving everything
        #get new element from the _todo deque
        p, i = todo.popleft() #first one is (None, 0)
        pred = bbs[p] if (not p is None) else None #check if p is None; if NOT assign bbs[p] - to get rid of the init None
        #sym-same as
        # if (p is None):
        #     pred = None
        # else:
        #     pred = 1
        #
        if i in bbs:
            bb = bbs[i]
        else:
            # logging.info(hex(i))
            #sanity check?
            if i >= len(code):
                logging.info('Jumptarget outside of code???')
                logging.info(p, i)
                continue
            #sanity check?
            if (pred) and (i != pred.ins[-1].next_addr) and (ord(code[i]) != 0x5b): #JUMPDEST
                # logging.info('WARNING, ILLEGAL JUMP-TARGET %x for BB @ %x'%(i, pred.start))
                continue

            #dissasmble the code at index i to Instruction objects list(iterable) using the opcode lib
            instructions = list(disass(code, i))

            if not instructions: # if no inst come back?
                continue

            bb = BB(instructions) #init a new BB using the list of dissasmbled instructions
            bbs[bb.start] = bb #save it to return dict; bb.start = self.ins[0].addr

            #figure indirect jumps
            for s in bb.get_succ_addrs(valid_jump_targets):
                # logging.info('Link from %x to %x', bb.start, s)
                #
                todo.append((bb.start, s)) #append current bb.start as key, and the computed dest_addr as value to deque
            if not bb.jump_resolved: #??? check if the indirect-jump was resolved OR the must_visit is empty
                resolve_later.append(bb)

        #???dependent edges?
        if pred:
            #sanity check?
            if p != pred.start or i != bb.start:
                logging.info('WEIRD SHIT')
                logging.info('p=%x, i=%x, pred=%x, bb=%x' % (p, i, pred.start, bb.start))
                pass

            bb.pred.add(pred) #add this pred to the currecnt block.pred var
            pred.succ.add(bb)

    return bbs.values()
