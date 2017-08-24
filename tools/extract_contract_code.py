#!/usr/bin/env python2.7
import sys
from datetime import datetime
import logging

from binascii import unhexlify, hexlify
from ethanalyze.project import Project
from ethanalyze.cfg import CFG, backward_slice, run, slice_to_program
from ethanalyze.memory import resolve_all_memory
from ethanalyze.disassemble import generate_BBs_recursive

logging.basicConfig(level=logging.DEBUG)

def extract_contract_code(code, fname=''):
    icfg = CFG(generate_BBs_recursive(code), fix_xrefs=True)
    p = Project(code, cfg=icfg)
    with open('./cfg%s-%s.dot' % (
                '-' + fname if fname else fname, str(datetime.now()).replace(' ', '-').replace(':', '')),
              'w') as outfile:
        outfile.write(icfg.to_dot())
    returns = icfg.filter_ins('RETURN')
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
                state = p.run(slice_to_program(b))
                return str(state.memory[start:stop])
            except:
                pass
    return None


if __name__=='__main__':
    if len(sys.argv) < 2:
        print 'Usage: %s <codefile>'%sys.argv[0]
        exit(-1)
    with open(sys.argv[1]) as infile:
        inbuffer = infile.read().rstrip()
    code = unhexlify(inbuffer)
    if not '\x39' in code:
        logging.warning('No CODECOPY in this contract!!')
    contract = extract_contract_code(code, sys.argv[1])
    if contract:
        print hexlify(contract)
    else:
        logging.error('Could not find contract code')
