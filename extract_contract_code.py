#!/usr/bin/env python2.7
import logging
import sys
from binascii import unhexlify, hexlify
from datetime import datetime

import os

from ethanalyze.cfg import CFG
from ethanalyze.slicing import backward_slice, slice_to_program
from ethanalyze.disassembly import generate_BBs_recursive
from ethanalyze.memory import resolve_all_memory
from ethanalyze.project import Project

logging.basicConfig(level=logging.DEBUG)


def extract_contract_code(code, fname=''):
    icfg = CFG(generate_BBs_recursive(code), fix_xrefs=True)
    p = Project(code, cfg=icfg)
    path = '.'
    if fname:
        path, fname = os.path.split(fname)
        fname = '-' + fname
    now = str(datetime.now()).replace(' ', '-').replace(':', '')
    fname = 'cfg%s-%s.dot' % (fname, now)
    with open(os.path.join(path, fname), 'w') as outfile:
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
                logging.exception('Exception while running')
                pass
    return None


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print 'Usage: %s <codefile>' % sys.argv[0]
        exit(-1)
    with open(sys.argv[1]) as infile:
        inbuffer = infile.read().rstrip()
    code = unhexlify(inbuffer)
    if '\x39' not in code:
        logging.warning('No CODECOPY in this contract!!')
    contract = extract_contract_code(code, sys.argv[1])
    if contract:
        print hexlify(contract)
    else:
        logging.error('Could not find contract code')
