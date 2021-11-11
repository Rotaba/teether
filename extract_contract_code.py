#!/usr/bin/env python2.7
import logging
import os
import sys
from binascii import unhexlify, hexlify
from datetime import datetime

from ethanalyze.cfg import CFG
from ethanalyze.disassembly import generate_BBs_recursive
from ethanalyze.memory import resolve_all_memory
from ethanalyze.project import Project
from ethanalyze.slicing import backward_slice, slice_to_program

logging.basicConfig(level=logging.DEBUG)

#called by the compile.sh to create a CFG of a contract, check BS and create a contract.code (constructor stub?)
def extract_contract_code(code, fname=''):
    icfg = CFG(generate_BBs_recursive(code), fix_xrefs=True)
    #logging.info(icfg)
    p = Project(code, cfg=icfg) #create new project based on code and the above CFG

    #create a dot from the BB generated above
    #path = '.'
    #if fname:
    #    path, fname = os.path.split(fname)
    #    fname = '-' + fname
    #now = str(datetime.now()).replace(' ', '-').replace(':', '')
    # create a .dot graph
    #fname = 'cfg%s-%s.dot' % (fname, now)
    #with open(os.path.join(path, fname), 'w') as outfile:
    #    outfile.write(icfg.to_dot())

    #find RETURNs in code
    returns = icfg.filter_ins('RETURN')
    #check BS for the instructions and gen MemoryInfo object from the writes/reads
    memory_infos = resolve_all_memory(icfg, code)
    for r in returns:

        if not r in memory_infos: #if the return_inst is not in mem - take next return_inst from retruns
            continue

        rmi = memory_infos[r].reads
        if len(rmi.points) != 2:
            continue

        (start, _), (stop, _) = rmi.points

        bs = backward_slice(r, memory_info=memory_infos)
        # try to run that resolved_memory infos slice in the EVM
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
    #read .code file
    with open(sys.argv[1]) as infile:
        inbuffer = infile.read().rstrip()
    #solc -bin output is hexedecimal! we need it as binary
    code = unhexlify(inbuffer)

    if '\x39' not in code:
        logging.warning('No CODECOPY in this contract!!') #CODECOPY is used to copy the runtime part of the contract in EVM's memory

    #take .code and create a .contract.code to be written in a file
    contract = extract_contract_code(code, sys.argv[1])

    if contract:
        print hexlify(contract) #return the .contract.code file
    else:
        logging.error('Could not find contract code')
