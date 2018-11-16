#!/usr/bin/env python2.7
import logging
import sys

import z3

from ethanalyze.constraints import dependency_summary
from ethanalyze.evm import concrete
import ethanalyze.project as project
import ethanalyze.slicing as slicing

logging.basicConfig(level=logging.DEBUG)

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print 'Usage: %s <code> <pc>' % sys.argv[0]
        exit(-1)

    codepath = sys.argv[1]
    pc = int(sys.argv[2])

    if codepath.endswith('.json'):
        import json
        with open(codepath,'rb') as f:
            jd = json.load(f)
        p = project.Project.from_json(jd)
    else:
        p = project.load(codepath)

    ins = p.cfg._ins_at[pc]
    for s in slicing.backward_slice(ins):
        print '\n'.join(map(str, s))
        print '='*32
