#!/usr/bin/env python2.7
# coding: utf-8
import sys
import json
import ethanalyze

def main(path):
    with open(path,'rb') as f:
        jd = json.load(f)
    
    p = ethanalyze.project.Project.from_json(jd)
    sloads = p.filter_ins('SLOAD')
    locs = set()
    for sload in sloads:
        for s in ethanalyze.slicing.backward_slice(sload):
            try:
                st = ethanalyze.evm.run(ethanalyze.slicing.slice_to_program(s), check_initialized=True)
                locs.add(st.stack[-1])
            except:
                continue
            
    for l in sorted(locs):
        print '0x%064x'%l

if __name__ == '__main__':
    if len(sys.argv)<2:
        print >> sys.stderr, 'Usage: %d <project.json>'%sys.argv[0]
    main(sys.argv[1])
