#!/usr/bin/env python2.7
import sys
import logging
from binascii import unhexlify, hexlify
import ethanalyze

logging.basicConfig(level=logging.DEBUG)

if __name__=='__main__':
    if len(sys.argv)<2:
        print 'Usage: %s <code>'%sys.argv[0]
        exit(-1)
    with open(sys.argv[1]) as infile:
        inbuffer = infile.read().rstrip()
    code = unhexlify(inbuffer)
    for call, path, target, amount, state, constraints, sha_constraints in ethanalyze.call_constraints(code):
        print '='*32
        print 'Call: %s'%call
        print 'Path taken: %s'%(' -> '.join('%x'%addr for addr in path))
        print 'Summary: %s'%(', '.join(map(str, ethanalyze.dependency_summary(constraints + [target] + [amount], sha_constraints))))
        print '-'*32
        print 'Target: %s'%(' '.join(str(target).split()))
        print 'Amount: %s'%(' '.join(str(amount).split()))
        print 'Constraints: %d'%len(constraints)
        for i, c in enumerate(constraints):
            print '%4d.)\t%s'%(i, ' '.join(('%s'%c).split()))
        for k,v in sha_constraints.iteritems():
            print '  %s = KECCAK(%s)'%(k, ''.join(str(v).split()))
