#!/usr/bin/env python2.7
import sys
import logging
from binascii import unhexlify, hexlify
import ethereum

logging.basicConfig(level=logging.DEBUG)

if __name__=='__main__':
    if len(sys.argv)<2:
        print 'Usage: %s <code>'%sys.argv[0]
        exit(-1)
    detailed = len(sys.argv)>2 and '-v' in sys.argv
    with open(sys.argv[-1]) as infile:
        inbuffer = infile.read().rstrip()
    code = unhexlify(inbuffer)
    for store, path, address, value, state, constraints, sha_constraints in ethereum.store_constraints(code):
        print '='*32
        print 'Call: %s'%store
        print 'Path taken: %s'%(' -> '.join('%x'%addr for addr in path))
        print 'Summary: %s'%(', '.join(map(str, ethereum.dependency_summary(constraints + [address, value], sha_constraints))))
        if detailed:
            print '-'*32
            print 'Address: %s'%(' '.join(str(address).split()))
            print 'Value: %s'%(' '.join(str(value).split()))
            print 'Constraints: %d'%len(constraints)
            for i, c in enumerate(constraints):
                print '%4d.)\t%s'%(i, ' '.join(('%s'%c).split()))
            print 'Hashes: %d'%len(sha_constraints)
            for k,v in sha_constraints.iteritems():
                print '  %s = KECCAK(%s)'%(k, ''.join(str(v).split()))
        print ''
