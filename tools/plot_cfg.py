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
    with open(sys.argv[1]) as infile:
        inbuffer = infile.read().rstrip()
    code = unhexlify(inbuffer)
    cfg = ethereum.CFG(list(ethereum.BBs(code)))
    print ethereum.to_dot(cfg)
