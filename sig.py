#!/usr/bin/env python2.7
import sha3
import sys

def sig(name):
    return sha3.keccak_256(name).hexdigest()[:8]

if __name__=='__main__':
    if len(sys.argv)>1:
        for arg in sys.argv[1:]:
            print sig(arg), arg
    else:
        name = raw_input('Method signature: ')
        print sig(name), name
