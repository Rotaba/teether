#!/usr/bin/env python2.7
import sys
import logging
from binascii import unhexlify, hexlify
import ethereum


logging.basicConfig(level=logging.DEBUG)

if __name__=='__main__':
    if len(sys.argv) < 2:
        print 'Usage: %s <codefile>'%sys.argv[0]
        exit(-1)
    with open(sys.argv[1]) as infile:
        inbuffer = infile.read().rstrip()
    code = unhexlify(inbuffer)
    if not '\x39' in code:
        logging.warning('No CODECOPY in this contract!!')
    contract = ethereum.extract_contract_code(code, sys.argv[1])
    if contract:
        print hexlify(contract)
    else:
        logging.error('Could not find contract code')
