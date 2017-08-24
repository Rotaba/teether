#!/usr/bin/env python2.7
import logging
import sys

import z3

from ethanalyze.constraints import dependency_summary
from ethanalyze.evm import concrete
from ethanalyze.project import Project

logging.basicConfig(level=logging.DEBUG)


def store_constraints(codepath):
    p = Project.load(codepath)
    store_ins = p.cfg.filter_ins('SSTORE')
    if not store_ins:
        logging.info('No STORE instructions')
        return
    logging.info('Found %d STORE instructions' % len(store_ins))
    for store, path, r in p.get_constraints(store_ins, [1]):
        r.simplify()
        if len(r.state.stack) < 2:
            logging.error('Stack underflow?? Trace: %s', ', '.join('%x' % i for i in r.state.trace))
            continue
        address = r.state.stack[-1]
        value = r.state.stack[-2]
        if not concrete(address):
            address = z3.simplify(address)
        if not concrete(value):
            value = z3.simplify(value)
        yield store, path, address, value, r


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print 'Usage: %s <code>' % sys.argv[0]
        exit(-1)
    detailed = len(sys.argv) < 3 or '--short' not in sys.argv
    for store, path, address, value, r in store_constraints(sys.argv[-1]):
        print '=' * 32
        print 'Call: %s' % store
        print 'Path taken: %s' % (' -> '.join('%x' % addr for addr in path))
        print 'Summary: %s' % (', '.join(map(str, dependency_summary(r.constraints + [address, value], r.sha_constraints))))
        if detailed:
            print '-' * 32
            print 'Address: %s' % (' '.join(str(address).split()))
            print 'Value: %s' % (' '.join(str(value).split()))
            print 'Constraints: %d' % len(r.constraints)
            for i, c in enumerate(r.constraints):
                print '%4d.)\t%s' % (i, ' '.join(('%s' % c).split()))
            print 'Hashes: %d' % len(r.sha_constraints)
            for k, v in r.sha_constraints.iteritems():
                print '  %s = KECCAK(%s)' % (k, ''.join(str(v).split()))
        print ''
