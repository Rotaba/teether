#!/usr/bin/env python2.7
import sys
import logging
from binascii import unhexlify, hexlify

import z3

from ethanalyze.project import Project
from ethanalyze.slicing import backward_slice
from ethanalyze.constraints import dependency_summary
from ethanalyze.evm import concrete, IntractablePath

logging.basicConfig(level=logging.DEBUG)


def store_constraints(code):
    p = Project(code)
    store_ins = p.cfg.filter_ins('SSTORE')
    if not store_ins:
        logging.info('No STORE instructions')
        return
    logging.info('Found %d STORE instructions' % len(store_ins))
    for store in store_ins:
        # Find slices where the second argument to STORE (value) is possibly influenced by user-controlled data
        interesting_slices = [bs for bs in backward_slice(store, [1]) if any(
            ins.name in ['ORIGIN', 'CALLER', 'CALLVALUE', 'CALLDATALOAD', 'CALLDATASIZE', 'CALLDATACOPY', 'EXTCODESIZE',
                         'EXTCODECOPY', 'MLOAD', 'SLOAD'] for ins in bs)]
        # Check if ins.bb is set, as slices include padding instructions (PUSH, POP)
        interesting_sub_paths = [[ins.bb.start for ins in bs if ins.bb] for bs in interesting_slices]
        path_count = 0
        pruned = 0
        for path in p.cfg.get_paths(store):
            path_count += 1
            # If this path is NOT a superset of an interesting slice, skip it
            if not any(all(loc in path for loc in sub_path) for sub_path in interesting_sub_paths):
                pruned += 1
                continue
            try:
                state, constraints, sha_constraints = p.run_symbolic(path)
            except IntractablePath:
                continue
            except Exception as e:
                logging.exception('Failed path due to %s', e)
                continue
            if len(state.stack) < 2:
                logging.error('Stack underflow?? Trace: %s', ', '.join('%x' % i for i in state.trace))
                continue
            address = state.stack[-1]
            value = state.stack[-2]
            if not concrete(address):
                address = z3.simplify(address)
            if not concrete(value):
                value = z3.simplify(value)
            yield store, path, address, value, state, list(z3.simplify(c) for c in constraints), {k: z3.simplify(v) for
                                                                                                  k, v in
                                                                                                  sha_constraints.items()}


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print 'Usage: %s <code>' % sys.argv[0]
        exit(-1)
    detailed = len(sys.argv) > 2 and '-v' in sys.argv
    with open(sys.argv[-1]) as infile:
        inbuffer = infile.read().rstrip()
    code = unhexlify(inbuffer)
    for store, path, address, value, state, constraints, sha_constraints in store_constraints(code):
        print '=' * 32
        print 'Call: %s' % store
        print 'Path taken: %s' % (' -> '.join('%x' % addr for addr in path))
        print 'Summary: %s' % (', '.join(map(str, dependency_summary(constraints + [address, value], sha_constraints))))
        if detailed:
            print '-' * 32
            print 'Address: %s' % (' '.join(str(address).split()))
            print 'Value: %s' % (' '.join(str(value).split()))
            print 'Constraints: %d' % len(constraints)
            for i, c in enumerate(constraints):
                print '%4d.)\t%s' % (i, ' '.join(('%s' % c).split()))
            print 'Hashes: %d' % len(sha_constraints)
            for k, v in sha_constraints.iteritems():
                print '  %s = KECCAK(%s)' % (k, ''.join(str(v).split()))
        print ''
