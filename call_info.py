#!/usr/bin/env python2.7
import logging
import sys
from binascii import unhexlify

import z3
from ethanalyze.constraints import dependency_summary
from ethanalyze.project import Project
from ethanalyze.slicing import backward_slice

from ethanalyze.evm import concrete, IntractablePath

logging.basicConfig(level=logging.DEBUG)


def call_constraints(code):
    p = Project(code)
    call_ins = p.cfg.filter_ins('CALL')
    if not call_ins:
        logging.info('No CALL instructions')
        return
    logging.info('Found %d CALL instructions' % len(call_ins))
    for call in call_ins:
        # Find slices where the second argument to CALL (destination) is possibly influenced by user-controlled data
        interesting_slices = [bs for bs in backward_slice(call, [1]) if any(
            ins.name in ['ORIGIN', 'CALLER', 'CALLVALUE', 'CALLDATALOAD', 'CALLDATASIZE', 'CALLDATACOPY', 'EXTCODESIZE',
                         'EXTCODECOPY', 'MLOAD', 'SLOAD'] for ins in bs)]
        # Check if ins.bb is set, as slices include padding instructions (PUSH, POP)
        interesting_sub_paths = [[ins.bb.start for ins in bs if ins.bb] for bs in interesting_slices]
        path_count = 0
        pruned = 0
        for path in p.cfg.get_paths(call):
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
            if len(state.stack) < 3:
                logging.error('Stack underflow??')
                continue
            target = state.stack[-2]
            amount = state.stack[-3]
            if not concrete(target):
                target = z3.simplify(z3.Extract(159, 0, target))
            if not concrete(amount):
                amount = z3.simplify(amount)
            yield call, path, target, amount, state, list(z3.simplify(c) for c in constraints), {k: z3.simplify(v) for
                                                                                                 k, v in
                                                                                                 sha_constraints.items()}


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print 'Usage: %s <code>' % sys.argv[0]
        exit(-1)
    with open(sys.argv[1]) as infile:
        inbuffer = infile.read().rstrip()
    code = unhexlify(inbuffer)
    for call, path, target, amount, state, constraints, sha_constraints in call_constraints(code):
        print '=' * 32
        print 'Call: %s' % call
        print 'Path taken: %s' % (' -> '.join('%x' % addr for addr in path))
        print 'Summary: %s' % (
        ', '.join(map(str, dependency_summary(constraints + [target] + [amount], sha_constraints))))
        print '-' * 32
        print 'Target: %s' % (' '.join(str(target).split()))
        print 'Amount: %s' % (' '.join(str(amount).split()))
        print 'Constraints: %d' % len(constraints)
        for i, c in enumerate(constraints):
            print '%4d.)\t%s' % (i, ' '.join(('%s' % c).split()))
        for k, v in sha_constraints.iteritems():
            print '  %s = KECCAK(%s)' % (k, ''.join(str(v).split()))
