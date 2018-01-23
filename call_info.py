#!/usr/bin/env python2.7
import logging
import sys

import z3

from ethanalyze.constraints import dependency_summary
from ethanalyze.evm import concrete
import ethanalyze.project as project

logging.basicConfig(level=logging.INFO)


def call_constraints(codepath):
    if codepath.endswith('.json'):
        import json
        with open(codepath,'rb') as f:
            jd = json.load(f)
        p = project.Project.from_json(jd)
    else:
        p = project.load(codepath)
    call_ins = p.cfg.filter_ins('CALL')
    if not call_ins:
        logging.info('No CALL instructions')
        return
    logging.info('Found %d CALL instructions' % len(call_ins))
    for call, path, r in p.get_constraints(call_ins, [1, 2]):
        r.simplify()
        if len(r.state.stack) < 3:
            logging.error('Stack underflow??')
            continue
        target = r.state.stack[-2]
        amount = r.state.stack[-3]
        if not concrete(target):
            target = z3.simplify(z3.Extract(159, 0, target))
        if not concrete(amount):
            amount = z3.simplify(amount)
        yield call, path, target, amount, r


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print 'Usage: %s <code>' % sys.argv[0]
        exit(-1)
    detailed = len(sys.argv) < 3 or '--short' in sys.argv
    for call, path, target, amount, r in call_constraints(sys.argv[1]):
        print '=' * 32
        print 'Call: %s' % call
        print 'Path taken: %s' % (' -> '.join('%x' % addr for addr in path))
        print 'Summary: %s' % (
            ', '.join(map(str, dependency_summary(r.constraints + [target] + [amount], r.sha_constraints))))
        if detailed:
            print '-' * 32
            print 'Target: %s' % (' '.join(str(target).split()))
            print 'Amount: %s' % (' '.join(str(amount).split()))
            print 'Constraints: %d' % len(r.constraints)
            for i, c in enumerate(r.constraints):
                print '%4d.)\t%s' % (i, ' '.join(('%s' % c).split()))
            for k, v in r.sha_constraints.iteritems():
                print '  %s = KECCAK(%s)' % (k, ''.join(str(v).split()))
        print ''
