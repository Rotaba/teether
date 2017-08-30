#!/usr/bin/env python2.7
import sys

import ethanalyze.project

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print 'Usage: %s <code>' % sys.argv[0]
        exit(-1)
    p = ethanalyze.project.load(sys.argv[1])
    print p.cfg.to_dot()
