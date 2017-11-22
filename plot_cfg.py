#!/usr/bin/env python2.7
import resource
import sys

import logging
logging.basicConfig(level=logging.INFO)

import ethanalyze.project

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print 'Usage: %s <code>' % sys.argv[0]
        exit(-1)

    
    mem_limit = 4*1024*1024*1024 # 4GB
    resource.setrlimit(resource.RLIMIT_AS, (mem_limit, mem_limit))
    p = ethanalyze.project.load(sys.argv[1])
    print p.cfg.to_dot()
