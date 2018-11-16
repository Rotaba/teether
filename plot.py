# coding: utf-8

import ethanalyze
from binascii import unhexlify, hexlify
with open('../timeout') as infile:
    data = infile.read()
    
p = ethanalyze.project.Project(unhexlify(data))
p.cfg.data_dependence()
p.cfg.dominators
with open('../timeout_color.dot','w') as f:
    f.write(p.cfg.to_dot())
