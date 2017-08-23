#!/usr/bin/env python2.7
# coding: utf-8
import fileinput

data = '\n'.join([line for line in fileinput.input()])

if 'verifiedbytecode' in data:
    div = data.index('verifiedbytecode')
    start = data.index('>', div)+1
    end = data.index('<', start)
else:
    div = data.index('dividcode')
    start = data.index('0x', div)+2
    end = data.index('<', start)

print data[start:end]
