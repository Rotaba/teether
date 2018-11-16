#!/usr/bin/env python2.7
import sys
from binascii import unhexlify, hexlify

import ethanalyze


def assemble(code):
    instructions = []
    refs = {}
    for line in code.splitlines():
        tokens = line.upper().split(':')
        if len(tokens)==2:
            label = tokens[0].strip()
            ins = tokens[1]
        else:
            label = None
            ins = tokens[0]
        tokens = ins.split()
        if not tokens:
            continue
        if tokens[0] != 'PUSH':
            if tokens[0] not in ethanalyze.opcodes.reverse_opcodes:
                print >> sys.stderr, 'Unknown instruction "%s"'%tokens[0]
                continue
            instructions.append((chr(ethanalyze.opcodes.reverse_opcodes[tokens[0]]), '', label))
        elif tokens[0] == 'PUSH':
            if tokens[1].startswith('@'):
                ref_label = tokens[1][1:]
                if ref_label not in refs:
                    refs[ref_label] = []
                refs[ref_label].append(len(instructions))
                instructions.append(('REFPUSH', ref_label, label))
            else:
                v = int(tokens[1], 16)
                hex_v = '%x'%v
                if len(hex_v)%2 == 1:
                    hex_v = '0'+hex_v
                v_size = len(hex_v)/2
                instructions.append((chr(ethanalyze.opcodes.reverse_opcodes['PUSH%d'%v_size]), unhexlify(hex_v), label))
    refsize = 1
    while sum(len(i)+len(a) if i!= 'REFPUSH' else 1+refsize for i,a,l in instructions) >= 256**refsize:
        refsize += 1
    mask = '%%0%dx'%(refsize*2)
    code = ''
    labels = {}
    pc = 0
    for i,a,l in instructions:
        if l is not None:
            labels[l] = pc
        if i=='REFPUSH':
            pc += 1+refsize
        else:
            pc += 1+len(a)

    for i,a,l in instructions:
        if i=='REFPUSH':
            i = chr(ethanalyze.opcodes.reverse_opcodes['PUSH%d'%refsize])
            a = unhexlify(mask%labels[a])
        code += i+a
    return code


if __name__ == '__main__':
    import fileinput
    print hexlify(assemble('\n'.join(fileinput.input())))
