CALLVALUE
PUSH @b
JUMPI
CALLER
PUSH @a
JUMP
b: JUMPDEST
PUSH 0
a: JUMPDEST
PUSH 0
MSTORE
CALLVALUE
PUSH 0x1337
GT
PUSH @c
JUMPI
PUSH 1
PUSH @d
JUMP
c: JUMPDEST
PUSH 0
d: JUMPDEST
MLOAD
