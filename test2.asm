CALLVALUE
PUSH @b
JUMPI
PUSH @a2
PUSH 0x00
PUSH @c
JUMP
a2: JUMPDEST
STOP
b: JUMPDEST
PUSH @b2
PUSH 0xff
PUSH @c
JUMP
b2: JUMPDEST
STOP
c: JUMPDEST
POP
JUMP