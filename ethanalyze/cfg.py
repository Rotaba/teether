import logging
from binascii import hexlify
from collections import defaultdict, deque

from .opcodes import opcodes
from .memory import UninitializedRead


class Instruction(object):
    def __init__(self, addr, op, arg=None):
        opinfo = opcodes[op]
        inslen = (op - 0x5f) + 1 if 0x60 <= op <= 0x7f else 1
        self.addr = addr
        self.next_addr = self.addr + inslen
        self.op = op
        self.name = opinfo[0]
        self.arg = arg
        self.ins = opinfo[1]
        self.outs = opinfo[2]
        self.delta = self.outs - self.ins
        self.bb = None

    def __str__(self):
        return '(%5d) %4x:\t%02x\t-%d +%d = %d\t%s%s' % (
            self.addr, self.addr, self.op, self.ins, self.outs, self.delta, self.name,
            '(%d) %s' % (int(hexlify(self.arg), 16), '\t%s' % hexlify(self.arg)) if self.arg else '')

    def __repr__(self):
        return str(self)


class BB(object):
    def __init__(self, ins):
        self.ins = ins
        for i in ins:
            i.bb = self
        self.start = self.ins[0].addr
        self.pred = set()
        self.succ = set()
        self.succ_addrs = set()
        self.jump_resolved = False

    def _find_jump_target(self):
        if len(self.ins) >= 2 and 0x60 <= self.ins[-2].op <= 0x71:
            self.jump_resolved = True
            return int(hexlify(self.ins[-2].arg), 16)
        else:
            return None

    def get_succ_addrs_full(self):
        from .slicing import slice_to_program, backward_slice
        from .evm import ExternalData, run
        new_succ_addrs = set()
        if not self.jump_resolved:
            bs = backward_slice(self.ins[-1], [0])
            for b in bs:
                if 0x60 <= b[-1].op <= 0x7f:
                    succ_addr = int(hexlify(b[-1].arg), 16)
                    if not succ_addr in self.succ_addrs:
                        self.succ_addrs.add(succ_addr)
                        new_succ_addrs.add(succ_addr)
                else:
                    p = slice_to_program(b)
                    try:
                        succ_addr = run(p, check_initialized=True).stack.pop()
                        if not succ_addr in self.succ_addrs:
                            self.succ_addrs.add(succ_addr)
                            new_succ_addrs.add(succ_addr)
                    except ExternalData as e:
                        pass
                        # logging.exception('WARNING, COULD NOT EXECUTE SLICE', repr(e))
                    except UninitializedRead as e:
                        pass
                        # logging.exception('WARNING, COULD NOT EXECUTE SLICE', repr(e))
        return (self.succ_addrs, new_succ_addrs)

    def get_succ_addrs(self):
        if self.ins[-1].op in (0x56, 0x57):
            jump_target = self._find_jump_target()
            if jump_target:
                self.succ_addrs.add(jump_target)
        else:
            self.jump_resolved = True
        if self.ins[-1].op not in (0x00, 0x56, 0xf3, 0xfd, 0xfe, 0xff):
            fallthrough = self.ins[-1].next_addr
            if fallthrough:
                self.succ_addrs.add(fallthrough)
        return self.succ_addrs

    def __str__(self):
        s = 'BB @ %x' % self.start
        if self.pred:
            s += '\n'
            s += '\n'.join('%x ->' % pred.start for pred in self.pred)
        s += '\n'
        s += '\n'.join(str(ins) for ins in self.ins)
        if self.succ:
            s += '\n'
            s += '\n'.join(' -> %x' % succ.start for succ in self.succ)
        return s

    def __repr__(self):
        return str(self)


class CFG(object):
    def __init__(self, bbs, fix_xrefs=True):
        self.bbs = sorted(bbs, key=lambda bb: bb.start)
        self._bb_at = {bb.start: bb for bb in self.bbs}
        if fix_xrefs:
            self._xrefs()

    def filter_ins(self, names):
        if isinstance(names, basestring):
            names = [names]
        return [ins for bb in self.bbs for ins in bb.ins if ins.name in names]

    def _xrefs(self):
        self._easy_xrefs()
        self._hard_xrefs()

    def _easy_xrefs(self):
        for pred in self.bbs:
            for succ_addr in pred.get_succ_addrs():
                if succ_addr and succ_addr in self._bb_at:
                    succ = self._bb_at[succ_addr]
                    pred.succ.add(succ)
                    succ.pred.add(pred)

    def _hard_xrefs(self):
        new_link = True
        links = set()
        while new_link:
            new_link = False
            for pred in self.bbs:
                if not pred.jump_resolved:
                    # only interested in jump-target
                    succ_addrs, new_succ_addrs = pred.get_succ_addrs_full()
                    for succ_addr in new_succ_addrs:
                        if not succ_addr in self._bb_at:
                            logging.warn(
                                'WARNING, NO BB @ %x (possible successor of BB @ %x)' % (succ_addr, pred.start))
                            continue
                        succ = self._bb_at[succ_addr]
                        pred.succ.add(succ)
                        succ.pred.add(pred)
                        if not (pred.start, succ.start) in links:
                            new_link = True
                            links.add((pred.start, succ.start))

    def __str__(self):
        return '\n\n'.join(str(bb) for bb in self.bbs)

    def to_dot(self):
        s = 'digraph g {\n'
        s += '\tsplines=ortho;\n'
        s += '\tnode[fontname="courier"];\n'
        for bb in sorted(self.bbs, key=lambda x: x.start):
            s += '\t%d [shape=box,label=<<b>%x</b>:<br align="left"/>%s<br align="left"/>>];\n' % (bb.start, bb.start,
                                                                                                   '<br align="left"/>'.join(
                                                                                                       '%4x: %02x %s %s' % (
                                                                                                           ins.addr,
                                                                                                           ins.op,
                                                                                                           ins.name,
                                                                                                           hexlify(
                                                                                                               ins.arg) if ins.arg else '')
                                                                                                       for ins in
                                                                                                       bb.ins))
        s += '\n'
        for bb in sorted(self.bbs, key=lambda x: x.start):
            for succ in sorted(bb.succ, key=lambda x: x.start):
                s += '\t%d -> %d;\n' % (bb.start, succ.start)
        s += '}'
        return s

    @staticmethod
    def get_paths(ins, loop_limit=1):
        path = [ins.addr, ins.bb.start]
        loops = defaultdict(int)
        pred = ins.bb.pred
        todo = list()  # deque() for BFS
        todo.append((path, loops, pred))
        while todo:
            path, loops, pred = todo.pop()
            if path[-1] == 0:
                yield path[::-1]
            for p in pred:
                if loops[p] < loop_limit:
                    new_path = path + [p.start]
                    new_pred = p.pred
                    new_loops = defaultdict(int, loops)
                    new_loops[p] += 1
                    todo.append((new_path, new_loops, new_pred))

    def get_successful_paths_from(self, path, loop_limit=1):
        loops = defaultdict(int)
        bbs = [self._bb_at[p] for p in path if p in self._bb_at]
        for bb in bbs:
            loops[bb] = 1
        todo = deque()
        todo.appendleft((path, loops, bbs[-1].succ))
        while todo:
            path, loop, succ = todo.pop()
            for s in succ:
                if loops[s] < loop_limit:
                    new_path = path + [s.start]
                    if s.ins[-1].name in ('STOP', 'RETURN'):
                        yield new_path + [s.ins[-1].addr]
                    else:
                        new_loops = defaultdict(int, loops)
                        new_loops[s] += 1
                        todo.appendleft((new_path, new_loops, s.succ))
