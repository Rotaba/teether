import logging
from binascii import hexlify
from collections import defaultdict, deque

from .cfg_back_traversal import traverse_back
from .memory import UninitializedRead
from .opcodes import opcodes


def unique(l):
    last = None
    for i in l:
        if i != last:
            yield i
        last = i


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
        self.gas = opinfo[3]
        self.delta = self.outs - self.ins
        self.bb = None

    def __str__(self):
        return '(%5d) %4x:\t%02x\t-%d +%d = %d\t%s%s' % (
            self.addr, self.addr, self.op, self.ins, self.outs, self.delta, self.name,
            '(%d) %s' % (int(hexlify(self.arg), 16), '\t%s' % hexlify(self.arg)) if self.arg else '')

    def __repr__(self):
        return str(self)

    def __hash__(self):
        return 17 * self.addr + 19 * self.op + 23 * hash(self.arg)

    def __eq__(self, other):
        return (self.addr == other.addr and
                self.op == other.op and
                self.arg == other.arg)


class BB(object):
    def __init__(self, ins):
        self.ins = ins
        for i in ins:
            i.bb = self
        self.start = self.ins[0].addr
        self.pred = set()
        self.succ = set()
        self.succ_addrs = set()
        self.pred_paths = defaultdict(set)
        self.branch = self.ins[-1].op == 0x57
        self.indirect_jump = self.ins[-1].op in (0x56, 0x57)
        self.ancestors = set()
        self.descendants = set()
        # maintain a set of 'must_visit' contraints to limit
        # backward-slices to only new slices after new egdes are added
        # initialliy, no constrain is given (= empty set)
        self.must_visit = [set()]
        # also maintain an estimate of how fast we can get from here
        # to the root of the cfg
        # how fast meaning, how many JUMPI-branches we have to take
        self.estimate_constraints = (1 if self.branch else 0) if self.start == 0 else None
        # and another estimate fo many backwards branches
        # we will encouter to the root
        self.estimate_back_branches = 0 if self.start == 0 else None

    @property
    def jump_resolved(self):
        return not self.indirect_jump or len(self.must_visit) == 0

    def update_ancestors(self, new_ancestors):
        new_ancestors = new_ancestors - self.ancestors
        if new_ancestors:
            self.ancestors.update(new_ancestors)
            for s in self.succ:
                s.update_ancestors(new_ancestors)

    def update_descendants(self, new_descendants):
        new_descendants = new_descendants - self.descendants
        if new_descendants:
            self.descendants.update(new_descendants)
            for p in self.pred:
                p.update_descendants(new_descendants)

    def update_estimate_constraints(self):
        if all(p.estimate_constraints is None for p in self.pred):
            return
        best_estimate = min(p.estimate_constraints for p in self.pred if p.estimate_constraints is not None)
        if self.branch:
            best_estimate += 1
        if self.estimate_constraints is None or best_estimate < self.estimate_constraints:
            self.estimate_constraints = best_estimate
            for s in self.succ:
                s.update_estimate_constraints()

    def update_estimate_back_branches(self):
        if all(p.estimate_back_branches is None for p in self.pred):
            return
        best_estimate = min(p.estimate_back_branches for p in self.pred if p.estimate_back_branches is not None)
        if len(self.pred)>1:
            best_estimate += 1
        if self.estimate_back_branches is None or best_estimate != self.estimate_back_branches:
            self.estimate_back_branches = best_estimate
            for s in self.succ:
                s.update_estimate_back_branches()

    def add_succ(self, other, path):
        self.succ.add(other)
        other.pred.add(self)
        self.update_descendants(other.descendants | {other.start})
        other.update_ancestors(self.ancestors | {self.start})
        other.update_estimate_constraints()
        other.update_estimate_back_branches()
        other.pred_paths[self].add(tuple(path))
        seen = set()
        todo = deque()
        todo.append(other)
        while todo:
            bb = todo.popleft()
            if bb not in seen:
                seen.add(bb)
                if bb.indirect_jump:
                    bb.must_visit.append({self.start})
                #logging.debug('BB@%x, must_visit: %s', bb.start, bb.must_visit)
                todo.extend(s for s in bb.succ if s not in seen)

    def _find_jump_target(self):
        if len(self.ins) >= 2 and 0x60 <= self.ins[-2].op <= 0x71:
            self.must_visit = []
            return int(hexlify(self.ins[-2].arg), 16)
        else:
            return None

    def get_succ_addrs_full(self, valid_jump_targets):
        from .slicing import slice_to_program, backward_slice
        from .evm import ExternalData, run
        new_succ_addrs = set()
        if self.indirect_jump and not self.jump_resolved:
            bs = backward_slice(self.ins[-1], [0], must_visits=self.must_visit)
            for b in bs:
                if 0x60 <= b[-1].op <= 0x7f:
                    succ_addr = int(hexlify(b[-1].arg), 16)
                else:
                    p = slice_to_program(b)
                    try:
                        succ_addr = run(p, check_initialized=True).stack.pop()
                    except (ExternalData, UninitializedRead):
                        continue
                if succ_addr not in valid_jump_targets:
                    logging.warning('Jump to invalid address')
                    continue
                path = tuple(unique(ins.bb.start for ins in b if ins.bb))
                if succ_addr not in self.succ_addrs:
                    self.succ_addrs.add(succ_addr)
                if (path, succ_addr) not in new_succ_addrs:
                    new_succ_addrs.add((path, succ_addr))
        # We did our best,
        # if someone finds a new edge, jump_resolved will be set to False by the BFS in add_succ
        self.must_visit = []
        return self.succ_addrs, new_succ_addrs

    def get_succ_addrs(self, valid_jump_targets):
        if self.ins[-1].op in (0x56, 0x57):
            jump_target = self._find_jump_target()
            if jump_target is not None:
                self.indirect_jump = False
                if jump_target in valid_jump_targets:
                    self.succ_addrs.add(jump_target)
            else:
                self.indirect_jump = True
        else:
            self.must_visit = []
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

    def __cmp__(self, other):
        return cmp(self.start, other.start)


class CFG(object):
    def __init__(self, bbs, fix_xrefs=True, fix_only_easy_xrefs=False):
        self.bbs = sorted(bbs)
        self._bb_at = {bb.start: bb for bb in self.bbs}
        self.valid_jump_targets = frozenset({bb.start for bb in self.bbs if bb.ins[0].name == 'JUMPDEST'})
        if fix_xrefs or fix_only_easy_xrefs:
            self._xrefs(fix_only_easy_xrefs)

    @property
    def bb_addrs(self):
        return frozenset(self._bb_at.keys())

    def filter_ins(self, names):
        if isinstance(names, basestring):
            names = [names]
        return [ins for bb in self.bbs for ins in bb.ins if ins.name in names]

    def _xrefs(self, fix_only_easy_xrefs=False):
        #logging.debug('Fixing Xrefs')
        self._easy_xrefs()
        #logging.debug('Easy Xrefs fixed, turning to hard ones now')
        if not fix_only_easy_xrefs:
            self._hard_xrefs()
            #logging.debug('Hard Xrefs also fixed, good to go')

    def _easy_xrefs(self):
        for pred in self.bbs:
            for succ_addr in pred.get_succ_addrs(self.valid_jump_targets):
                if succ_addr and succ_addr in self._bb_at:
                    succ = self._bb_at[succ_addr]
                    pred.add_succ(succ, {pred.start})

    def _hard_xrefs(self):
        new_link = True
        links = set()
        while new_link:
            new_link = False
            for pred in self.bbs:
                if not pred.jump_resolved:
                    succ_addrs, new_succ_addrs = pred.get_succ_addrs_full(self.valid_jump_targets)
                    for new_succ_path, succ_addr in new_succ_addrs:
                        if not succ_addr in self._bb_at:
                            logging.warn(
                                'WARNING, NO BB @ %x (possible successor of BB @ %x)' % (succ_addr, pred.start))
                            continue
                        succ = self._bb_at[succ_addr]
                        pred.add_succ(succ, new_succ_path)
                        if not (pred.start, succ.start) in links:
                            #logging.debug('found new link from %x to %x', pred.start, succ.start)
                            with open('cfg-tmp%d.dot' % len(links), 'w') as outfile:
                                outfile.write(self.to_dot())
                            new_link = True
                            links.add((pred.start, succ.start))

    def __str__(self):
        return '\n\n'.join(str(bb) for bb in self.bbs)

    def to_dot(self):
        s = 'digraph g {\n'
        s += '\tsplines=ortho;\n'
        s += '\tnode[fontname="courier"];\n'
        for bb in sorted(self.bbs):
            from_block = 'From: ' + ', '.join('%x' % pred.start for pred in sorted(bb.pred))
            if bb.estimate_constraints is not None:
                from_block += '<br align="left"/>Min constraints from root: %d' % bb.estimate_constraints
            if bb.estimate_back_branches is not None:
                from_block += '<br align="left"/>Min back branches to root: %d' % bb.estimate_back_branches
            to_block = 'To: ' + ', '.join('%x' % succ.start for succ in sorted(bb.succ))
            ins_block = '<br align="left"/>'.join(
                '%4x: %02x %s %s' % (ins.addr, ins.op, ins.name, hexlify(ins.arg) if ins.arg else '') for ins in bb.ins)
            # ancestors = 'Ancestors: %s'%(', '.join('%x'%addr for addr in sorted(a for a in bb.ancestors)))
            # descendants = 'Descendants: %s' % (', '.join('%x' % addr for addr in sorted(a for a in bb.descendants)))
            # s += '\t%d [shape=box,label=<<b>%x</b>:<br align="left"/>%s<br align="left"/>%s<br align="left"/>%s<br align="left"/>>];\n' % (
            #    bb.start, bb.start, ins_block, ancestors, descendants)
            s += '\t%d [shape=box,label=<%s<br align="left"/><b>%x</b>:<br align="left"/>%s<br align="left"/>%s<br align="left"/>>];\n' % (
                bb.start, from_block, bb.start, ins_block, to_block)
        s += '\n'
        for bb in sorted(self.bbs):
            for succ in sorted(bb.succ):
                pths = succ.pred_paths[bb]
                s += '\t%d -> %d [xlabel="%s"];\n' % (
                    bb.start, succ.start, '|'.join(' -> '.join('%x' % a for a in p) for p in pths))
        s += '}'
        return s

    def to_json(self):
        return {'bbs':[{'start': bb.start,
                           'succs': [{'start': succ.start, 'paths': list(succ.pred_paths[bb])} for succ in
                                     sorted(bb.succ)]} for bb in sorted(self.bbs)]}

    @staticmethod
    def from_json(json_dict, code):
        from disassembly import disass
        bbs = list()
        for bb_dict in json_dict['bbs']:
            bbs.append(BB(list(disass(code, bb_dict['start']))))
        cfg = CFG(bbs, fix_xrefs=False)
        for bb_dict in json_dict['bbs']:
            bb = cfg._bb_at[bb_dict['start']]
            for succ_dict in bb_dict['succs']:
                succ = cfg._bb_at[succ_dict['start']]
                for path in succ_dict['paths']:
                    bb.add_succ(succ, path)
        return cfg



    @staticmethod
    def get_paths(start_ins, loop_limit=1, predicate=lambda st, pred: True):

        def initial_data(ins):
            return ins.addr, ins.bb.start

        def advance_data(path):
            return path

        def update_data(path, new_bb):
            return tuple(list(path) + [new_bb.start])

        def finish_path(path):
            return path[-1] == 0

        # TODO: BETTER FIX TO PREVENT INFINITE LOOPS
        for path in traverse_back(start_ins, 10, initial_data, advance_data, update_data, finish_path,
                                  predicate=predicate):
            yield path[::-1]

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
