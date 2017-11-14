import logging
from binascii import unhexlify
from collections import defaultdict

from .cfg import CFG
from .disassembly import generate_BBs
from .evm import run, run_symbolic, IntractablePath, concrete, ExternalData
from .slicing import interesting_slices
from .slicing import slice_to_program


def load(path):
    with open(path) as infile:
        return Project(unhexlify(infile.read().strip()))


class Project(object):
    def __init__(self, code, cfg=None):
        self.code = code
        self._prg = None
        self._cfg = cfg
        self._writes = None

    @property
    def writes(self):
        if not self._writes:
            self._analyze_writes()
        return self._writes

    @property
    def symbolic_writes(self):
        return self.writes[None]

    @property
    def cfg(self):
        if not self._cfg:
            self._cfg = CFG(generate_BBs(self.code))
        return self._cfg

    @property
    def prg(self):
        if not self._prg:
            self._prg = {ins.addr: ins for bb in self.cfg.bbs for ins in bb.ins}
        return self._prg

    def filter_ins(self, names):
        return self.cfg.filter_ins(names)

    def run(self, program):
        return run(program, code=self.code)

    def run_symbolic(self, path, inclusive=False):
        return run_symbolic(self.prg, path, self.code, inclusive=inclusive)

    def get_constraints(self, instructions, args=None, inclusive=False, predicate=None):
        for ins in instructions:
            if args:
                slices = interesting_slices(ins, args)
                # Check if ins.bb is set, as slices include padding instructions (PUSH, POP)
                interesting_sub_paths = [[i.bb.start for i in bs if i.bb] for bs in slices]
            for path in self.cfg.get_paths(ins, predicate=predicate):
                logging.debug('Path %s', ' -> '.join('%x' % p for p in path))
                # If this path is NOT a superset of an interesting slice, skip it
                if args and not any(all(loc in path for loc in sub_path) for sub_path in interesting_sub_paths):
                    continue
                try:
                    logging.debug('This could be interesting...')
                    yield ins, path, self.run_symbolic(path, inclusive)
                except IntractablePath:
                    continue
                except ExternalData:
                    continue
                except Exception as e:
                    logging.exception('Failed path due to %s', e)
                    continue

    def _analyze_writes(self):
        sstore_ins = self.filter_ins('SSTORE')
        self._writes = defaultdict(set)
        for store in sstore_ins:
            for bs in interesting_slices(store):
                bs.append(store)
                prg = slice_to_program(bs)
                path = sorted(prg.keys())
                try:
                    r = run_symbolic(prg, path, self.code, inclusive=True)
                except IntractablePath:
                    logging.exception('Intractable Path while analyzing writes')
                    continue
                addr = r.state.stack[-1]
                if concrete(addr):
                    self._writes[addr].add(store)
                else:
                    self._writes[None].add(store)
        self._writes = dict(self._writes)

    def get_writes_to(self, addr):
        concrete_writes = set()
        if concrete(addr) and addr in self.writes:
            concrete_writes = self.writes[addr]
        return concrete_writes, self.symbolic_writes
