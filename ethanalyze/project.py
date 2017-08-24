from binascii import unhexlify
import logging

from .opcodes import potentially_user_controlled
from .disassembly import generate_BBs
from .cfg import CFG
from .evm import run, run_symbolic, IntractablePath
from .slicing import backward_slice


class Project(object):

    @staticmethod
    def load(path):
        with open(path) as infile:
            return Project(unhexlify(infile.read().strip()))

    def __init__(self, code, cfg=None):
        self.code = code
        self._prg = None
        self._cfg = cfg

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

    def run_symbolic(self, path):
        return run_symbolic(self.prg, path, self.code)

    def get_constraints(self, instructions, args=None):
        for ins in instructions:
            interesting_slices = [bs for bs in backward_slice(ins, args) if any(
                ins.name in potentially_user_controlled for ins in bs)]
            # Check if ins.bb is set, as slices include padding instructions (PUSH, POP)
            interesting_sub_paths = [[i.bb.start for i in bs if i.bb] for bs in interesting_slices]
            pruned = 0
            for path in self.cfg.get_paths(ins):
                # If this path is NOT a superset of an interesting slice, skip it
                if not any(all(loc in path for loc in sub_path) for sub_path in interesting_sub_paths):
                    continue
                try:
                    yield ins, path, self.run_symbolic(path)
                except IntractablePath:
                    continue
                except Exception as e:
                    logging.exception('Failed path due to %s', e)
                    continue
