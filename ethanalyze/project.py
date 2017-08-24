from binascii import unhexlify

from .disassemble import generate_BBs
from .cfg import CFG
from .evm import run, run_symbolic


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
        return run(program, self.code)

    def run_symbolic(self, path):
        return run_symbolic(self.prg, path, self.code)