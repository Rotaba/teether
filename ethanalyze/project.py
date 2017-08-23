from binascii import unhexlify
from .ethereum import CFG, generate_BBs, cfg_to_program, run_symbolic


class Project(object):

    @staticmethod
    def load(path):
        with open(path) as infile:
            return Project(unhexlify(infile.read().strip()))

    def __init__(self, code):
        self.code = code
        self._prg = None
        self._cfg = None

    @property
    def cfg(self):
        if not self._cfg:
            self._cfg = CFG(generate_BBs(self.code))
        return self._cfg

    @property
    def prg(self):
        if not self._prg:
            self._prg = cfg_to_program(self.cfg)
        return self._prg

    def filter_ins(self, names):
        return self.cfg.filter_ins(names)

    def run_symbolic(self, path):
        return run_symbolic(self.prg, path, self.code)