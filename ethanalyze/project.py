import logging
from binascii import unhexlify
from collections import defaultdict

from .explorer import Explorer
from .opcodes import external_data
from .cfg import CFG
from .disassembly import generate_BBs
from .evm import run, run_symbolic, IntractablePath, concrete, ExternalData
from .slicing import interesting_slices, concrete_addr_slices
from .slicing import slice_to_program

#R:
from copy import copy

def load(path):
    with open(path) as infile:
        return Project(unhexlify(infile.read().strip()))

def load_json(path):
    import json
    with open(path) as infile:
        return Project.from_json(json.load(infile))


#init for new P, writes
class Project(object):
    def __init__(self, code, cfg=None, contract_addr=None):
        self.code = code
        self._prg = None
        self._cfg = cfg
        self._writes = None
        #R
        self.contract_addr = contract_addr

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
            self._cfg = CFG(generate_BBs(self.code)) #generate BB of the CFG
        return self._cfg

    @property
    def prg(self):
        if not self._prg:
            #??? diff to code?
            #Program; dict; inst_addr as key, instruction as value?
            self._prg = {ins.addr: ins for bb in self.cfg.bbs for ins in bb.ins}
        return self._prg

    def to_json(self):
        from binascii import hexlify
        return {'code': hexlify(self.code), 'cfg': self.cfg.to_json()}

    @staticmethod
    def from_json(json_dict):
        code = unhexlify(json_dict['code'])
        cfg = CFG.from_json(json_dict['cfg'], code)
        return Project(code, cfg)

    def run(self, program):
        return run(program, code=self.code)

    def run_symbolic(self, path, inclusive=False, getHead=False, callee_project=None, state=None, term_on_interCall=False, storage_index=None):
        return run_symbolic(self.prg, path, self.code, inclusive=inclusive, state=state, term_on_interCall=term_on_interCall, storage_index=storage_index)

    def get_constraints(self, instructions, args=None, inclusive=False, find_sstore=False,
                        find_terminate=False, import_state=None, term_on_interCall=False, storage_index=None):
        # only check instructions that have a chance to reach root
        instructions = [ins for ins in instructions if (0 in ins.bb.ancestors|{ins.bb.start}) ]
        if not instructions:
            return
        #create a dict inst_addr as key, inst as value
        imap = {ins.addr: ins for ins in instructions}
        #for path in self.cfg.get_paths(instructions, predicate=predicate):

        #init A* explorer with CFG
        exp = Explorer(self.cfg)

        # check the given inst for Attacker in-/directly controllable BackwardSlices
        if find_sstore:
            sstores = self.cfg.filter_ins('SSTORE', reachable=True)
            slices = [(sstore, ins) for sstore in sstores for ins in instructions]
        elif args and args==[42]:
            slices = [(ins,) for ins in instructions]
        elif args:
            # interesting slices ; #As we require that
            # this argument is potentially attacker controlled, slices
            # are then filtered for those containing instructions whose
            # results can be directly (ORIGIN, CALLER, CALLVALUE,CALLDATALOAD, CALLDATASIZE, CALLDATACOPY)
            # or
            # in-directly (SLOAD, MLOAD) controlled by an attacker
            # (there's a chance we could change those slots on other path).
            slices = [s + (ins,) for ins in instructions for s in interesting_slices(ins, args, reachable=True)]
        #R:
        elif find_terminate:
        #TODO although suicide is a valid terminating op, it could lead to false positives on attempt_exploit/?
            term_instr = self.cfg.filter_ins('RETURN', reachable=True) + self.cfg.filter_ins('STOP', reachable=True)
                                #+ self.cfg.filter_ins('SUICIDE', reachable=True)
            imap = {ins.addr: ins for ins in term_instr} #or else it would fail on ins = imap[path[-1]] below
            slices = [(ins, t_i) for t_i in term_instr for ins in instructions]
        ## R:
        # elif interesting_wo_call_inbetween:
        #     inter_slices = [s + (ins,) for ins in instructions for s in interesting_slices(ins,[0], reachable=True)] #notice args -> [0]
        #     call_ins = self.cfg.filter_ins('DELEGATECALL', reachable=True) #TODO add the CALLCODE/CALL to the list of flitered ops - notice that those three are also the llok after CC ops
        #                # + self.cfg.filter_ins('CALL',reachable=True) + self.cfg.filter_ins('CALLCODE', reachable=True)
        #     # imap = {ins.addr: ins for ins in terminating_instr}  # or else it would fail on ins = imap[path[-1]]
        #     for call_op in  call_ins:
        #         for sli in inter_slices:
        #             if call_op in sli:
        #                 inter_slices.remove(sli)
        ## J:
        else: #no flag; just boring path to requested op
            slices = [(ins,) for ins in instructions]

        #debugg:
        token = 0

        # explore the newly newly acquired BackwardSlices using the A*Explorer to generate paths
        # generate constrains for the Paths we found using symbolic exec;
        for path in exp.find(slices, avoid=external_data):
            #if slices is a tupel like in the "find_sstore" flag; it would llok for possible combinations where the SSTORE is on the path of RETURN/STOP
            logging.info('Path on slice %s', ' -> '.join('%x' % p for p in path))
            try:
                  #use last inst_addr in path as index to get the corresponding inst from imap
                ins = imap[path[-1]]
                # becasue this is a loop; we can't simply pass a object as ref - on next loop it will be altered; so we pass a copy
                copy_of_i_s = copy(import_state)
                #debugg
                # if (token > 500) and False:
                #     break
                # else:
                #     token += 1
                #     print token
                # logging.info("g_c path %s" % path)
                yield ins, path, self.run_symbolic(path, inclusive, state=copy_of_i_s, term_on_interCall=term_on_interCall, storage_index=storage_index)
            except IntractablePath as e:
                bad_path = [i for i in e.trace if i in self.cfg._bb_at] + [e.remainingpath[0]]
                dd = self.cfg.data_dependence(self.cfg._ins_at[e.trace[-1]])
                if not any(i.name in ('MLOAD', 'SLOAD') for i in dd):
                    ddbbs = set(i.bb.start for i in dd)
                    ##gitHUB fix, old: bad_path_start = next(j for j,i in enumerate(bad_path) if i in ddbbs)
                    bad_path_start = next((j for j, i in enumerate(bad_path) if i in ddbbs), 0)
                    bad_path = bad_path[bad_path_start:]
                logging.info("Bad path: %s" % (', '.join('%x' % i for i in bad_path)))
                exp.add_to_blacklist(bad_path)
                continue
            except ExternalData:
                continue
            except Exception as e:
                logging.exception('Failed path due to %s', e)
                continue



    # #both FULL and PART functions call get_constrains twice; once for head and once for callee
    # # this meant that when head gave 1 value back; it would break when callee asked for get_constrains
    # # so I created a clone; it's a hack - but it works
    # def get_constraints_CLONE(self, instructions, args=None, inclusive=False, find_sstore=False,
    #                     find_terminate=False, import_state=None, term_on_DC=False, storage_index=None):
    #     # only check instructions that have a chance to reach root
    #     instructions = [ins for ins in instructions if (0 in ins.bb.ancestors | {ins.bb.start})]
    #     if not instructions:
    #         return
    #     # create a dict inst_addr as key, inst as value
    #     imap = {ins.addr: ins for ins in instructions}
    #     # for path in self.cfg.get_paths(instructions, predicate=predicate):
    #
    #     # init A* explorer with CFG
    #     exp = Explorer(self.cfg)
    #
    #     # check the given inst for Attacker in-/directly controllable BackwardSlices
    #     if find_sstore:
    #         sstores = self.cfg.filter_ins('SSTORE', reachable=True)
    #         slices = [(sstore, ins) for sstore in sstores for ins in instructions]
    #     elif args:
    #         # interesting slices ; #As we require that
    #         # this argument is potentially attacker controlled, slices
    #         # are then filtered for those containing instructions whose
    #         # results can be directly (ORIGIN, CALLER, CALLVALUE,CALLDATALOAD, CALLDATASIZE, CALLDATACOPY)
    #         # or
    #         # in-directly (SLOAD, MLOAD) controlled by an attacker
    #         # (there's a chance we could change those slots on other path).
    #         slices = [s + (ins,) for ins in instructions for s in interesting_slices(ins, args, reachable=True)]
    #     # R:
    #     elif find_terminate:
    #         # TODO although suicide is a valid terminating op, it could lead to false positives on attempt_exploit/?
    #         term_instr = self.cfg.filter_ins('RETURN', reachable=True) + self.cfg.filter_ins('STOP', reachable=True)
    #         # + self.cfg.filter_ins('SUICIDE', reachable=True)
    #         imap = {ins.addr: ins for ins in term_instr}  # or else it would fail on ins = imap[path[-1]] below
    #         slices = [(ins, t_i) for t_i in term_instr for ins in instructions]
    #     ## R:
    #     # elif interesting_wo_call_inbetween:
    #     #     inter_slices = [s + (ins,) for ins in instructions for s in interesting_slices(ins,[0], reachable=True)] #notice args -> [0]
    #     #     call_ins = self.cfg.filter_ins('DELEGATECALL', reachable=True) #TODO add the CALLCODE/CALL to the list of flitered ops - notice that those three are also the llok after CC ops
    #     #                # + self.cfg.filter_ins('CALL',reachable=True) + self.cfg.filter_ins('CALLCODE', reachable=True)
    #     #     # imap = {ins.addr: ins for ins in terminating_instr}  # or else it would fail on ins = imap[path[-1]]
    #     #     for call_op in  call_ins:
    #     #         for sli in inter_slices:
    #     #             if call_op in sli:
    #     #                 inter_slices.remove(sli)
    #     ## J:
    #     else:  # no flag; just boring path to requested op
    #         slices = [(ins,) for ins in instructions]
    #
    #     # explore the newly newly acquired BackwardSlices using the A*Explorer to generate paths
    #     # generate constrains for the Paths we found using symbolic exec;
    #     for path in exp.find(slices, avoid=external_data):
    #         # if slices is a tupel like in the "find_sstore" flag; it would llok for possible combinations where the SSTORE is on the path of RETURN/STOP
    #         logging.debug('Path %s', ' -> '.join('%x' % p for p in path))
    #         try:
    #             # logging.info("g_c_CLONE path %s" % path)
    #             # use last inst_addr in path as index to get the corresponding inst from imap
    #             ins = imap[path[-1]]
    #             # becasue this is a loop; we can't simply pass a object as ref - on next loop it will be altered; so we pass a copy
    #             copy_of_i_s = copy(import_state)
    #             yield ins, path, self.run_symbolic(path, inclusive, state=copy_of_i_s, term_on_DC=term_on_DC, storage_index=storage_index)
    #         except IntractablePath as e:
    #             bad_path = [i for i in e.trace if i in self.cfg._bb_at] + [e.remainingpath[0]]
    #             dd = self.cfg.data_dependence(self.cfg._ins_at[e.trace[-1]])
    #             if not any(i.name in ('MLOAD', 'SLOAD') for i in dd):
    #                 ddbbs = set(i.bb.start for i in dd)
    #                 bad_path_start = next(j for j, i in enumerate(bad_path) if i in ddbbs)
    #                 bad_path = bad_path[bad_path_start:]
    #             logging.info("Bad path: %s" % (', '.join('%x' % i for i in bad_path)))
    #             exp.add_to_blacklist(bad_path)
    #             continue
    #         except ExternalData:
    #             continue
    #         except Exception as e:
    #             logging.exception('Failed path due to %s', e)
    #             continue



    #search for SSTOREs
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
