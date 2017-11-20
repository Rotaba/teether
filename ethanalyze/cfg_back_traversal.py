import logging
from Queue import PriorityQueue

from .frontierset import FrontierSet


class TraversalState(object):
    def __init__(self, bb, gas, must_visit, data):
        self.bb = bb
        self.gas = gas
        self.must_visit = must_visit.copy()
        self.data = data

    def __hash__(self):
        return sum(a * b for a, b in zip((23, 29, 31), (hash(self.bb), hash(self.must_visit), hash(self.data))))

    def __eq__(self, other):
        return self.bb == other.bb and self.must_visit == other.must_visit and self.data == other.data

    def __str__(self):
        return 'At: %x, Gas: %s, Must-Visit: %s, Data: %s, Hash: %x' % (self.bb.start, self.gas, self.must_visit, self.data, hash(self))


def generate_sucessors(state, new_data, update_data, predicate=lambda st,pred:True):
    new_todo = []
    if state.gas is None or state.gas > 0:
        logging.debug('[tr] [gs] passed first if')
        new_gas = state.gas
        if state.gas and len(state.bb.pred) > 1:
            new_gas = state.gas - 1
        logging.debug('[tr] [gs] Preds: %s', state.bb.pred)
        for p in state.bb.pred:
            if not predicate(state.data, p):
                continue
            new_must_visits = []
            for path in state.bb.pred_paths[p]:
                new_must_visit = state.must_visit.copy()
                for a, b in zip(path[:-1], path[1:]):
                    new_must_visit.add(b, a)
                if p.start in new_must_visit.frontier:
                    new_must_visit.remove(p.start)
                if not new_must_visit.all.issubset(p.ancestors):
                    logging.debug('[tr] [gs] Cannot reach any necessary states, aborting! Needed: %s, reachable: %s', new_must_visit, p.ancestors)
                    continue
                new_must_visits.append(new_must_visit)

            for new_must_visit in minimize(new_must_visits):
                new_todo.append(TraversalState(p, new_gas, new_must_visit, update_data(new_data, p)))
    return new_todo


def traverse_back(ins, initial_gas, initial_data, advance_data, update_data, finish_path, must_visits=[], predicate=lambda st,p:True):
    """

    :param ins:
    :param initial_gas: Starting "gas". Can be None, in which case it is unlimited
    :param initial_data:
    :param advance_data:
    :param update_data:
    :param must_visits:
    :return:
    """
    logging.debug('[tr] Starting traversal at %x', ins.addr)
    data = initial_data
    bb = ins.bb
    gas = initial_gas
    # keep tuples of (len(must_visit), state)
    # this way, the least restricted state are preferred
    # which should maximize caching efficiency
    todo = PriorityQueue()
    if not must_visits:
        must_visits = [FrontierSet()]
    for must_visit in minimize(FrontierSet(mv) if mv is not FrontierSet else mv for mv in must_visits):
        todo.put((len(must_visit),
                  TraversalState(bb, gas, must_visit, data)))

    cache = set()
    while not todo.empty():
        _, state = todo.get()
        # if this BB can be reached via multiple paths, check if we want to cache it
        # or whether another path already reached it with the same state
        if len(state.bb.succ) > 1:
            if state in cache:
                logging.debug('[tr] CACHE HIT')
                continue
            cache.add(state)
        logging.debug('[tr] Cachesize: %d\t(slicing %x, currently at %x)', len(cache), ins.addr, state.bb.start)
        logging.debug('[tr] Current state: %s', state)
        new_data = advance_data(state.data)
        if finish_path(new_data):
            logging.debug('[tr] finished path (%s)', new_data)
            yield new_data
        else:
            logging.debug('[tr] continuing path (%s)', new_data)
            new_todo = generate_sucessors(state, new_data, update_data, predicate=predicate)
            for nt in new_todo:
                todo.put((len(nt.must_visit), nt))


def minimize(must_visits):
    todo = sorted(must_visits, key=len)
    while todo:
        must_visit = todo[0]
        yield must_visit
        todo = [mv for mv in todo[1:] if not must_visit.issubset(mv)]
