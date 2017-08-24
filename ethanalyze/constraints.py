import logging
from binascii import hexlify
from collections import defaultdict

from z3 import z3, z3util

import utils
from .evm import IntractablePath
from .z3util import get_vars, to_bytes


def array_to_array(array_model, length=0):
    l = array_model.as_list()
    entries, else_value = l[:-1], l[-1]
    length = max(max(e[0].as_long() for e in entries) + 1, length)
    arr = [else_value.as_long()] * length
    for e in entries:
        arr[e[0].as_long()] = e[1].as_long()
    return arr


def get_level(name):
    try:
        if '_' in name:
            return int(name[name.rfind('_') + 1:])
        else:
            return int(name)
    except:
        return 0


def model_to_calls(model):
    calls = defaultdict(dict)
    for v in model:
        name = v.name()
        if name.startswith('CALLDATA'):
            call_index = get_level(name[9:])
            calls[call_index]['payload'] = ''.join(map(chr, array_to_array(model[v])))
        elif name.startswith('CALLVALUE'):
            call_index = get_level(name[10:])
            calls[call_index]['value'] = model[v].as_long()
        elif name.startswith('CALLER'):
            call_index = get_level(name[7:])
            calls[call_index]['caller'] = model[v].as_long()
        else:
            logging.warning('CANNOT CONVERT %s', name)
            #            call[name] = model[v].as_long()

    return [v for k, v in sorted(calls.iteritems(), reverse=True)]


def check_and_model(constraints, sha_constraints):

    if not sha_constraints:
        sol = z3.Solver()
        sol.add(constraints)
        if sol.check() != z3.sat:
            raise IntractablePath()
        return sol.model()

    unresolved = set(sha_constraints.keys())
    sol = z3.Solver()
    todo = constraints
    while todo:
        new_todo = []
        for c in todo:
            if any(x in unresolved for x in get_vars(c)):
                new_todo.append(c)
            else:
                sol.add(c)
        unresolved_vars = set(v for c in new_todo for v in get_vars(c))
        if sol.check() != z3.sat:
            raise IntractablePath()
        m = sol.model()
        for u in set(unresolved):
            c = sha_constraints[u]
            if any(x in unresolved_vars for x in get_vars(c)):
                continue
            v = m.eval(c)
            logging.debug("Hashing %s", hexlify(to_bytes(v)))
            if z3util.is_expr_val(v):
                sha = utils.big_endian_to_int(utils.sha3(to_bytes(v)))
                sol.add(c == v)
                sol.add(u == sha)
                unresolved.remove(u)
        todo = new_todo
    if sol.check() != z3.sat:
        raise IntractablePath()
    return sol.model()


def dependency_summary(constraints, sha_constraints, detailed=False):
    if detailed:
        _get_vars = get_vars
    else:
        _get_vars = z3util.get_vars
    all_dependencies = set(x for c in constraints if z3.is_expr(c) for x in _get_vars(z3.simplify(c)))
    changed = True
    while changed:
        changed = False
        for x in set(all_dependencies):
            if x in sha_constraints:
                changed = True
                all_dependencies.discard(x)
                all_dependencies.update(_get_vars(z3.simplify(sha_constraints[x])))
    return all_dependencies