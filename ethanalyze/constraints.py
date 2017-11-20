import copy
import itertools
import logging
from binascii import hexlify
from collections import defaultdict

from z3 import z3, z3util

import utils
from .evm import IntractablePath, simplify_non_const_hashes, SymRead, concrete
from .z3_extra_util import get_vars_non_recursive, to_bytes


class UnresolvedConstraints(Exception):
    def __init__(self, unresolved):
        super(UnresolvedConstraints, self).__init__(unresolved)
        self.unresolved = unresolved


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
        if name.startswith('CALLDATASIZE'):
            # ignore for now...
            pass
        elif name.startswith('CALLDATA'):
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

    return [v for k, v in sorted(calls.iteritems())]


def symread_eq(a, b, MAX_SYM_READ_SIZE=512):
    if not isinstance(a, SymRead) and not isinstance(b, SymRead):
        if a.size() != b.size():
            return z3.BoolVal(False)
        else:
            return a == b
    elif isinstance(a, SymRead) and isinstance(b, SymRead):
        # both have symbolic size
        return z3.And(a.size == b.size,
                      *(z3.If(z3.ULT(i, a.size), a.memory[a.start + i] == b.memory[b.start + i], True) for i in
                        xrange(MAX_SYM_READ_SIZE)))
    else:
        if isinstance(b, SymRead):
            # ensure that a is the one with symbolic size
            a, b = b, a
        return z3.And(a.size == (b.size() // 8), z3.Concat(*a.memory.read(a.start, b.size() // 8)) == b)


def symread_neq(a, b, MAX_SYM_READ_SIZE=512):
    return z3.Not(symread_eq(a, b, MAX_SYM_READ_SIZE))


def symread_substitute(x, subst):
    if not isinstance(x, SymRead):
        return z3.simplify(z3.substitute(x, subst))
    else:
        new_symread = copy.copy(x)
        new_symread.memory.memory = z3.simplify(z3.substitute(new_symread.memory.memory, subst))
        if not concrete(new_symread.start):
            new_symread.start = z3.simplify(z3.substitute(new_symread.start, subst))
        if not concrete(new_symread.size):
            new_symread.size = z3.simplify(z3.substitute(new_symread.size, subst))
        return new_symread


def check_model_and_resolve(constraints, sha_constraints):
    constraints = [simplify_non_const_hashes(c, sha_constraints.keys()) for c in constraints]
    logging.debug('-' * 32)
    extra_constraints = []

    while True:
        for a, b in itertools.combinations(sha_constraints.keys(), 2):
            if (not isinstance(sha_constraints[a], SymRead) and not isinstance(sha_constraints[b], SymRead) and
                        sha_constraints[a].size() != sha_constraints[b].size()):
                continue
            s = z3.Solver()
            s.add(constraints + extra_constraints + [a != b, symread_neq(sha_constraints[a], sha_constraints[b])])
            check_result = s.check()
            logging.debug("Checking hashes %s and %s: %s", a, b, check_result)
            if check_result == z3.unsat:
                logging.debug("Hashes MUST be equal: %s and %s", a, b)
                extra_constraints.append(symread_eq(sha_constraints[a], sha_constraints[b]))
                subst = [(a, b)]
                constraints = [z3.simplify(z3.substitute(c, subst)) for c in constraints]
                sha_constraints = {z3.substitute(sha, subst): symread_substitute(sha_value, subst) for
                                   sha, sha_value in
                                   sha_constraints.items()}
                break
            else:
                logging.debug("Hashes COULD be equal: %s and %s", a, b)
        else:
            break


    return check_and_model(constraints + extra_constraints, sha_constraints)


def check_and_model(constraints, sha_constraints):
    logging.debug(' ' * 16 + '-' * 16)
    if not sha_constraints:
        sol = z3.Solver()
        sol.add(constraints)
        if sol.check() != z3.sat:
            raise IntractablePath()
        return sol.model()

    unresolved = set(sha_constraints.keys())
    sol = z3.Solver()
    todo = constraints
    progress = True
    while todo and progress:
        new_todo = []
        progress = False
        for c in todo:
            if any(x in unresolved for x in get_vars_non_recursive(c, True)):
                new_todo.append(c)
            else:
                progress = True
                sol.add(c)
        unresolved_vars = set(v.get_id() for c in new_todo for v in get_vars_non_recursive(c, True))
        logging.debug("Unresolved vars: %s", ','.join(map(str, unresolved_vars)))
        if sol.check() != z3.sat:
            raise IntractablePath()
        m = sol.model()
        unresolved_todo = list(set(unresolved))
        while unresolved_todo:
            u = unresolved_todo.pop()
            c = sha_constraints[u]
            if isinstance(c, SymRead):
                vars = set()
                if not concrete(c.start):
                    vars |= get_vars_non_recursive(c.start, True)
                if not concrete(c.size):
                    vars |= get_vars_non_recursive(c.size, True)
                logging.debug("Trying to resolve %s, start and size vars: %s", u, ','.join(map(str, vars)))
                if any(x.get_id() in unresolved_vars for x in vars):
                    continue
                start = c.start
                if not concrete(c.start):
                    tmp = m.eval(c.start)
                    if not z3util.is_expr_val(tmp):
                        continue
                    start = tmp.as_long()
                    sol.add(c.start == start)
                size = c.size
                if not concrete(c.size):
                    tmp = m.eval(c.size)
                    if not z3util.is_expr_val(tmp):
                        continue
                    size = tmp.as_long()
                    sol.add(c.size == size)

                data = z3.Concat(*c.memory.read(start, size))
                sha_constraints = dict(sha_constraints)
                sha_constraints[u] = data
                unresolved_todo.append(u)
            else:
                vars = get_vars_non_recursive(c, True)
                logging.debug("Trying to resolve %s, vars: %s", u, ','.join(map(str, vars)))
                if any(x.get_id() in unresolved_vars for x in vars):
                    continue
                v = m.eval(c)
                if z3util.is_expr_val(v):
                    logging.debug("%s can be resolved", u)
                    logging.debug("Hashing %s", hexlify(to_bytes(v)))
                    sha = utils.big_endian_to_int(utils.sha3(to_bytes(v)))
                    sol.add(c == v)
                    sol.add(u == sha)
                    unresolved.remove(u)
                    progress = True
        todo = new_todo
    if sol.check() != z3.sat:
        raise IntractablePath()
    if todo:
        raise UnresolvedConstraints(unresolved)
    return sol.model()


def dependency_summary(constraints, sha_constraints, detailed=False):
    all_dependencies = set(x for c in constraints if z3.is_expr(c) for x in
                           get_vars_non_recursive(z3.simplify(c), include_select=detailed))
    changed = True
    while changed:
        changed = False
        for x in set(all_dependencies):
            if x in sha_constraints:
                changed = True
                all_dependencies.discard(x)
                all_dependencies.update(
                    get_vars_non_recursive(z3.simplify(sha_constraints[x], include_select=detailed)))
    return all_dependencies
