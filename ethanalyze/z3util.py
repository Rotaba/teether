import logging
from binascii import unhexlify

import z3


def to_bytes(v):
    s = (v.size() / 8) * 2
    fmt = '%%0%dx' % s
    v_str = fmt % (v.as_long())
    return unhexlify(v_str)


def get_vars(f, rs=set()):
    """
    shameless copy of z3util.get_vars,
    but returning select-operations as well.
    E.g.
    >>> x = z3.Array('x', z3.IntSort(), z3.IntSort())
    >>> get_vars(x[5])
    [x[5]]
    whereas
    >>> x = z3.Array('x', z3.IntSort(), z3.IntSort())
    >>> z3util.get_vars(x[5])
    [x]
    """
    if not rs:
        f = z3.simplify(f)

    if f.decl().kind() == z3.Z3_OP_SELECT:
        arr, idx = f.children()
        if z3.is_const(arr):
            if z3.z3util.is_expr_val(idx):
                return rs | {f}
            else:
                return rs | {f, idx}
    if z3.is_const(f):
        if z3.z3util.is_expr_val(f):
            return rs
        else:  # variable
            return rs | {f}

    else:
        for f_ in f.children():
            rs = get_vars(f_, rs)

        return set(rs)


def add_suffix(expr, level, additional_subst):
    substitutions = {k:v for k,v in additional_subst}
    for v in z3.z3util.get_vars(expr):
        if v not in substitutions:
            if v.sort_kind() == z3.Z3_INT_SORT:
                substitutions[v] = z3.Int('%s_%d' % (v.decl().name(), level))
            elif v.sort_kind() == z3.Z3_BOOL_SORT:
                substitutions[v] = z3.Bool('%s_%d' % (v.decl().name(), level))
            elif v.sort_kind() == z3.Z3_BV_SORT:
                substitutions[v] = z3.BitVec('%s_%d' % (v.decl().name(), level), v.size())
            elif v.sort_kind() == z3.Z3_ARRAY_SORT:
                substitutions[v] = z3.Array('%s_%d' % (v.decl().name(), level), v.domain(), v.range())
            else:
                raise Exception('CANNOT CONVERT %s (%d)' % (v, v.sort_kind()))
    subst = substitutions.items()
    return z3.substitute(expr, subst)