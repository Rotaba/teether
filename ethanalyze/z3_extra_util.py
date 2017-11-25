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


def get_vars_non_recursive(f, include_select=False, include_indices=True):
    todo = [f]
    rs = set()
    seen = set()
    while todo:
        expr = todo.pop()
        if expr.get_id() in seen:
            continue
        seen.add(expr.get_id())
        if include_select and expr.decl().kind() == z3.Z3_OP_SELECT:
            arr, idx = expr.children()
            if z3.is_const(arr):
                if not include_indices or z3.z3util.is_expr_val(idx):
                    rs.add(expr)
                else:
                    rs.add(expr)
                    todo.append(idx)
        elif z3.is_const(expr):
            if not z3.z3util.is_expr_val(expr):
                rs.add(expr)
        else:
            todo.extend(expr.children())

    return rs