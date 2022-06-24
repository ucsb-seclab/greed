import numbers
import z3


def ctx_or_symbolic(v, ctx, xid):
    return ctx.get(v, z3.BitVec('%s_%d' % (v, xid), 256))


def concrete(v):
    return isinstance(v, numbers.Number)


def is_false(cond, s=None):
    s = s or get_solver()

    # backup the solver
    s.push()

    # add the constraint
    s.add(cond)

    # check if sat
    res = (s.check() == z3.unsat)

    # restore the solver
    s.pop()

    return res


def is_true(cond, s=None):
    # NOTE: This differs from `not is_false(cond)`, which corresponds to "may be true"
    return is_false(z3.Not(cond), s)


def is_unsat(cond, s=None):
    s = s or get_solver()

    # backup the solver
    s.push()

    # add the constraint
    s.add(cond)

    # check if sat
    res = (s.check() == z3.unsat)

    # restore the solver
    s.pop()

    return res


def is_sat(cond, s=None):
    s = s or get_solver()

    # backup the solver
    s.push()

    # add the constraint
    s.add(cond)

    # check if sat
    res = (s.check() == z3.sat)

    # restore the solver
    s.pop()

    return res


def get_solver():
    z3.set_param('rewriter.blast_select_store', True)
    return z3.SolverFor('QF_ABV')


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
            else:
                todo.extend(expr.children())
        elif z3.is_const(expr):
            if not z3.z3util.is_expr_val(expr):
                rs.add(expr)
        else:
            todo.extend(expr.children())

    return rs


def translate_xid(expr, old_xid, new_xid):
    if old_xid == new_xid:
        return z3.substitute(expr, [])

    def raw(s):
        return '_'.join(s.split('_')[:-1])

    substitutions = dict()

    for v in get_vars_non_recursive(expr):
        if v not in substitutions:
            v_name = raw(v.decl().name())
            if v.sort_kind() == z3.Z3_INT_SORT:
                substitutions[v] = z3.Int('%s_%d' % (v_name, new_xid))
            elif v.sort_kind() == z3.Z3_BOOL_SORT:
                substitutions[v] = z3.Bool('%s_%d' % (v_name, new_xid))
            elif v.sort_kind() == z3.Z3_BV_SORT:
                substitutions[v] = z3.BitVec('%s_%d' % (v_name, new_xid), v.size())
            elif v.sort_kind() == z3.Z3_ARRAY_SORT:
                substitutions[v] = z3.Array('%s_%d' % (v_name, new_xid), v.domain(), v.range())
            else:
                raise Exception('CANNOT CONVERT %s (%d)' % (v, v.sort_kind()))
    subst = list(substitutions.items())
    return z3.substitute(expr, subst)
