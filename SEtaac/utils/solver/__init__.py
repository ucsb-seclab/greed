from SEtaac.utils.solver.shortcuts import *


# NOTHING HERE WORKS ########


def concrete(v):
    print("WARNING: concrete is NOT PROPERLY IMPLEMENTED. Please replace with Solver.is_concrete()")
    return False


def is_false(cond, s=None):
    raise Exception("NOT IMPLEMENTED. Please replace with Solver.is_formula_false()")


def is_true(cond, s=None):
    raise Exception("NOT IMPLEMENTED. Please replace with Solver.is_formula_true()")


def translate_xid(expr, old_xid, new_xid):
    if old_xid != new_xid:
        raise Exception("NOT IMPLEMENTED")
    return expr
