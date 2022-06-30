from SEtaac.utils.solver.shortcuts import *




















####### NOTHING HERE WORKS ########
def concrete(v):
    return False
    raise Exception("This doesn't work")
    # return isinstance(v, numbers.Number)


def is_false(cond, s=None):
    raise Exception("This doesn't work")
    # s = s or get_solver()
    #
    # # backup the solver
    # s.push()
    #
    # # add the constraint
    # s.add(cond)
    #
    # # check if sat
    # res = (s.check() == z3.unsat)
    #
    # # restore the solver
    # s.pop()
    #
    # return res


def is_true(cond, s=None):
    raise Exception("This doesn't work")
    # NOTE: This differs from `not is_false(cond)`, which corresponds to "may be true"
    # return is_false(z3.Not(cond), s)

#
# def is_unsat(cond, s=None):
#     raise Exception("This doesn't work")
#     # s = s or get_solver()
#     #
#     # # backup the solver
#     # s.push()
#     #
#     # # add the constraint
#     # s.add(cond)
#     #
#     # # check if sat
#     # res = (s.check() == z3.unsat)
#     #
#     # # restore the solver
#     # s.pop()
#     #
#     # return res


# def is_sat(cond, s=None):
#     raise Exception("This doesn't work")
#     # s = s or get_solver()
#     #
#     # # backup the solver
#     # s.push()
#     #
#     # # add the constraint
#     # s.add(cond)
#     #
#     # # check if sat
#     # res = (s.check() == z3.sat)
#     #
#     # # restore the solver
#     # s.pop()
#     #
#     # return res


def get_vars_non_recursive(f, include_select=False, include_indices=True):
    raise Exception("This doesn't work")
    # todo = [f]
    # rs = set()
    # seen = set()
    # while todo:
    #     expr = todo.pop()
    #     if expr.get_id() in seen:
    #         continue
    #     seen.add(expr.get_id())
    #     if include_select and expr.decl().kind() == z3.Z3_OP_SELECT:
    #         arr, idx = expr.children()
    #         if z3.is_const(arr):
    #             if not include_indices or z3.z3util.is_expr_val(idx):
    #                 rs.add(expr)
    #             else:
    #                 rs.add(expr)
    #                 todo.append(idx)
    #         else:
    #             todo.extend(expr.children())
    #     elif z3.is_const(expr):
    #         if not z3.z3util.is_expr_val(expr):
    #             rs.add(expr)
    #     else:
    #         todo.extend(expr.children())
    #
    # return rs


def translate_xid(expr, old_xid, new_xid):
    return expr

    raise Exception("This doesn't work")
    # if old_xid == new_xid:
    #     return z3.substitute(expr, [])
    #
    # def raw(s):
    #     return '_'.join(s.split('_')[:-1])
    #
    # substitutions = dict()
    #
    # for v in get_vars_non_recursive(expr):
    #     if v not in substitutions:
    #         v_name = raw(v.decl().name())
    #         if v.sort_kind() == z3.Z3_INT_SORT:
    #             substitutions[v] = z3.Int('%s_%d' % (v_name, new_xid))
    #         elif v.sort_kind() == z3.Z3_BOOL_SORT:
    #             substitutions[v] = z3.Bool('%s_%d' % (v_name, new_xid))
    #         elif v.sort_kind() == z3.Z3_BV_SORT:
    #             substitutions[v] = z3.BitVec('%s_%d' % (v_name, new_xid), v.size())
    #         elif v.sort_kind() == z3.Z3_ARRAY_SORT:
    #             substitutions[v] = z3.Array('%s_%d' % (v_name, new_xid), v.domain(), v.range())
    #         else:
    #             raise Exception('CANNOT CONVERT %s (%d)' % (v, v.sort_kind()))
    # subst = list(substitutions.items())
    # return z3.substitute(expr, subst)


def get_all_models(solver, terminals, n_max=256):
    raise Exception("This doesn't work")
    # if len(terminals) == 0:
    #     assert solver.check() == z3.sat
    #     return [solver.model()]
    #
    # t = terminals[0]
    #
    # # get all the solutions for the current terminal
    # solutions = eval_n_terminal(solver, t, n_max)
    #
    # # for every solution: backup the solver, fix the solution, recurse, restore the solver
    # models = []
    # for solution in solutions:
    #     # log.debug(f'processing solution {solution} for terminal {t}')
    #     solver.push()
    #     solver.add(t == solution)
    #     models += get_all_models(solver, terminals[1:], n_max)
    #     solver.pop()
    #
    # return models


def get_all_constraints(solver, expression, model):
    raise Exception("This doesn't work")
    # terminals = get_vars_non_recursive(solver, expression)
    # return [t == model[t] for t in terminals]


def eval_n_terminal(solver, t, n):
    raise Exception("This doesn't work")
    # solver.push()
    # solutions = []
    # for _ in range(n):
    #     if solver.check() == z3.unsat:
    #         break
    #     model = solver.model()
    #     sol = model.eval(t, model_completion=True)
    #     solutions += [sol]
    #
    #     # enforce distinct solutions
    #     solver.add(t != sol)
    # solver.pop()
    #
    # return solutions


def eval_all_expression(solver, expression, verifier=lambda expression: None, n_max=256):
    raise Exception("This doesn't work")
    # if isinstance(expression, (AbstractString, AbstractChar)):
    #     expression = expression.bv_repr
    #
    # terminals = get_vars_non_recursive(expression)
    # models = get_all_models(solver, terminals, n_max)
    # solutions = {model: model.eval(expression, model_completion=True).as_string() for model in models}
    #
    # for model, solution in dict(solutions).items():
    #     try:
    #         verifier(solution)
    #     except:
    #         del solutions[model]
    #
    # return solutions


def eval_one_expression(solver, expression, verifier=lambda expression: None):
    raise Exception("This doesn't work")
    # solutions = eval_all_expression(solver, expression, verifier, n_max=1)
    # return dict([list(solutions.items())[0], ])


def get_one_model(solver):
    raise Exception("This doesn't work")
    # terminals = []
    #
    # for expression in solver.assertions():
    #     terminals += get_vars_non_recursive(expression)
    #
    # return get_all_models(solver, terminals, 1)[0]


def get_all_terminals(solver):
    raise Exception("This doesn't work")
    # terminals = set()
    #
    # for expression in solver.assertions():
    #     terminals.update(get_vars_non_recursive(expression, include_select=True))
    #
    # return terminals


def eval_one_array(solver, array, length):
    solver.is_sat()
    return [int(solver.BW.get_value_str(Array_Select(array, BVV(i, 256))), 2) for i in range(length)]
