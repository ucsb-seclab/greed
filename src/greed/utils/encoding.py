from greed.solver.shortcuts import BV_And, BVV


def addr(expr):
    return BV_And(expr, BVV(2 ** 160 - 1, 256))
