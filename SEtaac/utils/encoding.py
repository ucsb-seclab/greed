from SEtaac.solver.shortcuts import *


def addr(expr):
    return BV_And(expr, BVV(2 ** 160 - 1, 256))
