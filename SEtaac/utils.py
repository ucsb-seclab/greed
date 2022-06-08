import numbers

import z3
from sha3 import keccak_256

TT256 = 2 ** 256
TT256M1 = 2 ** 256 - 1
TT255 = 2 ** 255
SECP256K1P = 2 ** 256 - 4294968273


def sha3(data):
    return keccak_256(data).digest()


def ctx_or_symbolic(v, ctx, xid):
    return ctx.get(v, z3.BitVec('%s_%d' % (v, xid), 256))


def addr(expr):
    return expr & (2 ** 160 - 1)


def big_endian_to_int(x):
    return int.from_bytes(x, byteorder='big')


def int_to_big_endian(v):
    return v.to_bytes(length=(v.bit_length() + 7) // 8, byteorder='big')


def to_string(value):
    return str(value)


def bytearray_to_bytestr(value):
    return bytes(value)


def encode_int32(v):
    return int_to_big_endian(v).rjust(32, b'\x00')


def bytes_to_int(value):
    return big_endian_to_int(bytes(value))


def bytearray_to_int(value):
    return bytes_to_int(bytearray_to_bytestr(value))


def is_pow2(x):
    return x and not x & (x - 1)


def log2(x):
    if not is_pow2(x):
        raise ValueError("%d is not a power of 2!" % x)
    i = -1
    while x:
        x >>= 1
        i += 1
    return i


def to_signed(i):
    return i if i < TT255 else i - TT256


class Denoms:
    def __init__(self):
        self.wei = 1
        self.babbage = 10 ** 3
        self.ada = 10 ** 3
        self.kwei = 10 ** 6
        self.lovelace = 10 ** 6
        self.mwei = 10 ** 6
        self.shannon = 10 ** 9
        self.gwei = 10 ** 9
        self.szabo = 10 ** 12
        self.finney = 10 ** 15
        self.mether = 10 ** 15
        self.ether = 10 ** 18
        self.turing = 2 ** 256 - 1


denoms = Denoms()


def unique(l):
    last = None
    for i in l:
        if i != last:
            yield i
        last = i


def is_subseq(a, b):
    a = tuple(a)
    b = tuple(b)
    # True iff a is a subsequence (not substring!) of b
    p = 0
    for x in a:
        try:
            p = b.index(x, p) + 1
        except ValueError:
            return False
    return True


def is_substr(a, b):
    a = tuple(a)
    b = tuple(b)
    # True iff a is a substring of b
    p = 0
    l = len(a)
    while True:
        try:
            p = b.index(a[0], p)
            if b[p:p + l] == a:
                return True
            p += 1
        except ValueError:
            break
    return False


def gen_exec_id():
    if "xid" not in gen_exec_id.__dict__:
        gen_exec_id.xid = 0
    else:
        gen_exec_id.xid += 1
    return gen_exec_id.xid


# z3 utils #

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


def translate_xid(expr, xid):
    substitutions = dict()

    def raw(s):
        return '_'.join(s.split('_')[:-1])

    for v in get_vars_non_recursive(expr):
        if v not in substitutions:
            v_name = raw(v.decl().name())
            if v.sort_kind() == z3.Z3_INT_SORT:
                substitutions[v] = z3.Int('%s_%d' % (v_name, xid))
            elif v.sort_kind() == z3.Z3_BOOL_SORT:
                substitutions[v] = z3.Bool('%s_%d' % (v_name, xid))
            elif v.sort_kind() == z3.Z3_BV_SORT:
                substitutions[v] = z3.BitVec('%s_%d' % (v_name, xid), v.size())
            elif v.sort_kind() == z3.Z3_ARRAY_SORT:
                substitutions[v] = z3.Array('%s_%d' % (v_name, xid), v.domain(), v.range())
            else:
                raise Exception('CANNOT CONVERT %s (%d)' % (v, v.sort_kind()))
    subst = list(substitutions.items())
    return z3.substitute(expr, subst)