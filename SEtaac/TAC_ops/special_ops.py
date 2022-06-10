import z3

from SEtaac import utils
from SEtaac.memory import SymRead
from SEtaac.utils import concrete, is_true

__all__ = ['TAC_Sha3']


class TAC_Sha3:
    __internal_name__ = "SHA3"

    def __init__(self, op1, res):
        self.op1_var = None
        self.op2_var = None
        self.res_var = None

        self.op1_val = None
        self.op2_val = None
        self.res_val = None

    def parse(self, raw_stmt):
        self.op1_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.res_var = raw_stmt.defs[0]

        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def handle(self, state):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]

        state.memory.extend(arg1, arg2)
        mm = state.memory.read(arg1, arg2)
        if not isinstance(mm, SymRead) and all(concrete(m) for m in mm):
            data = utils.bytearray_to_bytestr(mm)
            return utils.big_endian_to_int(utils.sha3(data))
        else:
            if not isinstance(mm, SymRead):
                sha_data = z3.simplify(z3.Concat([m if z3.is_expr(m) else z3.BitVecVal(m, 8) for m in mm]))
                for k, v in state.sha_constraints.items():
                    if isinstance(v, SymRead):
                        continue
                    if v.size() == sha_data.size() and is_true(v == sha_data):
                        sha = k
                        break
                else:
                    sha = z3.BitVec('SHA3_%x_%d' % (state.instruction_count, state.xid), 256)
                    state.sha_constraints[sha] = sha_data
            else:
                sha_data = mm
                sha = z3.BitVec('SHA3_%x_%d' % (state.instruction_count, state.xid), 256)
                state.sha_constraints[sha] = sha_data
            succ.registers[self.res_var] = sha

        return [succ]

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} = {} SHA3 {}".format(res, op1, op2)
