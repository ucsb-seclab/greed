import z3

from SEtaac import utils
from SEtaac.memory import SymRead
from SEtaac.utils import concrete, is_true
from SEtaac.TAC_ops import TAC_Binary

__all__ = ['TAC_Sha3']


class TAC_Sha3(TAC_Binary):
    __internal_name__ = "SHA3"

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

        succ.pc = succ.next_statement()
        return [succ]
