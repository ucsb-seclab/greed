import z3

from SEtaac import utils
from SEtaac.memory import SymRead
from SEtaac.utils import concrete, is_true

from .base import TAC_Binary, TAC_BinaryNoRes, TAC_NoOperands, TAC_Ternary, TAC_TernaryNoRes, TAC_Quaternary, TAC_QuaternaryNoRes, TAC_Unary, TAC_UnaryNoRes
from ..state import SymbolicEVMState

__all__ = ['TAC_Sha3', 'TAC_Address', 'TAC_Balance', 'TAC_Origin', 'TAC_Caller',
           'TAC_Callvalue', 'TAC_Calldataload', 'TAC_Calldatasize', 'TAC_Calldatacopy',
           'TAC_Codesize', 'TAC_Codecopy', 'TAC_Gasprice', 'TAC_Extcodesize', 'TAC_Extcodecopy',
           'TAC_Returndatasize', 'TAC_Returndatacopy', 'TAC_Extcodehash', 'TAC_Blockhash', 'TAC_Coinbase',
           'TAC_Timestamp', 'TAC_Number', 'TAC_Difficulty', 'TAC_Chainid', 'TAC_Gaslimit', 'TAC_Selfbalance',
           'TAC_Basefee', 'TAC_Create', 'TAC_Create2' 'TAC_Revert', 'TAC_Pc', 'TAC_Invalid', 'TAC_Selfdestruct']


class TAC_Sha3(TAC_Binary):
    __internal_name__ = "SHA3"
    __aliases__ = {'offset_var': 'op1_var', 'offset_val': 'op1_val', 
                   'size_var'  : 'op2_var', 'size_val'  : 'op2_val',
                   'hash_var'  : 'res_var', 'hash_val'  : 'res_val'}

    def handle(self, state:SymbolicEVMState):
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


class TAC_Address(TAC_NoOperands):
    __internal_name__ = "ADDRESS"
    __aliases__ = {'address_var': 'res_var', 'address_val': 'res_val'}

    def handle(self, state:SymbolicEVMState):
        pass


class TAC_Balance(TAC_Unary):
    __internal_name__ = "BALANCE"
    __aliases__ = { 
                    'address_var': 'op1_var', 'address_val': 'op1_val',
                    'balance_var': 'res_var', 'balance_val': 'res_val'
                  }

    def handle(self, state:SymbolicEVMState):
        pass 


class TAC_Origin(TAC_NoOperands):
    __internal_name__ = "ORIGIN"
    __aliases__ = {'address_var': 'res_var', 'address_val': 'res_val'}

    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Caller(TAC_NoOperands):
    __internal_name__ = "CALLER"
    __aliases__ = {'address_var': 'res_var', 'address_val': 'res_val'}

    def handle(self, state:SymbolicEVMState):
        pass


class TAC_Callvalue(TAC_NoOperands):
    __internal_name__ = "CALLVALUE"
    __aliases__ = {'value_var': 'res_var', 'value_val': 'res_val'}

    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Calldataload(TAC_Unary):
    __internal_name__ = "CALLDATALOAD"
    __aliases__ = {'byte_offset_var': 'op1_var', 'byte_offset_val': 'op1_val',
                   'calldata_var'   : 'res_var', 'calldata_val'   : 'res_val'}

    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Calldatasize(TAC_NoOperands):
    __internal_name__ = "CALLDATASIZE"
    __aliases__ = {'calldatasize_var': 'res_var', 'calldatasize_val': 'res_val'}

    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Calldatacopy(TAC_TernaryNoRes):
    __internal_name__ = "CALLDATACOPY"
    __aliases__ = {
                   'destOffset_var'    : 'op1_var', 'destOffset_val'    : 'op1_val',
                   'calldataOffset_var': 'op2_var', 'calldataOffset_val': 'op2_val',
                   'size_var'          : 'op3_var', 'size_val'          : 'op3_val',
                  }

    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Codesize(TAC_NoOperands):
    __internal_name__ = "CODESIZE"
    __aliases__ = {
                   'size_var': 'op1_var', 'size_val': 'op1_val'
                  }

    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Codecopy(TAC_TernaryNoRes):
    __internal_name__ = "CODECOPY"
    __aliases__ = {
                   'destOffset_var': 'op1_var', 'destOffset_val': 'op1_val',
                   'offset_var'    : 'op2_var', 'offset_val'    : 'op2_val',
                   'size_var'      : 'op3_var', 'size_val'      : 'op3_val'
                  }

    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Gasprice(TAC_NoOperands):
    __internal_name__ = "GASPRICE"
    __aliases__ = {
                   'price_var': 'res_var', 'price_val': 'res_val'
                  }

    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Extcodesize(TAC_Unary):
    __internal_name__ = "EXTCODESIZE"
    __aliases__ = {
                   'address_var': 'op1_var', 'address_val': 'op1_val',
                   'size_var'   : 'res_var', 'size_val'   : 'res_val'
                  }

    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Extcodecopy(TAC_QuaternaryNoRes):
    __internal_name__ = "EXTCODESIZE"
    __aliases__ = {
                   'address_var'     : 'op1_var', 'address_val'      : 'op1_val',
                   'destOffset_var'  : 'op2_var', 'destOffset_val'   : 'op2_val',
                   'offset_var'      : 'op3_var', 'offset_val'       : 'op3_val',
                   'size_var'        : 'op4_var', 'size_val'         : 'op4_val'
                  }

    def handle(self, state:SymbolicEVMState):
        pass


class TAC_Returndatasize(TAC_NoOperands):
    __internal_name__ = "RETURNDATASIZE"
    __aliases__ = {
                   'size_var': 'res_var', 'size_val': 'res_val'
                  }

    def handle(self, state:SymbolicEVMState):
        pass


class TAC_Returndatacopy(TAC_TernaryNoRes):
    __internal_name__ = "RETURNDATACOPY"
    __aliases__ = {
                   'destOffset_var': 'op1_var', 'destOffset_val': 'op1_val',
                   'offset_var'    : 'op2_var', 'offset_val'    : 'op2_val',
                   'size_var'      : 'op3_var', 'size_val'      : 'op3_val'
                  }

    def handle(self, state:SymbolicEVMState):
        pass


class TAC_Extcodehash(TAC_Unary):
    __internal_name__ = "EXTCODEHASH"
    __aliases__ = {
                   'address_var'   : 'op1_var', 'address_val'   : 'op1_val',
                   'hash_var'      : 'res_var', 'hash_val'      : 'res_val'
                  }

    def handle(self, state:SymbolicEVMState):
        pass


class TAC_Blockhash(TAC_Unary):
    __internal_name__ = "BLOCKHASH"
    __aliases__ = {
                   'blockNumber_var'   : 'op1_var', 'blockNumber_val'   : 'op1_val',
                   'hash_var'          : 'res_var', 'hash_val'          : 'res_val'
                  }

    def handle(self, state:SymbolicEVMState):
        pass


class TAC_Coinbase(TAC_NoOperands):
    __internal_name__ = "COINBASE"
    __aliases__ = {
                   'address_var'   : 'res_var', 'address_val'   : 'res_val',
                  }

    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Timestamp(TAC_NoOperands):
    __internal_name__ = "TIMESTAMP"
    __aliases__ = {
                   'timestamp_var': 'res_var', 'timestamp_val': 'res_val',
                  }

    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Number(TAC_NoOperands):
    __internal_name__ = "NUMBER"
    __aliases__ = {
                   'blockNumber_var': 'res_var', 'blockNumber_val': 'res_val',
                  }

    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Difficulty(TAC_NoOperands):
    __internal_name__ = "DIFFICULTY"
    __aliases__ = {
                   'difficulty_var': 'res_var', 'difficulty_val': 'res_val',
                  }

    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Gaslimit(TAC_NoOperands):
    __internal_name__ = "GASLIMIT"
    __aliases__ = {
                   'gasLimit_var': 'res_var', 'gasLimit_val': 'res_val',
                  }

    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Chainid(TAC_NoOperands):
    __internal_name__ = "CHAINID"
    __aliases__ = {
                   'chainID_var': 'res_var', 'chainID_val': 'res_val',
                  }

    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Selfbalance(TAC_NoOperands):
    __internal_name__ = "SELFBALANCE"
    __aliases__ = {
                   'balance_var': 'res_var', 'balance_val': 'res_val',
                  }

    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Basefee(TAC_NoOperands):
    __internal_name__ = "BASEFEE"
    __aliases__ = {
                   'baseFee_var': 'res_var', 'baseFee_val': 'res_val',
                  }

    def handle(self, state:SymbolicEVMState):
        pass


class TAC_Revert(TAC_BinaryNoRes):
    __internal_name__ = "REVERT"
    __aliases__ = {
                   'offset_var': 'op1_var', 'offset_val': 'op1_val',
                   'size_var'  : 'op2_var', 'size_val'  : 'op2_val',
                  }

    def handle(self, state:SymbolicEVMState):
        pass


class TAC_Create(TAC_Ternary):
    __internal_name__ = "CREATE"
    __aliases__ = {
                   'value_var'   : 'op1_var', 'value_val'   : 'op1_val',
                   'offset_var'  : 'op2_var', 'offset_val'  : 'op2_val',
                   'size_var'    : 'op3_var', 'size_val'    : 'op3_val',
                   'address_var' : 'res_var', 'address_val' : 'res_val'
                  }

    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Create2(TAC_Quaternary):
    __internal_name__ = "CREATE2"
    __aliases__ = {
                   'value_var'      : 'op1_var', 'value_val'   : 'op1_val',
                   'offset_var'     : 'op2_var', 'offset_val'  : 'op2_val',
                   'size_var'       : 'op3_var', 'size_val'    : 'op3_val',
                   'salt_var'       : 'op4_var', 'salt_val'    : 'op4_val',
                   'address_var'    : 'res_var', 'address_val' : 'res_val'
                  }

    def handle(self, state:SymbolicEVMState):
        pass



class TAC_Pc(TAC_NoOperands):
    __internal_name__ = "PC"
    __aliases__ = {
                   'counter_var': 'res_var', 'counter_val': 'res_val',
                  }

    def handle(self, state:SymbolicEVMState):
        pass


class TAC_Invalid(TAC_NoOperandsNoRes):
    __internal_name__ = "INVALID"

    def handle(self, state:SymbolicEVMState):
        pass


class TAC_Selfdestruct(TAC_UnaryNoRes):
    __internal_name__ = "SELFDESTRUCT"
    __aliases__ = {
                   'address_var': 'op1_var', 'address_val': 'op1_val'
                  }

    def handle(self, state:SymbolicEVMState):
        pass