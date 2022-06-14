from re import L
import z3

from SEtaac import utils
from SEtaac.exceptions import ExternalData, SymbolicError, VMException
from SEtaac.memory import SymRead
from SEtaac.utils import concrete, is_true

from .base import TAC_Binary, TAC_BinaryNoRes, TAC_NoOperands, TAC_Ternary, TAC_TernaryNoRes, \
                  TAC_Quaternary, TAC_QuaternaryNoRes, TAC_Unary, TAC_UnaryNoRes, TAC_NoOperandsNoRes
from ..state import SymbolicEVMState

__all__ = ['TAC_Sha3', 'TAC_Address', 'TAC_Balance', 'TAC_Origin', 'TAC_Caller',
           'TAC_Callvalue', 'TAC_Calldataload', 'TAC_Calldatasize', 'TAC_Calldatacopy',
           'TAC_Codesize', 'TAC_Codecopy', 'TAC_Gasprice', 'TAC_Extcodesize', 'TAC_Extcodecopy',
           'TAC_Returndatasize', 'TAC_Returndatacopy', 'TAC_Extcodehash', 'TAC_Blockhash', 'TAC_Coinbase',
           'TAC_Timestamp', 'TAC_Number', 'TAC_Difficulty', 'TAC_Chainid', 'TAC_Gaslimit', 'TAC_Selfbalance',
           'TAC_Basefee', 'TAC_Create', 'TAC_Create2', 'TAC_Revert', 'TAC_Pc', 'TAC_Invalid', 'TAC_Selfdestruct',
           'TAC_Stop', 'TAC_Gas']


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

class TAC_Stop(TAC_NoOperandsNoRes):
    __internal_name__ = "STOP"

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()

        succ.constraints.append(z3.Or(*(z3.ULE(succ.calldatasize, access) for access in succ.calldata_accesses)))
        succ.halt = True

        succ.set_next_pc()
        return [succ]



class TAC_Address(TAC_NoOperands):
    __internal_name__ = "ADDRESS"
    __aliases__ = {'address_var': 'res_var', 'address_val': 'res_val'}

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()

        succ.registers[self.res_var] = utils.ctx_or_symbolic('ADDRESS', succ.ctx, succ.xid)

        succ.set_next_pc()
        return [succ]


class TAC_Balance(TAC_Unary):
    __internal_name__ = "BALANCE"
    __aliases__ = { 
                    'address_var': 'op1_var', 'address_val': 'op1_val',
                    'balance_var': 'res_var', 'balance_val': 'res_val'
                  }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]

        if concrete(arg1):
            succ.registers[self.res_var] = utils.ctx_or_symbolic('BALANCE-%x' % arg1, succ.ctx, succ.xid)
        elif is_true(utils.addr(arg1) == utils.addr(utils.ctx_or_symbolic('ADDRESS', succ.ctx, succ.xid))):
            succ.registers[self.res_var] = self.balance
        elif is_true(utils.addr(arg1) == utils.addr(utils.ctx_or_symbolic('ORIGIN', succ.ctx, succ.xid))):
            succ.registers[self.res_var] = utils.ctx_or_symbolic('BALANCE-ORIGIN', succ.ctx, succ.xid)
        elif is_true(utils.addr(arg1) == utils.addr(utils.ctx_or_symbolic('CALLER', succ.ctx, succ.xid))):
            succ.registers[self.res_var] = utils.ctx_or_symbolic('BALANCE-CALLER', succ.ctx, succ.xid)
        else:
            raise SymbolicError('balance of symbolic address (%s)' % str(z3.simplify(arg1)))

        succ.set_next_pc()
        return [succ]


class TAC_Origin(TAC_NoOperands):
    __internal_name__ = "ORIGIN"
    __aliases__ = {'address_var': 'res_var', 'address_val': 'res_val'}

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()

        succ.registers[self.res_var] = utils.ctx_or_symbolic('ORIGIN', succ.ctx, succ.xid)

        succ.set_next_pc()
        return [succ]

class TAC_Caller(TAC_NoOperands):
    __internal_name__ = "CALLER"
    __aliases__ = {'address_var': 'res_var', 'address_val': 'res_val'}

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()

        succ.registers[self.res_var] = utils.ctx_or_symbolic('CALLER', succ.ctx, succ.xid)

        succ.set_next_pc()
        return [succ]


class TAC_Callvalue(TAC_NoOperands):
    __internal_name__ = "CALLVALUE"
    __aliases__ = {'value_var': 'res_var', 'value_val': 'res_val'}

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()

        succ.registers[self.res_var] = utils.ctx_or_symbolic('CALLVALUE', succ.ctx, succ.xid)

        succ.set_next_pc()
        return [succ]

class TAC_Calldataload(TAC_Unary):
    __internal_name__ = "CALLDATALOAD"
    __aliases__ = {'byte_offset_var': 'op1_var', 'byte_offset_val': 'op1_val',
                   'calldata_var'   : 'res_var', 'calldata_val'   : 'res_val'}

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]

        succ.constraints.append(z3.UGE(succ.calldatasize, arg1 + 32))
        succ.calldata_accesses.append(arg1 + 32)
        if not concrete(arg1):
            succ.constraints.append(z3.ULT(arg1, succ.MAX_CALLDATA_SIZE))
        succ.registers[self.res_var] = z3.Concat([succ.calldata[arg1 + i] for i in range(32)])

        succ.set_next_pc()
        return [succ]

class TAC_Calldatasize(TAC_NoOperands):
    __internal_name__ = "CALLDATASIZE"
    __aliases__ = {'calldatasize_var': 'res_var', 'calldatasize_val': 'res_val'}

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()

        succ.registers[self.res_var] = succ.calldatasize

        succ.set_next_pc()
        return [succ]

class TAC_Calldatacopy(TAC_TernaryNoRes):
    __internal_name__ = "CALLDATACOPY"
    __aliases__ = {
                   'destOffset_var'    : 'op1_var', 'destOffset_val'    : 'op1_val',
                   'calldataOffset_var': 'op2_var', 'calldataOffset_val': 'op2_val',
                   'size_var'          : 'op3_var', 'size_val'          : 'op3_val',
                  }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]
        arg3 = succ.registers[self.op3_var]

        succ.constraints.append(z3.UGE(succ.calldatasize, arg2 + arg3))
        succ.calldata_accesses.append(arg2 + arg3)
        if not concrete(arg2):
            succ.constraints.append(z3.ULT(arg2, succ.MAX_CALLDATA_SIZE))
        if concrete(arg3):
            for i in range(arg3):
                succ.memory[arg1 + i] = succ.calldata[arg2 + i]
        else:
            succ.constraints.append(z3.ULT(arg3, succ.MAX_CALLDATA_SIZE))
            for i in range(succ.MAX_CALLDATA_SIZE):
                succ.memory[arg1 + i] = z3.If(arg3 < i, succ.memory[arg1 + i], succ.calldata[arg2 + i])

        succ.set_next_pc()
        return [succ]

class TAC_Codesize(TAC_NoOperands):
    __internal_name__ = "CODESIZE"
    __aliases__ = {
                   'size_var': 'op1_var', 'size_val': 'op1_val'
                  }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()

        succ.registers[self.res_var] = len(succ.code)

        succ.set_next_pc()
        return [succ]

class TAC_Codecopy(TAC_TernaryNoRes):
    __internal_name__ = "CODECOPY"
    __aliases__ = {
                   'destOffset_var': 'op1_var', 'destOffset_val': 'op1_val',
                   'offset_var'    : 'op2_var', 'offset_val'    : 'op2_val',
                   'size_var'      : 'op3_var', 'size_val'      : 'op3_val'
                  }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]
        arg3 = succ.registers[self.op3_var]

        if concrete(arg1) and concrete(arg2) and concrete(arg3):
            self.memory.extend(arg1, arg3)
            for i in range(arg3):
                if arg2 + i < len(self.code):
                    self.memory[arg1 + i] = self.code[arg2 + i]
                else:
                    self.memory[arg1 + i] = 0
        else:
            raise SymbolicError('Symbolic code index @ %s' % self.pc)

        succ.set_next_pc()
        return [succ]

class TAC_Gasprice(TAC_NoOperands):
    __internal_name__ = "GASPRICE"
    __aliases__ = {
                   'price_var': 'res_var', 'price_val': 'res_val'
                  }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()

        succ.registers[self.res_var] = utils.ctx_or_symbolic('GASPRICE', succ.ctx, succ.xid)

        succ.set_next_pc()
        return [succ]

class TAC_Extcodesize(TAC_Unary):
    __internal_name__ = "EXTCODESIZE"
    __aliases__ = {
                   'address_var': 'op1_var', 'address_val': 'op1_val',
                   'size_var'   : 'res_var', 'size_val'   : 'res_val'
                  }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]

        if concrete(arg1):
            succ.registers[self.res_var] = utils.ctx_or_symbolic('CODESIZE-%x' % arg1, succ.ctx, succ.xid)
        elif is_true(arg1 == utils.addr(utils.ctx_or_symbolic('ADDRESS', succ.ctx, succ.xid))):
            succ.registers[self.res_var] = utils.ctx_or_symbolic('CODESIZE-ADDRESS', succ.ctx, succ.xid)
        elif is_true(arg1 == utils.addr(utils.ctx_or_symbolic('CALLER', succ.ctx, succ.xid))):
            succ.registers[self.res_var] = utils.ctx_or_symbolic('CODESIZE-CALLER', succ.ctx, succ.xid)
        else:
            raise SymbolicError('codesize of symblic address')

        succ.set_next_pc()
        return [succ]

class TAC_Extcodecopy(TAC_QuaternaryNoRes):
    __internal_name__ = "EXTCODECOPY"
    __aliases__ = {
                   'address_var'     : 'op1_var', 'address_val'      : 'op1_val',
                   'destOffset_var'  : 'op2_var', 'destOffset_val'   : 'op2_val',
                   'offset_var'      : 'op3_var', 'offset_val'       : 'op3_val',
                   'size_var'        : 'op4_var', 'size_val'         : 'op4_val'
                  }

    def handle(self, state:SymbolicEVMState):
        raise ExternalData('EXTCODECOPY')


class TAC_Returndatasize(TAC_NoOperands):
    __internal_name__ = "RETURNDATASIZE"
    __aliases__ = {
                   'size_var': 'res_var', 'size_val': 'res_val'
                  }

    def handle(self, state:SymbolicEVMState):
        raise ExternalData('RETURNDATASIZE')


class TAC_Returndatacopy(TAC_TernaryNoRes):
    __internal_name__ = "RETURNDATACOPY"
    __aliases__ = {
                   'destOffset_var': 'op1_var', 'destOffset_val': 'op1_val',
                   'offset_var'    : 'op2_var', 'offset_val'    : 'op2_val',
                   'size_var'      : 'op3_var', 'size_val'      : 'op3_val'
                  }

    def handle(self, state:SymbolicEVMState):
        raise ExternalData('RETURNDATACOPY')


class TAC_Extcodehash(TAC_Unary):
    __internal_name__ = "EXTCODEHASH"
    __aliases__ = {
                   'address_var'   : 'op1_var', 'address_val'   : 'op1_val',
                   'hash_var'      : 'res_var', 'hash_val'      : 'res_val'
                  }

    def handle(self, state:SymbolicEVMState):
        raise ExternalData('EXTCODEHASH')


class TAC_Blockhash(TAC_Unary):
    __internal_name__ = "BLOCKHASH"
    __aliases__ = {
                   'blockNumber_var'   : 'op1_var', 'blockNumber_val'   : 'op1_val',
                   'hash_var'          : 'res_var', 'hash_val'          : 'res_val'
                  }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]

        if not concrete(arg1):
            raise SymbolicError('symbolic blockhash index')
        succ.registers[self.res_var] = utils.ctx_or_symbolic('BLOCKHASH[%d]' % arg1, succ.ctx, succ.xid)

        succ.set_next_pc()
        return [succ]


class TAC_Coinbase(TAC_NoOperands):
    __internal_name__ = "COINBASE"
    __aliases__ = {
                   'address_var'   : 'res_var', 'address_val'   : 'res_val',
                  }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()

        succ.registers[self.res_var] = utils.ctx_or_symbolic('COINBASE', succ.ctx, succ.xid)

        succ.set_next_pc()
        return [succ]

class TAC_Timestamp(TAC_NoOperands):
    __internal_name__ = "TIMESTAMP"
    __aliases__ = {
                   'timestamp_var': 'res_var', 'timestamp_val': 'res_val',
                  }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()

        ts = utils.ctx_or_symbolic('TIMESTAMP', succ.ctx, succ.xid)
        if not concrete(ts):
            succ.constraints.append(z3.UGE(ts, succ.min_timestamp))
            succ.constraints.append(z3.ULE(ts, succ.max_timestamp))
        succ.registers[self.res_var] = ts

        succ.set_next_pc()
        return [succ]

class TAC_Number(TAC_NoOperands):
    __internal_name__ = "NUMBER"
    __aliases__ = {
                   'blockNumber_var': 'res_var', 'blockNumber_val': 'res_val',
                  }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()

        succ.registers[self.res_var] = utils.ctx_or_symbolic('NUMBER', succ.ctx, succ.xid)

        succ.set_next_pc()
        return [succ]

class TAC_Difficulty(TAC_NoOperands):
    __internal_name__ = "DIFFICULTY"
    __aliases__ = {
                   'difficulty_var': 'res_var', 'difficulty_val': 'res_val',
                  }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()

        succ.registers[self.res_var] = utils.ctx_or_symbolic('DIFFICULTY', succ.ctx, succ.xid)

        succ.set_next_pc()
        return [succ]

class TAC_Gaslimit(TAC_NoOperands):
    __internal_name__ = "GASLIMIT"
    __aliases__ = {
                   'gasLimit_var': 'res_var', 'gasLimit_val': 'res_val',
                  }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()

        succ.registers[self.res_var] = utils.ctx_or_symbolic('GASLIMIT', succ.ctx, succ.xid)

        succ.set_next_pc()
        return [succ]

class TAC_Chainid(TAC_NoOperands):
    __internal_name__ = "CHAINID"
    __aliases__ = {
                   'chainID_var': 'res_var', 'chainID_val': 'res_val',
                  }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()

        chainid = {'mainnet': 1, 'ropsten': 3, 'rinkeby': 4, 'goerli': 5, 'kotti': 6, 'classic': 61, 'mordor': 63,
                   'astor': 212, 'dev': 2018}
        succ.registers[self.res_var] = chainid['mainnet']

        succ.set_next_pc()
        return [succ]

class TAC_Selfbalance(TAC_NoOperands):
    __internal_name__ = "SELFBALANCE"
    __aliases__ = {
                   'balance_var': 'res_var', 'balance_val': 'res_val',
                  }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()

        succ.registers[self.res_var] = succ.balance

        succ.set_next_pc()
        return [succ]

class TAC_Basefee(TAC_NoOperands):
    __internal_name__ = "BASEFEE"
    __aliases__ = {
                   'baseFee_var': 'res_var', 'baseFee_val': 'res_val',
                  }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()

        # todo: if the current block is known, this is known
        succ.registers[self.res_var] = utils.ctx_or_symbolic('BASEFEE', succ.ctx, succ.xid)

        succ.set_next_pc()
        return [succ]


class TAC_Revert(TAC_BinaryNoRes):
    __internal_name__ = "REVERT"
    __aliases__ = {
                   'offset_var': 'op1_var', 'offset_val': 'op1_val',
                   'size_var'  : 'op2_var', 'size_val'  : 'op2_val',
                  }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]

        if not concrete(arg1) or not concrete(arg2):
            raise SymbolicError('symbolic memory index')
        succ.memory.extend(arg1, arg2)
        succ.constraints.append(z3.Or(*(z3.ULE(succ.calldatasize, access) for access in succ.calldata_accesses)))
        succ.halt = True

        succ.set_next_pc()
        return [succ]


class TAC_Create(TAC_Ternary):
    __internal_name__ = "CREATE"
    __aliases__ = {
                   'value_var'   : 'op1_var', 'value_val'   : 'op1_val',
                   'offset_var'  : 'op2_var', 'offset_val'  : 'op2_val',
                   'size_var'    : 'op3_var', 'size_val'    : 'op3_val',
                   'address_var' : 'res_var', 'address_val' : 'res_val'
                  }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]

        succ.constraints.append(z3.UGE(succ.balance, arg1))
        succ.balance -= arg1
        succ.registers[self.res_var] = utils.addr(
            z3.BitVec('EXT_CREATE_%d_%d' % (succ.instruction_count, succ.xid), 256))

        succ.set_next_pc()
        return [succ]


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
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]

        succ.constraints.append(z3.UGE(succ.balance, arg1))
        succ.balance -= arg1
        # todo: this is deployed at a deterministic address
        succ.registers[self.res_var] = utils.addr(
            z3.BitVec('EXT_CREATE2_%d_%d' % (succ.instruction_count, succ.xid), 256))

        succ.set_next_pc()
        return [succ]


class TAC_Pc(TAC_NoOperands):
    __internal_name__ = "PC"
    __aliases__ = {
                   'counter_var': 'res_var', 'counter_val': 'res_val',
                  }

    def handle(self, state:SymbolicEVMState):
        # todo: this pc will most probably be different from what the evm expects
        raise VMException("PC not available if executing TAC")

        # succ = state.copy()
        # succ.registers[self.res_var] = succ.pc

        # succ.set_next_pc()
        # return [succ]


class TAC_Invalid(TAC_NoOperandsNoRes):
    __internal_name__ = "INVALID"

    def handle(self, state:SymbolicEVMState):
        # todo: should INVALID halt the execution?
        succ = state.copy()

        succ.halt = True

        succ.set_next_pc()
        return [succ]


class TAC_Selfdestruct(TAC_UnaryNoRes):
    __internal_name__ = "SELFDESTRUCT"
    __aliases__ = {
                   'address_var': 'op1_var', 'address_val': 'op1_val'
                  }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()

        # todo: consider the target address
        succ.constraints.append(z3.Or(*(z3.ULE(succ.calldatasize, access) for access in succ.calldata_accesses)))
        succ.halt = True

        succ.set_next_pc()
        return [succ]


class TAC_Gas(TAC_NoOperands):
    __internal_name__ = "GAS"
    __aliases__ = {
                   'gas_var': 'res_var', 'gas_val': 'res_val'
                  }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        succ.set_next_pc()

        succ.registers[self.res_var] = z3.BitVec('GAS_%x' % succ.instruction_count, 256)

        return [succ]
