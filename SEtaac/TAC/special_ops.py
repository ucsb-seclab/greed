import logging

import sha3

from SEtaac import options, utils
from SEtaac.TAC.base import TAC_Statement
from SEtaac.sha3 import Sha3
from SEtaac.solver.shortcuts import *
from SEtaac.state import SymbolicEVMState
from SEtaac.utils.exceptions import VMExternalData, VMSymbolicError, VMException
from SEtaac.utils.extra import UUIDGenerator

log = logging.getLogger(__name__)

__all__ = ['TAC_Sha3', 'TAC_Address', 'TAC_Balance', 'TAC_Origin', 'TAC_Caller',
           'TAC_Callvalue', 'TAC_Calldataload', 'TAC_Calldatasize', 'TAC_Calldatacopy',
           'TAC_Codesize', 'TAC_Codecopy', 'TAC_Gasprice', 'TAC_Extcodesize', 'TAC_Extcodecopy',
           'TAC_Returndatasize', 'TAC_Returndatacopy', 'TAC_Extcodehash', 'TAC_Blockhash', 'TAC_Coinbase',
           'TAC_Timestamp', 'TAC_Number', 'TAC_Difficulty', 'TAC_Chainid', 'TAC_Gaslimit', 'TAC_Selfbalance',
           'TAC_Basefee', 'TAC_Create', 'TAC_Create2', 'TAC_Return', 'TAC_Revert', 'TAC_Pc', 'TAC_Invalid',
           'TAC_Selfdestruct', 'TAC_Stop', 'TAC_Gas']


class TAC_Sha3(TAC_Statement):
    __internal_name__ = "SHA3"
    __aliases__ = {'offset_var': 'arg1_var', 'offset_val': 'arg1_val',
                   'size_var': 'arg2_var', 'size_val': 'arg2_val',
                   'hash_var': 'res1_var', 'hash_val': 'res1_val'}

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):

        new_sha = Sha3(state, state.memory, self.offset_val, self.size_val)
        for sha in state.sha_observed:
            new_sha.instantiate_ackermann_constraints(sha)
            
        state.sha_observed.append(new_sha)

        state.registers[self.res1_var] = new_sha.symbol
        
        # Checks to see if we have only one solution, if not, as of now we give up and 
        # keep thre unconstrained symbol + the ackermann constraints, otherwise let's 
        # calculate the possible solutions and apply the constraints.
        if options.GREEDY_SHA:
            log.debug(f"Using GREEDY_SHA strategy to try to resolve {new_sha.symbol.name}")
            size_sol = state.solver.eval(self.size_val, raw=True)
            log.debug(f"    Size solution: {bv_unsigned_value(size_sol)}")
            offset_sol = state.solver.eval(self.offset_val, raw=True)
            log.debug(f"    Offset solution: {bv_unsigned_value(offset_sol)}")
            
            if not state.solver.is_formula_sat(NotEqual(self.size_val, size_sol)) and \
                                not state.solver.is_formula_sat(NotEqual(self.offset_val, offset_sol)):

                # Get a solution for the input buffer
                buffer_sol = state.solver.eval_memory_at(state.memory, offset_sol, 
                                                                        size_sol, 
                                                                        raw=True)

                if not state.solver.is_formula_sat(NotEqual(state.memory.readn(offset_sol, size_sol), buffer_sol)):
                    # Everything has only one solution, we can calculate the SHA
                    keccak256 = sha3.keccak_256()
                    buffer_sol = bv_unsigned_value(buffer_sol).to_bytes(bv_unsigned_value(size_sol), 'big')
                    keccak256.update(buffer_sol)
                    res = keccak256.hexdigest()
                    log.debug(f"    Calculated concrete SHA3 {res}")
                    
                    # Constraining parameters to their calculated solutions
                    state.add_constraint(Equal(self.offset_val, offset_sol))
                    state.add_constraint(Equal(self.size_val, size_sol))

                    # Constraining the fresh SHA symbol to its solution given this buffer 
                    state.add_constraint(Equal(state.registers[self.res1_var], BVV(int(res,16),256)))

                    # Constraining the SHA3 input buffer to the solution just calculated
                    for x,b in zip(range(0, bv_unsigned_value(size_sol)), buffer_sol):
                        state.add_constraint(Equal(state.memory[BVV(bv_unsigned_value(offset_sol)+x,256)], BVV(b,8)))
                    
                    # Just set the solution here
                    state.registers[self.res1_var] = BVV(int(res,16),256)
                else:
                    log.debug(f"    Cannot calculate concrete SHA3 for {new_sha.symbol.name} due to multiple SHA solutions")
            else:
                log.debug(f"    Cannot calculate concrete SHA3 for {new_sha.symbol.name} due to multiple size and offset solutions")

        state.set_next_pc()

        return [state]


class TAC_Stop(TAC_Statement):
    __internal_name__ = "STOP"

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        # todo: implement revert
        # succ.add_constraint(z3.Or(*(z3.ULE(succ.calldatasize, access) for access in succ.calldata_accesses)))
        state.halt = True

        return [state]


class TAC_Address(TAC_Statement):
    __internal_name__ = "ADDRESS"
    __aliases__ = {'address_var': 'res1_var', 'address_val': 'res1_val'}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = ctx_or_symbolic('ADDRESS', state.ctx, state.xid)
        state.set_next_pc()
        return [state]


class TAC_Balance(TAC_Statement):
    __internal_name__ = "BALANCE"
    __aliases__ = {
        'address_var': 'arg1_var', 'address_val': 'arg1_val',
        'balance_var': 'res1_var', 'balance_val': 'res1_val'
    }

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        if is_concrete(self.address_val):
            state.registers[self.res1_var] = ctx_or_symbolic('BALANCE-%x' % bv_unsigned_value(self.address_val), state.ctx, state.xid)
        elif state.solver.is_formula_true(Equal(utils.addr(self.address_val), utils.addr(ctx_or_symbolic('ADDRESS', state.ctx, state.xid)))):
            state.registers[self.res1_var] = state.balance
        elif state.solver.is_formula_true(Equal(utils.addr(self.address_val), utils.addr(ctx_or_symbolic('ORIGIN', state.ctx, state.xid)))):
            state.registers[self.res1_var] = ctx_or_symbolic('BALANCE-ORIGIN', state.ctx, state.xid)
        elif state.solver.is_formula_true(Equal(utils.addr(self.address_val), utils.addr(ctx_or_symbolic('CALLER', state.ctx, state.xid)))):
            state.registers[self.res1_var] = ctx_or_symbolic('BALANCE-CALLER', state.ctx, state.xid)
        else:
            state.registers[self.res1_var] = BVS('SYM-BALANCE-%x' % self.address_val.id, 256)

        state.set_next_pc()
        return [state]


class TAC_Origin(TAC_Statement):
    __internal_name__ = "ORIGIN"
    __aliases__ = {'address_var': 'res1_var', 'address_val': 'res1_val'}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = ctx_or_symbolic('ORIGIN', state.ctx, state.xid)

        state.set_next_pc()
        return [state]


class TAC_Caller(TAC_Statement):
    __internal_name__ = "CALLER"
    __aliases__ = {'address_var': 'res1_var', 'address_val': 'res1_val'}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = ctx_or_symbolic('CALLER', state.ctx, state.xid)

        state.set_next_pc()
        return [state]


class TAC_Callvalue(TAC_Statement):
    __internal_name__ = "CALLVALUE"
    __aliases__ = {'value_var': 'res1_var', 'value_val': 'res1_val'}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = ctx_or_symbolic('CALLVALUE', state.ctx, state.xid)

        state.set_next_pc()
        return [state]


class TAC_Calldataload(TAC_Statement):
    uuid_generator = UUIDGenerator()

    __internal_name__ = "CALLDATALOAD"
    __aliases__ = {'byte_offset_var': 'arg1_var', 'byte_offset_val': 'arg1_val',
                   'calldata_var': 'res1_var', 'calldata_val': 'res1_val'}

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        # WARNING: According to the EVM specification if your CALLDATA is less than 32 bytes, you read zeroes.
        
        calldataload_res = state.calldata.readn(self.byte_offset_val, BVV(32, 256))

        state.registers[self.res1_var] = calldataload_res

        log.debug("CALLDATALOAD:" +
                  str({v: bv_unsigned_value(k) if is_concrete(k) else "<SYMBOL>" for v, k in self.arg_vals.items()}) +
                  f" --> {{{self.res1_var}: {bv_unsigned_value(state.registers[self.res1_var]) if is_concrete(state.registers[self.res1_var]) else '<SYMBOL>'}}}")

        state.set_next_pc()
        return [state]


class TAC_Calldatasize(TAC_Statement):
    __internal_name__ = "CALLDATASIZE"
    __aliases__ = {'calldatasize_var': 'res1_var', 'calldatasize_val': 'res1_val'}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = state.calldatasize

        state.set_next_pc()
        return [state]


class TAC_Calldatacopy(TAC_Statement):
    __internal_name__ = "CALLDATACOPY"
    __aliases__ = {
        'destOffset_var': 'arg1_var', 'destOffset_val': 'arg1_val',
        'calldataOffset_var': 'arg2_var', 'calldataOffset_val': 'arg2_val',
        'size_var': 'arg3_var', 'size_val': 'arg3_val',
    }

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        state.memory.memcopy(self.destOffset_val, state.calldata.copy(state), self.calldataOffset_val, self.size_val)

        state.set_next_pc()
        return [state]


class TAC_Codesize(TAC_Statement):
    __internal_name__ = "CODESIZE"
    __aliases__ = {
        'size_var': 'arg1_var', 'size_val': 'arg1_val'
    }

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = ctx_or_symbolic('CODESIZE-ADDRESS', state.ctx, state.xid)

        state.set_next_pc()
        return [state]


class TAC_Codecopy(TAC_Statement):
    __internal_name__ = "CODECOPY"
    __aliases__ = {
        'destOffset_var': 'arg1_var', 'destOffset_val': 'arg1_val',
        'offset_var': 'arg2_var', 'offset_val': 'arg2_val',
        'size_var': 'arg3_var', 'size_val': 'arg3_val'
    }

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        if is_concrete(self.destOffset_val) and is_concrete(self.offset_val) and is_concrete(self.size_val):
            for i in range(bv_unsigned_value(self.size_val)):
                if bv_unsigned_value(self.offset_val) + i < len(state.code):
                    code_at_i = state.code[bv_unsigned_value(self.offset_val) + i]
                    state.memory[BV_Add(self.destOffset_val, BVV(i, 256))] = BVV(code_at_i, 8)
                else:
                    state.memory[BV_Add(self.destOffset_val, BVV(i, 256))] = BVV(0, 8)
        else:
            raise VMSymbolicError('Symbolic code index @ %s (CODECOPY)' % state.pc)

        state.set_next_pc()
        return [state]


class TAC_Gasprice(TAC_Statement):
    __internal_name__ = "GASPRICE"
    __aliases__ = {
        'price_var': 'res1_var', 'price_val': 'res1_val'
    }

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = ctx_or_symbolic('GASPRICE', state.ctx, state.xid)

        state.set_next_pc()
        return [state]


class TAC_Extcodesize(TAC_Statement):
    __internal_name__ = "EXTCODESIZE"
    __aliases__ = {
        'address_var': 'arg1_var', 'address_val': 'arg1_val',
        'size_var': 'res1_var', 'size_val': 'res1_val'
    }

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):

        if options.DEFAULT_EXTCODESIZE:
            state.registers[self.res1_var] = BVV(42,256)
            state.set_next_pc()
            return [state]
        
        if is_concrete(self.address_val):
            state.registers[self.res1_var] = ctx_or_symbolic('CODESIZE-%x' % bv_unsigned_value(self.address_val), state.ctx, state.xid)
        elif state.solver.is_formula_true(Equal(self.address_val, utils.addr(ctx_or_symbolic('ADDRESS', state.ctx, state.xid)))):
            state.registers[self.res1_var] = ctx_or_symbolic('CODESIZE-ADDRESS', state.ctx, state.xid)
        elif state.solver.is_formula_true(Equal(self.address_val, utils.addr(ctx_or_symbolic('CALLER', state.ctx, state.xid)))):
            state.registers[self.res1_var] = ctx_or_symbolic('CODESIZE-CALLER', state.ctx, state.xid)
        else:
            state.registers[self.res1_var] = ctx_or_symbolic('CODESIZE-SYMBOLIC', state.ctx, state.xid)
            log.warning('CODESIZE of symbolic address')
            # raise VMSymbolicError('codesize of symblic address')

        state.set_next_pc()
        return [state]


class TAC_Extcodecopy(TAC_Statement):
    __internal_name__ = "EXTCODECOPY"
    __aliases__ = {
        'address_var': 'arg1_var', 'address_val': 'arg1_val',
        'destOffset_var': 'arg2_var', 'destOffset_val': 'arg2_val',
        'offset_var': 'arg3_var', 'offset_val': 'arg3_val',
        'size_var': 'arg4_var', 'size_val': 'arg4_val'
    }

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        raise VMExternalData('EXTCODECOPY')


class TAC_Returndatasize(TAC_Statement):
    __internal_name__ = "RETURNDATASIZE"
    __aliases__ = {
        'size_var': 'res1_var', 'size_val': 'res1_val'
    }

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = state.returndata['size']

        state.set_next_pc()
        return [state]


class TAC_Returndatacopy(TAC_Statement):
    __internal_name__ = "RETURNDATACOPY"
    __aliases__ = {
        'destOffset_var': 'arg1_var', 'destOffset_val': 'arg1_val',
        'offset_var': 'arg2_var', 'offset_val': 'arg2_val',
        'size_var': 'arg3_var', 'size_val': 'arg3_val'
    }

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        raise VMExternalData('RETURNDATACOPY')


class TAC_Extcodehash(TAC_Statement):
    __internal_name__ = "EXTCODEHASH"
    __aliases__ = {
        'address_var': 'arg1_var', 'address_val': 'arg1_val',
        'hash_var': 'res1_var', 'hash_val': 'res1_val'
    }

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        if not is_concrete(self.address_val):
            state.registers[self.res1_var] = BVS('EXTCODEHASH[%d]' % self.address_val.id, 256)
        else:
            state.registers[self.res1_var] = ctx_or_symbolic('EXTCODEHASH[%s]' % hex(bv_unsigned_value(self.address_val)), state.ctx, state.xid)

        state.set_next_pc()
        return [state]


class TAC_Blockhash(TAC_Statement):
    __internal_name__ = "BLOCKHASH"
    __aliases__ = {
        'blockNumber_var': 'arg1_var', 'blockNumber_val': 'arg1_val',
        'hash_var': 'res1_var', 'hash_val': 'res1_val'
    }

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        if not is_concrete(self.blockNumber_val):
            state.registers[self.res1_var] = BVS('BLOCKHASH[%d]' % self.blockNumber_val.id, 256)
        else:
            state.registers[self.res1_var] = ctx_or_symbolic('BLOCKHASH[%d]' % bv_unsigned_value(self.blockNumber_val), state.ctx, state.xid)

        state.set_next_pc()
        return [state]


class TAC_Coinbase(TAC_Statement):
    __internal_name__ = "COINBASE"
    __aliases__ = {
        'address_var': 'res1_var', 'address_val': 'res1_val',
    }

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = ctx_or_symbolic('COINBASE', state.ctx, state.xid)

        state.set_next_pc()
        return [state]


class TAC_Timestamp(TAC_Statement):
    __internal_name__ = "TIMESTAMP"
    __aliases__ = {
        'timestamp_var': 'res1_var', 'timestamp_val': 'res1_val',
    }

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        ts = ctx_or_symbolic('TIMESTAMP', state.ctx, state.xid)
        
        if not is_concrete(ts):
            state.add_constraint(BV_UGE(ts, BVV(int(state.min_timestamp), 256)))
            state.add_constraint(BV_ULE(ts, BVV(int(state.max_timestamp), 256)))
        
        state.registers[self.res1_var] = ts

        state.set_next_pc()
        return [state]


class TAC_Number(TAC_Statement):
    __internal_name__ = "NUMBER"
    __aliases__ = {
        'blockNumber_var': 'res1_var', 'blockNumber_val': 'res1_val',
    }

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = ctx_or_symbolic('NUMBER', state.ctx, state.xid)

        state.set_next_pc()
        return [state]


class TAC_Difficulty(TAC_Statement):
    __internal_name__ = "DIFFICULTY"
    __aliases__ = {
        'difficulty_var': 'res1_var', 'difficulty_val': 'res1_val',
    }

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = ctx_or_symbolic('DIFFICULTY', state.ctx, state.xid)

        state.set_next_pc()
        return [state]


class TAC_Gaslimit(TAC_Statement):
    __internal_name__ = "GASLIMIT"
    __aliases__ = {
        'gasLimit_var': 'res1_var', 'gasLimit_val': 'res1_val',
    }

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = ctx_or_symbolic('GASLIMIT', state.ctx, state.xid)

        state.set_next_pc()
        return [state]


class TAC_Chainid(TAC_Statement):
    __internal_name__ = "CHAINID"
    __aliases__ = {
        'chainID_var': 'res1_var', 'chainID_val': 'res1_val',
    }

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        chainid = {'mainnet': 1, 'ropsten': 3, 'rinkeby': 4, 'goerli': 5, 'kotti': 6, 'classic': 61, 'mordor': 63,
                   'astor': 212, 'dev': 2018}
        state.registers[self.res1_var] = chainid['mainnet']

        state.set_next_pc()
        return [state]


class TAC_Selfbalance(TAC_Statement):
    __internal_name__ = "SELFBALANCE"
    __aliases__ = {
        'balance_var': 'res1_var', 'balance_val': 'res1_val',
    }

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = state.balance

        state.set_next_pc()
        return [state]


class TAC_Basefee(TAC_Statement):
    __internal_name__ = "BASEFEE"
    __aliases__ = {
        'baseFee_var': 'res1_var', 'baseFee_val': 'res1_val',
    }

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        # todo: if the current block is known, this is known
        state.registers[self.res1_var] = ctx_or_symbolic('BASEFEE', state.ctx, state.xid)

        state.set_next_pc()
        return [state]


class TAC_Return(TAC_Statement):
    __internal_name__ = "RETURN"

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        # todo: there's probably something more to handle here
        state.halt = True

        return [state]


class TAC_Revert(TAC_Statement):
    __internal_name__ = "REVERT"
    __aliases__ = {
        'offset_var': 'arg1_var', 'offset_val': 'arg1_val',
        'size_var': 'arg2_var', 'size_val': 'arg2_val',
    }

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        # if not is_concrete(self.offset_val) or not is_concrete(self.size_val):
        #     raise VMSymbolicError('symbolic memory index')
        # succ.add_constraint(BV_Or(*(BV_ULE(succ.calldatasize, access) for access in succ.calldata_accesses)))
        state.revert = True
        state.halt = True

        # succ.set_next_pc()
        return [state]


class TAC_Create(TAC_Statement):
    __internal_name__ = "CREATE"
    __aliases__ = {
        'value_var': 'arg1_var', 'value_val': 'arg1_val',
        'offset_var': 'arg2_var', 'offset_val': 'arg2_val',
        'size_var': 'arg3_var', 'size_val': 'arg3_val',
        'address_var': 'res1_var', 'address_val': 'res1_val'
    }

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        state.add_constraint(BV_UGE(state.balance, self.value_val))
        state.balance = BV_Sub(state.balance, self.value_val)

        if options.DEFAULT_CREATE_RESULT_ADDRESS:
            state.registers[self.res1_var] = BVV(0xc0ffee254729296a45a3885639AC7E10F9d54979,256)
        else:
            state.registers[self.res1_var] = BVS('EXT_CREATE_%d_%d', state.xid, state.instruction_count, 256)

        state.set_next_pc()
        return [state]


class TAC_Create2(TAC_Statement):
    __internal_name__ = "CREATE2"
    __aliases__ = {
        'value_var': 'arg1_var', 'value_val': 'arg1_val',
        'offset_var': 'arg2_var', 'offset_val': 'arg2_val',
        'size_var': 'arg3_var', 'size_val': 'arg3_val',
        'salt_var': 'arg4_var', 'salt_val': 'arg4_val',
        'address_var': 'res1_var', 'address_val': 'res1_val'
    }

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        state.add_constraint(BV_UGE(state.balance, self.value_val))
        state.balance = BV_Sub(state.balance, self.value_val)

        if options.DEFAULT_CREATE2_RESULT_ADDRESS:
            state.registers[self.res1_var] = BVV(0xbeefed254729296a45a3885639AC7E10F9d54979,256)
        else:
            state.registers[self.res1_var] = BVS('EXT_CREATE2_%d_%d', state.xid, state.instruction_count, 256)

        state.set_next_pc()
        return [state]


class TAC_Pc(TAC_Statement):
    __internal_name__ = "PC"
    __aliases__ = {
        'counter_var': 'res1_var', 'counter_val': 'res1_val',
    }

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        # todo: this pc will most probably be different from what the evm expects
        raise VMException("PC not available if executing TAC")

        # state.registers[self.res1_var] = state.pc
        # state.set_next_pc()
        # return [state]


class TAC_Invalid(TAC_Statement):
    __internal_name__ = "INVALID"

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        state.halt = True

        return [state]


class TAC_Selfdestruct(TAC_Statement):
    __internal_name__ = "SELFDESTRUCT"
    __aliases__ = {
        'address_var': 'arg1_var', 'address_val': 'arg1_val'
    }

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        # todo: consider the target address
        # succ.add_constraint(z3.Or(*(z3.ULE(succ.calldatasize, access) for access in succ.calldata_accesses)))
        log.fatal("{} NOT implemented".format(self.__internal_name__))
        state.halt = True

        return [state]


class TAC_Gas(TAC_Statement):
    __internal_name__ = "GAS"
    __aliases__ = {
        'gas_var': 'res1_var', 'gas_val': 'res1_val'
    }

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = ctx_or_symbolic('GAS_%x' % state.instruction_count, state.ctx, state.xid)

        state.set_next_pc()
        return [state]
