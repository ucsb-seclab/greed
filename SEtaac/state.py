import datetime
from collections import defaultdict
from SEtaac.exceptions import VMException

import z3

from SEtaac import utils
from SEtaac.memory import SymbolicMemory
from SEtaac.storage import SymbolicStorage
from SEtaac.utils import concrete, translate_xid

class AbstractEVMState(object):
    def __init__(self, code=None):
        self.code = code or bytearray()
        self.pc = 0
        self.memory = None
        self.trace = list()
        self.gas = None


class SymbolicEVMState(AbstractEVMState):
    def __init__(self, xid, project, program=None, code=None):
        super(SymbolicEVMState, self).__init__(code)
        self.program = program
        self.xid = xid
        self.project = project

        self.memory = SymbolicMemory()
        self.storage = SymbolicStorage(self.xid)
        self.registers = defaultdict(None)
        self.ctx = dict()

        self.callstack = list()

        self.instruction_count = 0
        self.halt = False
        self.error = None

        self.gas = z3.BitVec('GAS_%d' % self.xid, 256)
        self.start_balance = z3.BitVec('BALANCE_%d' % self.xid, 256)
        self.balance = self.start_balance
        self.balance += utils.ctx_or_symbolic('CALLVALUE', self.ctx, self.xid)

        self.ctx['CODESIZE-ADDRESS'] = len(code) if code else 0  # todo: code can be None

        self.constraints = list()
        self.sha_constraints = dict()

        # make sure we can exploit it in the foreseeable future
        self.min_timestamp = (datetime.datetime.now() - datetime.datetime(1970, 1, 1)).total_seconds()
        self.max_timestamp = (datetime.datetime(2020, 1, 1) - datetime.datetime(1970, 1, 1)).total_seconds()

        self.MAX_CALLDATA_SIZE = 256
        self.calldata = z3.Array('CALLDATA_%d' % self.xid, z3.BitVecSort(256), z3.BitVecSort(8))
        self.calldatasize = z3.BitVec('CALLDATASIZE_%d' % self.xid, 256)
        self.calldata_accesses = [0]

    @property
    def curr_stmt(self):
        # todo: pass project to state
        # todo: pc is the statement id
        return self.project._statement_at[self.pc]

    def set_next_pc(self):
        # todo: add get_statement to project.factory
        # actually look at curr_stmt(self)

        # get block
        curr_bb = self.project.factory.block(self.curr_stmt.block_ident)
        stmt_list_idx = curr_bb.statements.index(self.curr_stmt)
        remaining_stmts = curr_bb.statements[stmt_list_idx+1:]
        cfgnode = curr_bb.function.cfg.blockids_to_cfgnode[curr_bb.ident]

        # case 1: middle of the block
        if remaining_stmts:
            self.pc = remaining_stmts[0].stmt_ident
        elif len(cfgnode.succ) == 0:
            self.halt = True
        elif len(cfgnode.succ) == 1:
            self.pc = cfgnode.succ[0].bb.first_ins.stmt_ident
        elif len(cfgnode.succ) == 2:
            #  case 3: end of the block and two targets
            #  we need to set the fallthrough to the state. 
            #  The handler of the JUMPI has already created the state at the jump target. 
            assert(self.curr_stmt.__internal_name__ == "JUMPI")
            not_fallthrough = self.registers[self.curr_stmt.destination_var]
            
            # We need make sure this is concrete to check against the successors of the node
            if not concrete(not_fallthrough):
                raise VMException("Symbolic destination for JUMPI. This should not happen.")
            else:
                # Fallthrough addresses are block addresses
                fallthrough_node = list(filter(lambda n: n.bb.ident != not_fallthrough, cfgnode.succ))[0]
                self.pc = fallthrough_node.bb.first_ins.stmt_ident
        else:
            raise VMException("We have more than two successors for {}?!".format(curr_bb))

    def copy(self):
        # assume unchanged xid
        new_state = SymbolicEVMState(self.xid, project=self.project, program=self.program, code=self.code)

        new_state.pc = self.pc

        new_state.memory = self.memory.copy(self.xid)
        new_state.storage = self.storage.copy(self.xid)
        new_state.registers = dict(self.registers)
        new_state.ctx = dict(self.ctx)

        new_state.callstack = list(self.callstack)

        new_state.instruction_count = self.instruction_count
        new_state.halt = self.halt
        new_state.error = self.error

        new_state.gas = self.gas
        new_state.start_balance = self.start_balance
        new_state.balance = self.balance

        new_state.constraints = list(self.constraints)
        new_state.sha_constraints = dict(self.sha_constraints)

        new_state.min_timestamp = self.min_timestamp
        new_state.max_timestamp = self.max_timestamp

        new_state.MAX_CALLDATA_SIZE = self.MAX_CALLDATA_SIZE
        new_state.calldata = self.calldata
        new_state.calldatasize = self.calldatasize
        new_state.calldata_accesses = list(self.calldata_accesses)

        return new_state

    def __str__(self):
        return "State at {}".format(self.pc)

    def __repr__(self):
        return str(self)
