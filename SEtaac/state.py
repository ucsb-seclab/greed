import datetime
import z3
from collections import defaultdict

from SEtaac import utils
from SEtaac.exceptions import VM_NoSuccessors, VM_UnexpectedSuccessors
from SEtaac.memory import SymbolicMemory
from SEtaac.storage import SymbolicStorage


class SymbolicEVMState:
    def __init__(self, xid, project, program=None, code=None):
        self.code = code or bytearray()
        self.program = program
        self.xid = xid
        self.project = project

        self._pc = None
        self.trace = list()

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
    def pc(self):
        return self._pc

    @pc.setter
    def pc(self, value):
        self.trace.append(self._pc)
        self.instruction_count += 1
        self._pc = value

    @property
    def curr_stmt(self):
        return self.project._statement_at[self._pc]

    def set_next_pc(self):
        try:
            self.pc = self.get_next_pc()
        except VM_NoSuccessors:
            self.halt = True

    def get_next_pc(self):
        # get block
        curr_bb = self.project.factory.block(self.curr_stmt.block_ident)
        stmt_list_idx = curr_bb.statements.index(self.curr_stmt)
        remaining_stmts = curr_bb.statements[stmt_list_idx + 1:]

        # case 1: middle of the block
        if remaining_stmts:
            return remaining_stmts[0].stmt_ident
        elif len(curr_bb.succ) == 0:
            raise VM_NoSuccessors
        elif len(curr_bb.succ) == 1:
            return curr_bb.succ[0].first_ins.stmt_ident
        elif len(curr_bb.succ) == 2:
            #  case 3: end of the block and two targets
            #  we need to set the fallthrough to the state.
            #  The handler of the JUMPI has already created the state at the jump target.
            assert (self.curr_stmt.__internal_name__ == "JUMPI")

            # guess and refine target_bb_id
            target_bb_id = hex(self.registers[self.curr_stmt.destination_var])
            target_bb = self.project.factory.block(target_bb_id + curr_bb.function.id)
            if not target_bb:
                target_bb = self.project.factory.block(target_bb_id)
            target_bb_id = target_bb.ident

            # find and return fallthrough branch
            fallthrough_bb = [bb for bb in curr_bb.succ if bb.ident != target_bb_id][0]
            return fallthrough_bb.first_ins.stmt_ident
        else:
            raise VM_UnexpectedSuccessors("More than two successors for {}?!".format(curr_bb))

    def copy(self):
        # assume unchanged xid
        new_state = SymbolicEVMState(self.xid, project=self.project, program=self.program, code=self.code)

        new_state._pc = self._pc
        new_state.trace = list(self.trace)

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
