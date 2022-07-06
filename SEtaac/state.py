import datetime
from collections import defaultdict

from SEtaac.utils import gen_uuid
from SEtaac.utils.exceptions import VMNoSuccessors, VMUnexpectedSuccessors
from SEtaac.memory import SymbolicMemory
from SEtaac.registers import SymbolicRegisters
from SEtaac.storage import SymbolicStorage
from SEtaac.utils.solver.shortcuts import *


class SymbolicEVMState:
    def __init__(self, xid, project, partial_init=False):
        self.xid = xid
        self.project = project
        self.code = project.code

        self.uuid = gen_uuid()

        if partial_init:
            # this is only used when copying the state
            return

        self._pc = None
        self.trace = list()

        self.memory = SymbolicMemory()
        self.storage = SymbolicStorage(self.xid)
        self.registers = SymbolicRegisters()
        self.ctx = dict()

        self.callstack = list()

        self.instruction_count = 0
        self.halt = False
        self.revert = False
        self.error = None

        self.gas = BVS(f'GAS_{self.xid}', 256)
        self.start_balance = BVS(f'BALANCE_{self.xid}', 256)
        self.balance = self.start_balance

        callvalue = ctx_or_symbolic('CALLVALUE', self.ctx, self.xid)
        self.balance = BV_Add(self.balance, callvalue)

        self.ctx['CODESIZE-ADDRESS'] = len(self.code)

        self.constraints = list()
        self.sha_constraints = dict()

        # make sure we can exploit it in the foreseeable future
        self.min_timestamp = (datetime.datetime.now() - datetime.datetime(1970, 1, 1)).total_seconds()
        self.max_timestamp = (datetime.datetime(2020, 1, 1) - datetime.datetime(1970, 1, 1)).total_seconds()

        self.MAX_CALLDATA_SIZE = 256
        self.calldata = Array('CALLDATA_%d' % self.xid, BVSort(256), BVSort(8))
        self.calldatasize = BVS(f'CALLDATASIZE_{self.xid}', 256)
        self.constraints.append(BV_ULT(self.calldatasize, BVV(self.MAX_CALLDATA_SIZE + 1, 256)))
        # self.calldata_accesses = [0]

    @property
    def pc(self):
        return self._pc

    @pc.setter
    def pc(self, value):
        self._pc = value

    @property
    def curr_stmt(self):
        return self.project.factory.statement(self._pc)

    def set_next_pc(self):
        try:
            self.pc = self.get_next_pc()
        except VMNoSuccessors:
            self.halt = True

    def get_next_pc(self):
        # get block
        curr_bb = self.project.factory.block(self.curr_stmt.block_id)
        stmt_list_idx = curr_bb.statements.index(self.curr_stmt)
        remaining_stmts = curr_bb.statements[stmt_list_idx + 1:]

        # case 1: middle of the block
        if remaining_stmts:
            return remaining_stmts[0].id
        elif len(curr_bb.succ) == 0:
            raise VMNoSuccessors
        elif len(curr_bb.succ) == 1:
            return curr_bb.succ[0].first_ins.id
        elif len(curr_bb.succ) == 2:
            #  case 3: end of the block and two targets
            #  we need to set the fallthrough to the state.
            #  The handler (e.g., JUMPI) has already created the state at the jump target.

            fallthrough_bb = curr_bb.fallthrough_edge
            return fallthrough_bb.first_ins.id
        else:
            raise VMUnexpectedSuccessors("More than two successors for {}?!".format(curr_bb))

    def import_context(self, state: "SymbolicEVMState"):
        self.storage = state.storage

        self.start_balance = state.balance
        self.balance = self.start_balance
        self.balance += ctx_or_symbolic('CALLVALUE', self.ctx, self.xid)

        self.constraints = state.constraints
        self.sha_constraints = state.sha_constraints

    def copy(self):
        # assume unchanged xid
        new_state = SymbolicEVMState(self.xid, project=self.project, partial_init=True)

        new_state._pc = self._pc
        new_state.trace = list(self.trace)

        new_state.memory = self.memory.copy(self.xid, self.xid)
        new_state.storage = self.storage.copy(self.xid, self.xid)
        new_state.registers = self.registers.copy()
        new_state.ctx = dict(self.ctx)

        new_state.callstack = list(self.callstack)

        new_state.instruction_count = self.instruction_count
        new_state.halt = self.halt
        new_state.revert = self.revert
        new_state.error = self.error

        new_state.gas = self.gas
        new_state.start_balance = self.start_balance
        new_state.balance = self.balance

        new_state.ctx['CODESIZE-ADDRESS'] = self.ctx['CODESIZE-ADDRESS']

        new_state.constraints = list(self.constraints)
        new_state.sha_constraints = dict(self.sha_constraints)

        new_state.min_timestamp = self.min_timestamp
        new_state.max_timestamp = self.max_timestamp

        new_state.MAX_CALLDATA_SIZE = self.MAX_CALLDATA_SIZE
        new_state.calldata = self.calldata
        new_state.calldatasize = self.calldatasize
        # new_state.calldata_accesses = list(self.calldata_accesses)

        return new_state

    def __str__(self):
        return f"State {self.uuid} at {self.pc}"

    def __repr__(self):
        return str(self)
