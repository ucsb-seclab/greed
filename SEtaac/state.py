import datetime
import logging

import z3

from collections import defaultdict

from SEtaac import utils
from SEtaac.exceptions import ExternalData, SymbolicError, IntractablePath, VMException
from SEtaac.memory import SymRead, SymbolicMemory
from SEtaac.storage import SymbolicStorage
from SEtaac.utils import concrete, is_true, get_solver, translate_xid


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
        return self.project.tac_parser.get_stmt_at(self.pc)

    def set_next_pc(self):
        # todo: read next statement from dict
        next_pcs = get_next_pcs(self.curr_stmt)
        assert len(next_pcs) == 1
        self.pc = next_pcs[0]

    def copy(self, new_xid=None):
        # todo: implement state copy
        # todo: there shouldn't be any need to set a new xid, in most cases
        # new_state = SymbolicEVMState(new_xid or self.xid, code=self.code)
        #
        # new_state.pc = self.pc
        # self.memory = None
        # self.trace = list()
        # self.gas = None
        #
        # new_state.storage = self.storage.copy(new_xid)
        # new_state.pc = self.pc
        # new_state.trace = list(self.trace)
        # new_state.start_balance = translate_xid(self.start_balance, new_xid)
        # new_state.balance = translate_xid(self.balance, new_xid)
        #
        # new_state.constraints = list(self.constraints)
        # new_state.sha_constraints = dict(self.sha_constraints)
        # new_state.ctx = dict(self.ctx)

        return self

    def gas_handler(self, ):
        return z3.BitVec('GAS_%x' % self.instruction_count, 256)

    def stop_handler(self, ):
        self.constraints.append(z3.Or(*(z3.ULE(self.calldatasize, access) for access in self.calldata_accesses)))
        self.halt = True
