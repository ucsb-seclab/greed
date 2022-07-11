import datetime
import logging
from collections import defaultdict

from SEtaac.utils import gen_uuid
from SEtaac.utils.exceptions import VMNoSuccessors, VMUnexpectedSuccessors
from SEtaac.memory import SymbolicMemory
from SEtaac.registers import SymbolicRegisters
from SEtaac.storage import SymbolicStorage
from SEtaac.utils.solver.shortcuts import *

log = logging.getLogger(__name__)

class SymbolicEVMState:
    def __init__(self, xid, project, partial_init=False, ctx=dict()):
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
        self.ctx = ctx

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

        self.term_to_sha_map = dict()

        # make sure we can exploit it in the foreseeable future
        self.min_timestamp = (datetime.datetime.now() - datetime.datetime(1970, 1, 1)).total_seconds()
        self.max_timestamp = (datetime.datetime(2020, 1, 1) - datetime.datetime(1970, 1, 1)).total_seconds()

        self.MAX_CALLDATA_SIZE = 256

        # CALLDATA is always defined as an Array
        #self.calldata = SymbolicMemory(tag='CALLDATA_%d' % self.xid)
        self.calldata = Array('CALLDATA_%d' % self.xid, BVSort(256), BVSort(8))

        if "CALLDATA" not in self.ctx:
            # We assume fully symbolic CALLDATA and CALLDATASIZE in this case
            self.calldatasize = BVS(f'CALLDATASIZE_{self.xid}', 256)
            self.constraints.append(BV_ULT(self.calldatasize, BVV(self.MAX_CALLDATA_SIZE + 1, 256)))
        else:
            # We want to give the possibility to specify interleaving of symbolic/concrete data bytes in the CALLDATA.
            # for instance: "CALLDATA" = ["0x1546138954SSSS81923899"]. There are 2 symbolic bytes represented by SSSS.
            calldata_arg = self.ctx['CALLDATA']
            assert(type(self.ctx['CALLDATA'])== str)
            calldata_arg = calldata_arg.replace("0x",'')

            # Parsing the CALLDATA
            # Since we have a string as input, we divide byte by byte here.
            calldata_bytes = [calldata_arg[i:i+2] for i in range(0,len(calldata_arg),2)]
            calldata_index = 0
            for cb in calldata_bytes:
                calldata_index_bvv = BVV(calldata_index,256)
                if cb == 'SS': # special char to instruct for a symbolic byte
                    #self.calldata[calldata_index_bvv] = BVS(f'CALLDATA_BYTE_{calldata_index}',8)
                    self.calldata = Array_Store(self.calldata, BVV(calldata_index,256), BVS(f'CALLDATA_BYTE_{calldata_index}',8))
                else:
                    #self.calldata[calldata_index_bvv] = BVV(int(cb,16), 8)'
                    log.debug("Initializing CALLDATA at {}".format(calldata_index))
                    self.calldata = Array_Store(self.calldata, BVV(calldata_index,256), BVV(int(cb,16), 8))
                calldata_index += 1

            if "CALLDATASIZE" in self.ctx:
                # If the CALLDATASIZE provided matches with the amount of data provided in CALLDATA we just use that
                # CALLDATASIZE is an `int` representing the number of BYTES in the CALLDATA
                if self.ctx["CALLDATASIZE"] == len(calldata_bytes):
                    # Let's keep the symbol to see it in the constraints :)
                    self.calldatasize = BVS(f'CALLDATASIZE_{self.xid}', 256)
                    # Pre-constraining it to the len of the CALLDATA
                    self.constraints.append(Equal(self.calldatasize, BVV(len(calldata_bytes), 256)))
                elif self.ctx["CALLDATASIZE"] > len(calldata_bytes):
                    # CALLDATASIZE is bigger than size(CALLDATA), we set the rest of the CALLDATA as symbolic
                    calldatasize_arg = self.ctx["CALLDATASIZE"]
                    self.calldatasize = BVS(f'CALLDATASIZE_{self.xid}', 256)
                    # CALLDATASIZE is the provided number
                    self.constraints.append(Equal(self.calldatasize, BVV(calldatasize_arg, 256)))
                else:
                    log.fatal("Provided CALLDATASIZE must be greater than CALLDATA bytes")
                    raise Exception
            else:
                # We set a symbolic CALLDATASIZE setting appropiate constraints
                self.calldatasize = BVS(f'CALLDATASIZE_{self.xid}', 256)
                # CALLDATASIZE is always less than the MAX_CALLDATA_SIZE
                self.constraints.append(BV_ULT(self.calldatasize, BVV(self.MAX_CALLDATA_SIZE + 1, 256)))
                # CALLDATASIZE is at >= than the provided CALLDATA bytes
                self.constraints.append(BV_UGE(self.calldatasize, BVV(len(calldata_bytes), 256)))
            
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
            log.debug("Next stmt is {}".format(remaining_stmts[0].id))
            return remaining_stmts[0].id
        elif len(curr_bb.succ) == 0:
            log.debug("Next stmt is NONE")
            raise VMNoSuccessors
        elif len(curr_bb.succ) == 1:
            log.debug("Next stmt is {}".format(curr_bb.succ[0].first_ins.id))
            return curr_bb.succ[0].first_ins.id
        elif len(curr_bb.succ) == 2:
            #  case 3: end of the block and two targets
            #  we need to set the fallthrough to the state.
            #  The handler (e.g., JUMPI) has already created the state at the jump target.

            fallthrough_bb = curr_bb.fallthrough_edge
            log.debug("Next stmt is {}".format(fallthrough_bb.first_ins.id))
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

        new_state.term_to_sha_map = dict(self.term_to_sha_map)

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
