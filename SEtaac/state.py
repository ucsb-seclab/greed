import datetime
import logging

from SEtaac import options
from SEtaac.lambda_memory import LambdaMemory
from SEtaac.utils.exceptions import VMNoSuccessors, VMUnexpectedSuccessors
from SEtaac.utils.extra import UUIDGenerator
from SEtaac.utils.solver.shortcuts import *

log = logging.getLogger(__name__)


class SymbolicEVMState:
    uuid_generator = UUIDGenerator()

    def __init__(self, xid, project, partial_init=False, init_ctx=None, options=None, max_calldatasize=None):
        self.xid = xid
        self.project = project
        self.code = project.code

        self.uuid = SymbolicEVMState.uuid_generator.next()

        if partial_init:
            # this is only used when copying the state
            return

        self._pc = None
        self.trace = list()

        self.solver = get_clean_solver()

        self.memory = LambdaMemory(tag=f"MEMORY_{self.xid}", value_sort=BVSort(8), default=BVV(0, 8), state=self)
        self.storage = LambdaMemory(tag=f"STORAGE_{self.xid}", value_sort=BVSort(256), state=self)
        self.registers = dict()
        self.ctx = dict()

        # We want every state to have an individual set
        # of options.
        self.options = options or list()

        self.callstack = list()

        self.returndata = {'size': None, 'instruction_count': None}

        self.instruction_count = 0
        self.breakpoints = {}
        self.halt = False
        self.revert = False
        self.error = None

        self.gas = BVS(f'GAS_{self.xid}', 256)
        self.start_balance = BVS(f'BALANCE_{self.xid}', 256)
        self.balance = self.start_balance

        callvalue = ctx_or_symbolic('CALLVALUE', self.ctx, self.xid)
        self.balance = BV_Add(self.balance, callvalue)

        self.ctx['CODESIZE-ADDRESS'] = BVV(len(self.code), 256)

        self._path_constraints = list()

        self.sha_observed = list()

        # make sure we can exploit it in the foreseeable future
        self.min_timestamp = (datetime.datetime.now() - datetime.datetime(1970, 1, 1)).total_seconds()
        self.max_timestamp = (datetime.datetime(2020, 1, 1) - datetime.datetime(1970, 1, 1)).total_seconds()

        self.MAX_CALLDATA_SIZE = max_calldatasize or option.MAX_CALLDATA_SIZE

        init_ctx = init_ctx or dict()
        if "CALLDATA" in init_ctx:
            # We want to give the possibility to specify interleaving of symbolic/concrete data bytes in the CALLDATA.
            # for instance: "CALLDATA" = ["0x1546138954SSSS81923899"]. There are 2 symbolic bytes represented by SSSS.
            assert isinstance(init_ctx['CALLDATA'], str), "Wrong type for CALLDATA initial context"

            # Parse the CALLDATA (divide the input string byte by byte)
            calldata_raw = init_ctx['CALLDATA'].replace("0x", '')
            calldata_bytes = [calldata_raw[i:i + 2] for i in range(0, len(calldata_raw), 2)]

            self.calldatasize = BVS(f'CALLDATASIZE_{self.xid}', 256)
            if "CALLDATASIZE" in init_ctx:
                # CALLDATASIZE is equal than size(CALLDATA), pre-constraining to this exact size
                self.add_constraint(Equal(self.calldatasize, BVV(init_ctx["CALLDATASIZE"], 256)))

                self.calldata = LambdaMemory(tag=f"CALLDATA_{self.xid}", value_sort=BVSort(8), default=BVV(0, 8), state=self)

                assert init_ctx["CALLDATASIZE"] >= len(calldata_bytes), "CALLDATASIZE is smaller than len(CALLDATA)"
                if init_ctx["CALLDATASIZE"] > len(calldata_bytes):
                    # CALLDATASIZE is bigger than size(CALLDATA), we set the unspecified CALLDATA as symbolic
                    for index in range(len(calldata_bytes), init_ctx["CALLDATASIZE"]):
                        self.calldata[BVV(index, 256)] = BVS(f'CALLDATA_BYTE_{index}', 8)
            else:
                self.calldata = LambdaMemory(tag=f"CALLDATA_{self.xid}", value_sort=BVSort(8), state=self)
                # CALLDATASIZE < MAX_CALLDATA_SIZE
                self.add_constraint(BV_ULT(self.calldatasize, BVV(self.MAX_CALLDATA_SIZE + 1, 256)))
                # CALLDATASIZE is >= than the length of the provided CALLDATA bytes
                self.add_constraint(BV_UGE(self.calldatasize, BVV(len(calldata_bytes), 256)))

            for index, cb in enumerate(calldata_bytes):
                if cb == 'SS':
                    # special sequence for symbolic bytes
                    self.calldata[BVV(index, 256)] = BVS(f'CALLDATA_BYTE_{index}', 8)
                else:
                    log.debug("Initializing CALLDATA at {}".format(index))
                    self.calldata[BVV(index, 256)] = BVV(int(cb, 16), 8)

        else:
            self.calldata = LambdaMemory(tag=f"CALLDATA_{self.xid}", value_sort=BVSort(8), state=self)

            # We assume fully symbolic CALLDATA and CALLDATASIZE in this case
            self.calldatasize = BVS(f'CALLDATASIZE_{self.xid}', 256)
            # CALLDATASIZE < MAX_CALLDATA_SIZE
            self.add_constraint(BV_ULT(self.calldatasize, BVV(self.MAX_CALLDATA_SIZE + 1, 256)))

        if "CALLER" in init_ctx:
            self.ctx["CALLER"] = BVV(init_ctx["CALLER"], 256)

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
            self.pc = self.get_fallthrough_pc()
        except VMNoSuccessors:
            self.halt = True

    # index: where to start
    # size: the amount of bytes to read, default 1.
    def dbg_read_memory(self, index, size=1):
        # WARNING: THIS IS JUST AN API EXPOSED TO USER,
        #          DO NOT USE IT INTERNALLY.
        assert(type(index) is int)
        return BV_Concat(self.memory[BVV(index, 256):BVV(index+size, 256)])

    def get_fallthrough_pc(self):
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
            fallthrough_bb = curr_bb.fallthrough_edge

            log.debug("Next stmt is {}".format(fallthrough_bb.first_ins.id))
            return fallthrough_bb.first_ins.id
        else:
            raise VMUnexpectedSuccessors("More than two successors for {}?!".format(curr_bb))

    def get_non_fallthrough_pc(self):
        curr_bb = self.project.factory.block(self.curr_stmt.block_id)
        stmt_list_idx = curr_bb.statements.index(self.curr_stmt)
        remaining_stmts = curr_bb.statements[stmt_list_idx + 1:]

        assert len(remaining_stmts) == 0, "Cannot jump in the middle of a block"
        assert len(curr_bb.succ) == 2, f"{len(curr_bb.succ)} successors for block {curr_bb}"

        fallthrough_bb = curr_bb.fallthrough_edge

        all_non_fallthrough_bbs = [bb for bb in curr_bb.succ if bb != fallthrough_bb]
        assert len(all_non_fallthrough_bbs) == 1
        non_fallthrough_bb = all_non_fallthrough_bbs[0]

        log.debug("Next stmt is {}".format(non_fallthrough_bb.first_ins.id))
        return non_fallthrough_bb.first_ins.id

    @property
    def sha_constraints(self):
        constraints = list()
        for sha in self.sha_observed:
            constraints += sha.constraints
        return constraints

    @property
    def constraints(self):
        return self._path_constraints + self.memory.constraints + self.calldata.constraints + \
               self.storage.constraints + self.sha_constraints
    
    def add_constraint(self, constraint):
        # Here you can inspect the constraints being added to the state.
        if options.STATE_STOP_AT_ADDCONSTRAINT in self.options:
            import ipdb; ipdb.set_trace()
        self._path_constraints.append(constraint)
        self.solver.add_assertion(constraint)
    
    def add_breakpoint(self, stmt_id, func=None):
        if not func:
            def justStop(state):
                import ipdb; ipdb.set_trace()
        self.breakpoints[stmt_id] = func

    def copy(self):
        # assume unchanged xid
        new_state = SymbolicEVMState(self.xid, project=self.project, partial_init=True)

        new_state._pc = self._pc
        new_state.trace = list(self.trace)

        new_state.solver = self.solver.copy()

        new_state.memory = self.memory.copy(new_state=new_state)
        new_state.storage = self.storage.copy(new_state=new_state)
        new_state.registers = dict(self.registers)
        new_state.ctx = dict(self.ctx)
        new_state.options = list(self.options)

        new_state.callstack = list(self.callstack)

        new_state.returndata = dict(self.returndata)

        new_state.instruction_count = self.instruction_count
        new_state.breakpoints = self.breakpoints
        new_state.halt = self.halt
        new_state.revert = self.revert
        new_state.error = self.error

        new_state.gas = self.gas
        new_state.start_balance = self.start_balance
        new_state.balance = self.balance

        new_state._path_constraints = list(self._path_constraints)

        new_state.sha_observed = [sha.copy(new_state=new_state) for sha in self.sha_observed]

        new_state.min_timestamp = self.min_timestamp
        new_state.max_timestamp = self.max_timestamp

        new_state.MAX_CALLDATA_SIZE = self.MAX_CALLDATA_SIZE
        new_state.calldata = self.calldata.copy(new_state=new_state)
        new_state.calldatasize = self.calldatasize

        return new_state

    def __str__(self):
        return f"State {self.uuid} at {self.pc}"

    def __repr__(self):
        return str(self)
