import datetime
import logging

from SEtaac import options as opt
from SEtaac.memory import LambdaMemory
from SEtaac.solver.shortcuts import *
from SEtaac.state_plugins import SimStatePlugin, SimStateSolver, SimStateGlobals, SimStateInspect
from SEtaac.utils.exceptions import VMNoSuccessors, VMUnexpectedSuccessors
from SEtaac.utils.extra import UUIDGenerator

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
    
        # Register default plugins
        self.active_plugins = dict()
        self._register_default_plugins()
        self._pc = None
        self.trace = list()
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
        self.halt = False
        self.revert = False
        self.error = None
        self.gas = BVS(f'GAS_{self.xid}', 256)
        self.start_balance = BVS(f'BALANCE_{self.xid}', 256)
        self.balance = BV_Add(self.start_balance, ctx_or_symbolic('CALLVALUE', self.ctx, self.xid))
        self.ctx['CODESIZE-ADDRESS'] = BVV(len(self.code), 256)
        self.sha_observed = list()

        # make sure we can exploit it in the foreseeable future
        self.min_timestamp = (datetime.datetime.now() - datetime.datetime(1970, 1, 1)).total_seconds()
        self.max_timestamp = (datetime.datetime(2020, 1, 1) - datetime.datetime(1970, 1, 1)).total_seconds()
        self.MAX_CALLDATA_SIZE = max_calldatasize or opt.MAX_CALLDATA_SIZE

        self.calldata = None
        self.calldatasize = None

        self.set_init_ctx(init_ctx)

    def set_init_ctx(self, init_ctx=None):
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
                log.debug(f"CALLDATASIZE MIN{len(calldata_bytes)}-MAX{self.MAX_CALLDATA_SIZE + 1}")
                self.calldata = LambdaMemory(tag=f"CALLDATA_{self.xid}", value_sort=BVSort(8), state=self)
                # CALLDATASIZE < MAX_CALLDATA_SIZE
                self.add_constraint(BV_ULT(self.calldatasize, BVV(self.MAX_CALLDATA_SIZE + 1, 256)))
                # CALLDATASIZE is >= than the length of the provided CALLDATA bytes
                self.add_constraint(BV_UGE(self.calldatasize, BVV(len(calldata_bytes), 256)))

            for index, cb in enumerate(calldata_bytes):
                if cb == 'SS':
                    log.debug(f"Storing symbolic byte at index {index} in CALLDATA")
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

    @property
    def curr_stmt(self):
        return self.project.factory.statement(self._pc)

    @property
    def constraints(self):
        return self.solver.constraints

    @pc.setter
    def pc(self, value):
        self._pc = value

    def set_next_pc(self):
        try:
            self.pc = self.get_fallthrough_pc()
        except VMNoSuccessors:
            self.halt = True

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
    
    def add_constraint(self, constraint):
        # Here you can inspect the constraints being added to the state.
        if opt.STATE_STOP_AT_ADDCONSTRAINT in self.options:
            import ipdb; ipdb.set_trace()
        self.solver.add_path_constraints(constraint)

    # Add here any default plugin that we want to ship
    # with a fresh state.
    def _register_default_plugins(self):
        self.register_plugin("solver", SimStateSolver())
        self.register_plugin("globals", SimStateGlobals())
        if opt.STATE_INSPECT:
            self.register_plugin("inspect", SimStateInspect())

    def register_plugin(self, name: str, plugin: SimStatePlugin):
        self.active_plugins[name] = plugin
        setattr(self, name, plugin)
        plugin.set_state(self)
        return plugin

    def copy(self):
        # assume unchanged xid
        new_state = SymbolicEVMState(self.xid, project=self.project, partial_init=True)

        new_state._pc = self._pc
        new_state.trace = list(self.trace)

        new_state.memory = self.memory.copy(new_state=new_state)
        new_state.storage = self.storage.copy(new_state=new_state)
        new_state.registers = dict(self.registers)
        new_state.ctx = dict(self.ctx)
        new_state.options = list(self.options)
        new_state.callstack = list(self.callstack)
        new_state.returndata = dict(self.returndata)
        new_state.instruction_count = self.instruction_count
        new_state.halt = self.halt
        new_state.revert = self.revert
        new_state.error = self.error
        new_state.gas = self.gas
        new_state.start_balance = self.start_balance
        new_state.balance = self.balance

        #new_state.sha_observed = [sha.copy(new_state=new_state) for sha in self.sha_observed]
        new_state.sha_observed = self.sha_observed
        new_state.min_timestamp = self.min_timestamp
        new_state.max_timestamp = self.max_timestamp
        new_state.MAX_CALLDATA_SIZE = self.MAX_CALLDATA_SIZE
        new_state.calldata = self.calldata.copy(new_state=new_state)
        new_state.calldatasize = self.calldatasize

        new_state.active_plugins = dict()
        # Copy all the plugins
        for p_name, p in self.active_plugins.items():
            new_state.register_plugin(p_name, p.copy())

        return new_state

    def reset(self, xid):
        self.xid = xid
        self.uuid = SymbolicEVMState.uuid_generator.next()

        # Register default plugins
        self.active_plugins = dict()
        self._register_default_plugins()

        self._pc = None
        self.trace = list()
        self.memory = LambdaMemory(tag=f"MEMORY_{self.xid}", value_sort=BVSort(8), default=BVV(0, 8), state=self)
        self.registers = dict()
        self.ctx = dict()  # todo: is it okay to reset this between transactions??

        self.callstack = list()
        self.returndata = {'size': None, 'instruction_count': None}
        self.instruction_count = 0
        self.halt = False
        self.revert = False
        self.error = None
        self.gas = BVS(f'GAS_{self.xid}', 256)
        self.start_balance = BVS(f'BALANCE_{self.xid}', 256)
        self.balance = BV_Add(self.start_balance, ctx_or_symbolic('CALLVALUE', self.ctx, self.xid))
        self.ctx['CODESIZE-ADDRESS'] = BVV(len(self.code), 256)
        self.sha_observed = list()

        self.calldata = None
        self.calldatasize = None

        return self

    def __str__(self):
        return f"State {self.uuid} at {self.pc}"

    def __repr__(self):
        return str(self)
