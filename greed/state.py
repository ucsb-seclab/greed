import datetime
import logging
import typing

from greed import options as opt
from greed.memory import LambdaMemory, PartialConcreteStorage
from greed.solver.shortcuts import *
from greed.state_plugins import SimStatePlugin, SimStateSolver, SimStateGlobals, SimStateInspect, ShaResolver
from greed.utils.exceptions import VMNoSuccessors, VMUnexpectedSuccessors
from greed.utils.exceptions import VMSymbolicError
from greed.utils.extra import UUIDGenerator

log = logging.getLogger(__name__)

if typing.TYPE_CHECKING:
    from greed.project import Project


class SymbolicEVMState:
    """
    This class represents a symbolic EVM state (SimState).
    """
    uuid_generator = UUIDGenerator()
    xid: int
    project: "Project"
    code: bytes
    uuid: int
    active_plugins: typing.Dict[str, SimStatePlugin]
    _pc: str
    trace: typing.List[str]
    memory: LambdaMemory
    options: typing.Dict[str, typing.Any]
    registers: typing.Dict[str, typing.Any]

    # default plugins
    solver: SimStateSolver
    globals: SimStateGlobals
    inspect: SimStateInspect


    def __init__(self, xid, project, partial_init=False, init_ctx=None, options=None, max_calldatasize=None, partial_concrete_storage=False):
        """
        Args:
            xid: The execution id 
            project: the greed project
            partial_init: Whether to partially initialize the object or not
            init_ctx: The initial context of the state (e.g., CALLER, ADDRESS, BALANCE, etc.)
            options: The options for this state
            max_calldatasize: The maximum size of the calldata
            partial_concrete_storage: Whether to use the partial concrete storage or not
        """
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

        # We want every state to have an individual set
        # of options.
        self.options = options or dict()            
        self.registers = dict()
        self.ctx = dict()
        self.callstack = list()
        self.returndata = {'size': BVV(0, 256), 'instruction_count': BVV(0, 256)}
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
        self.min_timestamp = (datetime.datetime(2022, 1, 1) - datetime.datetime(1970, 1, 1)).total_seconds()
        self.max_timestamp = (datetime.datetime.now() - datetime.datetime(1970, 1, 1)).total_seconds()
        self.MAX_CALLDATA_SIZE = max_calldatasize or opt.MAX_CALLDATA_SIZE

        self.calldata = None
        self.calldatasize = None

        # Apply init context to the state
        self.set_init_ctx(init_ctx)

        if not partial_concrete_storage:
            # Fully symbolic storage
            self.storage = LambdaMemory(tag=f"STORAGE_{self.xid}", value_sort=BVSort(256), state=self)
        else:
            log.debug("Using PartialConcreteStorage")
            self.storage = PartialConcreteStorage(tag=f"PCONCR_STORAGE_{self.xid}", value_sort=BVSort(256), state=self)

    def set_init_ctx(self, init_ctx=None):
        """
        This method applies the initial context to the state.
        Args:
            init_ctx: A dict storing the initial context of the state (e.g., CALLER, ADDRESS, BALANCE, etc.)
        """
        init_ctx = init_ctx or dict()

        if "CALLDATASIZE" in init_ctx:
            self.calldatasize = BVV(init_ctx["CALLDATASIZE"], 256)

            # If the CALLDATASIZE is fixed, update MAX_CALLDATASIZE
            self.MAX_CALLDATA_SIZE = init_ctx["CALLDATASIZE"]
        else:
            self.calldatasize = BVS(f'CALLDATASIZE_{self.xid}', 256)
            self.add_constraint(BV_ULE(self.calldatasize, BVV(self.MAX_CALLDATA_SIZE, 256)))

        if "CALLDATA" in init_ctx:
            # We want to give the possibility to specify interleaving of symbolic/concrete data bytes in the CALLDATA.
            # for instance: "CALLDATA" = ["0x1546138954SSSS81923899"]. There are 2 symbolic bytes represented by SSSS.
            assert isinstance(init_ctx['CALLDATA'], str), "Wrong type for CALLDATA initial context"

            # Parse the CALLDATA (divide the input string byte by byte)
            calldata_raw = init_ctx['CALLDATA'].replace("0x", '')
            calldata_bytes = [calldata_raw[i:i + 2] for i in range(0, len(calldata_raw), 2)]

            if "CALLDATASIZE" in init_ctx:
                self.calldata = LambdaMemory(tag=f"CALLDATA_{self.xid}", value_sort=BVSort(8), state=self)

                assert init_ctx["CALLDATASIZE"] >= len(calldata_bytes), "CALLDATASIZE is smaller than len(CALLDATA)"
            else:
                self.calldata = LambdaMemory(tag=f"CALLDATA_{self.xid}", value_sort=BVSort(8), state=self)

                # CALLDATASIZE is >= than the length of the provided CALLDATA bytes
                self.add_constraint(BV_UGE(self.calldatasize, BVV(len(calldata_bytes), 256)))

            for index, cb in enumerate(calldata_bytes):
                if cb == 'SS':
                    # special sequence for symbolic bytes
                    # log.debug(f"Storing symbolic byte at index {index} in CALLDATA")
                    self.calldata[BVV(index, 256)] = BVS(f'CALLDATA_BYTE_{index}', 8)
                else:
                    # log.debug("Initializing CALLDATA at {}".format(index))
                    self.calldata[BVV(index, 256)] = BVV(int(cb, 16), 8)
        else:
            self.calldata = LambdaMemory(tag=f"CALLDATA_{self.xid}", value_sort=BVSort(8), state=self)

        # make calldata read bvv(0) if reading past calldatasize
        # NOTE: too slow when symbolic, for now approximate with MAX_CALLDATA_SIZE
        # self.calldata.memsetinfinite(self.calldatasize, BVV(0, 8))
        # self.calldata.memsetinfinite(BVV(self.MAX_CALLDATA_SIZE, 256), BVV(0, 8))

        if "CALLER" in init_ctx:
            assert isinstance(init_ctx['CALLER'], str), "Wrong type for CALLER initial context"
            self.ctx["CALLER"] = BVV(int(init_ctx["CALLER"],16), 256)

        if "ORIGIN" in init_ctx:
            assert isinstance(init_ctx['ORIGIN'], str), "Wrong type for ORIGIN initial context"
            self.ctx["ORIGIN"] = BVV(int(init_ctx["ORIGIN"],16), 256)
        
        if "BALANCE" in init_ctx:
            assert isinstance(init_ctx['BALANCE'], int), "Wrong type for BALANCE initial context"
            self.add_constraint(Equal(self.start_balance, BVV(init_ctx['BALANCE'], 256)))
        
        if "ADDRESS" in init_ctx:
            assert isinstance(init_ctx['ADDRESS'], str), "Wrong type for ADDRESS initial context"
            self.ctx["ADDRESS"] = BVV(int(init_ctx["ADDRESS"],16), 256)

        if "NUMBER" in init_ctx:
            assert isinstance(init_ctx['NUMBER'], int), "Wrong type for NUMBER initial context"
            self.ctx["NUMBER"] = BVV(init_ctx["NUMBER"], 256)

        if "DIFFICULTY" in init_ctx:
            assert isinstance(init_ctx['DIFFICULTY'], int), "Wrong type for DIFFICULTY initial context"
            self.ctx["DIFFICULTY"] = BVV(init_ctx["DIFFICULTY"], 256)

        if "TIMESTAMP" in init_ctx:
            assert isinstance(init_ctx['TIMESTAMP'], int), "Wrong type for TIMESTAMP initial context"
            self.ctx["TIMESTAMP"] = BVV(init_ctx["TIMESTAMP"], 256)
        
        if "CALLVALUE" in init_ctx:
            assert isinstance(init_ctx['CALLVALUE'], int), "Wrong type for CALLVALUE initial context"
            self.ctx["CALLVALUE"] = BVV(init_ctx["CALLVALUE"], 256)

    @property
    def pc(self) -> str:
        return self._pc

    @property
    def curr_stmt(self):
        return self.project.factory.statement(self._pc)

    @property
    def constraints(self):
        return self.solver.constraints

    @pc.setter
    def pc(self, value: str):
        self._pc = value

    def set_next_pc(self):
        """
        This method sets the next pc to the state.
        Raises:
            VMNoSuccessors: If there are no successors
            VMUnexpectedSuccessors: If the successor does not match any of the expected successors
        """
        try:
            curr_bb = self.project.factory.block(self.curr_stmt.block_id)
            stmt_list_idx = curr_bb.statements.index(self.curr_stmt)
            remaining_stmts = curr_bb.statements[stmt_list_idx + 1:]
            if remaining_stmts:
                self.pc = remaining_stmts[0].id
            else:
                self.pc = self.get_fallthrough_pc()
        except VMNoSuccessors:
            self.halt = True
        except VMUnexpectedSuccessors:
            self.halt = True

    def get_fallthrough_pc(self):
        """
        This method returns the fallthrough pc of the current state
        """
        curr_bb = self.project.factory.block(self.curr_stmt.block_id)

        if len(curr_bb.succ) == 0:
            #  case 1: end of the block and no targets
            log.debug("Next stmt is NONE")
            raise VMNoSuccessors
        elif len(curr_bb.succ) == 1:
            #  case 2: end of the block and one target
            log.debug("Next stmt is {}".format(curr_bb.succ[0].first_ins.id))
            return curr_bb.succ[0].first_ins.id
        elif curr_bb.fallthrough_edge is None:
            raise VMNoSuccessors(f"Block {curr_bb} does not have a fallthrough edge.")
        else:
            #  case 3: end of the block and more than one target
            fallthrough_bb = curr_bb.fallthrough_edge
            log.debug("Next stmt is {}".format(fallthrough_bb.first_ins.id))
            return fallthrough_bb.first_ins.id

    def get_non_fallthrough_pc(self, destination_val):
        """
        This method returns the non fallthrough pc of the current state.
        """
        curr_bb = self.project.factory.block(self.curr_stmt.block_id)

        if not is_concrete(destination_val):
            raise VMSymbolicError(f'Symbolic jump destination currently not supported. ({destination_val=})')
        else:
            destination_val = hex(bv_unsigned_value(destination_val))

        # translation using TAC_OriginalStatement_Block
        candidate_destination_vals = self.project.tac_parser.statement_to_blocks_map[destination_val] + [destination_val]
        candidate_bbs = [bb for bb in curr_bb.succ if (bb.id in candidate_destination_vals) or ("0x"+bb.id.split("0x")[1] in candidate_destination_vals)]

        if len(candidate_bbs) == 0:
            raise VMSymbolicError(f'Unable to find jump destination. ({candidate_destination_vals=}, {curr_bb.succ=})')
        elif len(candidate_bbs) > 1:
            raise VMSymbolicError(f'Multiple jump destinations. ({candidate_destination_vals=}, {curr_bb.succ=})')

        non_fallthrough_bb = candidate_bbs[0]

        log.debug("Next stmt is {}".format(non_fallthrough_bb.first_ins.id))
        return non_fallthrough_bb.first_ins.id
    
    def add_constraint(self, constraint):
        """
        This method adds a constraint to the state.
        """
        # Here you can inspect the constraints being added to the state.
        if opt.STATE_STOP_AT_ADDCONSTRAINT in self.options:
            import ipdb; ipdb.set_trace()
        self.solver.add_path_constraint(constraint)

    # Add here any default plugin that we want to ship
    # with a fresh state.
    def _register_default_plugins(self):
        """
        This method registers the default plugins to the state.
        """
        self.register_plugin("solver", SimStateSolver())
        self.register_plugin("globals", SimStateGlobals())
        
        sha_resolver = ShaResolver() 
        self.register_plugin("sha_resolver",sha_resolver)
        sha_resolver.set_state(self)

        if opt.STATE_INSPECT:
            self.register_plugin("inspect", SimStateInspect())

    def register_plugin(self, name: str, plugin: SimStatePlugin):
        """
        This method registers a plugin to the state.
        """
        self.active_plugins[name] = plugin
        setattr(self, name, plugin)
        plugin.set_state(self)
        return plugin

    def copy(self):
        """
        Deep copy of the SimState.
        """
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

        new_state.sha_observed = [sha.copy(new_state=new_state) for sha in self.sha_observed]
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
        """
        This method resets the state.
        """
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
        self.returndata = {'size': BVV(0, 256), 'instruction_count': BVV(0, 256)}
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
