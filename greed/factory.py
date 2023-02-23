import logging

from greed.block import Block
from greed.sim_manager import SimulationManager
from greed.state import SymbolicEVMState


log = logging.getLogger(__name__)


class Factory:
    def __init__(self, project: "Project"):
        self.project = project

    def simgr(self, entry_state: SymbolicEVMState) -> SimulationManager:
        return SimulationManager(entry_state=entry_state, project=self.project)

    def entry_state(self, xid: str, init_ctx: dict = None, options: dict = None, max_calldatasize: int = None, partial_concrete_storage: bool = False) -> SymbolicEVMState:
        state = SymbolicEVMState(xid=xid, project=self.project, init_ctx=init_ctx, options=options, max_calldatasize=max_calldatasize, partial_concrete_storage=partial_concrete_storage)
        state.pc = self.block('0x0').first_ins.id
        return state

    def function(self, function_id: str) -> "TAC_Function":
        return self.project.function_at.get(function_id, None)

    def block(self, block_id: str) -> Block:
        return self.project.block_at.get(block_id, None)

    def statement(self, stmt_id: str) -> "TAC_Statement":
        return self.project.statement_at.get(stmt_id, None)
