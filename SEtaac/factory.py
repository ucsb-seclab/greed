import logging

from SEtaac.block import Block
from SEtaac.simulation_manager import SimulationManager
from SEtaac.state import SymbolicEVMState


log = logging.getLogger(__name__)


class Factory:
    def __init__(self, project: "Project"):
        self.project = project

    def simgr(self, entry_state: SymbolicEVMState) -> SimulationManager:
        return SimulationManager(entry_state=entry_state)

    def entry_state(self, xid: str, ctx:dict) -> SymbolicEVMState:
        state = SymbolicEVMState(xid=xid, project=self.project, ctx=ctx)
        state.pc = self.block('0x0').first_ins.id
        return state

    def function(self, function_id: str) -> "TAC_Function":
        return self.project.function_at.get(function_id, None)

    def block(self, block_id: str) -> Block:
        return self.project.block_at.get(block_id, None)

    def statement(self, stmt_id: str) -> Block:
        return self.project.statement_at.get(stmt_id, None)
