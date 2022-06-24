import dill
import itertools
import logging
import sys
from datetime import datetime

from SEtaac.cfg import TAC_Block
from SEtaac.TAC.TAC_parser import TACparser
from SEtaac.simulation_manager import SimulationManager
from SEtaac.state import SymbolicEVMState

log = logging.getLogger(__name__)


class Project(object):
    def __init__(self, target_dir: str):
        # Load the contract code
        with open(f"{target_dir}/contract.hex", "rb") as contract_file:
            self.code = contract_file.read()

        self.factory = Factory(project=self)

        tac_parser = TACparser(self.factory, target_dir)
        self.statement_at = tac_parser.parse_statements()
        self.block_at = tac_parser.parse_blocks()
        self.function_at = tac_parser.parse_functions()


class Factory:
    """
    Create objects like the simgr, entry_state, etc...
    """
    def __init__(self, project: Project):
        self.project = project

    def simgr(self, entry_state: SymbolicEVMState) -> SimulationManager:
        return SimulationManager(entry_state=entry_state)

    def entry_state(self, xid: str) -> SymbolicEVMState:
        state = SymbolicEVMState(xid=xid, project=self.project)
        state.pc = self.block('0x0').first_ins.id
        return state

    def function(self, function_id: str) -> TAC_Block:
        return self.project.function_at.get(function_id, None)

    def block(self, block_id: str) -> TAC_Block:
        return self.project.block_at.get(block_id, None)

    def statement(self, stmt_id: str) -> TAC_Block:
        return self.project.statement_at.get(stmt_id, None)
