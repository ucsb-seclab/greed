import dill
import logging
import sys
from datetime import datetime

from SEtaac.TAC.TAC_parser import TACparser
from SEtaac.cfg import TAC_Block
from SEtaac.function import TAC_Function
from SEtaac.simulation_manager import SimulationManager
from SEtaac.state import SymbolicEVMState

log = logging.getLogger(__name__)


class Project(object):
    def __init__(self, target_dir : str):
        # Load the TAC IR from the file dumped with gigahorse
        with open(f"{target_dir}/IR_DICT.dill", "rb") as tac_file:
            self.TAC_code_raw = dill.load(tac_file)

        # Load the TAC CFG exported by Gigahorse client
        with open(f"{target_dir}/TAC_CFG.dill", "rb") as cfgdata_file:
            self.TAC_cfg_raw = dill.load(cfgdata_file)

        self._statement_at = dict()

        # Object that creates other objects
        self.factory = FactoryObjects(TACparser(self.TAC_code_raw), project=self)
        self.functions = self._import_functions_gigahorse()

    def _import_functions_gigahorse(self):
        funcs = {}
        for _, func_data in self.TAC_cfg_raw['functions'].items():
            # Just to make sure there are no collision on function addresses
            assert (not funcs.get(func_data["addr"], None))
            tac_blocks = []
            for block_addr in func_data['blocks']:
                bb_obj = self.factory.block(block_addr)
                if bb_obj:
                    tac_blocks.append(bb_obj)

            function = TAC_Function(func_data["addr"], func_data["name"], func_data["is_public"],
                                    tac_blocks, func_data['arguments'])
            funcs[func_data["addr"]] = function

            # Set the function object to the blocks to be able to go back later
            for tac_block in tac_blocks:
                tac_block.function = funcs[func_data["addr"]]
                self._statement_at.update(tac_block._statement_at)

            function.make_cfg(self.factory, self.TAC_cfg_raw)

        self._statement_at['fake_exit'] = self.factory.TAC_parser._fake_exit_stmt
        return funcs


class FactoryObjects:
    """
    Create objects like the simgr, entry_state, etc...
    """
    def __init__(self, TAC_parser: TACparser, project):
        self.TAC_parser = TAC_parser
        self.project = project

    def simgr(self, entry_state: SymbolicEVMState) -> SimulationManager:
        return SimulationManager(entry_state=entry_state)

    def entry_state(self, xid: str) -> SymbolicEVMState:
        state = SymbolicEVMState(xid=xid, project=self.project)
        state.pc = self.block('0x0').first_ins.stmt_ident
        return state

    def block(self, block_id: str) -> TAC_Block:
        return self.TAC_parser.parse(block_id)
