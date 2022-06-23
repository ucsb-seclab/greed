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

        # Load the contract code
        with open(f"{target_dir}/contract.hex", "rb") as contract_file:
            self.code = contract_file.read()

        self._statement_at = dict()

        # Object that creates other objects
        self.factory = FactoryObjects(TACparser(self.TAC_code_raw), project=self)
        self.functions = self._import_functions_gigahorse()

        # build phi-map (as in gigahorse's decompiler)
        phimap = dict()
        for stmt in self._statement_at.values():
            if stmt.__internal_name__ != 'PHI':
                continue
            for v in stmt.arg_vars:
                if v in phimap:
                    phimap[stmt.res1_var] = phimap[v]
                    continue
                phimap[v] = stmt.res1_var

        # propagate phi map
        fixpoint = False
        while not fixpoint:
            fixpoint = True
            for v_old, v_new in phimap.items():
                if v_new in phimap:
                    phimap[v_old] = phimap[v_new]
                    fixpoint = False

        # rewrite statements
        for stmt in self._statement_at.values():
            if stmt.__internal_name__ == "PHI":
                stmt.num_args = 0
                stmt.num_ress = 0
                stmt.arg_vars = []
                stmt.res_vars = []
                stmt.__internal_name__ = "PHI (NOP)"
            stmt.arg_vars = [v if v not in phimap else phimap[v] for v in stmt.arg_vars]
            stmt.arg_vals = {v if v not in phimap else phimap[v]: val for v, val in stmt.arg_vals.items()}
            stmt.res_vars = [v if v not in phimap else phimap[v] for v in stmt.res_vars]
            stmt.res_vals = {v if v not in phimap else phimap[v]: val for v, val in stmt.res_vals.items()}

            # re-process args
            stmt.process_args()

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

                fallthrough_edge_ident = self.TAC_cfg_raw['fallthrough_edge'][tac_block.ident]
                tac_block.fallthrough_edge = self.factory.block(fallthrough_edge_ident)

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

    def entry_state(self, xid: str,
                    storage=None, start_balance=None,
                    constraints=None, sha_constraints=None) -> SymbolicEVMState:
        state = SymbolicEVMState(xid=xid, project=self.project,
                                 storage=storage, start_balance=start_balance,
                                 constraints=constraints, sha_constraints=sha_constraints)
        state.pc = self.block('0x0').first_ins.stmt_ident
        return state

    def block(self, block_id: str) -> TAC_Block:
        return self.TAC_parser.parse(block_id)
