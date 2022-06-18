import logging
import sys
from datetime import datetime

import dill

from SEtaac.TAC.TAC_parser import TACparser
from SEtaac.cfg import TAC_Block, make_cfg
from SEtaac.config import *
from SEtaac.function import TAC_Function
from SEtaac.simulation_manager import SimulationManager
from SEtaac.state import SymbolicEVMState

l = logging.getLogger("project")
l.setLevel(logging.INFO)

class Project(object):
    def __init__(self, binary:str="", cfg_data:str="", onchain_address:str=""):
        
        if binary == "" or cfg_data == "":
            l.fatal("Need gigahorse artifacts to create a project (IR_DICT and TAC_CFG)")
            sys.exit(0)

        # Load the TAC IR from the file dumped with gigahorse
        with open(binary, "rb") as bin_file:
            self.TAC_code_raw = dill.load(bin_file)

        # Load the TAC CFG exported by Gigahorse client
        with open(cfg_data, "rb") as cfgdata_file:
            self.TAC_cfg_raw = dill.load(cfgdata_file)

        self._statement_at = dict()

        # Object that creates other objects
        self.factory = FactoryObjects(TACparser(self.TAC_code_raw), project=self)
        self.functions = self._import_functions_gigahorse()
        for func in self.functions.values():
            make_cfg(self.factory, self.TAC_cfg_raw, func)


        # import the web3 provider just in case (from config)
        self.web3 = w3 
        self.onchain_address = onchain_address

        if self.onchain_address != '':
            # if we have an address let's use it as the name of the folder
            self._workspace_folder = os.path.join(WORKSPACE, self.onchain_address)
        else:
            # otherwise, let's use a random 12 chars strings
            self._workspace_folder = os.path.join(WORKSPACE, "project_" + datetime.now().strftime("%d/%m/%Y %H:%M:%S"))

        # Check whether the specified path exists or not and create the workspace for this project
        isExist = os.path.exists(self._workspace_folder)
        if not isExist:
            os.makedirs(self._workspace_folder)
    
    def _import_functions_gigahorse(self):
        funcs = {}
        for _, func_data in self.TAC_cfg_raw['functions'].items():
            # Just to make sure there are no collision on function addresses
            assert(not funcs.get(func_data["addr"], None))
            tac_blocks = []
            for block_addr in func_data['blocks']:
                bb_obj = self.factory.block(block_addr)
                if bb_obj:
                    tac_blocks.append(bb_obj) 

            funcs[func_data["addr"]] = TAC_Function(func_data["addr"], func_data["name"], func_data["is_public"], 
                                                    tac_blocks, func_data['arguments'])

            # Set the function object to the blocks
            # to be able to go back later  
            for tac_block in tac_blocks:
                tac_block.function = funcs[func_data["addr"]]
                self._statement_at.update(tac_block._statement_at)

        self._statement_at['fake_exit'] = self.factory.TAC_parser._fake_exit_stmt
        return funcs
    
    #@property
    #def cfg(self):
    #    if not self._cfg:
    #        self._cfg = CFG()
    #    return self._cfg

# This class create object like the simgr, entry_state, etc...
class FactoryObjects:
    def __init__(self, TAC_parser:TACparser, project):
        self.TAC_parser = TAC_parser
        self.project = project
        
    def simgr(self, entry_state:SymbolicEVMState) -> SimulationManager:
        return SimulationManager(entry_state=entry_state)
    
    def entry_state(self, xid:str) -> SymbolicEVMState:
        state = SymbolicEVMState(xid=xid, project=self.project)
        state.pc = self.block('0x0').first_ins.stmt_ident
        return state
    
    def block(self, block_id:str) -> TAC_Block:
        return self.TAC_parser.parse(block_id)
    
    # def statement(self, stmt_id:str):
    #     return self.TAC_parser.parse_stmt(stmt_id)