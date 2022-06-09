import os 
import datetime
import dill

from SEtaac.cfg import CFG
from SEtaac.simulation_manager import SimulationManager
from SEtaac.TAC_parser import TACparser
from SEtaac.state import SymbolicEVMState
from config import *

class Project(object):
    def __init__(self, binary, onchain_address=""):
        
        # Load the TAC IR from the file dumped with gigahorse
        with open(binary, "rb") as bin_file:
            self.TAC_code = dill.load(bin_file)
        
        # Object that creates other objects
        self.factory = FactoryObjects()
        self.TAC_parser = TACparser(self.TAC_code)
        self.cfg = None
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

    @property
    def cfg(self):
        if not self._cfg:
            self._cfg = CFG()
        return self._cfg

# This class create object like the simgr, entry_state, etc...
class FactoryObjects:
    def __init__(self):
        pass
    def simgr(self):
        return SimulationManager()
    
    def entry_state(self):
        return SymbolicEVMState()