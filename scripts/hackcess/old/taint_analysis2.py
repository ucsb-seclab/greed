import random

from . import ExplorationTechnique


class CalldataTaintAnalysis(ExplorationTechnique):

    def __init__(self, state, taint_begins:int, taint_size:int):
        super(TaintAnalysis, self).__init__()
        
        self.state = state 
        self.taint_begins = taint_begins
        self.taint_size = taint_size

        # Constraints that we need to add if we want to have 
        # a concrete memory layout that matches our taint
        self.extra_constraints = []

        self.tainted_registers = []

    def setup(self, simgr):
        return

    def check_state(self, simgr, state):
        return state
    
    def check_successors(self, simgr, successors):
        for succ in successors:
            prev_stmt = succ.trace[-1]
            if prev_stmt.__internal_name__ == "CALLDATACOPY":
                
        return successors

    def is_complete(self, simgr, stash='active'):
        return True
