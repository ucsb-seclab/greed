import random

from SEtaac.exploration_techniques.exploration_techniques import ExplorationTechnique

class TaintAnalysis(ExplorationTechnique):
    def __init__(self):
        super(TaintAnalysis, self).__init__()

    def setup(self, simgr):
        return
    
    def check_state(self, simgr, state):
        if state.curr_stmt.__internal_name__ in state.taints.keys():
            self.state.globals['check_taints'] = True
        return state
    
    def check_successors(self, simgr, successors):
        for succ in successors:
            if succ.globals.get('check_taints', None) == True:
                succ.globals.check_taints = False
                succ.taint.
        return successors 