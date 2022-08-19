
import logging 

from enum import Enum
from SEtaac import options
from SEtaac.utils.solver import Solver
from SEtaac.state_plugins import SimStatePlugin

log = logging.getLogger(__name__)

#
# This plugin stores constraints 
# in a layered way, keeping track 
# of constraints added at different frames.
# e.g.,
# self._path_constraints[0] = {eq,eq,bve}
# push()
# self._path_constraints[0] = {eq,eq,bve}
# self._path_constraints[1] = {add,add}
#
class SimStateConstraints(SimStatePlugin):
    def __init__(self):
        super(SimStateConstraints, self).__init__()
        
        self._path_constraints = dict{}
        self._memory_constraints = dict{}

        '''
        If we want to keep memory constraints separate 
        we can think to use this later
        self._memory_constraints["memory"] = dict{}
        self._memory_constraints["storage"] = dict{}
        self._memory_constraints["sha3"] = dict{}
        self._memory_constraints["calldata"] = dict{}
        '''

    # returns path constraints
    # If frame is None, returns ALL the currently active constraints,
    # otherwise, just return the constraints at a specific frame.
    def path_constraints(self, frame=None):
        return
    
    def memory_constraints(self, frame=None):
        return
    
    # clean a specific frame
    def clean_constraints_at(self, frame=None):
        return
    
    # returns ALL the active constraints in all the stashes
    def constraints(self):
        return

    # returns ALL the active constraints in all the stashes 
    # at a specific frame
    def constraints_at(self):
        return

    
