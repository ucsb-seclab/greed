

class ExplorationTechnique:

    # Any operations that needs to be done
    # on the simulation manager before starting 
    # the exploration with this technique.
    def setup(self, simgr):
        return

    # This method receives the current active 
    # stashes that can be manipulated/re-ordered
    # etc... 
    # This MUST return the stashes.
    def check_stashes(self, stashes):
        return stashes

    # This method receives the state 
    # we are going to generate the 
    # successors for.
    # This MUST return the state.
    def check_state(self, state):
        return state

    # This method receives all the successors
    # generated from a step of a state.
    # This MUST return the successors.
    def check_successors(self, successors):
        return successors


from .simgrviz import SimgrViz
from .dfs import DFS