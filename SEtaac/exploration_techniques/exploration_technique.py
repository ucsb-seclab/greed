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
    def check_stashes(self, simgr, stashes):
        return stashes

    # This method receives the state 
    # we are going to generate the 
    # successors for.
    # This MUST return the state.
    def check_state(self, simgr, state):
        return state

    # This method receives all the successors
    # generated from a step of a state.
    # This MUST return the successors.
    def check_successors(self, simgr, successors):
        return successors
    
    # This method indicate when the ET is done.
    # If you just want to be done when there are no
    # active states, just return True.
    def is_complete(self, simgr):
        return True
