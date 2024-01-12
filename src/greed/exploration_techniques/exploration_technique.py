class ExplorationTechnique:
    """
    Base Exploration Technique

    ALL THE STANDARD METHODS ARE NOT SUPPOSED TO BE CALLED MANUALLY
    """
    def setup(self, simgr):
        """
        Any operations that needs to be done on the simulation manager before starting
        the exploration with this technique.

        Args:
            simgr: Simulation Manager

        Returns: None

        """
        return

    def check_stashes(self, simgr, stashes):
        """
        This method receives the current active stashes that can be manipulated/re-ordered/etc...
        MUST return the stashes.

        Args:
            simgr: Simulation Manager
            stashes: All the active stashes

        Returns: MUST return the stashes.

        """
        return stashes

    def check_state(self, simgr, state):
        """
        This method receives the state that we are going to generate the successors for.
        MUST return the state.

        Args:
            simgr: Simulation Manager
            state: State that we are going to generate the successors for

        Returns: MUST return the state.

        """
        return state

    def check_successors(self, simgr, successors):
        """
        This method receives all the successors generated from a step of a state.
        MUST return the successors.

        Args:
            simgr: Simulation Manager
            successors: All the successors generated from a step of a state

        Returns: MUST return the filtered successors

        """
        return successors

    def is_complete(self, simgr):
        """
        This method indicate when the ET is done.
        If you just want to be done when there are no active states, just return True.

        Args:
            simgr: Simulation Manager

        Returns: Completion state

        """
        return True
