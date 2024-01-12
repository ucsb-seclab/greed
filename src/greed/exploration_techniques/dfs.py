from . import ExplorationTechnique


class DFS(ExplorationTechnique):
    """
    This Exploration technique implements a Classic Depth-First Search exploration
    Args:
        deferred_stash: the name of the stash where deferred states are put
    """
    def __init__(self, deferred_stash='deferred'):
        super(DFS, self).__init__()
        self.deferred_stash = deferred_stash

    def setup(self, simgr):
        """
        Setup the technique.
        Args:
            simgr: the simulation manager
        """
        if self.deferred_stash not in simgr.stashes:
            simgr.stashes[self.deferred_stash] = []

    def check_stashes(self, simgr, stashes, stash='active'):
        """
        If multiple states are in the active stash, move all but the oldest to the deferred stash.
        Args:
            simgr: the simulation manager
            stashes: the stashes
            stash: the name of the stash to check
        """
        if len(stashes[stash]) > 1:
            # Pick the oldest state
            keep = sorted(stashes[stash], key=lambda s: s.uuid)[0]
            # Move everything else to the deferred stash
            simgr.move(from_stash=stash, to_stash=self.deferred_stash, filter_func=lambda s: s != keep)
        elif len(stashes[stash]) == 0:
            # We are out of active. Do we have any deferred?
            if len(stashes[self.deferred_stash]) > 0:
                # Add last deferred to the active queue
                stashes[stash].append(stashes[self.deferred_stash].pop())

        return stashes

    def is_complete(self, simgr, stash='active'):
        """
        Check if the exploration is complete: there are no active states, and no deferred states.
        Args:
            simgr: the simulation manager
            stash: the name of the stash to check
        """
        # We are done if there are no active, or, no deferred.
        if len(simgr.stashes[stash]) == 0 and len(simgr.stashes[self.deferred_stash]) == 0:
            return True
        else:
            return False
