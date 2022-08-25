import random

from . import ExplorationTechnique


class DFS(ExplorationTechnique):
    """
    This Exploration technique implements a Classic Depth-First Search exploration
    """
    def __init__(self, deferred_stash='deferred'):
        super(DFS, self).__init__()
        self._random = random.Random()
        self._random.seed(10)
        self.deferred_stash = deferred_stash

    def setup(self, simgr):
        if self.deferred_stash not in simgr.stashes:
            simgr.stashes[self.deferred_stash] = []

    def check_stashes(self, simgr, stashes, stash='active'):
        # If we have more than one active, let's just pick
        # one randomly and step it.
        if len(stashes[stash]) > 1:
            # Pick the last after the shuffling
            keep = self._random.choice(stashes[stash])
            # Move everything else to the deferred
            simgr.move(from_stash=stash, to_stash=self.deferred_stash, filter_func=lambda s: s != keep)
            # Re-define the active stash
            stashes[stash] = [keep]

        # Ok, we are out of active
        if len(stashes[stash]) == 0:
            # Do we have any deferred?
            if len(stashes[self.deferred_stash]) == 0:
                return stashes
            # Add last deferred to the active queue
            stashes[stash].append(stashes[self.deferred_stash].pop())

        return stashes

    def is_complete(self, simgr, stash='active'):
        # We are done if there are no active, or, no deferred.
        if len(simgr.stashes[stash]) == 0 and len(simgr.stashes[self.deferred_stash]) == 0:
            return True
        else:
            return False
