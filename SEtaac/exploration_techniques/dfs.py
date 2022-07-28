
import hashlib
import logging
import networkx
import random

from typing import Callable
from SEtaac.state import SymbolicEVMState
from . import ExplorationTechnique


class DFS(ExplorationTechnique):
    def __init__(self, deferred_stash='deferred'):
        super(DFS,self).__init__()
        self._random = random.Random()
        self._random.seed(10)
        self.deferred_stash = deferred_stash

    def setup(self, simgr):
        if self.deferred_stash not in simgr._stashes:
            simgr._stashes[self.deferred_stash] = []

    def check_stashes(self, stashes, stash='active'):
        # If we have more than one active, let's just pick
        # one randomly and step it.
        if len(stashes[stash]) > 1:
            self._random.shuffle(stashes[stash])
            # Pick the last after the shuffling
            keep = stashes[stash].pop()
            # Move everything else to the deferred
            self._move(stashes[stash],stashes[self.deferred_stash])
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

    def check_state(self, state):
        return state

    def check_successors(self, successors):
        return successors

    def is_complete(self,simgr, stash='active'):
        # We are done if there are no active, or, no deferred.
        if len(simgr._stashes[stash]) == 0 and len(simgr._stashes[self.deferred_stash]) == 0:
            return True
        else:
            return False

    def _move(self, from_stash: str, to_stash: str, filter_func: Callable[[SymbolicEVMState], bool] = lambda s: True):
        for s in from_stash:
            if filter_func(s):
                from_stash.remove(s)
                to_stash.append(s)