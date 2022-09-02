import logging

from . import ExplorationTechnique

log = logging.getLogger(__name__)


class Prioritizer(ExplorationTechnique):
    """
    This Exploration technique implements a Classic Depth-First Search exploration
    """
    def __init__(self, scoring_function, deferred_stash='deferred'):
        super(Prioritizer, self).__init__()
        self.deferred_stash = deferred_stash

        # Will prioritize HIGHER scores (e.g., need to map distance --> -distance)
        self.scoring_function = scoring_function

    def setup(self, simgr):
        if self.deferred_stash not in simgr.stashes:
            simgr.stashes[self.deferred_stash] = []

    def check_stashes(self, simgr, stashes, stash='active'):
        if len(stashes[stash]) > 1:
            # LOCAL PRIORITIZATION: THIS PRIORITIZES ONLY AMONG THE SUCCESSORS
            keep = sorted(stashes[stash], key=self.scoring_function, reverse=True)[0]
            # Move everything else to the deferred stash
            simgr.move(from_stash=stash, to_stash=self.deferred_stash, filter_func=lambda s: s != keep)

            log.debug(f'prioritized: {keep}, {self.scoring_function(keep)}')
        elif len(stashes[stash]) == 0:
            # We are out of active. Do we have any deferred?
            if len(stashes[self.deferred_stash]) > 0:
                # GLOBAL PRIORITIZATION: THIS PRIORITIZES AMONG ALL STATES
                # simgr.move(from_stash=stash, to_stash=self.deferred_stash)
                prioritized = sorted(stashes[self.deferred_stash], key=self.scoring_function, reverse=True)[0]
                stashes[stash] = [prioritized]
                stashes[self.deferred_stash].remove(prioritized)

                # for s in simgr.stashes[self.deferred_stash]:
                #     print(s, self.scoring_function(s))

                log.debug(f'prioritized: {prioritized}, {self.scoring_function(prioritized)}')

        return stashes

    def is_complete(self, simgr, stash='active'):
        # We are done if there are no active, or, no deferred.
        if len(simgr.stashes[stash]) == 0 and len(simgr.stashes[self.deferred_stash]) == 0:
            return True
        else:
            return False
