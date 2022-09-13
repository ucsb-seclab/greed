import logging
import networkx as nx

from . import ExplorationTechnique

log = logging.getLogger(__name__)

class TraceExplore(ExplorationTechnique):
    """
    This technique follows a specifc trace collected statically.
    For the loops, as soon as we can get out, we'll just follow that 
    state, otherwise we'll follow the loop unless the generated state is 
    out of the collected trace (divergence). We save a checkpoint state
    whenever we can get 
    """
    def __init__(self, backward_slice, deferred_stash='te_deferred'):
        super(TraceExplore, self).__init__()

        # bslice is a list of tuple (block_id, distance_to_target_block)
        self.backward_slice = backward_slice
        # Here we put the states that were not descendent in score, but that were 
        # valid (e.g., looping states)
        self.deferred_stash = deferred_stash

        # For every block, keep its score in a dict using 
        # the block_id as key.
        self.block_to_score = {}
        for block in self.backward_slice:
            self.block_to_score[block[0].id] = block[1]

    def check_state(self, simgr, state):
        # NOTE: is this safe?
        state.globals['curr_distance'] = self.block_to_score[state.curr_stmt.block_id]
        
    def setup(self, simgr):
        if self.deferred_stash not in simgr.stashes:
            simgr.stashes[self.deferred_stash] = []
        
    def check_successors(self, simgr, successors):
        # List of valid SimState (not divergent)
        valid_successors = []
        
        # List of successors we want to progress 
        new_successors = []

        for succ in successors:
            if succ.curr_stmt.block_id in self.block_to_score.keys():
                valid_successors.append(succ)
            else:
                import ipdb; ipdb.set_trace()
                log.info(f'Diverging state {succ} being dropped')
                # If we are diverging, don't consider this state.
                continue
        
        assert(len(valid_successors) != 0)

        # Get the min distance across all the valid_successors
        min_distance = min([s.globals['curr_distance'] for s in valid_successors])

        # Get the successors that have the minimal distance ( we want to keep these )
        new_successors = list(filter(lambda x: (x.globals['curr_distance'] == min_distance), valid_successors))

        # Move the successors with greater distance to the te_deferred stash
        simgr.move(from_stash="active", to_stash=self.deferred_stash, filter_func=lambda s: s.globals['curr_distance'] != min_distance)

        return new_successors

            
            

