import logging
import networkx as nx

from . import ExplorationTechnique

log = logging.getLogger(__name__)

class DirectedSearch(ExplorationTechnique):
    """
    This technique prunes all states that cannot reach the block of a specified target statement.

    Possibly more effective when combined with DFS if only one path is needed:

    directed_search = DirectedSearch(target_stmt)
    simgr.use_technique(directed_search)

    dfs = DFS()
    simgr.use_technique(dfs)

    simgr.run(find=lambda s: s.curr_stmt.id == target_stmt_id)
    """
    def __init__(self, target_stmt, pruned_stash='pruned'):
        super(DirectedSearch, self).__init__()
        self._target_stmt = target_stmt
        self._target_block = None
        self.pruned_stash = pruned_stash

    def setup(self, simgr):
        self._target_block = simgr.project.factory.block(self._target_stmt.block_id)

    def check_successors(self, simgr, successors):
        new_successors = []
        pruned_cnt = 0
        for succ in successors:
            if self._is_reachable(succ, self._target_block, simgr.project.factory, simgr.project.callgraph):
                new_successors.append(succ)
            else:
                pruned_cnt += 1
                simgr.stashes[self.pruned_stash].append(succ)
        if pruned_cnt == len(successors):
            log.warning(f"Pruned all the successors! [{pruned_cnt}/{len(successors)}]")
        elif pruned_cnt != 0:
            log.warning(f"Pruned {pruned_cnt}/{len(successors)} successors")
        return new_successors

    # Check if the current state can reach 'block_b'
    def _is_reachable(self, state_a, block_b, factory, callgraph):
        block_a = factory.block(state_a.curr_stmt.block_id)
        if self._is_reachable_without_returns(block_a, block_b, factory, callgraph):
            # this is the simple case, no need to look at the callstack
            return True
        elif not state_a.callstack:
            # not reachable without returns, but the callstack is empty
            return False
        else:
            # otherwise we can look at the callstack
            callstack = list(state_a.callstack)
            while callstack:
                return_stmt_id, _ = callstack.pop()
                return_stmt = factory.statement(return_stmt_id)
                return_block = factory.block(return_stmt.block_id)

                # check if any RETURNPRIVATE is reachable
                for returnprivate_block_id in block_a.function.returnprivate_block_ids:
                    returnprivate_block = factory.block(returnprivate_block_id)
                    if self._is_reachable_without_returns(block_a, returnprivate_block, factory, callgraph):
                        break
                else:
                    # executed if there is no break
                    return False

                if self._is_reachable_without_returns(return_block, block_b, factory, callgraph):
                    return True
            return False

    # Check if 'block_a' can reach 'block_b'
    def _is_reachable_without_returns(self, block_a, block_b, factory, callgraph):
        function_a = block_a.function
        function_b = block_b.function
        if block_a == block_b:
            return True
        elif function_a == function_b:
            # check if reachable in intra-procedural cfg
            return block_b in block_a.descendants
        elif function_a and function_b:
            # for each path (in the callgraph) from function_a to function_b
            callgraph_paths = nx.all_simple_paths(callgraph, function_a, function_b)
            for path in callgraph_paths:
                first_call_target = path[1]
                # check if we can reach the first call (i.e., any "CALLPRIVATE <first_call_target>" in function_a)
                for callprivate_block_id in function_a.callprivate_target_sources[first_call_target.id]:
                    callprivate_block = factory.block(callprivate_block_id)
                    return self._is_reachable_without_returns(block_a, callprivate_block, factory, callgraph)
        else:
            return False
