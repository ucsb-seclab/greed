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

        for s in simgr.states:
            s.globals['directed_search_distance'] = None

    def check_successors(self, simgr, successors):
        new_successors = []
        pruned_cnt = 0
        for succ in successors:
            reachable, dist = self._is_reachable(succ, self._target_block, simgr.project.factory, simgr.project.callgraph)
            succ.globals['directed_search_distance'] = dist
            if reachable:
                new_successors.append(succ)
            else:
                pruned_cnt += 1
                simgr.stashes[self.pruned_stash].append(succ)
        if pruned_cnt > 0 and pruned_cnt == len(successors):
            log.fatal(f"DirectedSearch pruned all the successors! [{pruned_cnt}/{len(successors)}]")
        elif pruned_cnt != 0:
            log.debug(f"Pruned {pruned_cnt}/{len(successors)} successors")
        return new_successors

    # Check if the current state can reach 'block_b'
    def _is_reachable(self, state_a, block_b, factory, callgraph):
        block_a = factory.block(state_a.curr_stmt.block_id)
        reachable, dist = self._is_reachable_without_returns(block_a, block_b, factory, callgraph)
        if reachable:
            # this is the simple case, no need to look at the callstack
            log.debug(f"{state_a} -> {block_b} reachable without returns")
            return True, dist
        elif not state_a.callstack:
            # not reachable without returns, but the callstack is empty
            log.debug(f"[PRUNED] {state_a} -> {block_b} not reachable without returns and callstack is empty")
            return False, None
        else:
            # otherwise we can look at the callstack
            for _, saved_return_pc, _ in state_a.callstack:
                saved_return_stmt = factory.statement(saved_return_pc)
                saved_return_block = factory.block(saved_return_stmt.block_id)

                # check if any RETURNPRIVATE is reachable
                for returnprivate_block_id in block_a.function.returnprivate_block_ids:
                    returnprivate_block = factory.block(returnprivate_block_id)
                    reachable, dist1 = self._is_reachable_without_returns(block_a, returnprivate_block, factory, callgraph)
                    if reachable:
                        break
                else:
                    # executed if there is no break
                    return False, None

                reachable, dist2 = self._is_reachable_without_returns(saved_return_block, block_b, factory, callgraph)
                if reachable:
                    log.debug(f"{state_a} -> {block_b} reachable with returns")
                    return True, dist1 + dist2
            log.debug(f"[PRUNED] {state_a} -> {block_b} not reachable with returns")
            return False, None

    # Check if 'block_a' can reach 'block_b'
    @staticmethod
    def _is_reachable_without_returns(block_a, block_b, factory, callgraph):
        function_a = block_a.function
        function_b = block_b.function
        if block_a == block_b:
            return True, 1
        elif function_a == function_b:
            # check if reachable in intra-procedural cfg
            reachable = block_b in block_a.descendants
            dist = len(nx.bidirectional_shortest_path(block_a.cfg.graph, block_a, block_b)) if reachable else None
            return reachable, dist
        elif function_a and function_b:
            # for each path (in the callgraph) from function_a to function_b
            callgraph_paths = nx.all_simple_paths(callgraph, function_a, function_b)
            dist_candidates_for_path = list()
            for path in sorted(callgraph_paths, key=lambda p: len(p)):
                total_dist = 0

                # check if we can reach the first call (i.e., any "CALLPRIVATE <first_call_target>" in function_a)
                dist_candidates_for_step = list()
                first_call_target = path[1]

                # check callprivates for first step (function_a -> first_call_target)
                # NOTE: the first step is different because we are not stepping from the root, but from block_a
                for callprivate_block_id in function_a.callprivate_target_sources[first_call_target.id]:
                    callprivate_block = factory.block(callprivate_block_id)
                    reachable, dist = DirectedSearch._is_reachable_without_returns(block_a, callprivate_block, factory,
                                                                                   callgraph)
                    if reachable is True:
                        dist_candidates_for_step.append(dist)

                if dist_candidates_for_step:
                    # at least one reachable callprivate
                    total_dist += min(dist_candidates_for_step)
                else:
                    # no reachable callprivate
                    continue

                # approximate shortest path in the callgraph
                for a, b in zip(path[1:-1], path[2:]):
                    dist_candidates_for_step = list()
                    for callprivate_block_id in a.callprivate_target_sources[b.id]:
                        callprivate_block = factory.block(callprivate_block_id)
                        dist = len(nx.bidirectional_shortest_path(a.cfg.graph, a.cfg.root, callprivate_block))
                        dist_candidates_for_step.append(dist)
                    if dist_candidates_for_step:
                        total_dist += min(dist_candidates_for_step)
                    else:
                        continue

                # print([f.id for f in path], total_dist)
                dist_candidates_for_path.append(total_dist)

            if dist_candidates_for_path:
                return True, min(dist_candidates_for_path)
            else:
                return False, None


        return False, None
