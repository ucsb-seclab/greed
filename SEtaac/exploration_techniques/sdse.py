
import hashlib
import logging
import networkx
import random

from typing import Callable
from SEtaac.state import SymbolicEVMState
from . import ExplorationTechnique

# Shortest Distance Symbolic Execution.
# This technique tries to prune states that cannot reach the 
# block of a specific target statement.
class SDSE(ExplorationTechnique):
    def __init__(self, target_stmt):
        super(SDSE,self).__init__()
        self._target_stmt = target_stmt
        self._target_block = None

    def setup(self, simgr):
        self._target_block = self._project.factory.block(self._target_stmt.block_id)

    def check_stashes(self, stashes, stash='active'):
        return stashes

    def check_state(self, state):
        return state

    def check_successors(self, successors):
        new_successors = []
        for succ in successors:
            if self._is_reachable(succ, self._target_block):
                new_successors.append(succ)
        return new_successors

    def is_complete(self,simgr):
        return True 

    # Check if the current state can reach 'block_b'
    def _is_reachable(self, state_a, block_b):
        factory = self._project.factory
        callgraph = self._project.callgraph

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
                for returnprivate_block_id in block_b.function.returnprivate_block_ids:
                    returnprivate_block = factory.block(returnprivate_block_id)
                    if self._is_reachable_without_returns(block_b, returnprivate_block, factory, callgraph):
                        break
                else:
                    # executed if there is no break
                    return False

                if self._is_reachable_without_returns(return_block, block_b, factory, callgraph):
                    return True
            return False
    
    def _is_reachable_without_returns(block_a, block_b, factory, callgraph):
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

    def _move(self, from_stash: str, to_stash: str, filter_func: Callable[[SymbolicEVMState], bool] = lambda s: True):
        for s in from_stash:
            if filter_func(s):
                from_stash.remove(s)
                to_stash.append(s)