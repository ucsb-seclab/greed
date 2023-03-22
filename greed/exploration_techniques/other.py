from collections import defaultdict

from greed.solver.shortcuts import BVS

from . import ExplorationTechnique

class Whitelist(ExplorationTechnique):
    def __init__(self, whitelist):
        super().__init__()
        self.whitelist = whitelist

    def check_state(self, simgr, state):
        while state.curr_stmt.__internal_name__ not in self.whitelist:
            # stub res vars
            for res_var in state.curr_stmt.res_vars:
                state.registers[res_var] = BVS(res_var, 256)
            # skip to next statement
            state.set_next_pc()
        return state


class LoopLimiter(ExplorationTechnique):
    def __init__(self, n):
        super().__init__()
        self.n = n

    def setup(self, simgr):
        for state in simgr.states:
            state.globals["loop_counter"] = defaultdict(int)

    def check_state(self, simgr, state):
        state.globals["loop_counter"][state.pc] += 1
        if state.globals["loop_counter"][state.pc] > self.n:
            state.halt = True

        return state