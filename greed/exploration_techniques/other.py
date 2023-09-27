import logging

from collections import defaultdict

from greed.solver.shortcuts import is_concrete, BVV, BVS, BV_ULT, BV_UGT, Equal
from greed.exploration_techniques import ExplorationTechnique
from greed.analyses.slicing import forward_slice

log = logging.getLogger(__name__)


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
    

class MstoreConcretizer(ExplorationTechnique):
    def __init__(self):
        super().__init__()

        self.debug = False

        self.tac_induction_variables_starts_at_const = None
        self.tac_induction_variables_increases_by_const = None
        self.tac_upper_bounds = None

        self.loop_upper_bounds = None

        self.tac_induction_variables = None
        self.tac_loops = None
        self.tac_loop_blocks = None
        
        self.relevant_mstores = None

    def setup(self, simgr, _debug=False):
        self.debug = _debug

        for s in simgr.states:
            s.globals["bounds"] = dict()

        # get bounds
        self.tac_induction_variables_starts_at_const = simgr.project.tac_parser.parse_induction_variable_starts_at_const()
        self.tac_induction_variables_increases_by_const = simgr.project.tac_parser.parse_induction_variable_increases_by_const()
        self.tac_upper_bounds = simgr.project.tac_parser.parse_induction_variable_upper_bounds()
        DEFAULT_ITERATIONS = 5
        self.loop_upper_bounds = defaultdict(lambda: defaultdict(int))
        for loop_head_addr in self.tac_induction_variables_starts_at_const.keys() & self.tac_induction_variables_increases_by_const.keys() & self.tac_upper_bounds.keys():
            for induction_var, upper_bound_var in self.tac_upper_bounds[loop_head_addr].items():
                starts_at_const = self.tac_induction_variables_starts_at_const[loop_head_addr][induction_var]
                increases_by_const = self.tac_induction_variables_increases_by_const[loop_head_addr][induction_var]
                self.loop_upper_bounds[loop_head_addr][upper_bound_var] = starts_at_const + DEFAULT_ITERATIONS * increases_by_const

        # get loop blocks
        self.tac_induction_variables = simgr.project.tac_parser.parse_induction_variables()
        self.tac_loops = set(self.tac_induction_variables.keys())
        self.tac_loop_blocks = dict()
        for loop_addr, blocks_addrs in simgr.project.tac_parser.parse_blocks_in_loop().items():
            _tac_loop_blocks = {simgr.project.block_at[addr] for addr in blocks_addrs}
            self.tac_loop_blocks[loop_addr] = _tac_loop_blocks

        # find loop mstores
        self.relevant_mstores = set()
        for loop_head_addr in self.tac_induction_variables.keys():
            loop_head = simgr.project.block_at[loop_head_addr]

            # forward slice on induction vars
            target_addr = loop_head.first_ins.id
            target_vars = self.tac_induction_variables[loop_head_addr]
            slice = forward_slice(simgr.project, target_addr=target_addr, target_vars=target_vars)

            for i in slice:
                if i.__internal_name__ == "MSTORE":
                    self.relevant_mstores.add(i)


    def check_state(self, simgr, state):
        if not state.solver.is_sat():
            state.halt = True
            return state
        
        if self.debug:
            log.info(f"num constraints: {len(state.solver.constraints)}")
            log.info("current values of bounded vars:")
            for k, v in state.globals["bounds"].items():
                log.info(f"  {k}: {state.solver.eval(state.registers[k], raw=True)}")

        loop_head_addr = state.curr_stmt.block_id  # "candidate" loop head
        if (loop_head_addr in self.tac_loops and 
            len(state.trace) > 0 and
            state.trace[-1].block_id != loop_head_addr and
            self.project.block_at[state.trace[-1].block_id] not in self.tac_loop_blocks[loop_head_addr]):
            for upper_bound_var, upper_bound in self.loop_upper_bounds[loop_head_addr].items():
                if upper_bound_var not in state.registers:
                    continue
                state.add_constraint(BV_ULT(state.registers[upper_bound_var], BVV(upper_bound, 256)))
                state.globals["bounds"][upper_bound_var] = upper_bound
                log.info(f"---> ADDED DEFAULT UPPER BOUND ({upper_bound_var}:{upper_bound})")

        # SELECTIVELY CONCRETIZE MSTORES
        if (state.curr_stmt.__internal_name__ == "MSTORE" and
            not is_concrete(state.registers[state.curr_stmt.offset_var])):
            
            # find min mstore offset
            state.solver.push()
            SINGLE_SOL = True
            sol = state.solver.eval(state.registers[state.curr_stmt.offset_var], raw=True)
            log.info(f"candidate min mstore offset is: {sol}")
            state.add_constraint(BV_ULT(state.registers[state.curr_stmt.offset_var], sol))
            while state.solver.is_sat() is True:
                SINGLE_SOL = False
                sol = state.solver.eval(state.registers[state.curr_stmt.offset_var], raw=True)
                log.info(f"candidate min mstore offset is: {sol}")
                state.add_constraint(BV_ULT(state.registers[state.curr_stmt.offset_var], sol))
            state.solver.pop()
            log.info(f"actual min mstore offset ({SINGLE_SOL=}) is: {sol}")

            # branch and concretize on loop MSTORE
            if state.curr_stmt in self.relevant_mstores:
                state2 = state.copy()
                state2.add_constraint(BV_UGT(state.registers[state.curr_stmt.offset_var], sol))
                simgr.stashes["active"].append(state2)

            # concretize only relevant MSTORE (or single sol)
            if SINGLE_SOL or state.curr_stmt in self.relevant_mstores:
                state.registers[state.curr_stmt.offset_var] = sol
                state.add_constraint(Equal(state.registers[state.curr_stmt.offset_var], sol))

        return state