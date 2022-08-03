import random

from . import ExplorationTechnique

from SEtaac import options

# This ET implement the technique discussed in 
# https://www.researchgate.net/publication/351421422_SigRec_Automatic_Recovery_of_Function_Signatures_in_Smart_Contracts
# https://ieeexplore.ieee.org/ielx7/32/4359463/9426396/supp1-3078342.pdf?arnumber=9426396&tag=1
# for ABI recovery.
#
# The main features of this ET are:
#    - Target a single function
#    - No SAT checking (i.e., enforced LAZY_SOLVE)
#    - For every function, the ET executes the block ONLY once.

class TypeAware(ExplorationTechnique):
    def __init__(self, func_target):
        self.func_target = func_target
        self.visited_stmts = set()

        # Forcing LAZY_SOLVES at True
        options.LAZY_SOLVES = True

        self.curr_to_check = None
        super(TypeAware, self).__init__()

    def setup(self, simgr):
        return

    def check_state(self, simgr, state):
        print(f"state: {state.pc}")
        if state.curr_stmt.__internal_name__ == "CALLDATALOAD":
            assert(state.curr_stmt.num_ress == 1)
            self.curr_to_check = state.curr_stmt.res_vars[0]
        return state

    def check_successors(self, simgr, successors):
        new_successors = []
        for succ in successors:
            # Just keep states at unexplored blocks
            if succ.pc not in self.visited_stmts:
                new_successors.append(succ)
                self.visited_stmts.add(succ.pc)
            else:
                print(f"Skipping visited block {succ.pc}")
        
        if self.curr_to_check != None:
            for succ in new_successors:
                # Here we gotta check the constraints over the self.curr_to_check to see
                # if they match any rule
                print(f"succ[{succ.pc}][{self.curr_to_check}]={succ.registers[self.curr_to_check]}")
            self.curr_to_check = None
        return new_successors

    def is_complete(self, simgr, stash='active'):
        return True