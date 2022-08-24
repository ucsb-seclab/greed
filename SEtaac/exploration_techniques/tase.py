import random
import logging 

from . import ExplorationTechnique

from SEtaac import options

log = logging.getLogger(__name__)

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
        super(TypeAware, self).__init__()
        
        # The current function under TASE
        self.func_target = func_target

        # ID of visited statements 
        self.visited_stmts = set()

        # Forcing LAZY_SOLVES at True
        options.LAZY_SOLVES = True

        # Opcodes for which we have to check rules.
        self.target_opcodes = ["CALLDATALOAD", "CALLDATACOPY"]

        # Current opcode to investigate 
        # to match rules
        self.curr_to_check = None
        self.curr_opcode = None
        
        # Dictionary of the 31st rules. We need to check 
        # how many times we trigger a rule later to distinguish 
        # all the different arguments.
        self.rules = {}
        for x in range(1,31):
            self.rules[f"R{x}"] = 0

    def setup(self, simgr):
        return

    def check_state(self, simgr, state):
        if state.curr_stmt.__internal_name__ in self.target_opcodes:
            assert(state.curr_stmt.num_ress == 1)
            self.curr_to_check = state.curr_stmt.res_vars[0]
            self.curr_opcode = state.curr_stmt.__internal_name__
        return state

    def check_successors(self, simgr, successors):
        new_successors = []
        for succ in successors:
            # Just keep states at unexplored blocks
            if succ.pc not in self.visited_stmts:
                new_successors.append(succ)
                self.visited_stmts.add(succ.pc)
            else:
                log.debug(f"Skipping visited block {succ.pc}")
        
        if self.curr_to_check != None:
            for succ in new_successors:
                # Here we gotta check the constraints over the self.curr_to_check to see
                # if they match any rule
                import ipdb; ipdb.set_trace()
            self.curr_to_check = None
        return new_successors

    def is_complete(self, simgr, stash='active'):
        return True