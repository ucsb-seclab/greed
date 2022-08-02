import random

from . import ExplorationTechnique

# This ET implement the technique discussed in 
# https://www.researchgate.net/publication/351421422_SigRec_Automatic_Recovery_of_Function_Signatures_in_Smart_Contracts
# https://ieeexplore.ieee.org/ielx7/32/4359463/9426396/supp1-3078342.pdf?arnumber=9426396&tag=1
# for ABI recovery.
#
# The main features of this ET are:
#    - Rule checking every time there is a type-related instruction (i.e., CALLDATALOAD/CALLDATACOPY)
#    - No SAT checking (i.e., enforced LAZY_SOLVE)
#    - For every function, the ET executes the block ONLY once.

class TypeAware(ExplorationTechnique):
    def __init__(self):
        super(TypeAware, self).__init__()

    def setup(self, simgr):
        return

    def check_successors(self, simgr, successors):
        return successors

    def is_complete(self, simgr, stash='active'):
        return True