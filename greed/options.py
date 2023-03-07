

# GENERAL OPTIONS 
# ===============
# Global options valid for ALL the states 
# generated during the exploration.
# ===============

# web3 provider URI.
# As of now, this is used when the partial concrete
# storage is initialized.
WEB3_PROVIDER = 'http://0.0.0.0:8545'

# Wether we want to check for satisfiability 
# every time the execution can fork.
# Checking for SAT at every branch may considerably
# slow down the exploration, but reduces the amount 
# of states kept in the stashes (i.e., pruning)
LAZY_SOLVES = False

# Wether we want to try to calculate the SHA3 for 
# buffer that are concrete or have only 1 solution.
# This may slow down the exploration as we need to calculate
# a solution for input buffers/offset and length used by the sha.
GREEDY_SHA = False

# This is to enforce that two addresses constructed as
# base + offset, where 'base' is a SHA result, cannot ever overlap
# within a reasonable distance. This should avoid false positive 
# related to overlapping memory regions.
MIN_SHA_DISTANCE = 2**20

# Create a graph visualizing the exploration.
SIMGRVIZ = False

# Activate debugging capabilities through the
# SimStateInspect plugin (i.e., breakpoints)
STATE_INSPECT = False

# Default CALLDATASIZE considered.
# Can be overwritten by the entry_state constructor.
MAX_CALLDATA_SIZE = 256

# Wether or not to try to concretize the exponent 
# of a EXP instruction.
MATH_CONCRETIZE_SYMBOLIC_EXP_EXP = False

# Wether or not to try to concretize the base 
# of a EXP instruction.
MATH_CONCRETIZE_SYMBOLIC_EXP_BASE = False

# Whenever there is a symbolic base, but concrete exponent,
# this is the max amount of supported nested multiplications.
MATH_MULTIPLY_EXP_THRESHOLD = 10

# Weather we should always consider CALLS as succeeded or not.
# (Setting this to True will always set in the res_var a value of 1)
OPTIMISTIC_CALL_RESULTS = False 

# Wether we should use a default constant value for EXTCODESIZE
# If this is True, we will use a default value of 42 for EXTCODESIZE 
# (Unless the address is concrete, then we'll pick it from the context IF provided)
# Otherwise, the value is going to be symbolic.
DEFAULT_EXTCODESIZE = False

# Wether we should use a default constant address when 
# using the CREATE opcode.
DEFAULT_CREATE_RESULT_ADDRESS = False

# Wether we should use a default constant address when 
# using the CREATE2 opcode.
DEFAULT_CREATE2_RESULT_ADDRESS = False


# STATE OPTIONS
# =============================================
# Per-state options, can be enabled/disabled 
# for a single state.
# =============================================

# Wether we want to drop a debugging interface everytime we 
# add a constraint to the state.
STATE_STOP_AT_ADDCONSTRAINT = "STATE_STOP_AT_ADDCONSTRAINT" 


# SOLVER OPTIONS
# ==============
# Options that influence the solving capabilities
# ==============

# MAX size of the SHA3 input buffer that is considered.
### ex. at least 512 is needed for addr:0x080bf510FCbF18b91105470639e9561022937712 tx:0x32c3890f0878d111c4008ae22d5784da5984fa4391bec87f205b10ee44904f6f
MAX_SHA_SIZE = 512

SOLVER_YICES2 = "YICES2"
# Default is Yices2
SOLVER = SOLVER_YICES2

SOLVER_TIMEOUT = 0
