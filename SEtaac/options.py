

# GENERAL OPTIONS 
# ===============

# Exploration options
LAZY_SOLVES = False

# This is to enforce that two addresses constructed as
# base + offset, where 'base' is a SHA result, cannot ever overlap
# within a reasonable distance. This should avoid false positive 
# related to overlapping memory regions.
MIN_SHA_DISTANCE = 2**20

# Debugging options
SIMGRVIZ = False
STATE_INSPECT = False

# Max calldatasize considered
MAX_CALLDATA_SIZE = 256

# STATE OPTIONS
# ==============
STATE_STOP_AT_ADDCONSTRAINT = "STATE_STOP_AT_ADDCONSTRAINT" 


# SOLVER OPTIONS
# ==============
MAX_SHA_SIZE = 256
SOLVER_YICES2 = "YICES2"

# Default is Yices2
SOLVER = SOLVER_YICES2
