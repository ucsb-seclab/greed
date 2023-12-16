# 🕹️ Options

greed supports many option to tweak the behavior of symbolic execution.
These global options should be activated or de-activated before creating an entry state.

| Option Name | Default | Desc |
|-------------------|----------|----------|
| options.GREEDY_SHA  | False | calculate the result of the `KECCAK256` whenever the input buffer is fully concrete and has one solution |
| options.LAZY_SOLVES | False | check_sat() every time a new SimState is generated |



options.GREEDY_SHA = True
options.LAZY_SOLVES = False
options.STATE_INSPECT = False
options.MAX_SHA_SIZE = 300
options.OPTIMISTIC_CALL_RESULTS = True
options.DEFAULT_EXTCODESIZE = True
options.DEFAULT_CREATE2_RESULT_ADDRESS = True
options.DEFAULT_CREATE_RESULT_ADDRESS = True
options.MATH_CONCRETIZE_SYMBOLIC_EXP_EXP = True
options.MATH_CONCRETIZE_SYMBOLIC_EXP_BASE = True