# 🐣 Examples

## (1) Reaching an arbitrary CALL statement

In this example, we show how to automatically synthetize the `CALLDATA` to reach an arbitrary `CALL` statement in an unverified contract `0x204Db9Ca00912c0F9e6380342113f6A0147E6f8C` on chain.
This example demonstrates the usage of some of the greed APIs and how to use them to accomplish the task.

First, you should download the [contract bytecode](https://library.dedaub.com/ethereum/address/0x204db9ca00912c0f9e6380342113f6a0147e6f8c/bytecode) and place it in a `contract.hex` file:

```bash
degrigis@tati:~/contracts/0x204Db9Ca00912c0F9e6380342113f6A0147E6f8C$ cat contract.hex
0x6080604052600436106100595760003560e...
```

Then, use our script `analyze_hex.sh` (shipped with greed) to run Gigahorse against it:
( the script is in the `/greed/resources/` folder)

```bash
degrigis@tati:~/contracts/0x204Db9Ca00912c0F9e6380342113f6A0147E6f8C$ analyze_hex.sh --file ./contract.hex
```

This will produce many artifacts in the current folder:

```bash
degrigis@tati:~/contracts/0x204Db9Ca00912c0F9e6380342113f6A0147E6f8C$ ls -l
degrigis@tati:~/projects/greed-examples/contracts/0x204Db9Ca00912c0F9e6380342113f6A0147E6f8C$ ls -l
total 872
-rw-rw-r-- 1 degrigis degrigis    934 Dec 19 10:55 ActualReturnArgs.csv
-rw-rw-r-- 1 degrigis degrigis      2 Dec 19 10:55 AllCALLsClassified.csv
-rw-rw-r-- 1 degrigis degrigis     23 Dec 19 10:55 Analytics_ArrayCopy.csv
-rw-rw-r-- 1 degrigis degrigis     12 Dec 19 10:55 Analytics_ArrayHasTwoElementLengths.csv
-rw-rw-r-- 1 degrigis degrigis      0 Dec 19 10:55 Analytics_BlockHasNoTACBlock.csv
-rw-rw-r-- 1 degrigis degrigis      0 Dec 19 10:55 Analytics_BlockInMultipleFunctions.csv
-rw-rw-r-- 1 degrigis degrigis      0 Dec 19 10:55 Analytics_BlockInNoFunctions.csv
-rw-rw-r-- 1 degrigis degrigis      0 Dec 19 10:55 Analytics_BlockIsEmpty.csv
[ ... ]
```

Now, we have everything we need to start using greed! This is the analysis script to automatically generate the
`CALLDATA` needed to reach the target `CALL` statement (follow the comments).

```python
import logging 

from greed import Project, options
from greed.exploration_techniques import ExplorationTechnique, DirectedSearch, HeartBeat, Prioritizer, DFS
from greed.utils.extra import gen_exec_id
from greed.solver.shortcuts import *

LOGGING_FORMAT = "%(levelname)s | %(message)s"
logging.basicConfig(level=logging.INFO, format=LOGGING_FORMAT)
log = logging.getLogger("example")
log.setLevel(logging.INFO)

def config_greed():
    options.WEB3_PROVIDER = 'http://0.0.0.0:8545' # your web3 RPC node.
    options.GREEDY_SHA = True
    options.LAZY_SOLVES = False
    options.STATE_INSPECT = True
    options.MAX_SHA_SIZE = 300
    options.OPTIMISTIC_CALL_RESULTS = True
    options.DEFAULT_EXTCODESIZE = True
    options.DEFAULT_CREATE2_RESULT_ADDRESS = True
    options.DEFAULT_CREATE_RESULT_ADDRESS = True
    options.MATH_CONCRETIZE_SYMBOLIC_EXP_EXP = True
    options.MATH_CONCRETIZE_SYMBOLIC_EXP_BASE = True

def main():

    config_greed()
    
    block_ref = 16489409
    call_pc = "0x1f7"

    # Create the greed project
    proj = Project(target_dir="./contracts/0x204Db9Ca00912c0F9e6380342113f6A0147E6f8C/")

    # We want to reach this call statement
    call_stmt = proj.statement_at[call_pc]

    # Get information about the block to concretize the block context
    block_info = proj.w3.eth.get_block(block_ref)

    # Create the initial context
    init_ctx = {
                "CALLER": "0x6b6Ae9eDA977833B379f4b49655124b4e5c64086",
                "ORIGIN": "0x6b6Ae9eDA977833B379f4b49655124b4e5c64086",
                "ADDRESS": "0x204Db9Ca00912c0F9e6380342113f6A0147E6f8C",
                "NUMBER": block_info.number,
                "DIFFICULTY": block_info["totalDifficulty"],
                "TIMESTAMP": block_info["timestamp"]
                }

    # Generate a new execution id
    xid = gen_exec_id()

    # Create the entry state
    entry_state = proj.factory.entry_state(
                                        xid=xid,
                                        init_ctx=init_ctx,
                                        max_calldatasize=2048,
                                        partial_concrete_storage=True
                                        )
    
    # Setting up the simulation manager!
    simgr = proj.factory.simgr(entry_state=entry_state)

    # Enabling directed symbolic execution
    directed_search = DirectedSearch(call_stmt)
    simgr.use_technique(directed_search)

    # Together with the prioritizer, this technique will prioritize states that are closer to the target
    prioritizer = Prioritizer(scoring_function=lambda s: -s.globals['directed_search_distance'])
    simgr.use_technique(prioritizer)

    # Some nice output :)
    heartbeat = HeartBeat(beat_interval=1, show_op=True)
    simgr.use_technique(heartbeat)

    print(f"  Symbolically executing...")

    while True:
        try:
            # Run the simulation manager until we reach the call statement
            simgr.run(find=lambda s: s.curr_stmt.id == call_stmt.id)
        except Exception as e:
            print(e)
            continue

        # Found a state at the call statement!
        if len(simgr.found) == 1:
            print(f"   ✅ Found state for {call_stmt.__internal_name__} at {call_stmt.id}!")
            state = simgr.one_found
            
            # Get a solution for the calldata, this is the value that we should pass to 
            # reach the call statement!
            calldata_sol = state.solver.eval_memory(state.calldata, length=BVV(1024, 256))
            print(f"   📥 Calldata: {calldata_sol}")
            break

        elif len(simgr.found) == 0:
            # if we are here, it is not possible to reach the call statement given
            # the current context
            print(f"   ❌ No state found for {call_stmt.__internal_name__} at {call_stmt.id}!")
            break

if __name__ == "__main__":
    main()

```



## (2) Multi-transactions analysis