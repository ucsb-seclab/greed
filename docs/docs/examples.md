# 🐣 Examples

Here we show some examples to demonstrate the usage of some of the greed APIs and how to levereage them to accomplish a few interesting tasks.

## (1) Reachibility of a CALL statement

In this example, we show how to automatically synthetize the `CALLDATA` to reach an arbitrary `CALL` statement in an unverified contract `0x204Db9Ca00912c0F9e6380342113f6A0147E6f8C` on chain.

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

    # This is the PC of the target call 
    #(according to the contract.tac file in the Gigahorse analysis folder )
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



## (2) Mint a PudgyPenguin

In this example we show how one can synthetize the `CALLDATA` and the `CALLVALUE` necessary to mint() a PudgyPenguin(🐧) in the contract at `0xBd3531dA5CF5857e7CfAA92426877b022e612cf8`.

After you analyzed the [contract](https://library.dedaub.com/ethereum/address/0xbd3531da5cf5857e7cfaa92426877b022e612cf8/bytecode) as explained in the previous example, you can use the following script:

```python

import web3
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

    # 4 bytes of the mint() function
    # 0 --> 3
    calldata = "0x40c10f19"
    block_ref = 12878195

    # Create the greed project
    proj = Project(target_dir="./contracts/0xBd3531dA5CF5857e7CfAA92426877b022e612cf8/")

    # this is the pc of the STOP opcode in the mint function
    STOP = "0x43f"

    stop_stmt = proj.statement_at[STOP]

    block_info = proj.w3.eth.get_block(block_ref)

    # Let's set the CALLER to my account
    init_ctx = {
                "CALLDATA": calldata,
                "CALLER": "0x6b6Ae9eDA977833B379f4b49655124b4e5c64086",
                "ORIGIN": "0x6b6Ae9eDA977833B379f4b49655124b4e5c64086",
                "ADDRESS": "0xBd3531dA5CF5857e7CfAA92426877b022e612cf8",
                "NUMBER": block_info.number,
                "DIFFICULTY": block_info["totalDifficulty"],
                "TIMESTAMP": block_info["timestamp"]
                }

    xid = gen_exec_id()

    # Create the entry state
    entry_state = proj.factory.entry_state(
                                        xid=xid,
                                        init_ctx=init_ctx,
                                        max_calldatasize=68,
                                        partial_concrete_storage=True
                                        )

    # The second argument of mint is the "amount" of penguins to mint, we want that to be non-zero!
    entry_state.add_constraint(NotEqual(entry_state.calldata[BVV(67,256)], BVV(0,8)))

    # Set a constraint on the CALLVALUE
    entry_state.add_constraint(BV_ULE(entry_state.ctx['CALLVALUE'], BVV(0x6000000000000000, 256)))
    
    # When a Penguin is minted, we see a LOG4, let's setup an inspection
    # point and show a message! 
    def hi(simgr, state):
        log.debug(f'Emitted LOG4 at {state.curr_stmt.id}!')
    entry_state.inspect.stop_at_stmt(stmt_name="LOG4", func=hi)

    # Setting up the simulation manager
    simgr = proj.factory.simgr(entry_state=entry_state)

    directed_search = DirectedSearch(stop_stmt)
    simgr.use_technique(directed_search)

    prioritizer = Prioritizer(scoring_function=lambda s: -s.globals['directed_search_distance'])
    simgr.use_technique(prioritizer)

    heartbeat = HeartBeat(beat_interval=100, show_op=True)
    simgr.use_technique(heartbeat)

    print(f"  Symbolically executing...")

    while True:
        try:
            simgr.run(find=lambda s: s.curr_stmt.id == stop_stmt.id)
        except Exception as e:
            print(e)
            continue

        if len(simgr.found) == 1:
            print(f"   ✅ Found state for {stop_stmt.__internal_name__} at {stop_stmt.id}!")
            state = simgr.one_found

            # Fix the shas!
            if len(state.sha_observed) > 0:
                shas = state.sha_resolver.fix_shas()
                print(f'Fixed {len(shas)} shas in the state!')

            # Get a solution for the CALLDATA
            calldata_sol = state.solver.eval_memory(state.calldata, length=BVV(68,256), raw=True)
            
            # Get a solution for CALLVALUE (i.e., how much we paid for a penguin)
            # (Note: Yices2 does not expose a min() function, but you can find the minimum value
            # by using a bisection search)
            callvalue = state.solver.eval(state.ctx['CALLVALUE'])

            print(f"   📥 Calldata: {hex(bv_unsigned_value(calldata_sol))}")
            print(f"   💸 Callvalue: {callvalue}")
            
            break

        elif len(simgr.found) == 0:
            print(f"   ❌ No state found for {stop_stmt.__internal_name__} at {stop_stmt.id}!")
            break



if __name__ == "__main__":
    main()

```