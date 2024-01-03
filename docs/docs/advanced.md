# 🎓 Advanced Topics


## State Plugins

State plugins are (yet-another) concept that greed borrowed from angr.
A state plugin is designed to carry any additional state context during its life-cycle.
For instance, the default "globals" State Plugin can carry global variables useful for future decisions – such as the number of iterations of a specific loop.

You can design your own State Plugin by implementing the [SimStatePlugin](https://github.com/ucsb-seclab/greed/blob/main/greed/state_plugins/plugin.py) interface and installing it to a SimState.
The two main functions that need to be implemented when designing a custom plugin are: `__init__` and `copy`.
The former initializes the plugin with its default values, while the latter implements a deep copy of the plugin state (every plugin in a forking state must be copied to its successors). For example:
```python
from copy import deepcopy
from greed.state_plugins import SimStatePlugin

class mySimStateGlobals(SimStatePlugin):
    """
    A plugin that allows for global variables to be stored in the state.
    """
    def __init__(self, backer=None):
        super(mySimStateGlobals, self).__init__()
        self._backer = backer if backer is not None else dict()
        return

    ...

    def copy(self):
        new_backer = deepcopy(self._backer)
        return mySimStateGlobals(new_backer)

```

After creating a new plugin (e.g., `mySimStateGlobals`) you can install it into a state with:

```python
>>> state.register_plugin("myPluginName", mySimStateGlobals())
```

Later, you can access the methods and attributes of your plugin using the installed name:

```python
>>> state.myPluginName.myMethod()
```

## Memory Model

Symbolic memory reads and writes are arguably one of the most critical problems a symbolic executor must face to balance precision and scalability.
Many different strategies have been proposed during the past years that range from nested ITE expressions to SMT Arrays to a more balanced segmented memory model (this [paper](https://www.diag.uniroma1.it/~delia/papers/svtr19.pdf) does a pretty good job in providing an overview of all the currently available solutions).

Our choice of memory model for greed landed on a design similar to that of Frank et al. in [ETHBMC](https://www.usenix.org/system/files/sec20fall_frank_prepub_0.pdf). Specifically, we leverage an [extended version](https://llbmc.org/files/papers/VSTTE13.pdf) of the Theory of Arrays to model both the memory and the storage of a smart contract. We dubbed this memory model the "LambdaMemory".
Thanks to the LambdaMemory, every memory operation in greed can be fully symbolic. Additionally, this allows to symbolically model "memcopy" operations triggered by opcodes such as `CALLDATACOPY.`

While this memory model drastically improves the precision of symbolic execution, it also introduces additional complexity in the constraints and makes them hard to inspect.
Specifically, differently from angr, inspecting a variable pulled from memory will merely show a `Select` operation rather than a more expressive ITE operation.

## Partial Concrete Storage

???+ note
       To enable this mode, access to a web3 RPC endpoint is required. You can set the web3 provider via the option WEB3_PROVIDER in the greed [options](https://github.com/ucsb-seclab/greed/blob/main/greed/options.py#L12).
       If you don't have a private node, you can use any other provider such as [Infura](https://www.infura.io/) or [Alchemy](https://www.alchemy.com/).

A fully symbolic contract storage is not always a desirable option when performing symbolic execution.
In fact, when analyzing the state of a contract at a specific block, you might want to use the concrete values in its storage to prune some unfeasible paths and simplify the symbolic execution.

To do this, greed supports a "Partial Concrete Storage" mode that can be activated when creating a SimState:

```python
>>> ctx = {"ADDRESS": "0x6b6Ae9eDA977833B379f4b49655124b4e5c64086", "NUMBER": 18808898}
>>> entry_state = p.factory.entry_state(xid=xid, init_ctx=ctx, partial_concrete_storage=True)
```

When this mode is activated and greed encounters an `SLOAD` (let's say at slot id `0x5`), greed will automatically fetch the concrete value of slot `0x5` in the contract's on-chain storage at block `NUMBER` (`18808898`) instead of using an unconstrained symbol. Similarly, any subsequent (and possibly symbolic) `SSTORE` at slot `0x5` will overwrite its value. 

In other words, you can imagine this mode of operation as a "lazy" initialization of the contract's storage in the symbolic executor that uses its on-chain storage at the specified block.

## External Calls

Currently greed does not support external calls out-of-the-box. When one of the call opcodes (`CALL`/`DELEGATECALL`/`STATICCALL`/`CODECALL`) is executed during symbolic execution, our handlers simply "skip" the call and fill up the returned virtual register according to the option `OPTIMISTIC_CALL_RESULTS`. If `OPTIMISTIC_CALL_RESULTS` is active, greed will write the value `1` to the virtual register, indicating that the call was successfull.

While this is enough for certain analyses, at other times it might be important to follow the execution flow and execute the opcodes in the target (called) contract. This is currently a feature that must be implemented on top of greed.

???+ warning
       Implementing this feature requires particular care, especially in case of re-entrant code.


## Keccak256

In the EVM, the `SHA3` opcode calculates the Keccak256 hash of a given input buffer.
Tracking the constraints generated by cryptographic primitives such as `SHA3` is [notoriously impractical](https://link.springer.com/chapter/10.1007/978-3-642-19125-1_5). Simply put, the complexity of such procedures generates extremely complex constraints and immediately overwhelms and stalls any state-of-the-art constraint solver.

To overcome this issue, it is common practice to stub the `SHA3` opcode, returning thus a fresh unconstrained symbolic variable and proceeding with the analysis. However, this requires extra care: the connection between the input and output of the `SHA3` operation must be somehow modeled.
To do this, we use an approach similar to that of [ETHBMC](https://www.usenix.org/system/files/sec20fall_frank_prepub_0.pdf), leveraging the [Ackerman encoding](https://pdfs.semanticscholar.org/e4ac/6d84bd12069af44310c4e2816d6d9fc18d9e.pdf) for non-interpretable functions.

In practice, we handle the `SHA3` operations with a twofold strategy:

**(1)** During symbolic execution, we record all the information regarding `SHA` operations in the `sha_observed` attribute of a SimState (i.e., the snapshot of the state's memory at the SHA operation, the offset at which the input buffer is located, and the size of the requested operation). <!-- Then, in case the option `GREEDY_SHA` is active, we calculated (on the fly) the Keccak256 of fully concrete input buffers (or, symbolic buffers with one possible solution) and we assign this value to the result virtual registers. If no `GREEDY_SHA` is used  (or the input buffer is not concrete), we return a fresh symbolic variable (e.g., `<SHA1>`).  -->
For every observed `SHA` we return a fresh symbolic variable (e.g., `<SHA1>`) and [instantiate constraints](https://github.com/ucsb-seclab/greed/blob/main/greed/sha3.py#L44) that basically encode that the result of `SHA3` opcodes that operate on equivalent input buffers MUST be the same. 

**(2)** When concretizing a symbolic variable, e.g.: to synthethize the `CALLDATA` to reach a specific instruction, we must first "fix" the values of the observed SHAs (if any). We provide a "SHA resolution strategy" that fixes the observed SHAs in chronological order. Namely, the strategy iterates over all the observed SHAs starting from the earliest, calculates a solution for its input buffer, calculates the corresponding Keccak256 hash, and finally assigns the result to the symbolic variable associated to this SHA. The process repeats for each observed SHA. Eventually, if it is possible to assign a concrete value to all the observed SHAs, the state is ready to be concretized. If it is not possible to find a solution, the state will be marked as unsat.
Note that this process is not executed automatically, and must be explicitly called in your scripts. For example:

```python
shas = state.sha_resolver.fix_shas()  
```

## Multi-Transactions Execution

The state of a smart contract evolves across multiple transactions.
With greed, you can symbolically execute a contract, save one of its states, and create a new transaction from such state. For example:

```python
for xid, calldata in more_transactions:
    entry_state = entry_state.copy()
    entry_state.reset(xid=xid)
    entry_state.set_init_ctx({"CALLDATA": calldata})

    entry_state.pc = project.factory.block('0x0').first_ins.id
    simgr = project.factory.simgr(entry_state=entry_state)

    simgr.run(find=lambda s: (
        s.halt and 
        not s.error and
        s.trace[-1].__internal_name__ != 'REVERT')
    )

    if not simgr.found:
        break

    entry_state = simgr.one_found
```
