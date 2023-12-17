# 🚀 Advanced Topics


## State Plugins

State plugins are (yet-another) concepts that greed borrowed by angr.
A state plugin is designed to add any additional per-state-context that a SimState should carry with itself during its life-cycle.
For instance, the default "globals" State Plugin can carry global variables useful for future decision of an exploration technique such as the number of time a specific loop has been iterating.

Users can design their own State Plugins by implementing the [SimStatePlugin](https://github.com/ucsb-seclab/greed/blob/main/greed/state_plugins/plugin.py) interface and installing it to a SimState.
The two main functions that need to be implemented when designing a custom plugin are: `__init__` and `copy`.
The former initializes the plugin with its starting values, while the latter is responsible of implementing a full deep copy of the plugin state whenever the Simulation Manager decides to fork a SimState during symbolic execution (i.e., every plugins carried by a forking state must be cloned into its successors).

After you created a new plugin (e.g., `myNewStatePlugin`) you can install it into a state with:

```python
>>> state.register_plugin("myPluginName", myNewStatePlugin())
```

Later, you can access the methods and attributes of that plugin using the installed name:

```python
>>> state.myPluginName.hi
```

## Memory Model

Symbolic memory writes (and reads) are arguably one of the most critical issue a symbolic executor needs to deal with to mantain a good balance between precision and scalability.
Many different strategies have been proposed during the past years that ranges from nested ITE expressions to full SMT Array, to a more balanced segmented memory model (this [paper](https://www.diag.uniroma1.it/~delia/papers/svtr19.pdf) does a pretty good job in providing an overview of all the currently available solutions).

Our choice for greed landed on a similar design employed by Frank et al. in [ETHBMC](https://www.usenix.org/system/files/sec20fall_frank_prepub_0.pdf). Specifically, we leverage an [extended version](https://llbmc.org/files/papers/VSTTE13.pdf) of the Theory of Array to model both the memory and the storage of a smart contract. We dubbed this memory model the "LambdaMemory".
Thanks to the LambdaMemory, every memory operation can be always kept symbolic through the use of the `Select` and `Store` SMT Array operations, additionaly, we can symbolically model 'memcopy' operations triggered by opcode such as `CALLDATACOPY`.

While this memory model drastically improve the precision of symbolic execution (i.e., we do not have to early-concretize symbolic variables), the drawback is a bit more complexity in the constraints, and the loss of inspectability of those.
Specifically, differently from angr, inspecting a variable pulled from memory will merely show a `Select` operation rather than a full explicit ITE operation.

## Partial Concrete Storage

???+ note
       In order to enable this mode an access to a web3 RPC is required. You can set the web3 provider via the option WEB3_PROVIDER in the greed [options](https://github.com/ucsb-seclab/greed/blob/main/greed/options.py#L12) file.
       If you do not have a private node, you can use one of the public provider such as [Infura](https://www.infura.io/) or [Alchemy](https://www.alchemy.com/).

A fully symbolic contract storage is not always a desirable option when performing symbolic execution.
In fact, when we want to analyze the state of a contract at a specific block, we might want to use the concrete values in its storage to prune some unfeasible paths and in general simplify the symbolic execution.

To do this, greed supports a "Partial Concrete Storage" mode that can be activated when creating a SimState:

```python
>>> ctx = {"ADDRESS": "0x6b6Ae9eDA977833B379f4b49655124b4e5c64086"}
>>> entry_state = p.factory.entry_state(xid=xid, init_ctx=ctx, partial_concrete_storage=True)
```

When this mode is activated, whenever there is an `SLOAD` (let's say at slot id `0x5`), we are going to use the storage of the contract at `ADDRESS` (e.g., `0x6b6Ae9eDA977833B379f4b49655124b4e5c64086`) and automatically returns the value of slot `0x5` in the contract real storage (instead of a symbol).

Further `SSTORE` at slot `0x5` will overwrite this value. In other words, you can imagine this mode of operation as a "lazy" initialization of the storage of a contract (in the symbolic executor) with its real values on chain (at a specific block).




## External Calls

## Multi-Transactions Execution

## Keccak256

## Keccak256 Solutions






