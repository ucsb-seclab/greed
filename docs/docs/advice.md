# 🧐 A Word of Advice

## Concretizing symbolic values

When running greed, you will often find it helpful to concretize some symbolic values, for example, to inspect the actual value of a storage slot or to determine the concrete environment needed to reach a particular point in the execution (e.g., calldata).

Remember that:

(1) There are often inherent dependencies between symbolic values, and concretizing one might affect the satisfiability of the others. For example, to concretize the buffer of a `SHA3` operation, you will first need to concretize its offset and size, or to concretize the calldata buffer, you might need first to concretize the "calldatasize" as well – unless it is already concrete or known:

```python
calldatasize = state.solver.eval(state.calldatasize, raw=True)
calldata = state.solver.eval_memory(state.calldata, calldatasize)
```


(2) When you set up a concrete transaction, you will need to provide values other than the calldata, for example, the value of msg.sender (`CALLER`) and the transferred amount (`VALUE`). You can derive all these values from your final state. For example:

```python
caller = state.solver.eval(state.ctx['CALLER']).to_bytes(20, 'big').hex()
log.info(f'CALLER: 0x{caller}')
```