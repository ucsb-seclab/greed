<!-- markdownlint-disable -->

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/factory.py#L0"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

# <kbd>module</kbd> `greed.factory`






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/factory.py#L17"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `Factory`
This class is used as a constructor of different objects:  
- SimulationManager 
- SimState 
- Block 
- TAC_Statement 
- TAC_Function 

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/factory.py#L28"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(project: 'Project')
```








---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/factory.py#L42"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `block`

```python
block(block_id: str) → Block
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/factory.py#L34"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `entry_state`

```python
entry_state(
    xid: str,
    init_ctx: dict = None,
    options: dict = None,
    max_calldatasize: int = None,
    partial_concrete_storage: bool = False
) → SymbolicEVMState
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/factory.py#L39"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `function`

```python
function(function_id: str) → TAC_Function
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/factory.py#L31"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `simgr`

```python
simgr(entry_state: SymbolicEVMState) → SimulationManager
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/factory.py#L45"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `statement`

```python
statement(stmt_id: str) → TAC_Statement
```








---

_This file was automatically generated via [lazydocs](https://github.com/ml-tooling/lazydocs)._
