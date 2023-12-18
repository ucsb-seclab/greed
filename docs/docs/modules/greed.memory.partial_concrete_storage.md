<!-- markdownlint-disable -->

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/partial_concrete_storage.py#L0"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

# <kbd>module</kbd> `greed.memory.partial_concrete_storage`






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/partial_concrete_storage.py#L14"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `PartialConcreteStorage`
This class represents a partial concrete storage. When using the partial concrete storage, reads from the contract storage (SLOADs) are initialized with the concrete value on-chain (at the given block number). 

To use this, we need a web3 connection to the blockchain, the address of the contract and the block number. 

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/partial_concrete_storage.py#L25"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(tag=None, value_sort=None, state=None, partial_init=False)
```

Initialize the partial concrete storage. 

**Args:**
 
 - <b>`tag`</b>:  The unique identifier of the storage 
 - <b>`value_sort`</b>:  The sort of the values stored in the storage 
 - <b>`state`</b>:  The SimState associated with this storage 
 - <b>`partial_init`</b>:  If true, the storage is partially initialized (used for copy) 

**Raises:**
 
 - <b>`GreedException`</b>:  If the partial concrete storage is not initialized with the contract address and block number 
 - <b>`AssertionError`</b>:  If the partial concrete storage is not initialized with the tag and value sort 
 - <b>`AssertionError`</b>:  If w3 is not connected 


---

#### <kbd>property</kbd> constraints





---

#### <kbd>property</kbd> layer_level







---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/partial_concrete_storage.py#L72"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `add_constraint`

```python
add_constraint(formula)
```

Add a constraint to the storage. 

**Args:**
 
 - <b>`formula`</b>:  The constraint to add 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/partial_concrete_storage.py#L80"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `add_constraints`

```python
add_constraints(formulas)
```

Add a list of constraints to the storage. 

**Args:**
 
 - <b>`formulas`</b>:  The list of constraints to add 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/partial_concrete_storage.py#L154"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `copy`

```python
copy(new_state)
```

Copy the partial concrete storage. 

**Args:**
 
 - <b>`new_state`</b>:  The new SimState associated with the new storage 




---

_This file was automatically generated via [lazydocs](https://github.com/ml-tooling/lazydocs)._
