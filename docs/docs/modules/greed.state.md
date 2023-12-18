<!-- markdownlint-disable -->

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state.py#L0"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

# <kbd>module</kbd> `greed.state`






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state.py#L19"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `SymbolicEVMState`
This class represents a symbolic EVM state (SimState). 

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state.py#L41"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(
    xid,
    project,
    partial_init=False,
    init_ctx=None,
    options=None,
    max_calldatasize=None,
    partial_concrete_storage=False
)
```



**Args:**
 
 - <b>`xid`</b>:  The execution id  
 - <b>`project`</b>:  the greed project 
 - <b>`partial_init`</b>:  Whether to partially initialize the object or not 
 - <b>`init_ctx`</b>:  The initial context of the state (e.g., CALLER, ADDRESS, BALANCE, etc.) 
 - <b>`options`</b>:  The options for this state 
 - <b>`max_calldatasize`</b>:  The maximum size of the calldata 
 - <b>`partial_concrete_storage`</b>:  Whether to use the partial concrete storage or not 


---

#### <kbd>property</kbd> constraints





---

#### <kbd>property</kbd> curr_stmt





---

#### <kbd>property</kbd> pc







---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state.py#L281"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `add_constraint`

```python
add_constraint(constraint)
```

This method adds a constraint to the state. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state.py#L310"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `copy`

```python
copy()
```

Deep copy of the SimState. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state.py#L234"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `get_fallthrough_pc`

```python
get_fallthrough_pc()
```

This method returns the fallthrough pc of the current state 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state.py#L256"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `get_non_fallthrough_pc`

```python
get_non_fallthrough_pc(destination_val)
```

This method returns the non fallthrough pc of the current state. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state.py#L301"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `register_plugin`

```python
register_plugin(name: str, plugin: SimStatePlugin)
```

This method registers a plugin to the state. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state.py#L349"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `reset`

```python
reset(xid)
```

This method resets the state. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state.py#L103"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `set_init_ctx`

```python
set_init_ctx(init_ctx=None)
```

This method applies the initial context to the state. 

**Args:**
 
 - <b>`init_ctx`</b>:  A dict storing the initial context of the state (e.g., CALLER, ADDRESS, BALANCE, etc.) 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state.py#L214"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `set_next_pc`

```python
set_next_pc()
```

This method sets the next pc to the state. 

**Raises:**
 
 - <b>`VMNoSuccessors`</b>:  If there are no successors 
 - <b>`VMUnexpectedSuccessors`</b>:  If the successor does not match any of the expected successors 




---

_This file was automatically generated via [lazydocs](https://github.com/ml-tooling/lazydocs)._
