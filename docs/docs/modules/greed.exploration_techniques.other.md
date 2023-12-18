<!-- markdownlint-disable -->

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/other.py#L0"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

# <kbd>module</kbd> `greed.exploration_techniques.other`






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/other.py#L12"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `Whitelist`
This technique skips all statements that are not in the whitelist until one of them is reached. The result variables of the skipped statements are set to a fresh symbolic variable. 

**Args:**
 
 - <b>`whitelist`</b>:  the list of statements' names in the whitelist (e.g., ["MSTORE", "MLOAD"]) 

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/other.py#L19"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(whitelist)
```








---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/other.py#L23"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `check_state`

```python
check_state(simgr, state)
```

Check if the current statement is in the whitelist. If not, skip to the next statement. 


---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/other.py#L37"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `LoopLimiter`
This technique limits the number of times a loop can be executed. When the limit is reached, the state is halted. 

**Args:**
 
 - <b>`n`</b>:  the maximum number of times a loop can be executed 

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/other.py#L44"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(n)
```








---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/other.py#L57"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `check_state`

```python
check_state(simgr, state)
```

Check if the loop has been executed more than n times. If so, halt the state. 

**Args:**
 
 - <b>`simgr`</b>:  the simulation manager 
 - <b>`state`</b>:  the state to check 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/other.py#L48"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `setup`

```python
setup(simgr)
```

Setup the technique. 

**Args:**
 
 - <b>`simgr`</b>:  the simulation manager 


---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/other.py#L72"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `MstoreConcretizer`
This technique concretizes the offset of MSTOREs. 

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/other.py#L76"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__()
```








---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/other.py#L140"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `check_state`

```python
check_state(simgr, state)
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/other.py#L93"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `setup`

```python
setup(simgr, _debug=False)
```

Setup the technique. 

**Args:**
 
 - <b>`simgr`</b>:  the simulation manager 
 - <b>`_debug`</b>:  whether to print debug info 




---

_This file was automatically generated via [lazydocs](https://github.com/ml-tooling/lazydocs)._
