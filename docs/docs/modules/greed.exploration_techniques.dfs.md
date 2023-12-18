<!-- markdownlint-disable -->

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/dfs.py#L0"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

# <kbd>module</kbd> `greed.exploration_techniques.dfs`






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/dfs.py#L4"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `DFS`
This Exploration technique implements a Classic Depth-First Search exploration 

**Args:**
 
 - <b>`deferred_stash`</b>:  the name of the stash where deferred states are put 

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/dfs.py#L10"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(deferred_stash='deferred')
```








---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/dfs.py#L23"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `check_stashes`

```python
check_stashes(simgr, stashes, stash='active')
```

If multiple states are in the active stash, move all but the oldest to the deferred stash. 

**Args:**
 
 - <b>`simgr`</b>:  the simulation manager 
 - <b>`stashes`</b>:  the stashes 
 - <b>`stash`</b>:  the name of the stash to check 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/dfs.py#L44"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `is_complete`

```python
is_complete(simgr, stash='active')
```

Check if the exploration is complete: there are no active states, and no deferred states. 

**Args:**
 
 - <b>`simgr`</b>:  the simulation manager 
 - <b>`stash`</b>:  the name of the stash to check 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/dfs.py#L14"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `setup`

```python
setup(simgr)
```

Setup the technique. 

**Args:**
 
 - <b>`simgr`</b>:  the simulation manager 




---

_This file was automatically generated via [lazydocs](https://github.com/ml-tooling/lazydocs)._
