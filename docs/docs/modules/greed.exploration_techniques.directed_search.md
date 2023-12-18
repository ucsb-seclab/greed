<!-- markdownlint-disable -->

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/directed_search.py#L0"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

# <kbd>module</kbd> `greed.exploration_techniques.directed_search`






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/directed_search.py#L8"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `DirectedSearch`
This technique prunes all states that cannot reach the block of a specified target statement. 

Possibly more effective when combined with DFS if only one path is needed: 

directed_search = DirectedSearch(target_stmt) simgr.use_technique(directed_search) 

dfs = DFS() simgr.use_technique(dfs) 

simgr.run(find=lambda s: s.curr_stmt.id == target_stmt_id) 



**Args:**
 
 - <b>`target_stmt`</b>:  the target Statement that we want to reach 
 - <b>`pruned_stash`</b>:  the name of the stash where pruned states are put 

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/directed_search.py#L26"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(target_stmt, pruned_stash='pruned')
```








---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/directed_search.py#L43"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `check_successors`

```python
check_successors(simgr, successors)
```

Calculate the successors that can reach the target block, otherwise prune them. 

**Args:**
 
 - <b>`simgr`</b>:  the simulation manager 
 - <b>`successors`</b>:  the successors to check 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/directed_search.py#L32"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `setup`

```python
setup(simgr)
```

Setup the technique. 

**Args:**
 
 - <b>`simgr`</b>:  the simulation manager 




---

_This file was automatically generated via [lazydocs](https://github.com/ml-tooling/lazydocs)._
