<!-- markdownlint-disable -->

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/prioritizer.py#L0"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

# <kbd>module</kbd> `greed.exploration_techniques.prioritizer`






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/prioritizer.py#L8"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `Prioritizer`
This Exploration technique implements a DFS with prioritization of states. The prioritization is done by a scoring function that is applied to each state. For instance, the scoring function can be the distance (in basic blocks) from a target statement. 

**Args:**
 
 - <b>`scoring_function`</b>:  the scoring function 
 - <b>`deferred_stash`</b>:  the name of the stash where deferred states are put 

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/prioritizer.py#L17"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(scoring_function, deferred_stash='deferred')
```








---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/prioritizer.py#L28"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `check_stashes`

```python
check_stashes(simgr, stashes, stash='active')
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/prioritizer.py#L52"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `is_complete`

```python
is_complete(simgr, stash='active')
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/prioritizer.py#L24"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `setup`

```python
setup(simgr)
```








---

_This file was automatically generated via [lazydocs](https://github.com/ml-tooling/lazydocs)._
