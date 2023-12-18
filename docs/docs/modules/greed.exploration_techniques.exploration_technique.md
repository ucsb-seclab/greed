<!-- markdownlint-disable -->

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/exploration_technique.py#L0"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

# <kbd>module</kbd> `greed.exploration_techniques.exploration_technique`






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/exploration_technique.py#L1"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `ExplorationTechnique`
Base Exploration Technique 

ALL THE STANDARD METHODS ARE NOT SUPPOSED TO BE CALLED MANUALLY 




---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/exploration_technique.py#L20"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `check_stashes`

```python
check_stashes(simgr, stashes)
```

This method receives the current active stashes that can be manipulated/re-ordered/etc... MUST return the stashes. 



**Args:**
 
 - <b>`simgr`</b>:  Simulation Manager 
 - <b>`stashes`</b>:  All the active stashes 

Returns: MUST return the stashes. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/exploration_technique.py#L34"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `check_state`

```python
check_state(simgr, state)
```

This method receives the state that we are going to generate the successors for. MUST return the state. 



**Args:**
 
 - <b>`simgr`</b>:  Simulation Manager 
 - <b>`state`</b>:  State that we are going to generate the successors for 

Returns: MUST return the state. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/exploration_technique.py#L48"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `check_successors`

```python
check_successors(simgr, successors)
```

This method receives all the successors generated from a step of a state. MUST return the successors. 



**Args:**
 
 - <b>`simgr`</b>:  Simulation Manager 
 - <b>`successors`</b>:  All the successors generated from a step of a state 

Returns: MUST return the filtered successors 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/exploration_technique.py#L62"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `is_complete`

```python
is_complete(simgr)
```

This method indicate when the ET is done. If you just want to be done when there are no active states, just return True. 



**Args:**
 
 - <b>`simgr`</b>:  Simulation Manager 

Returns: Completion state 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/exploration_technique.py#L7"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `setup`

```python
setup(simgr)
```

Any operations that needs to be done on the simulation manager before starting the exploration with this technique. 



**Args:**
 
 - <b>`simgr`</b>:  Simulation Manager 

Returns: None 




---

_This file was automatically generated via [lazydocs](https://github.com/ml-tooling/lazydocs)._
