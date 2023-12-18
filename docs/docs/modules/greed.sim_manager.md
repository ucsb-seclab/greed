<!-- markdownlint-disable -->

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/sim_manager.py#L0"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

# <kbd>module</kbd> `greed.sim_manager`




**Global Variables**
---------------
- **TYPE_CHECKING**


---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/sim_manager.py#L15"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `SimulationManager`
This class is the main class for running the symbolic execution. The simulation manager is responsible for keeping track of the states, and for moving them between the different stashes according to the employed exploration techniques. 

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/sim_manager.py#L22"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(entry_state: SymbolicEVMState, project)
```



**Args:**
 
 - <b>`entry_state`</b>:  The entry state of the simulation manager 
 - <b>`project`</b>:  The greed project 


---

#### <kbd>property</kbd> active



**Returns:**
  All the active states 

---

#### <kbd>property</kbd> deadended



**Returns:**
  All the deadended states (halted states) 

---

#### <kbd>property</kbd> found



**Returns:**
  All the found states (states that met the `find` condition) 

---

#### <kbd>property</kbd> one_active



**Returns:**
  First element of the active stash, or None if the stash is empty 

---

#### <kbd>property</kbd> one_deadended



**Returns:**
  First element of the deadended stash, or None if the stash is empty 

---

#### <kbd>property</kbd> one_found



**Returns:**
  First element of the found stash, or None if the stash is empty 

---

#### <kbd>property</kbd> states



**Returns:**
  All the states in the simulation manager 



---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/sim_manager.py#L276"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `findall`

```python
findall(
    find: Callable[[SymbolicEVMState], bool] = <function SimulationManager.<lambda> at 0x7fac223da5c0>,
    prune: Callable[[SymbolicEVMState], bool] = <function SimulationManager.<lambda> at 0x7fac223da660>
)
```

Run the simulation manager, until the `find` condition of all the ET is met. 

**Args:**
 
 - <b>`find`</b>:  Function that will be called after each step. The matching states will be moved to the found stash 
 - <b>`prune`</b>:  Function that will be called after each step. The matching states will be moved to the pruned stash Yield: The found states 

**Raises:**
 
 - <b>`Exception`</b>:  If something goes wrong while stepping the simulation manager 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/sim_manager.py#L128"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `move`

```python
move(
    from_stash: str,
    to_stash: str,
    filter_func: Callable[[SymbolicEVMState], bool] = <function SimulationManager.<lambda> at 0x7fac223da020>
)
```

Move all the states that meet the filter_func condition from from_stash to to_stash 

**Args:**
 
 - <b>`from_stash`</b>:  Source stash 
 - <b>`to_stash`</b>:  Destination Stash 
 - <b>`filter_func`</b>:  A function that discriminates what states should be moved 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/sim_manager.py#L234"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `run`

```python
run(
    find: Callable[[SymbolicEVMState], bool] = <function SimulationManager.<lambda> at 0x7fac223da3e0>,
    prune: Callable[[SymbolicEVMState], bool] = <function SimulationManager.<lambda> at 0x7fac223da480>,
    find_all=False
)
```

Run the simulation manager, until the `find` condition is met.  The analysis will stop when there are no more active states, some states met the `find` condition  (these will be moved to the found stash), or the exploration techniques are done. If no ET are plugged, the default searching strategy is BFS. When techniques are plugged, their methods are executed following the same order they were plugged. 

e.g., assuming we have T1 and T2.  T1(check_stashes) -> T2(check_stashes) -> T1(check_state) -> T2(check_state)  
            -> T1(check_successors) -> T2(check_successors) 



**Args:**
 
 - <b>`find`</b>:  Function that will be called after each step. The matching states will be moved to the found stash 
 - <b>`prune`</b>:  Function that will be called after each step. The matching states will be moved to the pruned stash 
 - <b>`find_all`</b>:  If True, the analysis will continue until all the ET meet the `find` condition 

**Raises:**
 
 - <b>`Exception`</b>:  If something goes wrong while stepping the simulation manager 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/sim_manager.py#L47"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `set_error`

```python
set_error(s: str)
```

Set an error to the simulation manager 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/sim_manager.py#L182"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `single_step_state`

```python
single_step_state(state: SymbolicEVMState) → List[SymbolicEVMState]
```

Step a single state (calculate its successors) 

**Args:**
 
 - <b>`state`</b>:  The state to step 

**Returns:**
 The successors of the state 

**Raises:**
 
 - <b>`Exception`</b>:  If something goes wrong while generating the successors 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/sim_manager.py#L141"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `step`

```python
step(
    find: Callable[[SymbolicEVMState], bool] = <function SimulationManager.<lambda> at 0x7fac223da160>,
    prune: Callable[[SymbolicEVMState], bool] = <function SimulationManager.<lambda> at 0x7fac223da200>
)
```

Step the simulation manager, i.e., step all the active states. 

**Args:**
 
 - <b>`find`</b>:  A function that discriminates what states should be moved to the found stash 
 - <b>`prune`</b>:  A function that discriminates what states should be moved to the pruned stash 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/sim_manager.py#L119"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `use_technique`

```python
use_technique(technique: 'ExplorationTechnique')
```

Install an exploration technique in the simulation manager. 




---

_This file was automatically generated via [lazydocs](https://github.com/ml-tooling/lazydocs)._
