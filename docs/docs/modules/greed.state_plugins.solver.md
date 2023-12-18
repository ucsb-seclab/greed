<!-- markdownlint-disable -->

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/solver.py#L0"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

# <kbd>module</kbd> `greed.state_plugins.solver`






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/solver.py#L11"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `SimStateSolver`
A plugin that allows for constraints to be added to the state  and unified access to the solver backend. 

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/solver.py#L18"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(partial_init=False)
```






---

#### <kbd>property</kbd> constraints





---

#### <kbd>property</kbd> frame





---

#### <kbd>property</kbd> memory_constraints





---

#### <kbd>property</kbd> path_constraints





---

#### <kbd>property</kbd> timed_out







---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/solver.py#L99"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `add_memory_constraints`

```python
add_memory_constraints(constraint)
```

Add a memory constraint to the state (at the current frame level). 

**Args:**
 
 - <b>`constraint`</b>:  The constraint to add. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/solver.py#L90"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `add_path_constraints`

```python
add_path_constraints(constraint)
```

Add a path constraint to the state (at the current frame level). 

**Args:**
 
 - <b>`constraint`</b>:  The constraint to add. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/solver.py#L218"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `are_formulas_sat`

```python
are_formulas_sat(terms) → bool
```

Check if a list of formulas is satisfiable given the current state of the solver. 

**Args:**
 
 - <b>`terms`</b>:  The list of formulas to check. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/solver.py#L169"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `constraints_at`

```python
constraints_at(frame=None)
```

Returns the constraints at a specific frame or all the constraints if frame is None. 

**Args:**
 
 - <b>`frame`</b>:  The frame level in the solver to check. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/solver.py#L303"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `copy`

```python
copy() → SimStateSolver
```

Deep copy this state plugin. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/solver.py#L185"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `dispose_context`

```python
dispose_context()
```

Dispose the solver context. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/solver.py#L250"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `eval`

```python
eval(term, raw=False)
```

Evaluate a term. 

**Args:**
 
 - <b>`term`</b>:  The term to evaluate. 
 - <b>`raw`</b>:  If True, return the raw value of the term. 

**Returns:**
 The evaluated term. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/solver.py#L261"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `eval_memory`

```python
eval_memory(memory, length, raw=False)
```

Evaluate a memory region in the memory. 

**Args:**
 
 - <b>`memory`</b>:  The memory region to evaluate. 
 - <b>`length`</b>:  The length of the memory region to evaluate. 
 - <b>`raw`</b>:  If True, return the raw value of the memory region. 

**Returns:**
 The evaluated memory region. 

**Raises:**
 
 - <b>`AssertionError`</b>:  If the length is not concrete. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/solver.py#L281"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `eval_memory_at`

```python
eval_memory_at(array, offset, length, raw=False)
```

Evaluate a portion of a memory region starting at a given offset. 

**Args:**
 
 - <b>`array`</b>:  The memory region to evaluate. 
 - <b>`offset`</b>:  The offset to start evaluating from. 
 - <b>`length`</b>:  The length of the memory region to evaluate. 
 - <b>`raw`</b>:  If True, return the raw value of the memory region. 

**Returns:**
 The evaluated memory region. 

**Raises:**
 
 - <b>`AssertionError`</b>:  If the offset or the length is not concrete. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/solver.py#L192"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `is_concrete`

```python
is_concrete(term) → bool
```

Check if a term is concrete. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/solver.py#L242"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `is_formula_false`

```python
is_formula_false(formula) → bool
```

Check if a formula is false given the current state of the solver. 

**Args:**
 
 - <b>`formula`</b>:  The formula to check. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/solver.py#L210"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `is_formula_sat`

```python
is_formula_sat(formula) → bool
```

Check if a formula is satisfiable given the current state of the solver. 

**Args:**
 
 - <b>`formula`</b>:  The formula to check. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/solver.py#L234"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `is_formula_true`

```python
is_formula_true(formula) → bool
```

Check if a formula is true given the current state of the solver. 

**Args:**
 
 - <b>`formula`</b>:  The formula to check. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/solver.py#L226"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `is_formula_unsat`

```python
is_formula_unsat(formula) → bool
```

Check if a formula is unsatisfiable given the current state of the solver. 

**Args:**
 
 - <b>`formula`</b>:  The formula to check. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/solver.py#L198"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `is_sat`

```python
is_sat() → bool
```

Check if the solver is in a satisfiable state. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/solver.py#L204"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `is_unsat`

```python
is_unsat() → bool
```

Check if the solver is in an unsatisfiable state. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/solver.py#L156"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `memory_constraints_at`

```python
memory_constraints_at(frame=None)
```

Returns the memory constraints at a specific frame. If frame is None, returns ALL the currently active memory constraints. 

**Args:**
 
 - <b>`frame`</b>:  The frame level in the solver to check. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/solver.py#L143"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `path_constraints_at`

```python
path_constraints_at(frame: int = None)
```

Returns the path constraints at a specific frame. If frame is None, returns ALL the currently active path constraints. 

**Args:**
 
 - <b>`frame`</b>:  The frame level in the solver to check. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/solver.py#L69"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `pop`

```python
pop() → int
```

Pop a frame from the solver stack. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/solver.py#L83"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `pop_all`

```python
pop_all()
```

Pop all the frames from the solver stack. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/solver.py#L59"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `push`

```python
push() → int
```

Push a new frame on the solver stack. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/solver.py#L108"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `simplify`

```python
simplify()
```

Simplify registers by replacing them with their concrete values if possible. 




---

_This file was automatically generated via [lazydocs](https://github.com/ml-tooling/lazydocs)._
