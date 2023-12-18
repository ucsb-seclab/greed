<!-- markdownlint-disable -->

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/inspect.py#L0"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

# <kbd>module</kbd> `greed.state_plugins.inspect`




**Global Variables**
---------------
- **OP_BEFORE**
- **OP_AFTER**


---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/inspect.py#L11"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `SimStateInspect`
A plugin that allows for breakpoints to be set on statements. 

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/inspect.py#L16"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(breakpoints_stmt_ids=None, breakpoints_stmt=None)
```








---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/inspect.py#L52"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `copy`

```python
copy()
```

Deep copy this state plugin. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/inspect.py#L37"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `stop_at_stmt`

```python
stop_at_stmt(stmt_name=None, func=None, when=0)
```

Stop at a statement with a given name (e.g., CALL) 

**Args:**
 
 - <b>`stmt_name`</b>:  The name of the statement to stop at. 
 - <b>`func`</b>:  The function to call when the breakpoint is hit (default: ipdb.set_trace()) 
 - <b>`when`</b>:  Whether to stop before or after the statement. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/inspect.py#L22"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `stop_at_stmt_id`

```python
stop_at_stmt_id(stmt_id=None, func=None, when=0)
```

Stop at a statement with a given ID (i.e., PC) 

**Args:**
 
 - <b>`stmt_id`</b>:  The ID of the statement to stop at. 
 - <b>`func`</b>:  The function to call when the breakpoint is hit (default: ipdb.set_trace()) 
 - <b>`when`</b>:  Whether to stop before or after the statement. 




---

_This file was automatically generated via [lazydocs](https://github.com/ml-tooling/lazydocs)._
