<!-- markdownlint-disable -->

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/globals.py#L0"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

# <kbd>module</kbd> `greed.state_plugins.globals`






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/globals.py#L6"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `SimStateGlobals`
A plugin that allows for global variables to be stored in the state. This will act like a dictionary. 

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/globals.py#L11"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(backer=None)
```








---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/globals.py#L85"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `copy`

```python
copy()
```

Get a deep-copy of this plugin. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/globals.py#L67"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `get`

```python
get(k, alt=None)
```

Get the value of a global variable, or return an alternative value. 

**Args:**
 
 - <b>`k`</b>:  The name of the global variable. 
 - <b>`alt`</b>:  The alternative value to return if the global variable does not exist. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/globals.py#L61"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `items`

```python
items()
```

Get the names and values of all global variables. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/globals.py#L49"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `keys`

```python
keys()
```

Get the names of all global variables. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/globals.py#L76"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `pop`

```python
pop(k, alt=None)
```

Get the value of a global variable, and remove it from the state. 

**Args:**
 
 - <b>`k`</b>:  The name of the global variable. 
 - <b>`alt`</b>:  The alternative value to return if the global variable does not exist. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/globals.py#L55"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `values`

```python
values()
```

Get the values of all global variables. 




---

_This file was automatically generated via [lazydocs](https://github.com/ml-tooling/lazydocs)._
