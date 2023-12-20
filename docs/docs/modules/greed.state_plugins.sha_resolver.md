<!-- markdownlint-disable -->

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/sha_resolver.py#L0"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

# <kbd>module</kbd> `greed.state_plugins.sha_resolver`






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/sha_resolver.py#L9"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `ShaSolution`




<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/sha_resolver.py#L10"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(symbol_name, argOffset, argSize, inputBuffer, shaResult)
```









---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/sha_resolver.py#L21"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `ShaResolver`
A plugin that finds solutions for the observed sha3 operations in  a SimState. 

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/sha_resolver.py#L27"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(breakpoints_stmt_ids=None, breakpoints_stmt=None)
```








---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/sha_resolver.py#L33"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `clear_sha_frame`

```python
clear_sha_frame()
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/sha_resolver.py#L30"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `clear_solutions`

```python
clear_solutions()
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/sha_resolver.py#L133"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `copy`

```python
copy()
```

Deep copy this state plugin. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/sha_resolver.py#L38"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `fix_shas`

```python
fix_shas()
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/state_plugins/sha_resolver.py#L128"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `get_keccak256`

```python
get_keccak256(input_buffer, sha_size)
```








---

_This file was automatically generated via [lazydocs](https://github.com/ml-tooling/lazydocs)._
