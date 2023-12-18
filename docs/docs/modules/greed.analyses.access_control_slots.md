<!-- markdownlint-disable -->

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/analyses/access_control_slots.py#L0"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

# <kbd>module</kbd> `greed.analyses.access_control_slots`





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/analyses/access_control_slots.py#L210"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `dump_slice`

```python
dump_slice(full_slice, func, filename)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/analyses/access_control_slots.py#L258"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `get_access_control_slots`

```python
get_access_control_slots(project)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/analyses/access_control_slots.py#L37"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `ReverseExplorerState`




<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/analyses/access_control_slots.py#L38"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(
    project,
    func,
    target: str,
    caller=None,
    slices_stmts=None,
    slices_vars=None
)
```








---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/analyses/access_control_slots.py#L55"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `is_stmt`

```python
is_stmt()
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/analyses/access_control_slots.py#L51"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `step`

```python
step()
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/analyses/access_control_slots.py#L63"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `ReverseExplorer`




<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/analyses/access_control_slots.py#L64"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(project, first_state)
```








---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/analyses/access_control_slots.py#L71"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `run`

```python
run()
```








---

_This file was automatically generated via [lazydocs](https://github.com/ml-tooling/lazydocs)._
