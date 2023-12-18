<!-- markdownlint-disable -->

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/base.py#L0"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

# <kbd>module</kbd> `greed.TAC.base`






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/base.py#L12"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `Aliased`
This class allows us to use aliases for the attributes of a class. For example, if we have a class with the following attributes: ['a', 'b', 'c'], we can define a dictionary __aliases__ = {'x': 'a', 'y': 'b'} and then access the attributes of the class using the aliases.  





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/base.py#L35"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `TAC_Statement`
This class represents a TAC Statement. 

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/base.py#L41"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(
    block_id: str,
    stmt_id: str,
    uses: List[str] = None,
    defs: List[str] = None,
    values: Mapping[str, str] = None
)
```



**Args:**
 
 - <b>`block_id`</b>:  The id of the block that contains this statement. 
 - <b>`stmt_id`</b>:  The id of this statement. 
 - <b>`uses`</b>:  The list of variables used by this statement. 
 - <b>`defs`</b>:  The list of variables defined by this statement. 
 - <b>`values`</b>:  The static values of the variables used by this statement. 




---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/base.py#L184"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `copy`

```python
copy(alias_arg_map=None)
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/base.py#L164"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `handler_with_side_effects`

```python
handler_with_side_effects(
    func: Callable[[ForwardRef('TAC_Statement'), SymbolicEVMState], List[SymbolicEVMState]]
)
```

Decorator that executes the basic functionalities for handlers with side effects (can't just read and return statically computed results). 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/base.py#L131"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `handler_without_side_effects`

```python
handler_without_side_effects(
    func: Callable[[ForwardRef('TAC_Statement'), SymbolicEVMState], List[SymbolicEVMState]]
)
```

Decorator that executes the basic functionalities for handlers without side effects (can just read and return statically computed results). 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/base.py#L82"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `process_args`

```python
process_args()
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/base.py#L98"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `reset_arg_val`

```python
reset_arg_val()
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/base.py#L107"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `set_arg_val`

```python
set_arg_val(state: SymbolicEVMState)
```








---

_This file was automatically generated via [lazydocs](https://github.com/ml-tooling/lazydocs)._
