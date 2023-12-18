<!-- markdownlint-disable -->

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/flow_ops.py#L0"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

# <kbd>module</kbd> `greed.TAC.flow_ops`






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/flow_ops.py#L18"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `TAC_Jump`
This class represents a JUMP TAC statement. 




---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/base.py#L25"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `handle`

```python
handle(state: SymbolicEVMState)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/flow_ops.py#L31"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `TAC_Jumpi`







---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/base.py#L36"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `handle`

```python
handle(state: SymbolicEVMState)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/flow_ops.py#L88"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `TAC_BaseCall`
This class represents super class for all CALL TAC statements. 




---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/flow_ops.py#L158"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `set_likeyl_known_target_func`

```python
set_likeyl_known_target_func(target_function)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/flow_ops.py#L161"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `TAC_Call`







---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/base.py#L174"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `handle`

```python
handle(state: SymbolicEVMState)
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/flow_ops.py#L158"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `set_likeyl_known_target_func`

```python
set_likeyl_known_target_func(target_function)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/flow_ops.py#L181"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `TAC_Callcode`







---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/base.py#L194"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `handle`

```python
handle(state: SymbolicEVMState)
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/flow_ops.py#L158"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `set_likeyl_known_target_func`

```python
set_likeyl_known_target_func(target_function)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/flow_ops.py#L199"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `TAC_Delegatecall`







---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/base.py#L211"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `handle`

```python
handle(state: SymbolicEVMState)
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/flow_ops.py#L158"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `set_likeyl_known_target_func`

```python
set_likeyl_known_target_func(target_function)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/flow_ops.py#L218"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `TAC_Staticcall`







---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/base.py#L230"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `handle`

```python
handle(state: SymbolicEVMState)
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/TAC/flow_ops.py#L158"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `set_likeyl_known_target_func`

```python
set_likeyl_known_target_func(target_function)
```








---

_This file was automatically generated via [lazydocs](https://github.com/ml-tooling/lazydocs)._
