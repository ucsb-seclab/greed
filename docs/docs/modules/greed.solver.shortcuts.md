<!-- markdownlint-disable -->

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L0"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

# <kbd>module</kbd> `greed.solver.shortcuts`
This module provides shortcuts to the solver API to be used in greed scripts. 


---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L23"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `ctx_or_symbolic`

```python
ctx_or_symbolic(v, ctx, xid, nbits=256)
```

Given a variable name, if the var is in the context, return it,  otherwise create a new symbolic variable. 

**Args:**
 
 - <b>`v`</b>:  The variable name 
 - <b>`ctx`</b>:  The context 
 - <b>`xid`</b>:  The transaction id 
 - <b>`nbits`</b>:  The number of bits of the symbolic variable 


---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L41"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `concretize`

```python
concretize(state, val, force=False)
```

Given a value, if it is concrete, return it, otherwise  if the symbolic variable has only one possible solution, return it. If the symbolic variable has multiple possible solutions and force is True, add a constraint and return one of the possible solutions. 

**Args:**
 
 - <b>`state`</b>:  The state 
 - <b>`val`</b>:  The value 
 - <b>`force`</b>:  Whether to force the concretization 

**Returns:**
 The concrete value or None 


---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L72"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BVSort`

```python
BVSort(width)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L76"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BVV`

```python
BVV(value, width)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L80"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BVS`

```python
BVS(symbol, width)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L84"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `Array`

```python
Array(symbol, index_sort, value_sort)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L91"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `If`

```python
If(cond, value_if_true, value_if_false)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L98"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `Equal`

```python
Equal(a, b)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L102"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `NotEqual`

```python
NotEqual(a, b)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L106"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `Or`

```python
Or(*terms)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L110"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `And`

```python
And(*terms)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L114"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `Not`

```python
Not(a)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L121"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `bv_unsigned_value`

```python
bv_unsigned_value(bv)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L125"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `get_bv_by_name`

```python
get_bv_by_name(symbol)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L129"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `is_concrete`

```python
is_concrete(bv)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L133"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BV_Extract`

```python
BV_Extract(start, end, bv)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L137"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BV_Concat`

```python
BV_Concat(terms)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L141"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BV_Add`

```python
BV_Add(a, b)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L145"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BV_Sub`

```python
BV_Sub(a, b)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L149"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BV_Mul`

```python
BV_Mul(a, b)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L153"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BV_UDiv`

```python
BV_UDiv(a, b)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L157"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BV_SDiv`

```python
BV_SDiv(a, b)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L161"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BV_SMod`

```python
BV_SMod(a, b)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L165"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BV_SRem`

```python
BV_SRem(a, b)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L169"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BV_URem`

```python
BV_URem(a, b)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L173"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BV_Sign_Extend`

```python
BV_Sign_Extend(a, b)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L177"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BV_Zero_Extend`

```python
BV_Zero_Extend(a, b)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L181"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BV_UGE`

```python
BV_UGE(a, b)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L185"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BV_ULE`

```python
BV_ULE(a, b)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L189"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BV_UGT`

```python
BV_UGT(a, b)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L193"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BV_ULT`

```python
BV_ULT(a, b)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L197"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BV_SGE`

```python
BV_SGE(a, b)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L201"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BV_SLE`

```python
BV_SLE(a, b)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L205"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BV_SGT`

```python
BV_SGT(a, b)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L209"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BV_SLT`

```python
BV_SLT(a, b)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L213"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BV_And`

```python
BV_And(a, b)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L217"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BV_Or`

```python
BV_Or(a, b)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L221"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BV_Xor`

```python
BV_Xor(a, b)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L225"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BV_Not`

```python
BV_Not(a)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L229"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BV_Shl`

```python
BV_Shl(a, b)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L233"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BV_Shr`

```python
BV_Shr(a, b)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L237"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `BV_Sar`

```python
BV_Sar(a, b)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L244"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `Array_Store`

```python
Array_Store(arr, index, elem)
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/shortcuts.py#L248"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>function</kbd> `Array_Select`

```python
Array_Select(arr, index)
```








---

_This file was automatically generated via [lazydocs](https://github.com/ml-tooling/lazydocs)._
