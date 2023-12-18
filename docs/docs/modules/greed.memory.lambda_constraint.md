<!-- markdownlint-disable -->

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_constraint.py#L0"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

# <kbd>module</kbd> `greed.memory.lambda_constraint`






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_constraint.py#L8"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `LambdaConstraint`
Base class for uninstantiated constraints (see the LambdaMemory class) 

Extending the Theory of Arrays: memset, memcpy, and Beyond (https://llbmc.org/files/papers/VSTTE13.pdf) see 5.3 "Instantiating Quantifiers" 

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_constraint.py#L16"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(array=None, new_array=None, parent=None)
```








---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_constraint.py#L39"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `copy`

```python
copy(new_state)
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_constraint.py#L29"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `instantiate`

```python
instantiate(index)
```

Instantiate the constraint (on read) 

**Args:**
 
 - <b>`index`</b>:  The read index 

**Returns:**
 All instantiated constraints (recursively from the LambdaConstraint hierarchy) 


---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_constraint.py#L49"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `LambdaMemsetConstraint`
Uninstantiated memset constraint 

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_constraint.py#L53"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(array, start, value, size, new_array, parent)
```



**Args:**
 
 - <b>`array`</b>:  the SMT array on which the memset is applied 
 - <b>`start`</b>:  the start index 
 - <b>`value`</b>:  the value to write 
 - <b>`size`</b>:  how many bytes to write 
 - <b>`new_array`</b>:  the new array (after the memset) 
 - <b>`parent`</b>:  the parent LambdaConstraint 




---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_constraint.py#L85"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `copy`

```python
copy(new_state)
```

Copy the constraint (on state copy) 

**Args:**
 
 - <b>`new_state`</b>:  the new state 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_constraint.py#L68"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `instantiate`

```python
instantiate(index)
```

Instantiate the constraint (on read) 

**Args:**
 
 - <b>`index`</b>:  The read index 


---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_constraint.py#L102"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `LambdaMemsetInfiniteConstraint`
Uninstantiated memset infinite constraint 

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_constraint.py#L106"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(array, start, value, new_array, parent)
```



**Args:**
 
 - <b>`array`</b>:  the SMT array on which the memset is applied 
 - <b>`start`</b>:  the start index 
 - <b>`value`</b>:  the value to write 
 - <b>`new_array`</b>:  the new array (after the memset) 
 - <b>`parent`</b>:  the parent LambdaConstraint 




---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_constraint.py#L136"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `copy`

```python
copy(new_state)
```

Copy the constraint (on state copy) 

**Args:**
 
 - <b>`new_state`</b>:  the new state 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_constraint.py#L119"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `instantiate`

```python
instantiate(index)
```

Instantiate the constraint (on read) 

**Args:**
 
 - <b>`index`</b>:  The read index 


---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_constraint.py#L153"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `LambdaMemcopyConstraint`
Uninstantiated memcopy constraint 

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_constraint.py#L157"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(array, start, source, source_start, size, new_array, parent)
```



**Args:**
 
 - <b>`array`</b>:  the SMT array src 
 - <b>`start`</b>:  the start index 
 - <b>`source`</b>:  the source array 
 - <b>`source_start`</b>:  the start index of the source array 
 - <b>`size`</b>:  how many bytes to write 
 - <b>`new_array`</b>:  the SMT array target of the memcopy 
 - <b>`parent`</b>:  the parent LambdaConstraint 




---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_constraint.py#L196"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `copy`

```python
copy(new_state)
```

Copy the constraint (on state copy) 

**Args:**
 
 - <b>`new_state`</b>:  the new state 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_constraint.py#L175"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `instantiate`

```python
instantiate(index)
```

Instantiate the constraint (on read) 

**Args:**
 
 - <b>`index`</b>:  The read index 


---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_constraint.py#L215"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `LambdaMemcopyInfiniteConstraint`
Uninstantiated memcopy infinite constraint 

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_constraint.py#L219"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(array, start, source, source_start, new_array, parent)
```



**Args:**
 
 - <b>`array`</b>:  the SMT array src 
 - <b>`start`</b>:  the start index 
 - <b>`source`</b>:  the source array 
 - <b>`source_start`</b>:  the start index of the source array 
 - <b>`new_array`</b>:  the SMT array target of the memcopy 
 - <b>`parent`</b>:  the parent LambdaConstraint 




---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_constraint.py#L255"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `copy`

```python
copy(new_state)
```

Copy the constraint (on state copy) 

**Args:**
 
 - <b>`new_state`</b>:  the new state 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_constraint.py#L235"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `instantiate`

```python
instantiate(index)
```

Instantiate the constraint (on read) 

**Args:**
 
 - <b>`index`</b>:  The read index 




---

_This file was automatically generated via [lazydocs](https://github.com/ml-tooling/lazydocs)._
