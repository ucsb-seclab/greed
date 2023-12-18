<!-- markdownlint-disable -->

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_memory.py#L0"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

# <kbd>module</kbd> `greed.memory.lambda_memory`






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_memory.py#L11"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `LambdaMemory`
Implementation of an instantiation-based lambda memory 

Extending the Theory of Arrays: memset, memcpy, and Beyond (https://llbmc.org/files/papers/VSTTE13.pdf) see 5.3 "Instantiating Quantifiers" 

This is a memory implementation with memset/memsetinfinite/memcpy/memcpyinfinite primitives 

To provide such primitives, we generate constraints such as "for all indices in the copied range, read from the source array, else read from the old array" 

To make such constraints compatible with a Quantifier-Free logic, we use an instantiation-based approach, with layers of "uninstantiated constraints". The constraints are then instantiated ON READ (i.e., after reading index 42: "if 42 is in the copied range, read from the source array, else read from the old array"). 

Two successive copies can overlap with each other (RANGES CAN BE SYMBOLIC), which is why the layered architecture 
-and possibly useless constraints- are needed. 



**Example:**
  memcopy(start1, end1, source1, memory1)  # uninstantiated constraints: "for all indices i in (start1, end1), memory2[i] == source1[i], else memory2[i] == memory1[i]"  # instantiated constraints: 

 memcopy(start2, end2, source2, memory2)  # uninstantiated constraints: "for all indices i in (start1, end1), memory2[i] == source1[i], else memory2[i] == memory1[i]"  "for all indices i in (start2, end2), memory3[i] == source2[i], else memory3[i] == memory2[i]"  # instantiated constraints: 

 read(42) --> return memory3[42]  # uninstantiated constraints: "for all indices i in (start1, end1), memory2[i] == source1[i], else memory2[i] == memory1[i]"  "for all indices i in (start2, end2), memory3[i] == source2[i], else memory3[i] == memory2[i]"  # instantiated constraints:   "if 42 in (start1, end1), memory2[42] == source1[42], else memory2[42] == memory1[42]"  "if 42 in (start2, end2), memory3[42] == source2[42], else memory3[42] == memory2[42]" 

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_memory.py#L49"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(
    tag=None,
    value_sort=None,
    default=None,
    state=None,
    partial_init=False
)
```

Initialize the LambdaMemory. 

**Args:**
 
 - <b>`tag`</b>:  the tag of the memory, this is a unique identifier. 
 - <b>`value_sort`</b>:  the sort type of the values in the memory (e.g., BVSort(8)) 
 - <b>`default`</b>:  the default value of the memory when no writes have been performed 
 - <b>`state`</b>:  the SimState to which this memory belongs 
 - <b>`partial_init`</b>:  if True, do not initialize the memory 


---

#### <kbd>property</kbd> constraints

Get the constraints of the memory. 

**Returns:**
  the constraints 

---

#### <kbd>property</kbd> layer_level

How many layers of lambda constraints are there? 

**Returns:**
  the number of layers 



---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_memory.py#L79"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `add_constraint`

```python
add_constraint(formula)
```

Add a constraint to the memory. 

**Args:**
 
 - <b>`formula`</b>:  the constraint to add 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_memory.py#L87"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `add_constraints`

```python
add_constraints(formulas)
```

Add constraints to the memory. 

**Args:**
 
 - <b>`formulas`</b>:  the constraints to add 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_memory.py#L240"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `copy`

```python
copy(new_state)
```

Perform a deep copy of the memory. 

**Args:**
 
 - <b>`new_state`</b>:  the state to which the new memory belongs 

**Returns:**
 A deep copy of the LambdaMemory 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_memory.py#L205"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `memcopy`

```python
memcopy(start, source, source_start, size)
```

Perform a memcopy operation 

**Args:**
 
 - <b>`start`</b>:  the start index 
 - <b>`source`</b>:  the source memory 
 - <b>`source_start`</b>:  the start index of the source memory 
 - <b>`size`</b>:  the number of bytes to copy 

**Raises:**
 
 - <b>`AssertionError`</b>:  if the source memory is different from the current memory 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_memory.py#L223"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `memcopyinfinite`

```python
memcopyinfinite(start, source, source_start)
```

Perform a memcopyinfinite operation 

**Args:**
 
 - <b>`start`</b>:  the start index 
 - <b>`source`</b>:  the source memory 
 - <b>`source_start`</b>:  the start index of the source memory 

**Raises:**
 
 - <b>`AssertionError`</b>:  if the source memory is different from the current memory 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_memory.py#L178"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `memset`

```python
memset(start, value, size)
```

Perform a memset operation 

**Args:**
 
 - <b>`start`</b>:  the start index 
 - <b>`value`</b>:  the value to write 
 - <b>`size`</b>:  the number of bytes to write 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_memory.py#L192"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `memsetinfinite`

```python
memsetinfinite(start, value)
```

Perform a memsetinfinite operation 

**Args:**
 
 - <b>`start`</b>:  the start index 
 - <b>`value`</b>:  the value to write 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/memory/lambda_memory.py#L146"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `readn`

```python
readn(index, n)
```

Read n bytes from the memory at a specific index. 

**Args:**
 
 - <b>`index`</b>:  the index to read from 
 - <b>`n`</b>:  the number of bytes to read 

**Returns:**
 a BV_Concat formula representing the read 

**Raises:**
 
 - <b>`AssertionError`</b>:  if the length is symbolic 
 - <b>`AssertionError`</b>:  if the length is 0 




---

_This file was automatically generated via [lazydocs](https://github.com/ml-tooling/lazydocs)._
