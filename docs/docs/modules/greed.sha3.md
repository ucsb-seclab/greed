<!-- markdownlint-disable -->

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/sha3.py#L0"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

# <kbd>module</kbd> `greed.sha3`






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/sha3.py#L7"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `Sha3`
This class represents the memory used as a input buffer for the SHA3 operation. (SHA3 needs to be of type LambdaMemory to allow the (bounded) comparison between two SHA(s) (see ca. line 50)) 

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/sha3.py#L14"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(state=None, memory=None, start=None, size=None, partial_init=False)
```



**Args:**
 
 - <b>`state`</b>:  The SimState that triggers the SHA3 operation 
 - <b>`memory`</b>:  The memory associated to the SimState 
 - <b>`start`</b>:  The start of the input buffer for the SHA3 operation 
 - <b>`size`</b>:  The size of the input buffer for the SHA3 operation 
 - <b>`partial_init`</b>:  Whether to partially initialize the object or not 


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

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/sha3.py#L83"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `copy`

```python
copy(new_state)
```

Deep copy of the object. 

**Args:**
 
 - <b>`new_state`</b>:  The new state 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/sha3.py#L53"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `instantiate_ackermann_constraints`

```python
instantiate_ackermann_constraints(other)
```

This method instantiates the Ackermann constraints between the two SHA(s). 

**Args:**
 
 - <b>`other`</b>:  The other SHA3 object 




---

_This file was automatically generated via [lazydocs](https://github.com/ml-tooling/lazydocs)._
