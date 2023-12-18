<!-- markdownlint-disable -->

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/block.py#L0"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

# <kbd>module</kbd> `greed.block`






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/block.py#L7"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `Block`
A TAC Basic Block. 

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/block.py#L11"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(statements: List[TAC_Statement], block_id: str)
```



**Args:**
 
 - <b>`statements`</b>:  List of TAC statements 
 - <b>`block_id`</b>:  Block id 


---

#### <kbd>property</kbd> acyclic_subgraph



**Returns:**
  Subgraph with this basic block as the root node (without cycles) 

---

#### <kbd>property</kbd> ancestors



**Returns:**
  List of ancestors blocks 

---

#### <kbd>property</kbd> descendants



**Returns:**
  List of descendants blocks 

---

#### <kbd>property</kbd> pred



**Returns:**
  List of predecessors blocks 

---

#### <kbd>property</kbd> subgraph



**Returns:**
  Subgraph with this basic block as the root node (with cycles) 

---

#### <kbd>property</kbd> succ



**Returns:**
  List of successors blocks 






---

_This file was automatically generated via [lazydocs](https://github.com/ml-tooling/lazydocs)._
