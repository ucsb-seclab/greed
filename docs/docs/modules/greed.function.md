<!-- markdownlint-disable -->

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/function.py#L0"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

# <kbd>module</kbd> `greed.function`






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/function.py#L15"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `TAC_Function`
This class represents a TAC function. 

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/function.py#L19"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(
    id: str,
    signature: str,
    name: str,
    public: bool,
    blocks: List[Block],
    arguments: List[str]
)
```



**Args:**
 
 - <b>`id`</b>:  The id of the function 
 - <b>`signature`</b>:  The signature of the function 
 - <b>`name`</b>:  The name of the function 
 - <b>`public`</b>:  Whether the function is public or not 
 - <b>`blocks`</b>:  The list of blocks that compose the function 
 - <b>`arguments`</b>:  The list of arguments of the function 




---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/function.py#L61"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `build_cfg`

```python
build_cfg(factory: Factory, tac_block_succ: Mapping[str, List[str]])
```

Building the intra-functional CFG of a target function. 

**Args:**
 
 - <b>`factory`</b>:  The factory object 
 - <b>`tac_block_succ`</b>:  The mapping between block ids and their successors 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/function.py#L85"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `build_use_def_graph`

```python
build_use_def_graph()
```

Building the use-def graph of a target function. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/function.py#L126"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `dump_use_def_graph`

```python
dump_use_def_graph(filename)
```

Dump the use-def graph to a .dot file. 

**Args:**
 
 - <b>`filename`</b>:  The name of the output file. 




---

_This file was automatically generated via [lazydocs](https://github.com/ml-tooling/lazydocs)._
