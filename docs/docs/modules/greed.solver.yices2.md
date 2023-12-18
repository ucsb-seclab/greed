<!-- markdownlint-disable -->

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L0"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

# <kbd>module</kbd> `greed.solver.yices2`






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L12"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `YicesTerm`




<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L13"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(yices_id, operator=None, children=None, name=None, value=None)
```






---

#### <kbd>property</kbd> value







---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L35"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `dump`

```python
dump(pp=False)
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L42"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `pp`

```python
pp()
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L69"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `YicesTermBool`




<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L13"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(yices_id, operator=None, children=None, name=None, value=None)
```






---

#### <kbd>property</kbd> value







---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L35"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `dump`

```python
dump(pp=False)
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L42"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `pp`

```python
pp()
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L73"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `YicesTermBV`




<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L13"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(yices_id, operator=None, children=None, name=None, value=None)
```






---

#### <kbd>property</kbd> bitsize





---

#### <kbd>property</kbd> value







---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L35"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `dump`

```python
dump(pp=False)
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L42"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `pp`

```python
pp()
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L79"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `YicesTermArray`




<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L13"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(yices_id, operator=None, children=None, name=None, value=None)
```






---

#### <kbd>property</kbd> value







---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L35"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `dump`

```python
dump(pp=False)
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L42"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `pp`

```python
pp()
```






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L83"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `YicesType`




<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L84"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(yices_id, name)
```









---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L98"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `YicesTypeBV`




<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L84"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(yices_id, name)
```









---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L102"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `YicesTypeArray`




<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L84"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(yices_id, name)
```









---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L106"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `Yices2`
Backend for Yices2 

For the list of options see here. https://github.com/SRI-CSL/yices2/blob/bc50bebdc3aabb161328bbfc234a10da6dd3d5c4/doc/sphinx/source/context-operations.rst 

self.solver.enable_option("var-elim") self.solver.enable_option("arith-elim") self.solver.enable_option("flatten") self.solver.enable_option("assert-ite-bounds") self.solver.enable_option("eager-arith-lemmas") self.solver.enable_option("keep-ite") self.solver.enable_option("bvarith-elim") self.solver.enable_option("break-symmetries") 

cfg.set_config("arith-solver", 'simplex') 

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L125"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__()
```








---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L259"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `And`

```python
And(*terms: YicesTermBool) → YicesTermBool
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L226"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `Array`

```python
Array(symbol, index_sort: YicesTypeBV, value_sort: YicesTypeBV) → YicesTermArray
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L450"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `Array_Select`

```python
Array_Select(arr: YicesTermArray, index: YicesTermBV) → YicesTermBV
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L442"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `Array_Store`

```python
Array_Store(
    arr: YicesTermArray,
    index: YicesTermBV,
    elem: YicesTermBV
) → YicesTermArray
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L146"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BVS`

```python
BVS(symbol: str, width: int) → YicesTermBV
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L131"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BVSort`

```python
BVSort(width: int) → YicesTypeBV
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L136"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BVV`

```python
BVV(value: int, width: int) → YicesTermBV
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L291"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_Add`

```python
BV_Add(a: YicesTermBV, b: YicesTermBV) → YicesTermBV
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L399"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_And`

```python
BV_And(a: YicesTermBV, b: YicesTermBV) → YicesTermBV
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L285"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_Concat`

```python
BV_Concat(terms: List[YicesTermBV]) → YicesTermBV
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L278"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_Extract`

```python
BV_Extract(start: int, end: int, bv: YicesTermBV) → YicesTermBV
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L303"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_Mul`

```python
BV_Mul(a: YicesTermBV, b: YicesTermBV) → YicesTermBV
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L417"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_Not`

```python
BV_Not(a: YicesTermBV) → YicesTermBV
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L405"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_Or`

```python
BV_Or(a: YicesTermBV, b: YicesTermBV) → YicesTermBV
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L315"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_SDiv`

```python
BV_SDiv(a: YicesTermBV, b: YicesTermBV) → YicesTermBV
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L375"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_SGE`

```python
BV_SGE(a: YicesTermBV, b: YicesTermBV) → YicesTermBool
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L387"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_SGT`

```python
BV_SGT(a: YicesTermBV, b: YicesTermBV) → YicesTermBool
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L381"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_SLE`

```python
BV_SLE(a: YicesTermBV, b: YicesTermBV) → YicesTermBool
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L393"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_SLT`

```python
BV_SLT(a: YicesTermBV, b: YicesTermBV) → YicesTermBool
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L321"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_SMod`

```python
BV_SMod(a: YicesTermBV, b: YicesTermBV) → YicesTermBV
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L327"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_SRem`

```python
BV_SRem(a: YicesTermBV, b: YicesTermBV) → YicesTermBV
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L434"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_Sar`

```python
BV_Sar(a: YicesTermBV, b: YicesTermBV) → YicesTermBV
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L422"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_Shl`

```python
BV_Shl(a: YicesTermBV, b: YicesTermBV) → YicesTermBV
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L428"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_Shr`

```python
BV_Shr(a: YicesTermBV, b: YicesTermBV) → YicesTermBV
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L339"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_Sign_Extend`

```python
BV_Sign_Extend(a: YicesTermBV, b: int) → YicesTermBV
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L297"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_Sub`

```python
BV_Sub(a: YicesTermBV, b: YicesTermBV) → YicesTermBV
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L309"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_UDiv`

```python
BV_UDiv(a: YicesTermBV, b: YicesTermBV) → YicesTermBV
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L351"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_UGE`

```python
BV_UGE(a: YicesTermBV, b: YicesTermBV) → YicesTermBool
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L363"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_UGT`

```python
BV_UGT(a: YicesTermBV, b: YicesTermBV) → YicesTermBool
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L357"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_ULE`

```python
BV_ULE(a: YicesTermBV, b: YicesTermBV) → YicesTermBool
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L369"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_ULT`

```python
BV_ULT(a: YicesTermBV, b: YicesTermBV) → YicesTermBool
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L333"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_URem`

```python
BV_URem(a: YicesTermBV, b: YicesTermBV) → YicesTermBV
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L411"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_Xor`

```python
BV_Xor(a: YicesTermBV, b: YicesTermBV) → YicesTermBV
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L345"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_Zero_Extend`

```python
BV_Zero_Extend(a: YicesTermBV, b: int) → YicesTermBV
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L247"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `Equal`

```python
Equal(a: YicesTermBV, b: YicesTermBV) → YicesTermBool
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L236"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `If`

```python
If(
    cond: YicesTermBool,
    value_if_true: YicesTerm,
    value_if_false: YicesTerm
) → YicesTerm
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L271"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `Not`

```python
Not(a: YicesTermBool) → YicesTermBool
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L253"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `NotEqual`

```python
NotEqual(a: YicesTermBV, b: YicesTermBV) → YicesTermBool
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L265"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `Or`

```python
Or(*terms: YicesTermBool) → YicesTermBool
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L219"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `add_assertion`

```python
add_assertion(formula: YicesTermBool)
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L222"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `add_assertions`

```python
add_assertions(formulas: List[YicesTermBool])
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L153"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `bv_unsigned_value`

```python
bv_unsigned_value(bv: YicesTermBV) → int
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L464"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `copy`

```python
copy()
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L456"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `eval`

```python
eval(term: YicesTerm, raw=False)
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L161"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `get_bv_by_name`

```python
get_bv_by_name(symbol)
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L168"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `is_concrete`

```python
is_concrete(bv: YicesTermBV) → bool
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L209"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `is_formula_false`

```python
is_formula_false(formula: YicesTermBool) → bool
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L205"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `is_formula_true`

```python
is_formula_true(formula: YicesTermBool) → bool
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L216"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `pop`

```python
pop()
```





---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/yices2.py#L213"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `push`

```python
push()
```








---

_This file was automatically generated via [lazydocs](https://github.com/ml-tooling/lazydocs)._
