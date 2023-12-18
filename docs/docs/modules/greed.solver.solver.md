<!-- markdownlint-disable -->

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L0"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

# <kbd>module</kbd> `greed.solver.solver`






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L12"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `Solver`
This class represents a solver. Every solver must implement this interface. 




---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L219"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `And`

```python
And(*terms)
```

Return an SMT And with the given terms. 

**Args:**
 
 - <b>`terms`</b>:  The terms to AND 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L173"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `Array`

```python
Array(symbol, index_sort, value_sort)
```

Return an SMT Array. 

**Args:**
 
 - <b>`symbol`</b>:  The symbol of the array 
 - <b>`index_sort`</b>:  The index sort of the array 
 - <b>`value_sort`</b>:  The value sort of the array 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L487"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `Array_Select`

```python
Array_Select(arr, index)
```

Return an SMT Array_Select with the given terms. 

**Args:**
 
 - <b>`arr`</b>:  The array to select from 
 - <b>`index`</b>:  The index to select from 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L477"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `Array_Store`

```python
Array_Store(arr, index, elem)
```

Return an SMT Array_Store with the given terms. 

**Args:**
 
 - <b>`arr`</b>:  The array to store to 
 - <b>`index`</b>:  The index to store to 
 - <b>`elem`</b>:  The element to store 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L60"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BVS`

```python
BVS(symbol, width)
```

Return a bitvector symbol of the given width. 

**Args:**
 
 - <b>`symbol`</b>:  The name of the symbol 
 - <b>`width`</b>:  The width of the symbol 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L43"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BVSort`

```python
BVSort(width)
```

Return a bitvector sort of the given width. 

**Args:**
 
 - <b>`width`</b>:  The width of the bitvector 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L51"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BVV`

```python
BVV(value, width)
```

Return a bitvector value of the given width. 

**Args:**
 
 - <b>`value`</b>:  The value of the bitvector 
 - <b>`width`</b>:  The width of the bitvector 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L253"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_Add`

```python
BV_Add(a, b)
```

Return a bitvector addition of the given bitvectors. 

**Args:**
 
 - <b>`a`</b>:  The first bitvector 
 - <b>`b`</b>:  The second bitvector 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L415"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_And`

```python
BV_And(a, b)
```

Return a bitvector bitwise and of the given bitvectors. 

**Args:**
 
 - <b>`a`</b>:  The first bitvector 
 - <b>`b`</b>:  The second bitvector 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L245"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_Concat`

```python
BV_Concat(terms)
```

Return a bitvector concatenation of the given bitvectors. 

**Args:**
 
 - <b>`terms`</b>:  The bitvectors to concatenate 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L235"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_Extract`

```python
BV_Extract(start, end, bv)
```

Return a bitvector extract of the given bitvector. 

**Args:**
 
 - <b>`start`</b>:  The start of the extract 
 - <b>`end`</b>:  The end of the extract 
 - <b>`bv`</b>:  The bitvector to extract from 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L271"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_Mul`

```python
BV_Mul(a, b)
```

Return a bitvector multiplication of the given bitvectors. 

**Args:**
 
 - <b>`a`</b>:  The first bitvector 
 - <b>`b`</b>:  The second bitvector 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L442"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_Not`

```python
BV_Not(a)
```

Return a bitvector not of the given bitvector. 

**Args:**
 
 - <b>`a`</b>:  The bitvector to not 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L424"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_Or`

```python
BV_Or(a, b)
```

Return a bitvector bitwise or of the given bitvectors. 

**Args:**
 
 - <b>`a`</b>:  The first bitvector 
 - <b>`b`</b>:  The second bitvector 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L289"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_SDiv`

```python
BV_SDiv(a, b)
```

Return a bitvector signed division of the given bitvectors. 

**Args:**
 
 - <b>`a`</b>:  The first bitvector 
 - <b>`b`</b>:  The second bitvector 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L379"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_SGE`

```python
BV_SGE(a, b)
```

Return a bitvector signed greater or equal than of the given bitvectors. 

**Args:**
 
 - <b>`a`</b>:  The first bitvector 
 - <b>`b`</b>:  The second bitvector 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L397"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_SGT`

```python
BV_SGT(a, b)
```

Return a bitvector signed greater than of the given bitvectors. 

**Args:**
 
 - <b>`a`</b>:  The first bitvector 
 - <b>`b`</b>:  The second bitvector 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L388"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_SLE`

```python
BV_SLE(a, b)
```

Return a bitvector signed less or equal than of the given bitvectors. 

**Args:**
 
 - <b>`a`</b>:  The first bitvector 
 - <b>`b`</b>:  The second bitvector 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L406"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_SLT`

```python
BV_SLT(a, b)
```

Return a bitvector signed less than of the given bitvectors. 

**Args:**
 
 - <b>`a`</b>:  The first bitvector 
 - <b>`b`</b>:  The second bitvector 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L298"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_SMod`

```python
BV_SMod(a, b)
```

Return a bitvector signed modulo of the given bitvectors. 

**Args:**
 
 - <b>`a`</b>:  The first bitvector 
 - <b>`b`</b>:  The second bitvector 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L307"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_SRem`

```python
BV_SRem(a, b)
```

Return a bitvector signed remainder of the given bitvectors. 

**Args:**
 
 - <b>`a`</b>:  The first bitvector 
 - <b>`b`</b>:  The second bitvector 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L468"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_Sar`

```python
BV_Sar(a, b)
```

Return a bitvector arithmetic shift right of the given bitvector. 

**Args:**
 
 - <b>`a`</b>:  The bitvector to shift 
 - <b>`b`</b>:  The shift amount 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L450"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_Shl`

```python
BV_Shl(a, b)
```

Return a bitvector shift left of the given bitvector. 

**Args:**
 
 - <b>`a`</b>:  The bitvector to shift 
 - <b>`b`</b>:  The shift amount 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L459"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_Shr`

```python
BV_Shr(a, b)
```

Return a bitvector shift right of the given bitvector. 

**Args:**
 
 - <b>`a`</b>:  The bitvector to shift 
 - <b>`b`</b>:  The shift amount 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L325"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_Sign_Extend`

```python
BV_Sign_Extend(a, b)
```

Return a bitvector sign extension of the given bitvector. 

**Args:**
 
 - <b>`a`</b>:  The bitvector to extend 
 - <b>`b`</b>:  The width of the extension 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L262"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_Sub`

```python
BV_Sub(a, b)
```

Return a bitvector subtraction of the given bitvectors. 

**Args:**
 
 - <b>`a`</b>:  The first bitvector 
 - <b>`b`</b>:  The second bitvector 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L280"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_UDiv`

```python
BV_UDiv(a, b)
```

Return a bitvector unsigned division of the given bitvectors. 

**Args:**
 
 - <b>`a`</b>:  The first bitvector 
 - <b>`b`</b>:  The second bitvector 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L343"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_UGE`

```python
BV_UGE(a, b)
```

Return a bitvector unsigned greater or equal than of the given bitvectors. 

**Args:**
 
 - <b>`a`</b>:  The first bitvector 
 - <b>`b`</b>:  The second bitvector 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L361"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_UGT`

```python
BV_UGT(a, b)
```

Return a bitvector unsigned greater than of the given bitvectors. 

**Args:**
 
 - <b>`a`</b>:  The first bitvector 
 - <b>`b`</b>:  The second bitvector 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L352"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_ULE`

```python
BV_ULE(a, b)
```

Return a bitvector unsigned less or equal than of the given bitvectors. 

**Args:**
 
 - <b>`a`</b>:  The first bitvector 
 - <b>`b`</b>:  The second bitvector 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L370"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_ULT`

```python
BV_ULT(a, b)
```

Return a bitvector unsigned less than of the given bitvectors. 

**Args:**
 
 - <b>`a`</b>:  The first bitvector 
 - <b>`b`</b>:  The second bitvector 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L316"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_URem`

```python
BV_URem(a, b)
```

Return a bitvector unsigned remainder of the given bitvectors. 

**Args:**
 
 - <b>`a`</b>:  The first bitvector 
 - <b>`b`</b>:  The second bitvector 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L433"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_Xor`

```python
BV_Xor(a, b)
```

Return a bitvector bitwise xor of the given bitvectors. 

**Args:**
 
 - <b>`a`</b>:  The first bitvector 
 - <b>`b`</b>:  The second bitvector 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L334"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `BV_Zero_Extend`

```python
BV_Zero_Extend(a, b)
```

Return a bitvector zero extension of the given bitvector. 

**Args:**
 
 - <b>`a`</b>:  The bitvector to extend 
 - <b>`b`</b>:  The width of the extension 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L193"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `Equal`

```python
Equal(a, b)
```

Return an SMT Equal with the given terms. 

**Args:**
 
 - <b>`a`</b>:  The first term 
 - <b>`b`</b>:  The second term 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L183"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `If`

```python
If(cond, value_if_true, value_if_false)
```

Return an SMT If. 

**Args:**
 
 - <b>`cond`</b>:  The condition formula 
 - <b>`value_if_true`</b>:  The value if the condition is True 
 - <b>`value_if_false`</b>:  The value if the condition is False 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L227"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `Not`

```python
Not(a)
```

Return an SMT Not with the given term. 

**Args:**
 
 - <b>`a`</b>:  The term to NOT 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L202"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `NotEqual`

```python
NotEqual(a, b)
```

Return an SMT NotEqual with the given terms. 

**Args:**
 
 - <b>`a`</b>:  The first term 
 - <b>`b`</b>:  The second term 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L211"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `Or`

```python
Or(*terms)
```

Return an SMT Or with the given terms. 

**Args:**
 
 - <b>`terms`</b>:  The terms to OR 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L157"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `add_assertion`

```python
add_assertion(formula)
```

Add a formula to the solver. 

**Args:**
 
 - <b>`formula`</b>:  The formula to add 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L165"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `add_assertions`

```python
add_assertions(formulas)
```

Add a list of formulas to the solver. 

**Args:**
 
 - <b>`formulas`</b>:  The list of formulas to add 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L113"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `are_formulas_sat`

```python
are_formulas_sat(terms)
```

Return True if the given formulas are satisfiable. 

**Args:**
 
 - <b>`terms`</b>:  The list of formulas to check 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L69"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `bv_unsigned_value`

```python
bv_unsigned_value(bv)
```

Return the unsigned value of the given bitvector. 

**Args:**
 
 - <b>`bv`</b>:  The bitvector to evaluate 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L504"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `copy`

```python
copy()
```

Implement the cloning of the solver when forking. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L496"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `eval`

```python
eval(term)
```

Evaluate the given term. 

**Args:**
 
 - <b>`term`</b>:  The term to evaluate 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L77"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `get_bv_by_name`

```python
get_bv_by_name(bv)
```

Return the bitvector with the given name. 

**Args:**
 
 - <b>`bv`</b>:  The name of the bitvector 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L85"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `is_concrete`

```python
is_concrete(bv)
```

Return True if the given bitvector is concrete. 

**Args:**
 
 - <b>`bv`</b>:  The bitvector to check 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L137"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `is_formula_false`

```python
is_formula_false(formula)
```

Return True if the given formula is always False. 

**Args:**
 
 - <b>`formula`</b>:  The formula to check 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L105"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `is_formula_sat`

```python
is_formula_sat(formula)
```

Return True if the given formula is satisfiable. 

**Args:**
 
 - <b>`formula`</b>:  The formula to check 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L129"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `is_formula_true`

```python
is_formula_true(formula)
```

Return True if the given formula is always True. 

**Args:**
 
 - <b>`formula`</b>:  The formula to check 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L121"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `is_formula_unsat`

```python
is_formula_unsat(formula)
```

Return True if the given formula is unsatisfiable. 

**Args:**
 
 - <b>`formula`</b>:  The formula to check 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L93"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `is_sat`

```python
is_sat()
```

Return True if the solver is in a satisfiable state. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L99"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `is_unsat`

```python
is_unsat()
```

Return True if the solver is in an unsatisfiable state. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L151"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `pop`

```python
pop()
```

Pop the current context from the solver. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L145"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `push`

```python
push()
```

Push a new context on the solver. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/solver/solver.py#L17"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `solver_timeout`

```python
solver_timeout(func)
```








---

_This file was automatically generated via [lazydocs](https://github.com/ml-tooling/lazydocs)._
