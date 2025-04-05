"""
greed.analyse.safemath_funcs.patch

This module contains logic to patch SAFEMATH operations in a target contract
with our custom sim-procedures.

In practice, we accomplish this by inventing new opcodes for each of the
safemath operators. We then replace the body of the target function with
a single block that contains the new opcode, and a return.

For example, in pseudo-code

```
func add(a, b):
    c := a + b
    if c < a:
        revert
    return c
```

becomes

```
func add(a, b):
    c := SAFEADD(a, b)
    return c
```
"""

from .safe_ops import patch_function

