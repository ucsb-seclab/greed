import logging
from typing import TYPE_CHECKING

from collections import defaultdict

from greed.memory.lambda_constraint import (
    LambdaConstraint,
    LambdaMemsetConstraint,
    LambdaMemsetInfiniteConstraint,
    LambdaMemcopyConstraint,
    LambdaMemcopyInfiniteConstraint,
)
from greed.solver.shortcuts import *
from greed.utils.extra import UUIDGenerator

log = logging.getLogger(__name__)

if TYPE_CHECKING:
    from greed.state import SymbolicEVMState


class LambdaMemory:
    """
    Implementation of an instantiation-based lambda memory

    Extending the Theory of Arrays: memset, memcpy, and Beyond
    (https://llbmc.org/files/papers/VSTTE13.pdf)
    see 5.3 "Instantiating Quantifiers"

    This is a memory implementation with memset/memsetinfinite/memcpy/memcpyinfinite primitives

    To provide such primitives, we generate constraints such as "for all indices in the copied range,
    read from the source array, else read from the old array"

    To make such constraints compatible with a Quantifier-Free logic, we use an instantiation-based approach,
    with layers of "uninstantiated constraints". The constraints are then instantiated ON READ (i.e., after reading
    index 42: "if 42 is in the copied range, read from the source array, else read from the old array").

    Two successive copies can overlap with each other (RANGES CAN BE SYMBOLIC), which is why the layered architecture
    -and possibly useless constraints- are needed.

    Example:
        memcopy(start1, end1, source1, memory1)
        # uninstantiated constraints: "for all indices i in (start1, end1), memory2[i] == source1[i], else memory2[i] == memory1[i]"
        # instantiated constraints:

        memcopy(start2, end2, source2, memory2)
        # uninstantiated constraints: "for all indices i in (start1, end1), memory2[i] == source1[i], else memory2[i] == memory1[i]"
                                      "for all indices i in (start2, end2), memory3[i] == source2[i], else memory3[i] == memory2[i]"
        # instantiated constraints:

        read(42) --> return memory3[42]
        # uninstantiated constraints: "for all indices i in (start1, end1), memory2[i] == source1[i], else memory2[i] == memory1[i]"
                                      "for all indices i in (start2, end2), memory3[i] == source2[i], else memory3[i] == memory2[i]"
        # instantiated constraints:   "if 42 in (start1, end1), memory2[42] == source1[42], else memory2[42] == memory1[42]"
                                      "if 42 in (start2, end2), memory3[42] == source2[42], else memory3[42] == memory2[42]"
    """

    uuid_generator = UUIDGenerator()
    state: "SymbolicEVMState"

    def __init__(
        self, tag=None, value_sort=None, default=None, state=None, partial_init=False
    ):
        """
        Initialize the LambdaMemory.
        Args:
            tag: the tag of the memory, this is a unique identifier.
            value_sort: the sort type of the values in the memory (e.g., BVSort(8))
            default: the default value of the memory when no writes have been performed
            state: the SimState to which this memory belongs
            partial_init: if True, do not initialize the memory
        """
        if partial_init:
            return
        assert (
            tag is not None and value_sort is not None
        ), "Invalid LambdaMemory initialization"

        self.tag = tag
        self.value_sort = value_sort

        self.state = state

        self.root_lambda_constraint = LambdaConstraint()
        self._constraints = list()

        self.cache = defaultdict(dict)

        self._base = Array(
            f"{self.tag}_{LambdaMemory.uuid_generator.next()}_{self.layer_level}",
            BVSort(256),
            value_sort,
        )
        if default is not None:
            # use memsetinfinite to make this a ConstArray with default BVV(0, 8)
            self.memsetinfinite(BVV(0, 256), default)

        self.write_count = 0
        self.read_count = 0

    def add_constraint(self, formula):
        """
        Add a constraint to the memory.
        Args:
            formula: the constraint to add
        """
        self.state.solver.add_memory_constraint(formula)

    def add_constraints(self, formulas):
        """
        Add constraints to the memory.
        Args:
            formulas: the constraints to add
        """
        for formula in formulas:
            self.add_constraint(formula)

    def invalidate_cache(self, start=None, end=None):
        """
        Invalidate the cache range.
        """

        # if cache is empty, do nothing
        if len(self.cache) == 0:
            return

        # invalidate cache if range fully unspecified or fully symbolic
        if start is None and end is None:  # range fully unspecified
            self.cache = defaultdict(dict)
            return
        elif (
            start is not None
            and not is_concrete(start)
            and end is not None
            and not is_concrete(end)
        ) and self.state.solver.is_formula_sat(  # range fully symbolic
            BV_ULE(start, BVV(max(self.cache[1] or [0]), 256))
        ):  # could overlap with any cache slot
            self.cache = defaultdict(dict)
            return
        elif (
            start is not None
            and not is_concrete(start)
            and end is not None
            and not is_concrete(end)
        ):  # range fully symbolic
            # don't invalidate if cannot overlap with any cache slot
            return

        # else invalidate only the impacted cache slots
        if start is None or not is_concrete(start):
            start = BVV(0, 256)
        if end is None or not is_concrete(end):
            end = BVV(2**256 - 1, 256)
        start = bv_unsigned_value(start)
        end = bv_unsigned_value(end)
        for width in self.cache:
            for k in list(self.cache[width]):
                # if there is any overlap between [k, k+width) and [start, end), invalidate
                if any([start <= k + i < end for i in range(width)]):
                    del self.cache[width][k]

    @property
    def layer_level(self):
        """
        How many layers of lambda constraints are there?
        Returns:
            the number of layers
        """
        return self.root_lambda_constraint.depth - 1

    @property
    def constraints(self):
        """
        Get the constraints of the memory.
        Returns:
            the constraints
        """
        return self._constraints

    def __getitem__(self, index):
        """
        Read from the memory at a specific index.
        This will instantiate the lambda constraints at the index for the current layer.
        Args:
            index: the index to read from
        Returns:
            an Array_Select formula representing the read to that index
        """
        assert not isinstance(index, slice), "slice memory read not implemented"
        self.read_count += 1

        # check cache
        if is_concrete(index) and bv_unsigned_value(index) in self.cache[1]:
            return self.cache[1][bv_unsigned_value(index)]

        # instantiate and add lambda constraints
        new_constraints = self.root_lambda_constraint.instantiate(index)
        self.add_constraints(new_constraints)

        return Array_Select(self._base, index)

    def __setitem__(self, index, v):
        """
        Write to the memory at a specific index.
        This will register a write in the "following_writes" (caching).
        Args:
            index: the index to write to
            v: the value to write
        Returns:
            an Array_Store formula representing the write to that index
        """
        self.write_count += 1

        # update cache
        self.invalidate_cache(start=index, end=BV_Add(index, BVV(1, 256)))
        if is_concrete(index):
            self.cache[1][bv_unsigned_value(index)] = v

        self.root_lambda_constraint.following_writes[index] = v
        self._base = Array_Store(self._base, index, v)

    def readn(self, index, n):
        """
        Read n bytes from the memory at a specific index.
        Args:
            index: the index to read from
            n: the number of bytes to read
        Returns:
            a BV_Concat formula representing the read
        Raises:
            AssertionError: if the length is symbolic
            AssertionError: if the length is 0
        """
        assert is_concrete(n), "readn with symbolic length not implemented"
        n_val = bv_unsigned_value(n)
        assert n_val != 0, "invalid readn with length=0"

        # check cache
        if (
            is_concrete(index)
            and bv_unsigned_value(index) in self.cache[n_val]
        ):
            # print(f"cache hit {bv_unsigned_value(index)}: {self.cache[n_val][bv_unsigned_value(index)]}")
            return self.cache[n_val][bv_unsigned_value(index)]

        if n_val == 1:
            return self[index]
        else:
            vv = []
            if is_concrete(index):
                tag = f"READN_{self.tag}_BASE{self._base.id}_{bv_unsigned_value(index)}_{n_val}"

                # Optimization: attempt to read in word-size chunks, which is more cache-friendly
                index_val = bv_unsigned_value(index)
                for idx in range(index_val, index_val + n_val, 32):
                    # If we can read a whole chunk, try the cache
                    if idx + 32 <= index_val + n_val and idx in self.cache[32]:
                        vv.append(self.cache[32][idx])
                    else:
                        # We cannot read a chunk, just do it the normal way
                        for pos in range(idx, min(idx + 32, index_val + n_val)):
                            vv.append(self[BVV(pos, 256)])
            else:
                tag = f"READN_{self.tag}_BASE{self._base.id}_sym{index.id}_{n_val}"
                vv = list()
                for i in range(n_val):
                    read_index = BV_Add(index, BVV(i, 256))
                    vv.append(self[read_index])

            res = BVS(tag, n_val * 8)

            self.add_constraint(Equal(res, BV_Concat(vv)))
            # print(f"actual readn {bv_unsigned_value(index)}:{n_val} = {BV_Concat(vv)}")
            return res
 
    def writen(self, index, v, n):
        """Writes n bytes of a value (v) at a offset in memory (index). 
        
        Args:
            index: A YicesTermBV representing the offset in memory to write to.
            v: A YicesTermBV representing the value to write to memory.
            n: A YicesTermBVV representing the number of bytes to write to in memory.
        """
        assert is_concrete(n), "writen with symbolic length not implemented"
        assert bv_unsigned_value(n) != 0, "invalid writen with length=0"
        n_val = bv_unsigned_value(n)

        self.invalidate_cache(start=index, end=BV_Add(index, n))

        for i in range(n_val):
            m = BV_Extract((n_val - 1 - i) * 8, (n_val - 1 - i) * 8 + 7, v)
            self[BV_Add(index, BVV(i, 256))] = m

        # update cache
        if is_concrete(index):
            # print(f"caching writen {bv_unsigned_value(index)}:{bv_unsigned_value(n)} = {v}")
            self.cache[bv_unsigned_value(n)][bv_unsigned_value(index)] = v

    def memset(self, start, value, size):
        """
        Perform a memset operation
        Args:
            start: the start index
            value: the value to write
            size: the number of bytes to write
        """
        old_base = self._base
        self._base = Array(
            f"{self.tag}_{LambdaMemory.uuid_generator.next()}_{self.layer_level}",
            BVSort(256),
            BVSort(8),
        )

        # update cache
        self.invalidate_cache(start=start, end=BV_Add(start, size))

        self.root_lambda_constraint = LambdaMemsetConstraint(
            old_base, start, value, size, self._base, parent=self.root_lambda_constraint
        )

    def memsetinfinite(self, start, value):
        """
        Perform a memsetinfinite operation
        Args:
            start: the start index
            value: the value to write
        """
        old_base = self._base
        self._base = Array(
            f"{self.tag}_{LambdaMemory.uuid_generator.next()}_{self.layer_level}",
            BVSort(256),
            BVSort(8),
        )

        # update cache
        self.invalidate_cache(start=start)

        self.root_lambda_constraint = LambdaMemsetInfiniteConstraint(
            old_base, start, value, self._base, parent=self.root_lambda_constraint
        )

    def memcopy(self, start, source, source_start, size):
        """
        Perform a memcopy operation
        Args:
            start: the start index
            source: the source memory
            source_start: the start index of the source memory
            size: the number of bytes to copy
        Raises:
            AssertionError: if the source memory is different from the current memory
        """
        assert source != self, "ERROR: memcopy source was not copied"
        old_base = self._base
        self._base = Array(
            f"{self.tag}_{LambdaMemory.uuid_generator.next()}_{self.layer_level}",
            BVSort(256),
            BVSort(8),
        )

        # update cache
        self.invalidate_cache(start=start, end=BV_Add(start, size))

        self.root_lambda_constraint = LambdaMemcopyConstraint(
            old_base,
            start,
            source,
            source_start,
            size,
            self._base,
            parent=self.root_lambda_constraint,
        )

    def memcopyinfinite(self, start, source, source_start):
        """
        Perform a memcopyinfinite operation
        Args:
            start: the start index
            source: the source memory
            source_start: the start index of the source memory
        Raises:
            AssertionError: if the source memory is different from the current memory
        """
        assert source != self, "ERROR: memcopy source was not copied"
        old_base = self._base
        self._base = Array(
            f"{self.tag}_{LambdaMemory.uuid_generator.next()}_{self.layer_level}",
            BVSort(256),
            BVSort(8),
        )

        # update cache
        self.invalidate_cache(start=start)

        self.root_lambda_constraint = LambdaMemcopyInfiniteConstraint(
            old_base,
            start,
            source,
            source_start,
            self._base,
            parent=self.root_lambda_constraint,
        )

    def copy(self, new_state):
        """
        Perform a deep copy of the memory.
        Args:
            new_state: the state to which the new memory belongs
        Returns:
            A deep copy of the LambdaMemory
        """
        new_memory = LambdaMemory(partial_init=True)
        new_memory.tag = self.tag
        new_memory._base = self._base
        new_memory.state = new_state
        new_memory.root_lambda_constraint = self.root_lambda_constraint.copy(
            new_state=new_state
        )
        new_memory._constraints = list(self._constraints)
        new_memory.cache = defaultdict(dict)
        for width in self.cache:
            new_memory.cache[width].update(self.cache[width])
        new_memory.write_count = self.write_count
        new_memory.read_count = self.read_count

        return new_memory

    def __str__(self):
        return f"LambdaMemory\n" f"{self.root_lambda_constraint}"
