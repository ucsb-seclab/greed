import logging

from greed.memory.lambda_constraint import LambdaConstraint, LambdaMemsetConstraint, LambdaMemsetInfiniteConstraint, \
    LambdaMemcopyConstraint, LambdaMemcopyInfiniteConstraint
from greed.solver.shortcuts import *
from greed.utils.extra import UUIDGenerator

log = logging.getLogger(__name__)


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

    def __init__(self, tag=None, value_sort=None, default=None, state=None, partial_init=False):
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
        assert tag is not None and value_sort is not None, "Invalid LambdaMemory initialization"

        self.tag = tag
        self.value_sort = value_sort

        self.state = state

        self.root_lambda_constraint = LambdaConstraint()
        self._constraints = list()

        self._base = Array(f"{self.tag}_{LambdaMemory.uuid_generator.next()}_{self.layer_level}", BVSort(256), value_sort)
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
        self.state.solver.add_memory_constraints(formula)

    def add_constraints(self, formulas):
        """
        Add constraints to the memory.
        Args:
            formulas: the constraints to add
        """
        for formula in formulas:
            self.add_constraint(formula)

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
        assert bv_unsigned_value(n) != 0, "invalid readn with length=0"
        if bv_unsigned_value(n) == 1:
            return self[index]
        else:
            if is_concrete(index):
                tag = f"READN_{self.tag}_BASE{self._base.id}_{bv_unsigned_value(index)}_{bv_unsigned_value(n)}"
            else:
                tag = f"READN_{self.tag}_BASE{self._base.id}_sym{index.id}_{bv_unsigned_value(n)}"

            res = BVS(tag, bv_unsigned_value(n)*8)

            vv = list()
            for i in range(bv_unsigned_value(n)):
                read_index = BV_Add(index, BVV(i, 256))
                vv.append(self[read_index])

            self.state.add_constraint(Equal(res, BV_Concat(vv)))
            return res

    def memset(self, start, value, size):
        """
        Perform a memset operation
        Args:
            start: the start index
            value: the value to write
            size: the number of bytes to write
        """
        old_base = self._base
        self._base = Array(f"{self.tag}_{LambdaMemory.uuid_generator.next()}_{self.layer_level}", BVSort(256), BVSort(8))

        self.root_lambda_constraint = LambdaMemsetConstraint(old_base, start, value, size, self._base,
                                                             parent=self.root_lambda_constraint)

    def memsetinfinite(self, start, value):
        """
        Perform a memsetinfinite operation
        Args:
            start: the start index
            value: the value to write
        """
        old_base = self._base
        self._base = Array(f"{self.tag}_{LambdaMemory.uuid_generator.next()}_{self.layer_level}", BVSort(256), BVSort(8))

        self.root_lambda_constraint = LambdaMemsetInfiniteConstraint(old_base, start, value, self._base,
                                                                     parent=self.root_lambda_constraint)

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
        self._base = Array(f"{self.tag}_{LambdaMemory.uuid_generator.next()}_{self.layer_level}", BVSort(256), BVSort(8))

        self.root_lambda_constraint = LambdaMemcopyConstraint(old_base, start, source, source_start, size, self._base,
                                                              parent=self.root_lambda_constraint)

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
        self._base = Array(f"{self.tag}_{LambdaMemory.uuid_generator.next()}_{self.layer_level}", BVSort(256), BVSort(8))

        self.root_lambda_constraint = LambdaMemcopyInfiniteConstraint(old_base, start, source, source_start, self._base,
                                                                      parent=self.root_lambda_constraint)

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
        new_memory.root_lambda_constraint = self.root_lambda_constraint.copy(new_state=new_state)
        new_memory._constraints = list(self._constraints)
        new_memory.write_count = self.write_count
        new_memory.read_count = self.read_count

        return new_memory

    def __str__(self):
        return f"LambdaMemory\n" \
               f"{self.root_lambda_constraint}"
