import logging

from SEtaac.solver.shortcuts import *

log = logging.getLogger(__name__)


class LambdaConstraint:
    """
    Base class for uninstantiated constraints (see the LambdaMemory class)

    Extending the Theory of Arrays: memset, memcpy, and Beyond
    (https://llbmc.org/files/papers/VSTTE13.pdf)
    see 5.3 "Instantiating Quantifiers"
    """
    def __init__(self, array=None, new_array=None, parent=None):
        self.following_writes = dict()

        self.array = array
        self.new_array = new_array
        self.parent = parent

        self.depth = 1
        node = self.parent
        while node is not None:
            self.depth += 1
            node = node.parent

    def instantiate(self, index):
        """
        Instantiate the constraint (on read)
        Args:
            index: The read index

        Returns: All instantiated constraints (recursively from the LambdaConstraint hierarchy)

        """
        return []

    def copy(self, new_state):
        new_parent = None if self.parent is None else self.parent.copy(new_state=new_state)
        new_lambda_constraint = LambdaConstraint(array=self.array, new_array=self.new_array, parent=new_parent)
        return new_lambda_constraint

    def __str__(self):
        return f"[{len(self.following_writes)} following writes]\n" \
               f"LambdaConstraint"


class LambdaMemsetConstraint(LambdaConstraint):
    """
    Uninstantiated memset constraint
    """
    def __init__(self, array, start, value, size, new_array, parent):
        super().__init__(array, new_array, parent)
        self.start = start
        self.value = value
        self.size = size

    def instantiate(self, index):
        if index in self.following_writes:
            return []

        index_in_range = And(BV_ULE(self.start, index), BV_ULT(index, BV_Add(self.start, self.size)))
        instance = Equal(Array_Select(self.new_array, index),
                         If(index_in_range,
                            self.value,
                            Array_Select(self.array, index)))

        return [instance] + self.parent.instantiate(index)

    def copy(self, new_state):
        new_parent = None if self.parent is None else self.parent.copy(new_state=new_state)
        new_lambda_constraint = LambdaMemsetConstraint(array=self.array, start=self.start, value=self.value, size=self.size,
                                                       new_array=self.new_array, parent=new_parent)
        return new_lambda_constraint

    def __str__(self):
        return f"[{len(self.following_writes)} following writes]\n" \
               f"LambdaMemsetInfiniteConstraint(old:{self.array.pp()},new:{self.new_array.pp()},start:{self.start.pp()},size:{self.size.pp()},value:{self.value.pp()})\n" \
               f"{self.parent}"


class LambdaMemsetInfiniteConstraint(LambdaConstraint):
    """
    Uninstantiated memset infinite constraint
    """
    def __init__(self, array, start, value, new_array, parent):
        super().__init__(array, new_array, parent)
        self.start = start
        self.value = value

    def instantiate(self, index):
        if index in self.following_writes:
            return []

        index_in_range = BV_ULE(self.start, index)
        instance = Equal(Array_Select(self.new_array, index),
                         If(index_in_range,
                            self.value,
                            Array_Select(self.array, index)))

        return [instance] + self.parent.instantiate(index)

    def copy(self, new_state):
        new_parent = None if self.parent is None else self.parent.copy(new_state=new_state)
        new_lambda_constraint = LambdaMemsetInfiniteConstraint(array=self.array, start=self.start, value=self.value,
                                                               new_array=self.new_array, parent=new_parent)
        return new_lambda_constraint

    def __str__(self):
        return f"[{len(self.following_writes)} following writes]\n" \
               f"LambdaMemsetInfiniteConstraint(old:{self.array.pp()},new:{self.new_array.pp()},start:{self.start.pp()},value:{self.value.pp()})\n" \
               f"{self.parent}"


class LambdaMemcopyConstraint(LambdaConstraint):
    """
    Uninstantiated memcopy constraint
    """
    def __init__(self, array, start, source, source_start, size, new_array, parent):
        super().__init__(array, new_array, parent)
        self.start = start
        # WARNING: memcopy source is of type "memory", CALLER SHOULD TAKE CARE OF .copy()ing IT
        self.source = source
        self.source_start = source_start
        self.size = size

    def instantiate(self, index):
        if index in self.following_writes:
            return []

        index_in_range = And(BV_ULE(self.start, index), BV_ULT(index, BV_Add(self.start, self.size)))

        shift_to_source_offset = BV_Sub(self.source_start, self.start)
        
        instance = Equal(Array_Select(self.new_array, index),
                         If(index_in_range,
                            # memcopy source is of type "memory", don't access directly as an array
                            self.source[BV_Add(index, shift_to_source_offset)],
                            Array_Select(self.array, index)))

        return [instance] + self.parent.instantiate(index)

    def copy(self, new_state):
        new_parent = None if self.parent is None else self.parent.copy(new_state=new_state)
        new_source = self.source.copy(new_state=new_state)
        new_lambda_constraint = LambdaMemcopyConstraint(array=self.array, start=self.start, source=new_source,
                                                        source_start=self.source_start, size=self.size,
                                                        new_array=self.new_array, parent=new_parent)
        return new_lambda_constraint

    def __str__(self):
        return f"[{len(self.following_writes)} following writes]\n" \
               f"LambdaMemsetInfiniteConstraint(old:{self.array.pp()},new:{self.new_array.pp()},start:{self.start.pp()},size:{self.size.pp()},source:{self.source.tag},source_start:{self.source_start.pp()})\n" \
               f"{self.parent}"


class LambdaMemcopyInfiniteConstraint(LambdaConstraint):
    """
    Uninstantiated memcopy infinite constraint
    """
    def __init__(self, array, start, source, source_start, new_array, parent):
        super().__init__(array, new_array, parent)
        self.start = start
        # WARNING: memcopy source is of type "memory", CALLER SHOULD TAKE CARE OF .copy()ing IT
        self.source = source
        self.source_start = source_start

    def instantiate(self, index):
        if index in self.following_writes:
            return []

        index_in_range = BV_ULE(self.start, index)
        shift_to_source_offset = BV_Sub(self.source_start, self.start)
    
        instance = Equal(Array_Select(self.new_array, index),
                         If(index_in_range,
                            # memcopy source is of type "memory", don't access directly as an array
                            self.source[BV_Add(index, shift_to_source_offset)],
                            Array_Select(self.array, index)))

        return [instance] + self.parent.instantiate(index)

    def copy(self, new_state):
        new_parent = None if self.parent is None else self.parent.copy(new_state=new_state)
        new_source = self.source.copy(new_state=new_state)
        new_lambda_constraint = LambdaMemcopyInfiniteConstraint(array=self.array, start=self.start, source=new_source,
                                                                source_start=self.source_start,
                                                                new_array=self.new_array, parent=new_parent)
        return new_lambda_constraint

    def __str__(self):
        return f"[{len(self.following_writes)} following writes]\n" \
               f"LambdaMemsetInfiniteConstraint(old:{self.array.pp()},new:{self.new_array.pp()},start:{self.start.pp()},source:{self.source.tag},source_start:{self.source_start.pp()})\n" \
               f"{self.parent}"
