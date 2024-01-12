
from collections import defaultdict

from greed import options
from greed.memory import LambdaMemory
from greed.solver.shortcuts import *
from greed.utils.extra import UUIDGenerator


class Sha3(LambdaMemory):
    """
    This class represents the memory used as a input buffer for the SHA3 operation.
    (SHA3 needs to be of type LambdaMemory to allow the (bounded) comparison between two SHA(s) (see ca. line 50))
    """
    uuid_generator = UUIDGenerator()

    def __init__(self, state=None, memory=None, start=None, size=None, partial_init=False):
        """
        Args:
            state: The SimState that triggers the SHA3 operation
            memory: The memory associated to the SimState
            start: The start of the input buffer for the SHA3 operation
            size: The size of the input buffer for the SHA3 operation
            partial_init: Whether to partially initialize the object or not
        """

        self.cache = defaultdict(dict)

        if partial_init:
            return 

        self.uuid = Sha3.uuid_generator.next()

        super().__init__(tag=f"SHA3_{self.uuid}_MEMORY", value_sort=BVSort(8), default=BVV(0, 8), state=state)
        self.symbol = BVS(f"SHA3_{self.uuid}", 256)

        self.state = state
        
        # The source memory where we are fetching data from
        self.memory = memory.copy(new_state=self.state)
        # Where to start to hash in the source memory
        self.start = start
        # How much we should hash 
        self.size = size

        # limit max size to max_size
        self.max_size = options.MAX_SHA_SIZE
        self.add_constraint(BV_ULE(self.size, BVV(self.max_size, 256)))

        # Let's start to copy at offset 0 of this lambda memory (it's _base) the amount 
        # of bytes 'size' starting from 'start'
        self.memcopy(BVV(0, 256), self.memory.copy(state), start, size)

        self.is_concrete = False

        # TODO: we somehow want to make sure that there is never a constraint of the type SHA3_<x> == 0xhardcoded

    def instantiate_ackermann_constraints(self, other):
        """
        This method instantiates the Ackermann constraints between the two SHA(s).
        Args:
            other: The other SHA3 object
        """
        assert isinstance(other, Sha3)

        sha_data_len_is_equal = Equal(self.size, other.size)

        # Here we are building the final formula that summarizes the (bounded) comparison between the two SHA(s)
        # This instantiates the lambda constraints using as a reading offsets all the indexes in the range (0, max_size)
        bounded_bytes_are_equal = list()
        for i in range(self.max_size):
            bounded_bytes_are_equal.append(Equal(self[BVV(i, 256)], other[BVV(i, 256)]))

        sha_equal = Equal(self.symbol, other.symbol)
        sha_not_equal = NotEqual(self.symbol, other.symbol)

        #sha_distance = If(BV_UGE(self.symbol, other.symbol), 
        #                        BV_Sub(self.symbol, other.symbol),
        #                        BV_Sub(other.symbol, self.symbol))

        #sha_distance_more_than_x = BV_SGT(sha_distance, BVV(options.MIN_SHA_DISTANCE, 256))

        bounded_ackermann_constraint = If(And(*([sha_data_len_is_equal] + bounded_bytes_are_equal)),
                                          sha_equal,
                                          sha_not_equal)
        self.add_constraint(bounded_ackermann_constraint)
    
    def copy(self, new_state):
        """
        Deep copy of the object.
        Args:
            new_state: The new state
        """
        new_sha_memory = Sha3(partial_init=True)
        new_sha_memory.uuid = self.uuid
        new_sha_memory.tag = self.tag
        new_sha_memory._base = self._base
        new_sha_memory.state = new_state
        new_sha_memory.root_lambda_constraint = self.root_lambda_constraint.copy(new_state=new_state)
        new_sha_memory._constraints = list(self._constraints)
        new_sha_memory.write_count = self.write_count
        new_sha_memory.read_count = self.read_count
        new_sha_memory.symbol = self.symbol

        new_sha_memory.memory = self.memory.copy(new_state=new_state)

        new_sha_memory.start = self.start
        new_sha_memory.size = self.size
        new_sha_memory.max_size = self.max_size

        new_sha_memory.is_concrete = self.is_concrete

        for width in self.cache:
            new_sha_memory.cache[width].update(self.cache[width])

        return new_sha_memory
