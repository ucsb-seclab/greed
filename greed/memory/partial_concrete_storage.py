import logging
import sys
import web3
from greed import options as opt
from greed.memory import LambdaMemory
from greed.memory.lambda_constraint import LambdaConstraint
from greed.solver.shortcuts import *
from greed.utils.exceptions import GreedException
from greed.utils.extra import UUIDGenerator

log = logging.getLogger(__name__)

    
class PartialConcreteStorage:
    """
    This class represents a partial concrete storage.
    When using the partial concrete storage, reads from the contract storage (SLOADs) are
    initialized with the concrete value on-chain (at the given block number).

    To use this, we need a web3 connection to the blockchain, the address of the contract and the block number.
    """

    uuid_generator = UUIDGenerator()

    def __init__(self, tag=None, value_sort=None, state=None, partial_init=False):
        """
        Initialize the partial concrete storage.
        Args:
            tag: The unique identifier of the storage
            value_sort: The sort of the values stored in the storage
            state: The SimState associated with this storage
            partial_init: If true, the storage is partially initialized (used for copy)
        Raises:
            GreedException: If the partial concrete storage is not initialized with the contract address and block number
            AssertionError: If the partial concrete storage is not initialized with the tag and value sort
            AssertionError: If w3 is not connected
        """

        if partial_init:
            return
        assert tag is not None and value_sort is not None, "Invalid PartialConcreteStorage initialization"

        self.tag = tag
        self.value_sort = value_sort

        self.state = state

        # Initialize the web3 connection
        self.w3 = state.project.w3
        assert(self.w3 is not None), "Web3 provider not initialized. Cannot use the partial concrete storage"
        assert(self.w3.is_connected()), "Web3 connection not connected. Cannot use the partial concrete storage"

        if "ADDRESS" not in self.state.ctx:
            raise GreedException("Cannot initialize the PartialConcreteStorage with no contract address")
        else:
            self.contract_address = self.w3.to_checksum_address(f"{state.ctx['ADDRESS'].value:040x}")

        if "NUMBER" not in self.state.ctx:
            raise GreedException("Cannot initialize the PartialConcreteStorage with no reference block")
        else:
            self.chain_at = self.state.ctx["NUMBER"].value

        self.root_lambda_constraint = LambdaConstraint()
        self._constraints = list()
        
        self._base = Array(f"{self.tag}_{PartialConcreteStorage.uuid_generator.next()}_{self.layer_level}", BVSort(256), value_sort)

        self.write_count = 0
        self.read_count = 0
        
        self.concrete_cache = dict()
    
    def add_constraint(self, formula):
        """
        Add a constraint to the storage.
        Args:
            formula: The constraint to add
        """
        self.state.solver.add_memory_constraint(formula)

    def add_constraints(self, formulas):
        """
        Add a list of constraints to the storage.
        Args:
            formulas: The list of constraints to add
        """
        for formula in formulas:
            self.add_constraint(formula)

    @property
    def layer_level(self):
        return self.root_lambda_constraint.depth - 1

    @property
    def constraints(self):
        return self._constraints

    def __getitem__(self, index):
        """
        Read from the storage at the given index (SLOAD).
        IF the index is not concrete, this instantiate the lambda constraints and return an Array_Select.
        Otherwise, it reads the concrete value from the concrete cache
        (the concrete value is initialized with the value on-chain at the given block number).

        Args:
            index: The index to read from
        Returns:
            The concreate value read from the storage (if the index is concrete)
            an Array_Select (if the index is symbolic)
        Raises:
            AssertionError: If the index is a slice
        """
        assert not isinstance(index, slice), "slice memory read not implemented"
        self.read_count += 1
        
        if is_concrete(index):
            # Grab the concrete value
            index_val = index.value
            
            if index_val not in self.concrete_cache.keys():
                log.debug(f"Concrete read from chain@{self.chain_at} for storage index [{hex(index_val)}]")
                storage_value = self.w3.eth.get_storage_at(self.contract_address, index_val, block_identifier=self.chain_at)
                log.debug(f"   Value read is: {storage_value.hex()}")
                storage_value = int(storage_value.hex(), 16)
                storage_value_bvv = BVV(storage_value, 256)
                
                self.concrete_cache[index_val] = storage_value_bvv
                return storage_value_bvv
            else:
                log.debug(f"Concrete read from concrete cache")
                return self.concrete_cache[index_val]
        
        # instantiate and add lambda constraints
        new_constraints = self.root_lambda_constraint.instantiate(index)
        self.add_constraints(new_constraints)

        return Array_Select(self._base, index)

    def __setitem__(self, index, v):
        """
        Perform a write to the storage at the given index (SSTORE).
        IF the index is not concrete, then return an Array_Store.
        Otherwise just overwrite the concrete value in the concrete cache.
        """
        self.write_count += 1

        if is_concrete(index):
            # Grab the concrete value
            index_val = index.value
            self.concrete_cache[index_val] = v
        else:
            self.root_lambda_constraint.following_writes[index] = v
            self._base = Array_Store(self._base, index, v)

    def copy(self, new_state):
        """
        Copy the partial concrete storage.
        Args:
            new_state: The new SimState associated with the new storage
        """
        new_memory = PartialConcreteStorage(partial_init=True)
        new_memory.tag = self.tag
        new_memory._base = self._base
        new_memory.state = new_state
        new_memory.root_lambda_constraint = self.root_lambda_constraint.copy(new_state=new_state)
        new_memory._constraints = list(self._constraints)
        new_memory.write_count = self.write_count
        new_memory.read_count = self.read_count
        
        # Specific attributes
        new_memory.w3 = self.w3
        new_memory.chain_at = self.chain_at
        new_memory.contract_address = self.contract_address
        new_memory.concrete_cache = dict(self.concrete_cache)
        
        return new_memory

    def __str__(self):
        return f"PartialConcreteStorage\n" \
               f"{self.root_lambda_constraint}"
