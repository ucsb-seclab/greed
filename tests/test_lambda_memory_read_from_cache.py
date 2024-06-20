"""
Tests LambdaMemory's ability to use cache to avoid doing array ops
"""

from greed.state_plugins import SimStateSolver
from greed.solver.shortcuts import *
from greed.memory import LambdaMemory

def test_basic_store_read():
    """
    Tests basic operation: we can store a value and read (the exact same value) back
    """
    mem = _get_dummy_memory()

    to_write = BVV(0xDEADBEEFCAFE, 256)

    mem.writen(
        BVV(0, 256),
        to_write,
        BVV(32, 256),
    )

    read = mem.readn(
        BVV(0, 256),
        BVV(32, 256),
    )

    # We should have the same value that we wrote, because it was cached
    assert read.id == to_write.id

def test_readn_reads_words_from_cache():
    """
    Ensure that readn() reads and concats from cache when possible, avoiding
    any array operations.
    """
    mem = _get_dummy_memory()

    # Write two values to memory
    to_write_1 = BVV(0xDEADBEEFCAFE, 256)
    to_write_2 = BVV(0xCAFEBABE, 256)

    mem.writen(
        BVV(0, 256),
        to_write_1,
        BVV(32, 256),
    )
    mem.writen(
        BVV(32, 256),
        to_write_2,
        BVV(32, 256),
    )

    read = mem.readn(
        BVV(0, 256),
        BVV(64, 256),
    )

    # We should have a symbol
    assert read.operator == 'bvs'

    # The solver should not have any array operations -- dfs through the
    # current assertions to ensure
    queue = list(mem.state.solver.constraints)

    while queue:
        constraint = queue.pop(0)

        if getattr(constraint, 'operator', None) == 'array':
            raise AssertionError('Array operation found in solver')

        queue.extend(getattr(constraint, 'children', []))
    
    # The value should be the concatenation of the two values
    value = mem.state.solver.eval(read)
    expected = (0xDEADBEEFCAFE << 256) | 0xCAFEBABE
    assert hex(value) == hex(expected)

def test_readn_uses_array_fallback():
    """
    Test that when no cache is available, readn will fall back to using array
    operations.
    """
    mem = _get_dummy_memory()

    # Write one value to memory
    to_write = BVV(0xDEADBEEFCAFE, 256)
    mem.writen(
        BVV(0, 256),
        to_write,
        BVV(32, 256),
    )

    # Read unaligned
    read = mem.readn(
        BVV(10, 256),
        BVV(32, 256),
    )

    # We should have a symbol
    assert read.operator == 'bvs'

    # There should be an array op in the solver
    queue = list(mem.state.solver.constraints)
    while queue:
        constraint = queue.pop(0)

        if getattr(constraint, 'operator', None) == 'array':
            break

        queue.extend(getattr(constraint, 'children', []))
    else:
        raise AssertionError('Array operation not found in solver')

    # The value should be what we wrote, but shifted
    value = mem.state.solver.eval(read)
    expected = 0xDEADBEEFCAFE << (8 * 10)
    assert hex(value) == hex(expected)

_n_mems = 0
def _get_dummy_memory() -> LambdaMemory:
    global _n_mems

    ret = LambdaMemory(
        f'test_{_n_mems}',
        value_sort=BVSort(8),
        default=BVV(0, 8),
        state=DummyState()
    )

    _n_mems += 1

    return ret

class DummyState:
    def __init__(self):
        self.solver = SimStateSolver()
