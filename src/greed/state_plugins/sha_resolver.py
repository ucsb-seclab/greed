import logging

from eth_utils import keccak
from greed.state_plugins import SimStatePlugin
from greed.solver.shortcuts import *

log = logging.getLogger(__name__)

class ShaSolution():
    def __init__(self, symbol_name, argOffset, argSize, inputBuffer, shaResult):
        # The value are stored "raw" to let you plug into formulas
        self.symbol_name = symbol_name
        self.argOffset = argOffset
        self.argSize = argSize
        self.inputBuffer = inputBuffer
        self.shaResult = shaResult

    def __repr__(self):
        return f"{self.symbol_name} | inputBuffer {hex(bv_unsigned_value(self.inputBuffer))} bufferSize {self.argSize} | SHA3 {hex(bv_unsigned_value(self.shaResult))}"

class ShaResolver(SimStatePlugin):
    """
    A plugin that finds solutions for the observed sha3 operations in 
    a SimState.
    """

    def __init__(self, breakpoints_stmt_ids=None, breakpoints_stmt=None):
        super(ShaResolver, self).__init__()

    def clear_solutions(self):
        self.sha_models = dict()

    def clear_sha_frame(self):
        self.state.solver.pop()

    # This method fixes the SHAs in chronological order.
    # WARNING: it adds constraints to the state in a new frame.
    def fix_shas(self):

        # Push a new solver frame
        self.state.solver.push()

        # Store here the new generated model
        sha_model = list()

        # Just fix the SHAs in chronological order
        for sha_observed in self.state.sha_observed:
            log.debug(f" Fixing {sha_observed.symbol.name}")
            sha_sol = self._fix_sha(sha_observed)
            if sha_sol:
                sha_model.append(sha_sol)
            else:
                # Pop the solver frame
                self.state.solver.pop()
                return None

        if len(sha_model) == 0:
            # This is the case where there are no sha_observed.
            # in this case let's just pop the solver frame
            # because we did not fix any solution
            self.state.solver.pop()
            
        return sha_model

    def _fix_sha(self, sha_observed) -> ShaSolution:

        state = self.state

        #if self.state.solver.frame == 0:
        #    panic(worker_folder, msg="Wrong frame for solver during sha resolver (==0)")

        # Null size doesn't make any sense for SHA, let's rule this out
        #state.add_constraint(NotEqual(sha_observed.size, BVV(0,256)))
        #if not state.solver.is_sat():
        #    log.critical(f"Setting the size to NOT ZERO makes everything unsat?!")
        #    assert(False)

        # Get some solutions
        log.debug(f"  [{sha_observed.symbol.name}] getting solution for argOffset")
        sha_arg_offset = state.solver.eval(sha_observed.start, raw=True)
        log.debug(f"  [{sha_observed.symbol.name}] offsetArg at {hex(bv_unsigned_value(sha_arg_offset))}")
        log.debug(f"  [{sha_observed.symbol.name}] getting solution for argSize")
        sha_size = state.solver.eval(sha_observed.size, raw=True)
        log.debug(f"  [{sha_observed.symbol.name}] argSize at {hex(bv_unsigned_value(sha_size))}")
        log.debug(f"  [{sha_observed.symbol.name}] getting solution for inputBuffer")

        if not state.solver.is_sat():
            log.fatal("No solutions for SHAs")
            return None

        null_sha = False
        if bv_unsigned_value(sha_size) == 0:
            null_sha = True
            #log.warning("SHA with 0 size!")
            # if sha_size==0 then we return the null sha.
            sha_result = "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"

        if not null_sha:
            sha_input_buffer = state.solver.eval_memory_at(sha_observed, BVV(0,256), sha_size, raw=True)
            log.debug(f"  [{sha_observed.symbol.name}] Buffer for {sha_observed.symbol.name} set at {hex(bv_unsigned_value(sha_input_buffer))}")
            log.debug(f"  [{sha_observed.symbol.name}] calculating concrete SHA")
            sha_result = self.get_keccak256(sha_input_buffer, sha_size)
            log.debug(f"  [{sha_observed.symbol.name}] concrete SHA is {sha_result}")
        else:
            sha_input_buffer = None

        # Set constraints accordingly
        state.add_constraint(Equal(sha_observed.start, sha_arg_offset))
        state.add_constraint(Equal(sha_observed.size, sha_size))

        #log.debug(f"  Setting constraints to {sha_observed.symbol.name} input")
        if not null_sha:
            for x,b in zip(range(0, bv_unsigned_value(sha_size)),
                                    bv_unsigned_value(sha_input_buffer).to_bytes(bv_unsigned_value(sha_size), 'big')):
                #log.debug(f"    Constraining byte {x}")
                state.add_constraint(Equal(sha_observed[BVV(x,256)], BVV(b,8)))

        # Finally set the SHA result
        state.add_constraint(Equal(sha_observed.symbol, BVV(int(sha_result,16),256)))

        if not state.solver.is_sat():
            log.fatal("No solutions for SHAs")
            return None
        else:
            return ShaSolution(sha_observed.symbol.name, sha_arg_offset, sha_size, sha_input_buffer, BVV(int(sha_result,16),256))


    def get_keccak256(self, input_buffer, sha_size):
        input_buffer = bv_unsigned_value(input_buffer).to_bytes(bv_unsigned_value(sha_size), 'big')
        res = bytes(keccak(input_buffer)).hex()
        return res

    def copy(self):
        """
        Deep copy this state plugin.
        """
        return ShaResolver()
