import logging

import networkx as nx
import sha3

from SEtaac.solver.shortcuts import *

log = logging.getLogger(__name__)
log.setLevel(logging.INFO)

class ShaSolution():
    def __init__(self, symbol_name, argOffset, argSize, inputBuffer, shaResult):
        # The value are stored "raw" to let you plug into formulas
        self.symbol_name = symbol_name
        self.argOffset = argOffset
        self.argSize = argSize 
        self.inputBuffer = inputBuffer
        self.shaResult = shaResult
    
    def __repr__(self):
        return f"{self.symbol} | inputBuffer {hex(bv_unsigned_value(self.inputBuffer))} | SHA3 {hex(bv_unsigned_value(self.shaResult))}"


class ShaResolver():
    def __init__(self, state, sha_deps=None, sha_models=None):
        self.state = state
        self.starting_frame = self.state.solver.frame

        # Mantaining sha solutions 
        # <argOffset, argSize, inputBuffer, shaResult>
        # This is a dict of list of ShaSolutions
        # sha_models[0] = [ShaSolution(SHA1), ShaSolution(SHA2)...]
        # sha_models[1] = [ShaSolution(SHA1), ShaSolution(SHA2)...]
        self.sha_models = sha_models if sha_models else dict()
        self.num_models = len(self.sha_models.keys())
    
    def clear_solutions(self):
        self.sha_models = dict()
    
    def clear_sha_frame(self):
        self.state.solver.pop()
    
    # This method fixes the SHAs in chronological order.
    # WARNING: it adds constraints to the state in a new frame.
    def fix_shas(self):
        log.debug("Calling fix_shas")
        state = self.state
        state.solver.push()

        # Store here the new generated model
        sha_model = list()

        # Just fix the SHAs in chronological order
        for sha_observed in state.sha_observed:
            log.debug(f" Fixing {sha_observed.symbol.name}")
            sha_sol = self._fix_sha(sha_observed)
            if sha_sol:
                sha_model.append(sha_sol)
            else:
                return None
        
        # Save this model in the global dict
        self.sha_models[self.num_models] = sha_model

        # Return the last generated model for SHAs
        return sha_model
    
    # This method fixes a specific sha_observed.
    # WARNING: it adds constraints to the state in the current frame!
    def _fix_sha(self, sha_observed) -> ShaSolution:
        
        state = self.state

        assert(state.solver.frame != 0)

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

        # Let's exclude previous solutions for the inputBuffer for this SHA
        blocked_solutions = []
        
        for sha_model in self.sha_models.values():
            log.debug("We have {} models in the sha solutions")
            for sol in sha_model:
                if sol.symbol_name == sha_observed.symbol.name:
                    log.debug(f"Skipping solution for {sol.symbol_name}")
                    blocked_solutions.append(sol.inputBuffer)
        
        # Blocking already provided solutions
        # You can clean this through the clear_solutions API
        for blocked_solution in blocked_solutions:
            state.add_constraint(NotEqual(blocked_solution, sha_observed.readn(BVV(0,256), sha_size)))
        
        if not state.solver.is_sat():
            log.fatal("No solutions for SHAs")
            return None

        sha_input_buffer = state.solver.eval_memory_at(sha_observed, BVV(0,256), sha_size, raw=True)

        log.debug(f"  [{sha_observed.symbol.name}] Buffer for {sha_observed.symbol.name} set at {hex(bv_unsigned_value(sha_input_buffer))}")
        log.debug(f"  [{sha_observed.symbol.name}] calculating concrete SHA")
        sha_result = self.get_keccak256(sha_input_buffer, sha_size)
        log.debug(f"  [{sha_observed.symbol.name}] concrete SHA is {sha_result}")

        # Set constraints accordingly
        state.add_constraint(Equal(sha_observed.start, sha_arg_offset))
        state.add_constraint(Equal(sha_observed.size, sha_size))

        #log.debug(f"  Setting constraints to {sha_observed.symbol.name} input")
        for x,b in zip(range(0, bv_unsigned_value(sha_size)), 
                                bv_unsigned_value(sha_input_buffer).to_bytes(bv_unsigned_value(sha_size), 'big')):
            #log.debug(f"    Constraining byte {x}")
            state.add_constraint(Equal(sha_observed[BVV(x,256)], BVV(b,8)))

        # Finally set the SHA result
        state.add_constraint(Equal(sha_observed.symbol, BVV(int(sha_result,16),256)))

        return ShaSolution(sha_observed.symbol.name, sha_arg_offset, sha_size, sha_input_buffer, BVV(int(sha_result,16),256))
    
    def get_keccak256(self, input_buffer, sha_size):
        keccak256 = sha3.keccak_256()
        input_buffer = bv_unsigned_value(input_buffer).to_bytes(bv_unsigned_value(sha_size), 'big')
        keccak256.update(input_buffer)
        res = keccak256.hexdigest()
        return res

