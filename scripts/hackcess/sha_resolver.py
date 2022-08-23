
import logging 
import networkx as nx 
import sha3 

from SEtaac.utils.solver.shortcuts import *

log = logging.getLogger("ShaResolver")
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

        self.sha_deps = nx.DiGraph() if not sha_deps else sha_deps

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
    
    # Zero sum solver frames.
    def detect_sha_dependencies(self):
        
        sha_deps = self.sha_deps

        if len(sha_deps.nodes) != 0:
            log.info("sha_deps already initialized.")
            return

        state = self.state

        if len(state.sha_observed) == 1:
            # Well, we are done.
            sha_deps.add_node(state.sha_observed[0])

        log.info("Checking SHA dependecies")

        for curr_sha in state.sha_observed:
            state.solver.push()
            log.info(f"Checking dependencies for {curr_sha.symbol.name}")
            sha_deps.add_node(curr_sha)

            # Get a model for our SHA
            self._fix_sha(curr_sha)

            # Now, let's see what happened to the other SHAs
            for other_sha in state.sha_observed:
                if other_sha.symbol.name == curr_sha.symbol.name:
                    # Skip the current SHA under analysis
                    continue
                if sha_deps.has_edge(other_sha, curr_sha):
                    # OPTIMIZATION: if sha1 depends from sha2, sha2 CANNOT depend from sha1, so skip that.
                    continue

                # Can this other SHA still be concretized to 0? If yes, constraining the 
                # input buffer of 'sha_observed' didn't influence this SHA, hence, there 
                # is no dependency between these two SHAs.
                sha_model.add(Equal(other_sha.symbol, BVV(0,256)))
                if state.solver.are_formulas_sat(list(sha_model)):
                    continue
                else:
                    # Register the dependency
                    log.info(f"{curr_sha.symbol.name} depends from {other_sha.symbol.name}")
                    sha_deps.add_node(other_sha)
                    sha_deps.add_edge(curr_sha, other_sha)

            state.solver.pop()
        
        # We'll leave this clean
        assert(state.solver.frame == self.starting_frame)

        # We save the transitive reduction :)
        self.sha_deps = nx.transitive_reduction(sha_deps)

    def fix_shas(self):

        state = self.state
        state.solver.push()

        sha_model = list()

        last_shas = [sha for sha in self.sha_deps.nodes() if self.sha_deps.out_degree(sha) == 0]

        for sha_observed in last_shas:
            log.debug(f" Fixing {sha_observed.symbol.name}")
            sha_model.append(self._fix_sha(sha_observed))
            for pred_sha in nx.ancestors(self.sha_deps, sha_observed):
                log.debug(f" Fixing {pred_sha.symbol.name}")
                sha_models.append(self._fix_sha(pred_sha))
        
        # Save this model
        self.sha_models[self.num_models] = sha_model

        # Return the last generated model for SHAs
        return sha_model
        
    def _fix_sha(self, sha_observed):
        
        state = self.state

        # Null size doesn't make any sense for SHA, let's rule this out
        state.add_constraint(NotEqual(sha_observed.size, BVV(0,256)))

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
            for sol in sha_model:
                if sol.symbol_name == sha_observed.symbol.name:
                    log.debug(f"Skipping solution for {sol.symbol_name}")
                    blocked_solutions.append(sol.inputBuffer)
        
        # Blocking already provided solutions
        # You can clean this throug the clear_solutions API
        for blocked_solution in blocked_solutions:
            state.add_constraint(NotEqual(blocked_solution, sha_observed.readn(BVV(0,256), sha_size)))
        
        if not state.solver.is_sat():
            log.fatal("No solutions for SHAs")
            return ShaSolution()

        sha_input_buffer = state.solver.eval_memory_at(sha_observed, BVV(0,256), sha_size, raw=True)

        log.debug(f"Buffer for {sha_observed.symbol.name} set at {hex(bv_unsigned_value(sha_input_buffer))}")
        log.debug(f"  [{sha_observed.symbol.name}] calculating concrete SHA")
        sha_result = self.get_keccak256(sha_input_buffer, sha_size)
        log.debug(f"    [{sha_observed.symbol.name}] concrete SHA is {sha_result}")

        # Set constraints accordingly
        state.add_constraint(Equal(sha_observed.start, sha_arg_offset))
        state.add_constraint(Equal(sha_observed.size, sha_size))

        for x,b in zip(range(0, bv_unsigned_value(sha_size)), 
                                bv_unsigned_value(sha_input_buffer).to_bytes(bv_unsigned_value(sha_size), 'big')):
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

