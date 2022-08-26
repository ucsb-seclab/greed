import logging

from SEtaac import options
from SEtaac.solver.shortcuts import *
from SEtaac.state_plugins import SimStatePlugin

log = logging.getLogger(__name__)


class SimStateSolver(SimStatePlugin):
    def __init__(self, partial_init=False):
        super(SimStateSolver, self).__init__()

        if partial_init:
            # Used for copy
            return

        if options.SOLVER == options.SOLVER_YICES2:
            from SEtaac.solver import Yices2
            self._solver = Yices2()
        else:
            raise Exception(f"Unsupported solver {options.SOLVER}. Aborting.")

        # The solver backend
        assert(self._solver is not None)

        self._curr_frame_level = 0

        # Keep constraints organized in frames
        self._path_constraints = dict()
        self._memory_constraints = dict()
        
        self._path_constraints[0] = set()
        self._memory_constraints[0] = set()
    
    def _add_assertion(self, assertion):
        # Adding the constraint to the backend
        self._solver.add_assertion(assertion)

    def push(self):
        self._curr_frame_level += 1
        self._path_constraints[self._curr_frame_level] = set()
        self._memory_constraints[self._curr_frame_level] = set()
        self._solver.push()
        return self._curr_frame_level

    def pop(self):
        if self._curr_frame_level == 0:
            log.fatal("Cannot pop() level 0 frame")
            return self._curr_frame_level
        else:
            del self._path_constraints[self._curr_frame_level]
            del self._memory_constraints[self._curr_frame_level]
            self._curr_frame_level -= 1
            self._solver.pop()
            return self._curr_frame_level
    
    def add_path_constraints(self, constraint):
        self._path_constraints[self._curr_frame_level].add(constraint)
        self._add_assertion(constraint)

    def add_memory_constraints(self, constraint):
        self._memory_constraints[self._curr_frame_level].add(constraint)
        self._add_assertion(constraint)

    @property
    def frame(self):
        return self._curr_frame_level

    # returns path constraints
    # If frame is None, returns ALL the currently active constraints,
    # otherwise, just return the constraints at a specific frame.
    @property
    def path_constraints(self, frame: int = None):
        if not frame:
            all_csts = [c_set for c_set in self._path_constraints.values()]
            return list(set().union(*all_csts))
        else:
            return list(self._path_constraints[frame])

    # returns memory constraints
    # If frame is None, returns ALL the currently active constraints,
    # otherwise, just return the constraints at a specific frame.
    @property
    def memory_constraints(self, frame=None):
        if not frame:
            all_csts = [c_set for c_set in self._memory_constraints.values()]
            return list(set().union(*all_csts))
        else:
            return list(self._memory_constraints[frame])
    
    # returns ALL the active constraints in all the stashes
    @property
    def constraints(self, frame=None):
        if not frame:
            all_path_csts = [c_set for c_set in self._path_constraints.values()]
            all_mem_csts = [c_set for c_set in self._memory_constraints.values()]
            all_path_csts.extend(all_mem_csts)
            return list(set().union(*all_path_csts))
        else:
            path_csts = self._path_constraints[frame]
            mem_csts = self._memory_constraints[frame]
            return list(path_csts.union(mem_csts))

    def is_concrete(self, term) -> bool:
        return self._solver.is_concrete(term)

    def is_sat(self) -> bool:
        return self._solver.is_sat()

    def is_unsat(self) -> bool:
        return self._solver.is_unsat()

    def is_formula_sat(self, formula) -> bool:
        return self._solver.is_formula_sat(formula)

    def are_formulas_sat(self, terms) -> bool:
        return self._solver.are_formulas_sat(terms)

    def is_formula_unsat(self, formula) -> bool:
        return self._solver.is_formula_unsat(formula)

    def is_formula_true(self, formula) -> bool:
        return self._solver.is_formula_true(formula)

    def is_formula_false(self, formula) -> bool:
        return self._solver.is_formula_false(formula)

    def eval(self, term, raw=False):
        return self._solver.eval(term, raw)
    
    def eval_memory(self, memory, length, raw=False):
        assert(self.is_concrete(length))
        memory_to_eval = memory.readn(BVV(0, 256), length)
        return self.eval(memory_to_eval, raw=raw)

    def eval_memory_at(self, array, offset, length, raw=False):
        assert(self.is_concrete(offset))
        assert(self.is_concrete(length))
        memory_to_eval = array.readn(offset, length)
        return self.eval(memory_to_eval, raw=raw)

    def copy(self):
        new_solver = SimStateSolver(partial_init=True)
        new_solver._solver = self._solver  # no need to copy if solver is stateless

        new_solver._curr_frame_level = 0
        new_solver._path_constraints = dict()
        new_solver._memory_constraints = dict()
        new_solver._path_constraints[new_solver._curr_frame_level] = set()
        new_solver._memory_constraints[new_solver._curr_frame_level] = set()
        
        # Re-add all the constraints (Maybe one day Yices2 will do it for us with 
        # a full Context clone, as of now this is the "cloning dei poveri".
        while True:
            for path_constraint in self._path_constraints[new_solver._curr_frame_level]:
                new_solver.add_path_constraints(path_constraint)
            for mem_constraint in self._memory_constraints[new_solver._curr_frame_level]:
                new_solver.add_memory_constraints(mem_constraint)
            
            if new_solver._curr_frame_level == self._curr_frame_level:
                break
            else: 
                # Add the next frame
                new_solver.push()

        return new_solver
    



