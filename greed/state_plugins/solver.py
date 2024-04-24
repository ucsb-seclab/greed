import logging
from typing import Dict, List, Set, Optional, Union, TYPE_CHECKING

from greed import options
from greed.solver.shortcuts import *
from greed.state_plugins import SimStatePlugin
from greed.solver.solver import Solver, Term, BoolTerm, BVTerm

if TYPE_CHECKING:
    from greed.memory import LambdaMemory

log = logging.getLogger(__name__)


class SimStateSolver(SimStatePlugin):
    """
    A plugin that allows for constraints to be added to the state
    and unified access to the solver backend.
    """

    _solver: Solver
    _curr_frame_level: int
    _path_constraints: Dict[int, Set[BoolTerm]]
    _memory_constraints: Dict[int, Set[BoolTerm]]

    def __init__(self, partial_init=False):
        super(SimStateSolver, self).__init__()

        if partial_init:
            # Used for copy
            return

        if options.SOLVER == options.SOLVER_YICES2:
            from greed.solver import Yices2

            self._solver = Yices2()
        else:
            raise Exception(f"Unsupported solver {options.SOLVER}. Aborting.")

        # The solver backend
        assert self._solver is not None

        self._curr_frame_level = 0

        # Keep constraints organized in frames
        self._path_constraints = dict()
        self._memory_constraints = dict()

        self._path_constraints[0] = set()
        self._memory_constraints[0] = set()

    def _add_assertion(self, assertion: BoolTerm):
        """
        Adding the constraint to the backend
        Args:
            assertion: The constraint to add.
        """
        self._solver.add_assertion(assertion)

    def _add_assertions(self, assertions: List[BoolTerm]):
        """
        Adding the constraints to the backend
        Args:
            assertions: The constraints to add.
        """
        self._solver.add_assertions(assertions)

    def push(self) -> int:
        """
        Push a new frame on the solver stack.
        """
        self._curr_frame_level += 1
        self._path_constraints[self._curr_frame_level] = set()
        self._memory_constraints[self._curr_frame_level] = set()
        self._solver.push()
        return self._curr_frame_level

    def pop(self) -> int:
        """
        Pop a frame from the solver stack.
        """
        if self._curr_frame_level == 0:
            log.fatal("Cannot pop() level 0 frame")
            return self._curr_frame_level
        else:
            del self._path_constraints[self._curr_frame_level]
            del self._memory_constraints[self._curr_frame_level]
            self._curr_frame_level -= 1
            self._solver.pop()
            return self._curr_frame_level

    def pop_all(self):
        """
        Pop all the frames from the solver stack.
        """
        while self._curr_frame_level != 0:
            self.pop()

    def add_path_constraint(self, constraint: BoolTerm):
        """
        Add a path constraint to the state (at the current frame level).
        Args:
            constraint: The constraint to add.
        """
        self._path_constraints[self._curr_frame_level].add(constraint)
        self._add_assertion(constraint)

    def add_memory_constraint(self, constraint: BoolTerm):
        """
        Add a memory constraint to the state (at the current frame level).
        Args:
            constraint: The constraint to add.
        """
        self._memory_constraints[self._curr_frame_level].add(constraint)
        self._add_assertion(constraint)

    def simplify(self):
        """
        Simplify registers by replacing them with their concrete values if possible.
        """
        for reg_var, reg_val in self.state.registers.items():
            if reg_val.is_simplified is False:
                if is_concrete(reg_val):
                    # simplify to basic BVV
                    self.state.registers[reg_var] = self.state.solver.eval(reg_val, raw=True)
                else:
                    reg_val_sol = self.state.solver.eval(reg_val, raw=True)
                    if not self.state.solver.is_formula_sat(NotEqual(reg_val, reg_val_sol)):
                        self.state.registers[reg_var] = reg_val_sol
                self.state.registers[reg_var].is_simplified = True

    @property
    def timed_out(self) -> bool:
        return self._solver.timed_out

    @property
    def frame(self) -> int:
        return self._curr_frame_level

    @property
    def constraints(self) -> List[BoolTerm]:
        return self.constraints_at()

    @property
    def memory_constraints(self) -> List[BoolTerm]:
        return self.memory_constraints_at()

    @property
    def path_constraints(self) -> List[BoolTerm]:
        return self.path_constraints_at()

    def path_constraints_at(self, frame: Optional[int] = None) -> List[BoolTerm]:
        """
        Returns the path constraints at a specific frame.
        If frame is None, returns ALL the currently active path constraints.
        Args:
            frame: The frame level in the solver to check.
        """
        if not frame:
            all_csts = [c_set for c_set in self._path_constraints.values()]
            return list(set().union(*all_csts))
        else:
            return list(self._path_constraints[frame])

    def memory_constraints_at(self, frame: Optional[int] = None) -> List[BoolTerm]:
        """
        Returns the memory constraints at a specific frame.
        If frame is None, returns ALL the currently active memory constraints.
        Args:
            frame: The frame level in the solver to check.
        """
        if not frame:
            all_csts = [c_set for c_set in self._memory_constraints.values()]
            return list(set().union(*all_csts))
        else:
            return list(self._memory_constraints[frame])

    def constraints_at(self, frame: Optional[int] = None) -> List[BoolTerm]:
        """
        Returns the constraints at a specific frame or all the constraints if frame is None.
        Args:
            frame: The frame level in the solver to check.
        """
        if not frame:
            all_path_csts = [c_set for c_set in self._path_constraints.values()]
            all_mem_csts = [c_set for c_set in self._memory_constraints.values()]
            all_path_csts.extend(all_mem_csts)
            return list(set().union(*all_path_csts))
        else:
            path_csts = self._path_constraints[frame]
            mem_csts = self._memory_constraints[frame]
            return list(path_csts.union(mem_csts))

    def symbols_referenced_at(self, frame: Optional[int] = None) -> List[BVTerm]:
        """
        Returns the symbols referenced at a specific frame.
        If frame is None, returns ALL the currently active symbols.
        Args:
            frame: The frame level in the solver to check.
        """
        constraints = self.constraints_at(frame)
        
        # we need to DFS through the constraints to find all the symbols
        queue = constraints.copy()
        symbols: Dict[str, BVTerm] = {}
        while queue:
            constraint = queue.pop()
            if isinstance(constraint, BVTerm) and constraint.operator == "bvs":
                # we found a symbol
                # TODO this assumes implementation-specific knowledge (Yices2) (i.e., the name)
                symbols[constraint.name] = constraint
            else:
                # we found something else, just queue its children
                queue.extend(constraint.children)

        return list(symbols.values())

    def dispose_context(self):
        """
        Dispose the solver context.
        """
        if self._solver.solver.context:
            self._solver.solver.dispose()

    def is_concrete(self, term: Term) -> bool:
        """
        Check if a term is concrete.
        """
        return self._solver.is_concrete(term)

    def is_sat(self) -> bool:
        """
        Check if the solver is in a satisfiable state.
        """
        return self._solver.is_sat()

    def is_unsat(self) -> bool:
        """
        Check if the solver is in an unsatisfiable state.
        """
        return self._solver.is_unsat()

    def is_formula_sat(self, formula: BoolTerm) -> bool:
        """
        Check if a formula is satisfiable given the current state of the solver.
        Args:
            formula: The formula to check.
        """
        return self._solver.is_formula_sat(formula)

    def are_formulas_sat(self, terms: List[BoolTerm]) -> bool:
        """
        Check if a list of formulas is satisfiable given the current state of the solver.
        Args:
            terms: The list of formulas to check.
        """
        return self._solver.are_formulas_sat(terms)

    def is_formula_unsat(self, formula: BoolTerm) -> bool:
        """
        Check if a formula is unsatisfiable given the current state of the solver.
        Args:
            formula: The formula to check.
        """
        return self._solver.is_formula_unsat(formula)

    def is_formula_true(self, formula: BoolTerm) -> bool:
        """
        Check if a formula is true given the current state of the solver.
        Args:
            formula: The formula to check.
        """
        return self._solver.is_formula_true(formula)

    def is_formula_false(self, formula: BoolTerm) -> bool:
        """
        Check if a formula is false given the current state of the solver.
        Args:
            formula: The formula to check.
        """
        return self._solver.is_formula_false(formula)

    def eval(self, term, raw=False):
        """
        Evaluate a term.
        Args:
            term: The term to evaluate.
            raw: If True, return the raw value of the term.
        Returns:
            The evaluated term.
        """
        return self._solver.eval(term, raw)
    
    def eval_memory(self, memory, length, raw=False):
        """
        Evaluate a memory region in the memory.
        Args:
            memory: The memory region to evaluate.
            length: The length of the memory region to evaluate.
            raw: If True, return the raw value of the memory region.
        Returns:
            The evaluated memory region.
        Raises:
            AssertionError: If the length is not concrete.
        """
        assert self.is_concrete(length)
        memory_to_eval = memory.readn(BVV(0, 256), length)
        int_value = self.eval(memory_to_eval, raw=False)
        if raw is True:
            return BVV(int_value, bv_unsigned_value(length) * 8)
        else:
            return f"{int_value:0{bv_unsigned_value(length)*2}x}"

    def eval_memory_at(self, array, offset, length, raw=False):
        """
        Evaluate a portion of a memory region starting at a given offset.
        Args:
            array: The memory region to evaluate.
            offset: The offset to start evaluating from.
            length: The length of the memory region to evaluate.
            raw: If True, return the raw value of the memory region.
        Returns:
            The evaluated memory region.
        Raises:
            AssertionError: If the offset or the length is not concrete.
        """
        assert self.is_concrete(offset)
        assert self.is_concrete(length)
        memory_to_eval = array.readn(offset, length)
        int_value = self.eval(memory_to_eval, raw=False)
        if raw is True:
            return BVV(int_value, bv_unsigned_value(length) * 8)
        else:
            return f"{int_value:0{bv_unsigned_value(length)*2}x}"

    def copy(self) -> "SimStateSolver":
        """
        Deep copy this state plugin.
        """
        new_solver = SimStateSolver(partial_init=True)
        new_solver._solver = self._solver.copy()

        new_solver._curr_frame_level = 0
        new_solver._path_constraints = dict()
        new_solver._memory_constraints = dict()

        # Re-add all the constraints (Maybe one day Yices2 will do it for us with
        # a full Context clone, as of now this is the "cloning dei poveri".
        while True:
            level = new_solver._curr_frame_level
            new_solver._path_constraints[level] = set(self._path_constraints[level])
            new_solver._add_assertions(new_solver._path_constraints[level])
            new_solver._memory_constraints[level] = set(self._memory_constraints[level])
            new_solver._add_assertions(new_solver._memory_constraints[level])

            if new_solver._curr_frame_level == self._curr_frame_level:
                break
            else:
                # Add the next frame
                new_solver.push()

        return new_solver

    def dump_smt2(self, filename: str):
        """
        Dump the current state of the solver to a file.
        Args:
            filename: The file to dump the state to.
        """
        # The underlying solver (yices2) cannot iterate over its own
        # constraints in the context, so we must do that here.

        with open(filename, mode='w') as f:
            f.write("(set-logic QF_ABV)\n")
            f.write('\n')

            for symbol in self.symbols_referenced_at():
                bitwidth = symbol.bitsize
                f.write(f"(declare-fun {symbol.name} () (_ BitVec {bitwidth}))\n")
            f.write('\n')

            for c in self.constraints:
                f.write(f"(assert {c.dump_smt2()})\n")

            f.write('\n')
            f.write("(check-sat)\n")

