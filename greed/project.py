from typing import List, Tuple
import logging
import time
from collections import defaultdict

import networkx as nx

from greed import options as opt
from greed.factory import Factory
from greed.function import TAC_Function
from greed.TAC.gigahorse_ops import TAC_Callprivate, TAC_Callprivateargs
from greed.TAC.TAC_parser import TAC_parser

log = logging.getLogger(__name__)


class Project(object):
    """
    This is the main class for creating a greed Project!
    """
    code: str
    factory: Factory
    tac_parser: TAC_parser


    def __init__(self, target_dir: str):
        """
        Args:
            target_dir: The directory containing the contract.hex file and 
            all the GigaHorse output files.
        """
        # Load the contract code
        with open(f"{target_dir}/contract.hex", "r") as contract_file:
            self.code = bytes.fromhex(contract_file.read())

        self.factory = Factory(project=self)

        self.tac_parser = TAC_parser(self.factory, target_dir)
        self.statement_at = self.tac_parser.parse_statements()
        self.block_at = self.tac_parser.parse_blocks()
        self.function_at = self.tac_parser.parse_functions()

        # inject CALLPRIVATEARGS fake statements
        _fake_counters = defaultdict(int)
        for function in self.function_at.values():
            for arg in function.arguments[::-1]:
                root_block = self.factory.block(function.id)
                _counter = _fake_counters[arg]
                _fake_counters[arg] += 1
                fake_statement = TAC_Callprivateargs(block_id=root_block.id, stmt_id=f"fake_{arg}_{_counter}", defs=[arg])
                root_block.statements.insert(0, fake_statement)
                self.statement_at[fake_statement.id] = fake_statement
        
        # Do we have an official abi?
        self.abi = self.tac_parser.parse_abi()
        self.has_abi = (self.abi is not None)

        # build callgraph
        self.callgraph = nx.DiGraph()
        for source_function_id, source_function in self.function_at.items():
            for target_function_id in source_function.callprivate_target_sources.keys():
                target_function = self.factory.function(target_function_id)
                self.callgraph.add_edge(source_function, target_function)
        
        # NOTE: connect to w3 only on-demand
        self._w3 = None

        if opt.AUTO_PATCH_SAFEMATH:
            from greed.analyses.safemath_funcs import patch_safemath
            patch_safemath(self)

        self.sanity_check()

    @property
    def w3(self):
        if self._w3 is None:
            import web3
            self._w3 = web3.Web3(web3.Web3.HTTPProvider(opt.WEB3_PROVIDER))
            assert self._w3.is_connected()
        return self._w3

    def sanity_check(self, raise_on_failure=False) -> bool:
        """
        Perform standard sanity checks after loading a project.

        If any checks fail, this will return False. If raise_on_failure is True,
        it will also raise an exception on first failure.
        """
        t_start = time.time()
        # Tracks whether all checks passed. In order to gather more information,
        # we do not immediately return False when a check fails. Instead, we
        # continue checking, and only return False (the variable `checks_passed`) at the end.
        checks_passed = True

        #
        # Check: All CALLPRIVATE statements have the correct number of arguments
        #
        
        # First, gather all CALLPRIVATE statements
        callprivate_statements: List[TAC_Callprivate] = []
        for block in self.block_at.values():
            for statement in block.statements:
                if isinstance(statement, TAC_Callprivate):
                    callprivate_statements.append(statement)

        # Find the target function for each CALLPRIVATE statement
        callprivate_statements_with_target: List[Tuple[TAC_Callprivate, TAC_Function]] = []
        for statement in callprivate_statements:
            if not hasattr(statement, "arg1_val") or statement.arg1_val is None:
                log.debug(f"CALLPRIVATE statement {statement.id} has no known target function")
                continue

            target_block = self.factory.block(hex(statement.arg1_val.value))
            if target_block is None:
                log.debug(f"CALLPRIVATE statement {statement.id} has no known target function")
                continue

            target_function = target_block.function
            assert target_function is not None, f"Target block {target_block.id} of CALLPRIVATE statement {statement.id} has no function"

            callprivate_statements_with_target.append((statement, target_function))
        
        # Check that the number of arguments is correct
        for statement, target_function in callprivate_statements_with_target:
            if len(statement.arg_vars) - 1 != len(target_function.arguments): # NOTE: -1 because the first argument is the target block
                err_msg = f"CALLPRIVATE statement {statement.id} has {len(statement.arg_vars)} arguments, " \
                          f"but target function {target_function.id} expects {len(target_function.arguments)}"
                log.warning(err_msg)
                if raise_on_failure:
                    raise ValueError(err_msg)
                checks_passed = False

        elapsed = time.time() - t_start
        if checks_passed:
            log.debug(f"All sanity checks passed in {elapsed:.4f}s")
        else:
            log.warning(f"Some sanity checks failed in {elapsed:.4f}s")

        return checks_passed

    def dump_callgraph(self, filename):
        """
        Dump the callgraph in a dot file.
        Args:
            filename: The name of the file where to dump the callgraph.
        """
        dot = "digraph g {\n"
        dot += "splines=ortho;\n"
        dot += "node[fontname=\"courier\"];\n"
        
        for func in self.callgraph:
            color = "black"
                                    
            #label = []
            #label.append(f"func[{func.id}]: {func.signature}")
            #label = "\n".join(label)
            if func.signature != None:
                dot += f"\"{func.id}\" [shape=box, color={color}, \nlabel=\"{func.signature}\"];\n\n"
            else:
                dot += f"\"{func.id}\" [shape=box, color={color}]"

        dot += "\n"

        for a, b in self.callgraph.edges:
            dot += f"\"{a.id}\" -> \"{b.id}\";\n"

        dot += "}"

        with open(filename, "w") as dump_file:
            dump_file.write(dot)


