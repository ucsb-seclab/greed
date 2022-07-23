import logging

import networkx as nx

from SEtaac.TAC.TAC_parser import TAC_parser
from SEtaac.factory import Factory
from SEtaac.utils.solver.bitwuzla import Bitwuzla
from SEtaac.utils.solver.z3 import Z3
from SEtaac.utils.solver.shortcuts import *

log = logging.getLogger(__name__)


class Project(object):
    def __init__(self, target_dir: str):
        # Load the contract code
        with open(f"{target_dir}/contract.hex", "rb") as contract_file:
            self.code = contract_file.read()

        self.factory = Factory(project=self)

        # set the default solver
        set_solver(Bitwuzla)

        tac_parser = TAC_parser(self.factory, target_dir)
        self.statement_at = tac_parser.parse_statements()
        self.block_at = tac_parser.parse_blocks()
        self.function_at = tac_parser.parse_functions()

        # build callgraph
        self.callgraph = nx.DiGraph()
        for source_function_id, source_function in self.function_at.items():
            for target_function_id in source_function.callprivate_target_sources.keys():
                target_function = self.factory.function(target_function_id)
                self.callgraph.add_edge(source_function, target_function)
