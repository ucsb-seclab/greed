import logging
import networkx as nx
from collections import defaultdict

from SEtaac.TAC.TAC_parser import TAC_parser
from SEtaac.factory import Factory

log = logging.getLogger(__name__)


class Project(object):
    def __init__(self, target_dir: str):
        # Load the contract code
        with open(f"{target_dir}/contract.hex", "rb") as contract_file:
            self.code = contract_file.read()

        self.factory = Factory(project=self)

        tac_parser = TAC_parser(self.factory, target_dir)
        self.statement_at = tac_parser.parse_statements()
        self.block_at = tac_parser.parse_blocks()
        self.function_at = tac_parser.parse_functions()

        # build callgraph
        self.callgraph = nx.DiGraph()
        self.callprivate_source_target = dict()
        self.callprivate_target_sources = dict()

        for source_function_id, source_function in self.function_at.items():
            self.callprivate_source_target[source_function_id] = dict()
            self.callprivate_target_sources[source_function_id] = defaultdict(list)
            for source_block_id, target_function_id in source_function.get_callprivate_source_target().items():
                # populate source -> target map
                self.callprivate_source_target[source_function_id][source_block_id] = target_function_id
                # populate target -> source map
                self.callprivate_target_sources[source_function_id][target_function_id].append(source_block_id)
                # populate callgraph
                self.callgraph.add_edge(source_function, self.factory.function(target_function_id))
        