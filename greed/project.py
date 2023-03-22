import logging

import networkx as nx

from greed.TAC.TAC_parser import TAC_parser
from greed.TAC.gigahorse_ops import TAC_Callprivateargs
from greed.factory import Factory

log = logging.getLogger(__name__)


class Project(object):
    def __init__(self, target_dir: str):
        # Load the contract code
        with open(f"{target_dir}/contract.hex", "rb") as contract_file:
            self.code = contract_file.read()

        self.factory = Factory(project=self)

        self.tac_parser = TAC_parser(self.factory, target_dir)
        self.statement_at = self.tac_parser.parse_statements()
        self.block_at = self.tac_parser.parse_blocks()
        self.function_at = self.tac_parser.parse_functions()

        # inject CALLPRIVATEARGS fake statements
        for function in self.function_at.values():
            for arg in function.arguments[::-1]:
                root_block = self.factory.block(function.id)
                fake_statement = TAC_Callprivateargs(block_id=root_block.id, stmt_id=f"fake_{arg}", defs=[arg])
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
        
    def dump_callgraph(self, filename):
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


