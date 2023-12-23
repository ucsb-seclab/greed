import logging
import os

import networkx as nx
import web3

from collections import defaultdict

from greed.TAC.TAC_parser import TAC_parser
from greed.TAC.gigahorse_ops import TAC_Callprivateargs
from greed.factory import Factory
from greed import options as opt

log = logging.getLogger(__name__)


class Project(object):
    """
    This is the main class for creating a greed Project!
    """
    def __init__(self, target_dir: str):
        """
        Args:
            target_dir: The directory containing the contract.hex file and 
            all the GigaHorse output files.
        """
        # Load the contract code
        self.code = Project._load_bytecode(target_dir)

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
        
        # trying to connect to the w3 
        try:
            self.w3 = web3.Web3(web3.Web3.HTTPProvider(opt.WEB3_PROVIDER))
            if not self.w3.is_connected():
                self.w3 = None
        except Exception as e:
            self.w3 = None
        
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

    @staticmethod
    def _load_bytecode(target_dir: str) -> str:
        """
        Locate the contract bytecode. It may be labeled as either
        bytecode.hex or contract.hex. In the event that both are present,
        ensure that they are identical.
        """

        present_bytecode_files = []
        for fname in ["bytecode.hex", "contract.hex"]:
            full_path = os.path.join(target_dir, fname)
            try:
                with open(full_path) as bytecode_file:
                    log.debug(f"Found {full_path} in target directory")
                    present_bytecode_files.append(bytecode_file.read().strip())
            except FileNotFoundError:
                log.debug(f"File {full_path} not found in target directory")

        if len(present_bytecode_files) == 0:
            raise FileNotFoundError(
                "No bytecode.hex or contract.hex found in target directory"
            )

        if len(present_bytecode_files) > 1:
            if present_bytecode_files[0].strip() != present_bytecode_files[1]:
                raise ValueError(
                    "bytecode.hex and contract.hex are not identical in target directory"
                )
        
        return present_bytecode_files[0]
