import json
import logging
import networkx as nx
import os 
import sha3
from SEtaac.TAC.TAC_parser import TAC_parser
from SEtaac.factory import Factory
from SEtaac.utils.solver.shortcuts import *

from networkx.drawing.nx_agraph import write_dot

log = logging.getLogger(__name__)


class Project(object):
    def __init__(self, target_dir: str):
        # Load the contract code
        with open(f"{target_dir}/contract.hex", "rb") as contract_file:
            self.code = contract_file.read()

        self.factory = Factory(project=self)
        init_solver_shortcuts()

        tac_parser = TAC_parser(self.factory, target_dir)
        self.statement_at = tac_parser.parse_statements()
        self.block_at = tac_parser.parse_blocks()
        self.function_at = tac_parser.parse_functions()
        
        self.has_abi = False
        self.abi = None

        # Importing the ABI if there is one
        sig_to_name = {}
        if os.path.exists(f"{target_dir}/abi.json"):
            with open(f"{target_dir}/abi.json", "rb") as abi_file:
                abi = json.load(abi_file)
            funcs = [e for e in abi if e['type'] == 'function']
            for f in funcs:
                f_proto = f['name'] + '(' + ",".join([i['internalType'] for i in f['inputs']]) + ')'
                k = sha3.keccak_256()
                f_sig = k.update(f_proto.encode('utf-8'))
                sig_to_name[f"0x{k.hexdigest()[0:8]}"] = f_proto

            # Set the name of the function
            for f in self.function_at.values():
                if f.signature in sig_to_name.keys():
                    f.name = sig_to_name[f.signature]
            
            self.has_abi = True
            self.abi = abi

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


