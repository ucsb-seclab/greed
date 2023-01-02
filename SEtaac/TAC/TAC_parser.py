import itertools
import json
import logging
import os
from collections import defaultdict
from typing import Mapping, List, Tuple

import sha3

from SEtaac.TAC import tac_opcode_to_class_map
from SEtaac.TAC.gigahorse_ops import TAC_Nop
from SEtaac.TAC.special_ops import TAC_Stop
from SEtaac.block import Block
from SEtaac.factory import Factory
from SEtaac.function import TAC_Function
from SEtaac.utils import load_csv, load_csv_map, load_csv_multimap

log = logging.getLogger(__name__)


class TAC_parser:
    def __init__(self, factory: Factory, target_dir: str):
        self.factory = factory
        self.target_dir = target_dir

        self.phimap = None

    @staticmethod
    def stmt_sort_key(stmt_id: str) -> int:
        return int(stmt_id.split('0x')[1].split('_')[0], base=16)

    def parse_statements(self):
        # Load facts
        tac_function_blocks = load_csv_multimap(f"{self.target_dir}/InFunction.csv", reverse=True)
        tac_block_stmts = load_csv_multimap(f"{self.target_dir}/TAC_Block.csv", reverse=True)
        tac_op = load_csv_map(f"{self.target_dir}/TAC_Op.csv")

        tac_variable_value = load_csv_map(f"{self.target_dir}/TAC_Variable_Value.csv")
        tac_variable_value = {'v' + v.replace('0x', ''): val for v, val in tac_variable_value.items()}

        tac_defs: Mapping[str, List[Tuple[str, int]]] = defaultdict(list)
        for stmt_id, var, pos in load_csv(f"{self.target_dir}/TAC_Def.csv"):
            tac_defs[stmt_id].append((var, int(pos)))

        tac_uses: Mapping[str, List[Tuple[str, int]]] = defaultdict(list)
        for stmt_id, var, pos in load_csv(f"{self.target_dir}/TAC_Use.csv"):
            tac_uses[stmt_id].append((var, int(pos)))
        
        func_name_to_sig = load_csv_map(f"{self.target_dir}/ConstantPossibleSigHash.csv")
        # Entries with a signature longer than 10 characters are most likely false positives of the analysis, not safe to import.
        func_name_to_sig = {name:"0x"+signature[2:].zfill(8) for signature, name in func_name_to_sig.items() if len(signature) <= 10}

        fixed_calls : Mapping[str, List[Tuple[str, str]]] = defaultdict(list)
        for stmt_id, func_target in load_csv(f"{self.target_dir}/CallToSignature.csv"):
            # We want to skip the "LOCKXXX" target and keep only the one
            # that Gigahorse successfully resolved
            if "LOCK" in func_target: continue
            fixed_calls[stmt_id] = func_name_to_sig[func_target]

        for stmt_id, func_target in load_csv(f"{self.target_dir}/CallToSignatureFromSHA3.csv"):
            if "LOCK" in func_target: continue
            fixed_calls[stmt_id] = func_name_to_sig[func_target]
        
        # parse all statements block after block
        statements = dict()
        for block_id in itertools.chain(*tac_function_blocks.values()):
            for stmt_id in sorted(tac_block_stmts[block_id], key=TAC_parser.stmt_sort_key):
                opcode = tac_op[stmt_id]
                raw_uses = [var for var, _ in sorted(tac_uses[stmt_id], key=lambda x: x[1])]
                raw_defs = [var for var, _ in sorted(tac_defs[stmt_id], key=lambda x: x[1])]
                uses = ['v' + v.replace('0x', '') for v in raw_uses]
                defs = ['v' + v.replace('0x', '') for v in raw_defs]
                values = {v: tac_variable_value.get(v, None) for v in uses + defs}
                OpcodeClass = tac_opcode_to_class_map[opcode]
                statement = OpcodeClass(block_id=block_id, stmt_id=stmt_id, uses=uses, defs=defs, values=values)
                statements[stmt_id] = statement
                
                # Adding metadata for CALL statements
                if stmt_id in fixed_calls:
                    log.debug(f"Setting {statement} as fixed call to {fixed_calls[stmt_id]}")
                    statement.set_likeyl_known_target_func(fixed_calls[stmt_id])

            if not tac_block_stmts[block_id]:
                # Gigahorse sometimes creates empty basic blocks. If so, inject a NOP statement
                fake_stmt = TAC_Nop(block_id=block_id, stmt_id=block_id + '_fake_stmt')
                statements[block_id + '_fake_stmt'] = fake_stmt

        # inject a fake exit statement to simplify the handling of CALLPRIVATE without successors
        fake_exit_stmt = TAC_Stop(block_id='fake_exit', stmt_id='fake_exit')
        statements['fake_exit'] = fake_exit_stmt

        # parse phi-map and re-write statements
        # build phi-map (as in gigahorse decompiler)
        phimap = dict()
        for stmt in statements.values():
            if stmt.__internal_name__ != 'PHI':
                continue
            #phimap[stmt.res1_var] = stmt.res1_var
            for v in stmt.arg_vars:
                if v in phimap:
                    phimap[stmt.res1_var] = phimap[v]
                    continue
                phimap[v] = stmt.res1_var

        # propagate phi map
        fixpoint = False
        while not fixpoint:
            fixpoint = True
            for v_old, v_new in phimap.items():
                # (phimap[v_old] != phimap[v_new]) --> means "not already at local fixpoint"
                if v_new in phimap and (phimap[v_old] != phimap[v_new]):
                    phimap[v_old] = phimap[v_new]
                    fixpoint = False

        self.phimap = phimap

        # rewrite statements according to PHI map
        for stmt in statements.values():
            if stmt.__internal_name__ == "PHI":
                # remove all phi statements
                statements[stmt.id] = TAC_Nop(block_id=stmt.block_id, stmt_id=stmt.id)
                continue
            # rewrite other statements according to the phi map
            stmt.arg_vars = [phimap.get(v, v) for v in stmt.arg_vars]
            stmt.arg_vals = {phimap.get(v, v): val for v, val in stmt.arg_vals.items()}
            stmt.res_vars = [phimap.get(v, v) for v in stmt.res_vars]
            stmt.res_vals = {phimap.get(v, v): val for v, val in stmt.res_vals.items()}

            # re-process args
            stmt.process_args()

        return statements

    def parse_blocks(self):
        # Load facts
        tac_function_blocks = load_csv_multimap(f"{self.target_dir}/InFunction.csv", reverse=True)
        tac_block_stmts = load_csv_multimap(f"{self.target_dir}/TAC_Block.csv", reverse=True)
        tac_fallthrough_edge = load_csv_map(f"{self.target_dir}/IRFallthroughEdge.csv")
        tac_guarded_blocks = load_csv_map(f"{self.target_dir}/StaticallyGuardedBlock.csv")

        # parse all blocks
        blocks = dict()
        for block_id in itertools.chain(*tac_function_blocks.values()):
            statements = list()
            for stmt_id in sorted(tac_block_stmts[block_id], key=TAC_parser.stmt_sort_key):
                statement = self.factory.statement(stmt_id)
                statements.append(statement)
            if not statements:
                # Gigahorse sometimes creates empty basic blocks. If so, inject a NOP
                fake_stmt = self.factory.statement(block_id + '_fake_stmt')
                statements.append(fake_stmt)
            blocks[block_id] = Block(block_id=block_id, statements=statements)

        # set fallthrough edge
        for block_id in blocks:
            fallthrough_block_id = tac_fallthrough_edge.get(block_id, None)
            if fallthrough_block_id is not None:
                blocks[block_id].fallthrough_edge = blocks[fallthrough_block_id]
        
        # Import the guard information
        for block_id in blocks:
            if tac_guarded_blocks.get(block_id, None) is not None:
                blocks[block_id].guarded_by_caller = True
            else:
                blocks[block_id].guarded_by_caller = False

        # inject a fake exit block to simplify the handling of CALLPRIVATE without successors
        fake_exit_stmt = self.factory.statement('fake_exit')
        fake_exit_block = Block(block_id='fake_exit', statements=[fake_exit_stmt])
        fake_exit_block._succ = fake_exit_block._pred = fake_exit_block._ancestors = fake_exit_block._descendants = []
        blocks['fake_exit'] = fake_exit_block

        return blocks

    def parse_functions(self):
        # Load facts
        tac_block_function = load_csv_map(f"{self.target_dir}/InFunction.csv")
        tac_function_blocks = load_csv_multimap(f"{self.target_dir}/InFunction.csv", reverse=True)
        tac_func_id_to_public = load_csv_map(f"{self.target_dir}/PublicFunction.csv")
        tac_high_level_func_name = load_csv_map(f"{self.target_dir}/HighLevelFunctionName.csv")
        tac_block_succ = load_csv_multimap(f"{self.target_dir}/LocalBlockEdge.csv")
        tac_function_entry = load_csv(f"{self.target_dir}/IRFunctionEntry.csv")
        
        tac_formal_args: Mapping[str, List[Tuple[str, int]]] = defaultdict(list)
        for func_id, arg, pos in load_csv(f"{self.target_dir}/FormalArgs.csv"):
            tac_formal_args[func_id].append((arg, int(pos)))

        functions = dict()
        for block_id, in tac_function_entry:
            func_id = tac_block_function[block_id]
            is_public = func_id in tac_func_id_to_public or func_id == '0x0'
            is_fallback = tac_func_id_to_public.get(func_id, None) == '0x0'
            signature = tac_func_id_to_public.get(func_id, None)

            # Pad signature over 4 bytes
            if signature:
                signature = "0x"+signature[2:].zfill(8)

            high_level_name = 'fallback()' if is_fallback else tac_high_level_func_name[func_id]

            formals = [var for var, _ in sorted(tac_formal_args[func_id], key=lambda x: x[1])]

            blocks = [self.factory.block(id) for id in tac_function_blocks[func_id]]

            function = TAC_Function(block_id, signature, high_level_name, is_public, blocks, formals)
            function.cfg = function.build_cfg(self.factory, tac_block_succ)
            function.build_use_def_graph()
            functions[func_id] = function

            for b in blocks:
                b.function = function

        # rewrite aliases according to PHI map
        translate_alias = lambda alias: 'v' + alias.replace('0x', '')
        for function in functions.values():
            function.arguments = [self.phimap.get(translate_alias(a), translate_alias(a)) for a in function.arguments]

        return functions

    def parse_abi(self):
        if not os.path.exists(f"{self.target_dir}/abi.json"):
            return None
        with open(f"{self.target_dir}/abi.json", "rb") as abi_file:
            abi = json.load(abi_file)

        sig_to_name = {}
        funcs = [e for e in abi if e['type'] == 'function']
        for f in funcs:
            f_proto = f['name'] + '(' + ",".join([i['internalType'] for i in f['inputs']]) + ')'
            k = sha3.keccak_256()
            k.update(f_proto.encode('utf-8'))
            sig_to_name[f"0x{k.hexdigest()[0:8]}"] = f_proto

        # Set the function names
        for f in self.factory.project.function_at.values():
            if f.signature in sig_to_name.keys():
                f.name = sig_to_name[f.signature]

        return abi

    # The r_abi json is expected to be a dictionary of this kind:
    # <function_id>:<function_prototype>
    #
    # e.g.
    # {"0xd450e04c":"0xd450e04c(bytes,bytes,bytes,bytes,bytes)"  
    #
    def parse_recovered_abi(self):
        if not os.path.exists(f"{self.target_dir}/r_abi.json"):
            return None
        
        log.warning("Working with an automatically recovered abi")

        with open(f"{self.target_dir}/r_abi.json", "rb") as abi_file:
            abi = json.load(abi_file)

        for f in self.factory.project.function_at.values():
            proto = abi.get(f.signature, None) 
            if proto:
                f.name = proto
        
        return abi