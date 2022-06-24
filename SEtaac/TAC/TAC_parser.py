import itertools
import logging
from collections import defaultdict

from SEtaac import TAC
from SEtaac.TAC import tac_opcode_to_class_map
from SEtaac.TAC.gigahorse_ops import TAC_Nop
from SEtaac.TAC.special_ops import TAC_Stop
from SEtaac.cfg import TAC_Block
from SEtaac.function import TAC_Function
from SEtaac.utils import load_csv, load_csv_map, load_csv_multimap

l = logging.getLogger("tac_parser")
l.setLevel(logging.INFO)


class TACparser:
    def __init__(self, factory, target_dir):
        self.factory = factory
        self.target_dir = target_dir

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

        # parse all statements block after block
        statements = dict()
        for block_id in itertools.chain(*tac_function_blocks.values()):
            for stmt_id in sorted(tac_block_stmts[block_id], key=TACparser.stmt_sort_key):
                opcode = tac_op[stmt_id]
                raw_uses = [var for var, _ in sorted(tac_uses[stmt_id], key=lambda x: x[1])]
                raw_defs = [var for var, _ in sorted(tac_defs[stmt_id], key=lambda x: x[1])]
                uses = ['v' + v.replace('0x', '') for v in raw_uses]
                defs = ['v' + v.replace('0x', '') for v in raw_defs]
                values = {v: val for v, val in tac_variable_value.items() if v in uses + defs}
                OpcodeClass = tac_opcode_to_class_map[opcode]
                statement = OpcodeClass(block_id=block_id, stmt_id=stmt_id, uses=uses, defs=defs, values=values)
                statements[stmt_id] = statement

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
                if v_new in phimap:
                    phimap[v_old] = phimap[v_new]
                    fixpoint = False

        # rewrite statements
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

        # parse all blocks
        blocks = dict()
        for block_id in itertools.chain(*tac_function_blocks.values()):
            statements = list()
            for stmt_id in sorted(tac_block_stmts[block_id], key=TACparser.stmt_sort_key):
                statement = self.factory.statement(stmt_id)
                statements.append(statement)
            if not statements:
                # Gigahorse sometimes creates empty basic blocks. If so, inject a NOP
                fake_stmt = self.factory.statement(block_id + '_fake_stmt')
                statements.append(fake_stmt)
            blocks[block_id] = TAC_Block(block_id=block_id, statements=statements)

        # set fallthrough edge
        for block_id in blocks:
            fallthrough_block_id = tac_fallthrough_edge.get(block_id, None)
            if fallthrough_block_id is not None:
                blocks[block_id].fallthrough_edge = blocks[fallthrough_block_id]

        # inject a fake exit block to simplify the handling of CALLPRIVATE without successors
        fake_exit_stmt = self.factory.statement('fake_exit')
        fake_exit_block = TAC_Block(block_id='fake_exit', statements=[fake_exit_stmt])
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
            high_level_name = 'fallback()' if is_fallback else tac_high_level_func_name[func_id]
            formals = [var for var, _ in sorted(tac_formal_args[func_id], key=lambda x: x[1])]

            blocks = [self.factory.block(id) for id in tac_function_blocks[func_id]]

            function = TAC_Function(block_id, high_level_name, is_public, blocks, formals)
            function.cfg = function.build_cfg(self.factory, tac_block_succ)
            functions[func_id] = function

            for b in blocks:
                b.function = function

        return functions
