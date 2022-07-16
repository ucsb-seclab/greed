import logging
from collections import defaultdict
from typing import List, Mapping

from SEtaac.block import Block
from SEtaac.cfg import CFG
from SEtaac.factory import Factory


class TAC_Function:
    def __init__(self, id: str, signature: str, name: str, public: bool, blocks: List[Block], arguments: List[str]):
        self.id = id
        self.signature = signature
        self.name = name
        self.public = public
        self.blocks = blocks
        self.arguments = arguments

        # populate source -> target map
        self.callprivate_source_target = self._get_callprivate_source_target()
        # populate target -> source map
        self.callprivate_target_sources = defaultdict(list)
        for source, target in self.callprivate_source_target.items():
            self.callprivate_target_sources[target].append(source)

        self.returnprivate_block_ids = [stmt.block_id
                                        for bb in self.blocks
                                        for stmt in bb.statements
                                        if stmt.__internal_name__ == "RETURNPRIVATE"]

        self.cfg = None

    def _get_callprivate_source_target(self) -> Mapping[str, str]:
        call_targets = dict()
        for bb in self.blocks:
            for stmt in bb.statements:
                if stmt.__internal_name__ == "CALLPRIVATE":
                    target_bb_id = stmt.get_target_bb_id()
                    call_targets[stmt.block_id] = target_bb_id
        return call_targets

    # Building the intra-functional CFG of a target function.
    def build_cfg(self, factory: Factory, tac_block_succ: Mapping[str, List[str]]):
        cfg = CFG()
        for bb in self.blocks:
            bb.cfg = cfg
            cfg.graph.add_node(bb)

        for a in self.blocks:
            # Adding information about successors from Gigahorse analysis
            for b_id in tac_block_succ.get(a.id, []):
                cfg.graph.add_edge(a, factory.block(b_id))

        cfg.bbs = list(cfg.graph.nodes())
        cfg._bb_at = {bb.id: bb for bb in cfg.bbs}

        cfg.root = factory.block(self.id)

        return cfg
