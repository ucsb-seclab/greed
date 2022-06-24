import logging

from SEtaac.cfg import CFG


class TAC_Function:
    def __init__(self, id: str, name: str, public: bool, blocks: list, arguments: list):
        self.id = id
        self.name = name
        self.public = public
        self.blocks = blocks
        self.arguments = arguments
        self.cfg = None
        self.calls = self._get_calls()

    def _get_calls(self):
        internal_calls = []
        for bb in self.blocks:
            for s in bb.statements:
                if s.__internal_name__ == "CALLPRIVATE":
                    internal_calls.append(s.arg_vals[s.arg_vars[0]])
        return internal_calls

    # Building the intra-functional CFG of a target function.
    def build_cfg(self, factory, tac_block_succ: dict):
        cfg = CFG()
        for bb in self.blocks:
            bb.cfg = cfg
            cfg.graph.add_node(bb)

        for a in self.blocks:
            # Adding information about successors from Gigahorse analysis
            for b_id in tac_block_succ.get(a.ident, []):
                cfg.graph.add_edge(a, factory.block(b_id))

        cfg.bbs = list(cfg.graph.nodes())
        cfg._bb_at = {bb.ident: bb for bb in cfg.bbs}

        # find function root
        bbs_with_no_preds = [bb for bb in cfg.bbs if len(bb.pred) == 0]
        assert len(bbs_with_no_preds) == 1, f"Something went wrong while retrieving the root for function {self.id}"
        cfg.root = bbs_with_no_preds[0]

        return cfg
