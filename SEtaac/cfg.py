import logging
from SEtaac.bb import TAC_Block
from SEtaac.function import TAC_Function

import networkx as nx


l = logging.getLogger("cfg")
l.setLevel(logging.DEBUG)

class CFGNode(object):
    def __init__(self, bb:TAC_Block):
        self.bb = bb
        self.succ_addrs = set()

        # cached properties
        self._succ = None
        self._pred = None
        self._ancestors = None
        self._descendants = None

        self._acyclic_subgraph = None

    @property
    def succ(self):
        if self._succ is None:
            self._succ = list(self.cfg.graph.successors(self))
        return self._succ
    
    # WARNING: assuming BB indexed are UNIQUE.
    #def __hash__(self):
    #    return self.bb.first_ins.stmt_ident


    @property
    def pred(self):
        if self._pred is None:
            self._pred = list(self.cfg.graph.predecessors(self))
        return self._pred

    @property
    def ancestors(self):
        if self._ancestors is None:
            reversed_subtree = nx.dfs_tree(self.cfg.graph.reverse(), source=self)
            self._ancestors = list(set(reversed_subtree) - {self})
            # if there is a loop, add the current bb to it's ancestors
            for bb in self._ancestors:
                if self.cfg.graph.has_edge(self.cfg._bb_at[self.start], self.cfg._bb_at[bb.start]):
                    self._ancestors += [self]
                    break
        return self._ancestors

    @property
    def descendants(self):
        if self._descendants is None:
            subtree = nx.dfs_tree(self.cfg.graph, source=self)
            self._descendants = list(set(subtree) - {self})

            # if there is a loop, add the current bb to it's descendants
            for bb in self._descendants:
                if self.cfg.graph.has_edge(bb, self):
                    self._descendants += [self]
                    break

        return self._descendants

    @property
    def acyclic_subgraph(self):
        if self._acyclic_subgraph is None:
            self._acyclic_subgraph = nx.dfs_tree(self.cfg.graph, source=self)

        return self._acyclic_subgraph

    @property
    def subgraph(self):
        if self._acyclic_subgraph is None:
            self._acyclic_subgraph = nx.dfs_tree(self.cfg.graph, source=self)
            for node in self._acyclic_subgraph.nodes():
                for succ in node.succ:
                    if not self._acyclic_subgraph.has_edge(node, succ):
                        self._acyclic_subgraph.add_edge(node, succ)

        return self._acyclic_subgraph

    def __str__(self):
        return f'CFGNode @ {self.bb.ident}'

    def __repr__(self):
        return str(self)


class CFG(object):
    def __init__(self):

        self.graph = nx.DiGraph()

        # keep basic block organized in a dictionary
        self.blockids_to_cfgnode = dict()
        self._dominators = None
        
        '''
        self.trim()
        self.root = self._bb_at[0]
        self._ins_at = {i.addr: i for bb in self.bbs for i in bb.ins}
        self.shortest_paths = nx.single_source_shortest_path(self.graph, self.root)
        '''

    '''
    def filter_ins(self, names, reachable=False):
        if isinstance(names, str):
            names = [names]
        if not reachable:
            return [ins for bb in self.bbs for ins in bb.ins if ins.name in names]
        else:
            return [ins for bb in self.bbs for ins in bb.ins if ins.name in names and 0 in bb.ancestors | {bb.start}]
    '''

    @property
    def dominators(self):
        if not self._dominators:
            self._dominators = {k: v for k, v in nx.immediate_dominators(self.graph, 0).items()}
        return self._dominators

# Building the intra-functional CFG of a target function.
def make_cfg(factory, TAC_cfg_raw:dict, function:TAC_Function):

    cfg = CFG()
    blockids_to_cfgnode = {}

    for bb in function.blocks:
        cfgnode = CFGNode(bb)
        blockids_to_cfgnode[bb.ident] = cfgnode
        cfg.graph.add_node(cfgnode)
    
    for bb in function.blocks:        
        # Adding information about successors from Gigahorse analysis
        jump_data = TAC_cfg_raw['jump_data'].get(cfgnode.bb.ident, None)
        if jump_data:
            for j in jump_data:
                new_cfgnode = blockids_to_cfgnode[j]
                cfg.graph.add_edge(cfgnode, new_cfgnode)
    
    cfg.blockids_to_cfgnode = blockids_to_cfgnode
    function.cfg = cfg
