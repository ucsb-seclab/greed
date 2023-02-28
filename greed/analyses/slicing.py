import networkx as nx


def _get_stmt_level_cfg(target_function):
    stmt_level_cfg = nx.DiGraph()

    # inter-block edges
    for block_a, block_b in target_function.cfg.graph.edges():
        stmt_level_cfg.add_edge(block_a.statements[-1], block_b.statements[0])

    # intra-block edges
    for block in target_function.blocks:
        for stmt_a, stmt_b in zip(block.statements[:-1], block.statements[1:]):
            stmt_level_cfg.add_edge(stmt_a, stmt_b)

    return stmt_level_cfg


def _backward_slice_instructions(stmt_level_cfg, target_stmt, target_function, thin_slice=True):
    """
    Backward slice algorithm from https://www.math.arizona.edu/~glickenstein/math443f08/coogan.pdf
    """
    queue = {target_stmt, }
    relevant_map = {stmt.id: set() for block in target_function.blocks for stmt in block.statements}
    relevant_map[target_stmt.id] = set(target_stmt.arg_vars)
    # fixpoint for each edge i-j in the cfg
    while queue:
        curr = queue.pop()

        for pred in stmt_level_cfg.predecessors(curr):
            for var in relevant_map[curr.id]:
                # if i does not define a relevant variable var of j, add var to i’s relevant variables
                if var not in pred.res_vars and var not in relevant_map[pred.id]:
                    relevant_map[pred.id].add(var)
                    # if anything is updated, queue pred until fixpoint
                    queue.add(pred)
                # if i does define relevant variable var of j, add variables referenced by i to i’s relevant variables
                elif var in pred.res_vars:
                    for var2 in pred.arg_vars:
                        if var2 not in relevant_map[pred.id]:
                            relevant_map[pred.id].add(var2)
                            # if anything is updated, queue pred until fixpoint
                            queue.add(pred)

    slice = {target_stmt, }
    # for each edge i-j in the cfg
    for stmt_a, stmt_b in stmt_level_cfg.edges():
        # if i defines a relevant variable of j, add i to slice
        for var in relevant_map[stmt_b.id]:
            if var in stmt_a.res_vars:
                slice.add(stmt_a)

    if thin_slice is False:
        raise Exception("Only thin slice supported for now")

    return slice


def _forward_slice_instructions(stmt_level_cfg, target_stmt, target_function, thin_slice=True):
    """
    Forward slice algorithm (pretty much like the backward slice)
    """
    queue = {target_stmt, }
    relevant_map = {stmt.id: set() for block in target_function.blocks for stmt in block.statements}
    relevant_map[target_stmt.id] = set(target_stmt.res_vars)
    # fixpoint for each edge i-j in the cfg
    while queue:
        curr = queue.pop()

        for succ in stmt_level_cfg.successors(curr):
            for var in relevant_map[curr.id]:
                # add any relevant var of i to j's relevant vars
                if var not in relevant_map[succ.id]:
                    relevant_map[succ.id].add(var)
                    # if anything is updated, queue succ until fixpoint
                    queue.add(succ)

                # if j uses a relevant variable var of i, add j's defines to j's relevant variables
                if var in succ.arg_vars:
                    for var2 in succ.res_vars:
                        if var2 not in relevant_map[succ.id]:
                            relevant_map[succ.id].add(var2)
                            # if anything is updated, queue succ until fixpoint
                            queue.add(succ)

    slice = {target_stmt, }
    # for each edge i-j in the cfg
    for stmt_a, stmt_b in stmt_level_cfg.edges():
        # if j uses a relevant variable of i, add j to slice
        for var in relevant_map[stmt_a.id]:
            if var in stmt_b.arg_vars:
                slice.add(stmt_b)

    if thin_slice is False:
        raise Exception("Only thin slice supported for now")

    return slice


def _bidirectional_slice_instructions(stmt_level_cfg, target_stmt, target_function, thin_slice=True):
    """
    Forward+Backward slice algorithm
    """
    _forward_slice = _forward_slice_instructions(stmt_level_cfg, target_stmt, target_function, thin_slice)
    _backward_slice = _backward_slice_instructions(stmt_level_cfg, target_stmt, target_function, thin_slice)

    return _forward_slice | _backward_slice


def _slice(slicing_alg, p, target_addr, target_vars=None, thin_slice=True):
    target_stmt = p.factory.statement(target_addr)
    target_block = p.factory.block(target_stmt.block_id)
    target_function = target_block.function

    target_vars = target_vars or target_stmt.arg_vars
    assert all([v in target_stmt.arg_vars for v in target_vars])

    stmt_level_cfg = _get_stmt_level_cfg(target_function)

    slice = slicing_alg(stmt_level_cfg, target_stmt, target_function, thin_slice)

    # only keep nodes in slice
    for node in list(stmt_level_cfg.nodes()):
        if node not in slice:
            preds = list(stmt_level_cfg.predecessors(node))
            succs = list(stmt_level_cfg.successors(node))

            for pred in preds:
                stmt_level_cfg.remove_edge(pred, node)

            for succ in succs:
                stmt_level_cfg.remove_edge(node, succ)

            stmt_level_cfg.remove_node(node)

            for pred in preds:
                for succ in succs:
                    stmt_level_cfg.add_edge(pred, succ)

    return stmt_level_cfg


def backward_slice(p, target_addr, target_vars=None, thin_slice=True):
    return _slice(_backward_slice_instructions, p, target_addr, target_vars, thin_slice)


def forward_slice(p, target_addr, target_vars=None, thin_slice=True):
    return _slice(_forward_slice_instructions, p, target_addr, target_vars, thin_slice)


def bidirectional_slice(p, target_addr, target_vars=None, thin_slice=True):
    return _slice(_bidirectional_slice_instructions, p, target_addr, target_vars, thin_slice)
