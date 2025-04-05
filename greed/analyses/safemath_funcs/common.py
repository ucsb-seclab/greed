"""
Contains common functions for both the SAFEMATH's function analysis.
"""

import logging
from typing import TYPE_CHECKING, List, Optional, Tuple

import networkx as nx

if TYPE_CHECKING:
    from greed import Project
    from greed.block import Block
    from greed.function import TAC_Function
    from greed.TAC.gigahorse_ops import TAC_Returnprivate

log = logging.getLogger(__name__)


def basic_safemath_checks_pass(
    project: "Project", function: "TAC_Function"
) -> Optional[List[Tuple["TAC_Returnprivate", str]]]:
    """
    Performs basic checks to see if the function is a candidate for SAFEMATH.
    """
    if function.name in ["__function_selector__", "fallback()"]:
        log.debug(f"Skipping function {function.name}")
        return None

    # If the number of args is not 3, it's not a SAFEMATH function
    # (one for the return pc, and two for the operands)
    if len(function.arguments) != 3:
        log.debug(f"Function {function.name} does not have 3 arguments")
        return None

    # If the function has loops, it is not a SAFEMATH function
    cfg: "nx.DiGraph" = function.cfg.graph

    if not nx.is_directed_acyclic_graph(cfg):
        log.debug(f"Function {function.name} has loops")
        return None

    # Find the returning block (should only have one)
    return_blocks: List["Block"] = [
        block
        for block in cfg.nodes()
        if block.statements[-1].__internal_name__ == "RETURNPRIVATE"
    ]

    return_stmts_and_return_vars = []
    for return_block in return_blocks:
        return_stmt: "TAC_Returnprivate" = return_block.statements[-1]
        # Should only return one value (note: also +1 for the return pc)
        if len(return_stmt.arg_vars) != 2:
            log.debug(
                f"Function {function.name} block {return_block.id} does not return exactly one value"
            )
            return None

        return_var = return_stmt.arg_vars[1]
        return_stmts_and_return_vars.append((return_stmt, return_var))

    return return_stmts_and_return_vars
