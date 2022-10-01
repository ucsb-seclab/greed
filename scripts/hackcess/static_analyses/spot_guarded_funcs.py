import sys 
import logging 
import networkx as nx
import itertools 

from SEtaac import Project
from SEtaac.TAC.base import TAC_Statement
from SEtaac import options

import random

LOGGING_FORMAT = "%(levelname)s | %(name)s | %(message)s"
logging.basicConfig(level=logging.INFO, format=LOGGING_FORMAT)
l = logging.getLogger("SpotGuardedFuncs")
l.setLevel(logging.INFO)


def is_target(id, target):
    return id != target


MANIPULATION_OPS = ["SHA3", "ADD", "SUB", "MUL", "DIV", "SDIV" "MOD", "SMOD", "ADDMOD", "MULMOD", "EXP", 
                    "SIGNEXTEND", "BYTE", "SAR", "SHL", "SHR", "XOR", "AND", "OR", "NOT"]
CHECK_OPS = ["LT", "GT", "SLT", "SGT", "EQ", "ISZERO"]
CALL_OPS = ["CALL", "CALLCODE", "DELEGATECALL", "STATICCALL"]
MEMORY_OPS = ["MLOAD", "MSTORE", "MSTORE8", "SLOAD", "SSTORE"]



def analyze_caller_comparison_var(function ,caller_checked_against_var):
    import ipdb; ipdb.set_trace()
    pass

def scan_for_equality_check(statements, tainted_reg):
    last_taint = tainted_reg
    for s in statements:
        # Check if the result_reg_caller_stmt is used in the statement arg_vars
        for arg in s.arg_vars:
            if arg == last_taint:
                # All right, we need to propagate the static taint
                if s.__internal_name__ == "CALLPRIVATE":
                    # I don't expect this to happen, we will handle it 
                    # later if we encounter it
                    l.fatal(" CALLER is flowing in CALLPRIVATE. Fix Me.")
                    return False, None, None, None
                if s.__internal_name__ in CALL_OPS:
                    l.info(" CALLER is flowing in a CALL")
                    return False, None, None, None
                if s.__internal_name__ in MEMORY_OPS:
                    l.warning(" CALLER is flowing in a MEMORY operation")
                    # We do not track this statically for now.
                    return False, None, None, None
                elif s.__internal_name__ in MANIPULATION_OPS:
                    l.info(f" CALLER is flowing in a {s.__internal_name__}")
                    # Taint the result
                    last_taint = s.res1_var
                    # go to next statement!
                    break
                elif s.__internal_name__ == "EQ":
                    l.info(" <<CALLER is flowing in a EQ>>")
                    for argx in s.arg_vars:
                        if argx != arg:
                            the_other_arg_var = argx 
                            break
                    return True, last_taint, s.id, the_other_arg_var

    return False, last_taint, None, None

def check_for_sink(f, caller_bb, caller_stmt):
    idx=0

    # Check remaining statements in the 
    # current basic block 
    for stmt in caller_bb.statements:
        if stmt.id == caller_stmt.id:
            break
        else:
            idx+=1
    remaining_stmts = caller_bb.statements[idx+1:]

    tainted_reg = caller_stmt.res1_var
    found_eq, last_taint, check_caller_at, caller_checked_against_var = scan_for_equality_check(remaining_stmts, tainted_reg)
    if found_eq:
        l.info(f"Function {f.name} is guarded, CALLER is checked at {check_caller_at}!")
        analyze_caller_comparison_var(f,caller_checked_against_var)
    else:
        if last_taint == None:
            # This is when CALLER flows in CALLPRIVATE or CALL or MEMORY ops
            l.info(f"CALLER cannot be followed in function {f.name}")
        else:
            # Ok we did not find an equality check, let's inspect 
            # the remaining basic blocks
            for bb in caller_bb.descendants:
                found_eq, last_taint, check_caller_at, caller_checked_against_var = scan_for_equality_check(bb.statements, last_taint)
                if found_eq:
                    l.info(f"Function {f.name} is guarded, CALLER is checked at {check_caller_at}!")
                    l.info(f"CALLER is checked against {caller_checked_against_var}!")
                    # Let's try to understand who is the CALLER checked against
                    analyze_caller_comparison_var(f,caller_checked_against_var)
                    break
                else:
                    if last_taint == None:
                        # This is when CALLER flows in CALLPRIVATE or CALL or MEMORY ops
                        l.info(f"CALLER cannot be followed in function {f.name}")
                        break
                    else:
                        # We did not find an equality check, let's inspect 
                        # the remaining basic blocks
                        continue

if __name__ == "__main__":
    p = Project(target_dir=sys.argv[1])

    # Iterate over all the functions in the project
    for f in p.function_at.values():
        if f.public and f.id != '0x0':
            # Iterate over all the basic blocks in the function
            for bb in f.blocks:
                # Iterate over all the statements in the basic block
                for stmt in bb.statements:
                    # Check if the statement is a call
                    if isinstance(stmt, TAC_Statement) and stmt.__internal_name__ == 'CALLER':
                        l.info("Spotted CALLER at %s in %s", stmt, f.name)
                        # Check if CALLER result flows into any EQ
                        check_for_sink(f, bb, stmt)
