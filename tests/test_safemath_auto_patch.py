import os
from greed import Project

from greed.solver.shortcuts import *

from greed.utils.extra import gen_exec_id
from greed.analyses.safemath_funcs.types import SafeMathFunc
from greed.analyses.safemath_funcs import find_safemath_funcs
from greed.analyses.safemath_funcs.patch.safe_ops import patch_function

from common import run_test_simgr

def test_auto_patch_solidity_0_8():
    project_dir = os.path.join(
        os.path.dirname(os.path.realpath(__file__)),
        'test_safemath_auto_patch',
        'solidity_0.8_builtin',
    )

    p = Project(project_dir)

    safemath_funcs = find_safemath_funcs(p)

    # ensure we have one of each
    all_types = set(SafeMathFunc.__members__.values())
    found_types = set(func.func_kind for func in safemath_funcs)
    assert all_types == found_types, f'Expected {all_types}, found {found_types}'

    # Patch all of them
    for func in safemath_funcs:
        patch_function(p, func)
    
    xid = gen_exec_id()
    init_ctx = {
        'CALLVALUE': 0,
        'CALLDATASIZE': 0,
    }
    entry_state = p.factory.entry_state(xid=xid, init_ctx=init_ctx)
    simgr = p.factory.simgr(entry_state=entry_state)

    run_test_simgr(simgr)

def test_auto_patch_solidity_0_8_openzeppelin():
    project_dir = os.path.join(
        os.path.dirname(os.path.realpath(__file__)),
        'test_safemath_auto_patch',
        'solidity_0.8_openzeppelin',
    )

    p = Project(project_dir)

    safemath_funcs = find_safemath_funcs(p)

    # ensure we have one of each unsigned op
    all_types = {SafeMathFunc.ADD, SafeMathFunc.SUB, SafeMathFunc.MUL, SafeMathFunc.DIV, SafeMathFunc.MOD}
    found_types = set(func.func_kind for func in safemath_funcs)
    assert all_types == found_types, f'Expected {all_types}, found {found_types}'

    # Patch all of them
    for func in safemath_funcs:
        patch_function(p, func)
    
    xid = gen_exec_id()
    init_ctx = {
        'CALLVALUE': 0,
        'CALLDATASIZE': 0,
    }
    entry_state = p.factory.entry_state(xid=xid, init_ctx=init_ctx)
    simgr = p.factory.simgr(entry_state=entry_state)

    run_test_simgr(simgr)

def test_auto_patch_solidity_0_7_openzeppelin():
    project_dir = os.path.join(
        os.path.dirname(os.path.realpath(__file__)),
        'test_safemath_auto_patch',
        'solidity_0.7_openzeppelin',
    )

    p = Project(project_dir)

    safemath_funcs = find_safemath_funcs(p)

    # ensure we have one of each unsigned op
    all_types = {SafeMathFunc.ADD, SafeMathFunc.SUB, SafeMathFunc.MUL, SafeMathFunc.DIV, SafeMathFunc.MOD}
    found_types = set(func.func_kind for func in safemath_funcs)
    assert all_types == found_types, f'Expected {all_types}, found {found_types}'

    # Patch all of them
    for func in safemath_funcs:
        patch_function(p, func)
    
    xid = gen_exec_id()
    init_ctx = {
        'CALLVALUE': 0,
        'CALLDATASIZE': 0,
    }
    entry_state = p.factory.entry_state(xid=xid, init_ctx=init_ctx)
    simgr = p.factory.simgr(entry_state=entry_state)

    run_test_simgr(simgr)
