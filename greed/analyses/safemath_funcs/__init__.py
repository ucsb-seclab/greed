from typing import List, TYPE_CHECKING
import logging

from .builtin import identify_builtin_safemath_func
from .library import identify_library_safemath_func
from .types import SafeMathFuncReport, SafeMathFunc

if TYPE_CHECKING:
    from greed import Project

log = logging.getLogger(__name__)

def find_safemath_funcs(project: 'Project') -> List[SafeMathFuncReport]:
    """
    Find all functions that are doing SAFEMATH operations.
    """
    safemath_funcs: List[SafeMathFuncReport] = []

    known_safemath_funcs = set()

    for func_name, func in project.function_at.items():
        maybe_safemath_func = None

        try:
            maybe_safemath_func = identify_builtin_safemath_func(project, func)
        except KeyboardInterrupt:
            raise
        except:
            log.warning(f'Error while identifying SAFEMATH function in {func_name}, assuming this is not SAFEMATH...', exc_info=True)
            continue

        if maybe_safemath_func is not None:
            log.debug(f"Function {func_name} identified as SAFEMATH ({maybe_safemath_func})")
            safemath_funcs.append(
                SafeMathFuncReport(
                    func_kind=maybe_safemath_func,
                    func=func,
                    first_arg_at_start=True,
                )
            )
            known_safemath_funcs.add(func_name)

    for func in safemath_funcs:
        log.debug(f'Identified SAFEMATH function {func.func_kind} @ {func.func.name}')

    library_funcs: List[SafeMathFuncReport] = []
    for func_name, func in project.function_at.items():
        if func_name in known_safemath_funcs:
            # Skip, already known
            continue

        maybe_safemath_func_report = identify_library_safemath_func(project, func)
        if maybe_safemath_func_report is not None:
            log.debug(f"Function {func_name} identified as SAFEMATH ({maybe_safemath_func})")
            library_funcs.append(maybe_safemath_func_report)

    for func in library_funcs:
        log.debug(f'Identified library SAFEMATH function {func.func_kind} @ {func.func.name}')

    return safemath_funcs + library_funcs
