from .base import TAC_Statement
from .flow_ops import *
from .gigahorse_ops import *
from .log_ops import *
from .math_ops import *
from .mem_ops import *
from .special_ops import *


def get_all_subclasses(cls):
    all_subclasses = []
    for subclass in cls.__subclasses__():
        all_subclasses.append(subclass)
        all_subclasses.extend(get_all_subclasses(subclass))

    return all_subclasses


tac_opcode_to_class_map = {c.__internal_name__: c for c in get_all_subclasses(TAC_Statement)}
