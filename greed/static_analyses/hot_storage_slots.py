import logging

log = logging.getLogger(__name__)


def find_hot_slots(p):
    return p.tac_parser.parse_privileged_slots()
