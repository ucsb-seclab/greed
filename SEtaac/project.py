import logging

from SEtaac.TAC.TAC_parser import TAC_parser
from SEtaac.factory import Factory

log = logging.getLogger(__name__)


class Project(object):
    def __init__(self, target_dir: str):
        # Load the contract code
        with open(f"{target_dir}/contract.hex", "rb") as contract_file:
            self.code = contract_file.read()

        self.factory = Factory(project=self)

        tac_parser = TAC_parser(self.factory, target_dir)
        self.statement_at = tac_parser.parse_statements()
        self.block_at = tac_parser.parse_blocks()
        self.function_at = tac_parser.parse_functions()
