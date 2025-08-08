from typing import Dict

from greed.state_plugins.plugin import SimStatePlugin


class SimStateRegisters(SimStatePlugin):
    """
    This plugin tracks the (symbolic) registers of the EVM.
    """

    _registers: Dict[str, "Register"]

    def __init__(self):
        super().__init__()
        self._registers = {}

    def copy(self) -> "SimStateRegisters":
        ret = SimStateRegisters()
        ret._registers = {
            k: v.copy() for k, v in self._registers.items()
        }
        return ret

    def register(self, name) -> "Register":
        """
        Get a register by name, including its metadata.
        """
        ret = self._registers.get(name, None)
        if ret is None:
            ret = Register(name)
            self._registers[name] = ret
        return ret

    def get(self, k, default=None):
        reg = self.register(k)
        if reg.value is None:
            return default
        return reg.value

    def __getitem__(self, k):
        reg = self.register(k)
        reg.last_read_instruction_count = self.state.instruction_count
        return reg.value

    def __setitem__(self, k, v):
        reg = self.register(k)
        reg.value = v
        reg.last_written_instruction_count = self.state.instruction_count

    def __contains__(self, k):
        return k in self._registers

    def __iter__(self):
        return iter(self._registers)

    def __len__(self):
        return len(self._registers)


class Register:
    def __init__(self, name):
        self.name = name
        self.value = None
        self.last_written_instruction_count = 0
        self.last_read_instruction_count = 0
        self.phi_block_id = None

    def copy(self) -> "Register":
        ret = Register(self.name)
        ret.value = self.value
        ret.last_written_instruction_count = self.last_written_instruction_count
        ret.last_read_instruction_count = self.last_read_instruction_count
        ret.phi_block_id = self.phi_block_id
        return ret
