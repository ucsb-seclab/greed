import datetime
import logging

import z3

from collections import defaultdict

from SEtaac import utils
from SEtaac.exceptions import ExternalData, SymbolicError, IntractablePath, VMException
from SEtaac.memory import SymRead, SymbolicMemory
from SEtaac.storage import SymbolicStorage
from SEtaac.utils import concrete, is_true, get_solver, translate_xid


class AbstractEVMState(object):
    def __init__(self, code=None):
        self.code = code or bytearray()
        self.pc = 0
        self.memory = None
        self.trace = list()
        self.gas = None


class SymbolicEVMState(AbstractEVMState):
    def __init__(self, xid, program=None, code=None):
        super(SymbolicEVMState, self).__init__(code)
        self.program = program
        self.xid = xid

        self.memory = SymbolicMemory()
        self.storage = SymbolicStorage(self.xid)
        self.registers = defaultdict(None)

        self.instruction_count = 0
        self.halt = False
        self.error = None

        self.gas = z3.BitVec('GAS_%d' % self.xid, 256)
        self.start_balance = z3.BitVec('BALANCE_%d' % self.xid, 256)
        self.balance = self.start_balance
        self.balance += utils.ctx_or_symbolic('CALLVALUE', self.ctx, self.xid)

        self.ctx = dict()
        self.ctx['CODESIZE-ADDRESS'] = len(code)  # todo: code can be None

        self.constraints = list()
        self.sha_constraints = dict()

        # make sure we can exploit it in the foreseeable future
        self.min_timestamp = (datetime.datetime.now() - datetime.datetime(1970, 1, 1)).total_seconds()
        self.max_timestamp = (datetime.datetime(2020, 1, 1) - datetime.datetime(1970, 1, 1)).total_seconds()

        self.MAX_CALLDATA_SIZE = 256
        self.calldata = z3.Array('CALLDATA_%d' % self.xid, z3.BitVecSort(256), z3.BitVecSort(8))
        self.calldatasize = z3.BitVec('CALLDATASIZE_%d' % self.xid, 256)
        self.calldata_accesses = [0]

        self._handlers = {
            'ADD': self.add_handler,
            'SUB': self.sub_handler,
            'MUL': self.mul_handler,
            'DIV': self.div_handler,
            'MOD': self.mod_handler,
            'SDIV': self.sdiv_handler,
            'SMOD': self.smod_handler,
            'ADDMOD': self.addmod_handler,
            'MULMOD': self.mulmod_handler,
            'EXP': self.exp_handler,
            'SIGNEXTEND': self.signextend_handler,
            'LT': self.lt_handler,
            'GT': self.gt_handler,
            'SLT': self.slt_handler,
            'SGT': self.sgt_handler,
            'EQ': self.eq_handler,
            'ISZERO': self.iszero_handler,
            'AND': self.and_handler,
            'OR': self.or_handler,
            'XOR': self.xor_handler,
            'NOT': self.not_handler,
            'BYTE': self.byte_handler,
            'SHL': self.shl_handler,
            'SHR': self.shr_handler,
            'SAR': self.sar_handler,
            'SHA3': self.sha3_handler,
            'ADDRESS': self.address_handler,
            'BALANCE': self.balance_handler,
            'ORIGIN': self.origin_handler,
            'CALLER': self.caller_handler,
            'CALLVALUE': self.callvalue_handler,
            'CALLDATALOAD': self.calldataload_handler,
            'CALLDATASIZE': self.calldatasize_handler,
            'CALLDATACOPY': self.calldatacopy_handler,
            'CODESIZE': self.codesize_handler,
            'CODECOPY': self.codecopy_handler,
            'RETURNDATACOPY': self.returndatacopy_handler,
            'RETURNDATASIZE': self.returndatasize_handler,
            'GASPRICE': self.gasprice_handler,
            'EXTCODESIZE': self.extcodesize_handler,
            'EXTCODECOPY': self.extcodecopy_handler,
            'BLOCKHASH': self.blockhash_handler,
            'COINBASE': self.coinbase_handler,
            'TIMESTAMP': self.timestamp_handler,
            'NUMBER': self.number_handler,
            'DIFFICULTY': self.difficulty_handler,
            'GASLIMIT': self.gaslimit_handler,
            'MLOAD': self.mload_handler,
            'MSTORE': self.mstore_handler,
            'MSTORE8': self.mstore8_handler,
            'SLOAD': self.sload_handler,
            'SSTORE': self.sstore_handler,
            'JUMP': self.jump_handler,
            'JUMPI': self.jumpi_handler,
            'PC': self.pc_handler,
            'MSIZE': self.msize_handler,
            'GAS': self.gas_handler,
            'CREATE': self.create_handler,
            'CALL': self.call_handler,
            'CALLCODE': self.callcode_handler,
            'DELEGATECALL': self.delegatecall_handler,
            'STATICCALL': self.staticcall_handler,
            'RETURN': self.return_handler,
            'REVERT': self.revert_handler,
            'SELFDESTRUCT': self.selfdestruct_handler,
            'STOP': self.stop_handler,
        }

        self.handler_should_increment_pc = {
            h: (True if h not in ['JUMP', 'JUMPI'] else False)
            for h in self._handlers
        }


    @property
    def curr_stmt(self):
        # todo: pass project to state
        # todo: pc is the statement id
        return self.project.tac_parser.get_stmt_at(self.pc)

    def set_next_pc(self):
        # todo: read next statement from dict
        next_pcs = get_next_pcs(self.curr_stmt)
        assert len(next_pcs) == 1
        self.pc = next_pcs[0]

    def copy(self, new_xid=None):
        # todo: implement state copy
        # todo: there shouldn't be any need to set a new xid, in most cases
        new_state = SymbolicEVMState(new_xid, code=self.code)

        new_state.pc = self.pc
        self.memory = None
        self.trace = list()
        self.gas = None

        new_state.storage = self.storage.copy(new_xid)
        new_state.pc = self.pc
        new_state.trace = list(self.trace)
        new_state.start_balance = translate_xid(self.start_balance, new_xid)
        new_state.balance = translate_xid(self.balance, new_xid)

        new_state.constraints = list(self.constraints)
        new_state.sha_constraints = dict(self.sha_constraints)
        new_state.ctx = dict(self.ctx)

        return new_state

    def step(self):
        # todo: parse next instruction
        # todo: then execute correct handler and eventually assign return value to lhs

        self.trace.append(self.pc)
        self.instruction_count += 1

        ins = self.program[self.pc]
        self.gas -= ins.gas

        if ins.name in self._handlers:
            pass
            #self._handlers[ins.name]()  # todo: need to pass args here (can read ins.inputs to know how many)
        else:
            pass

        if self.handler_should_increment_pc[ins.name]:
            self.pc += 1

    # VM state manipulations
    def mload_handler(self, s0):
        self.memory.extend(s0, 32)
        mm = [self.memory[s0 + i] for i in range(32)]
        if all(concrete(m) for m in mm):
            return utils.bytes_to_int(self.memory.read(s0, 32))
        else:
            v = z3.simplify(z3.Concat([m if not concrete(m) else z3.BitVecVal(m, 8) for m in mm]))
            if z3.is_bv_value(v):
                return v.as_long()
            else:
                return v

    def mstore_handler(self, s0, s1):
        self.memory.extend(s0, 32)
        if concrete(s1):
            self.memory.write(s0, 32, utils.encode_int32(s1))
        else:
            for i in range(32):
                m = z3.simplify(z3.Extract((31 - i) * 8 + 7, (31 - i) * 8, s1))
                if z3.is_bv_value(m):
                    self.memory[s0 + i] = m.as_long()
                else:
                    self.memory[s0 + i] = m

    def mstore8_handler(self, s0, s1):
        self.memory.extend(s0, 1)
        self.memory[s0] = s1 % 256

    def sload_handler(self, s0):
        v = z3.simplify(self.storage[s0])
        if z3.is_bv_value(v):
            return v.as_long()
        else:
            return v

    def sstore_handler(self, s0, s1):
        self.storage[s0] = s1

    def msize_handler(self, ):
        return len(self.memory)

    def gas_handler(self, ):
        return z3.BitVec('GAS_%x' % self.instruction_count, 256)

    # Logs (aka "events")
    # todo: implement logs
    # elif op[:3] == 'LOG':
    #     """
    #     0xa0 ... 0xa4, 32/64/96/128/160 + len(data) gas
    #     a. Opcodes LOG0...LOG4 are added, takes 2-6 stack arguments
    #             MEMSTART MEMSZ (TOPIC1) (TOPIC2) (TOPIC3) (TOPIC4)
    #     b. Logs are kept track of during tx execution exactly the same way as selfdestructs
    #        (except as an ordered list, not a set).
    #        Each log is in the form [address, [topic1, ... ], data] where:
    #        * address is what the ADDRESS opcode would output
    #        * data is self.memory[MEMSTART: MEMSTART + MEMSZ]
    #        * topics are as provided by the opcode
    #     c. The ordered list of logs in the transaction are expressed as [log0, log1, ..., logN].
    #     """
    #     depth = int(op[3:])
    #     mstart, msz = stk.pop(), stk.pop()
    #     topics = [stk.pop() for _ in range(depth)]
    #     self.memory.extend(mstart, msz)
    #     # Ignore external effects...

    # Calls
    def _call_handler(self, s0, s1, s2, s3, s4, s5, s6):
        ostart = s5 if concrete(s5) else z3.simplify(s5)
        olen = s6 if concrete(s6) else z3.simplify(s6)

        if concrete(s1) and s1 <= 8:
            if s1 == 4:
                logging.info("Calling precompiled identity contract")
                istart = s3 if concrete(s3) else z3.simplify(s3)
                ilen = s4 if concrete(s4) else z3.simplify(s4)
                self.memory.copy(istart, ilen, ostart, olen)
                return 1
            else:
                raise SymbolicError("Precompiled contract %d not implemented" % s1)
        else:
            for i in range(olen):
                self.memory[ostart + i] = z3.BitVec('EXT_%d_%d_%d' % (self.instruction_count, i, self.xid), 8)
            logging.info("Calling contract %s (%d_%d)" % (s1, self.instruction_count, self.xid))
            return z3.BitVec('CALLRESULT_%d_%d' % (self.instruction_count, self.xid), 256)

    def call_handler(self, s0, s1, s2, s3, s4, s5, s6):
        self.constraints.append(z3.UGE(self.balance, s2))
        self.balance -= s2
        return self._call_handler(s0, s1, s2, s3, s4, s5, s6)

    def callcode_handler(self, s0, s1, s2, s3, s4, s5, s6):
        return self._call_handler(s0, s1, s2, s3, s4, s5, s6)

    def delegatecall_handler(self, s0, s1, s3, s4, s5, s6):
        s2 = utils.ctx_or_symbolic('CALLVALUE', self.ctx, self.xid)
        return self._call_handler(s0, s1, s2, s3, s4, s5, s6)

    def staticcall_handler(self, s0, s1, s3, s4, s5, s6):
        s2 = 0
        return self._call_handler(s0, s1, s2, s3, s4, s5, s6)

    # Terminate
    def return_handler(self, s0, s1):
        if concrete(s0) and concrete(s1):
            self.memory.extend(s0, s1)
        self.constraints.append(z3.Or(*(z3.ULE(self.calldatasize, access) for access in self.calldata_accesses)))
        self.halt = True

    def stop_handler(self, ):
        self.constraints.append(z3.Or(*(z3.ULE(self.calldatasize, access) for access in self.calldata_accesses)))
        self.halt = True
