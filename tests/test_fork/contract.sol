pragma solidity 0.8.7;

contract TestFork {

    function sstore(uint key, uint value) private {
        assembly {
            sstore(key, value)
        }
    }

    function sload(uint key) private view returns (uint value) {
        assembly {
            value := sload(key)
        }
    }

    function mstore(uint offset, uint value) private pure {
        assembly {
            mstore(offset, value)
        }
    }

    function mload(uint offset) private pure returns (uint value) {
        assembly {
            value := mload(offset)
        }
    }

    fallback() external {

        uint branch = 0;
        uint symbol = sload(0);

        if (symbol == 0) {
            branch = 0;
            sstore(42, 0x00);
            mstore(42, 0x00);
        } else {
            branch = 1;
            sstore(42, 0x01);
            mstore(42, 0x01);
        }

        if ((branch == 0) && (sload(42) != 0x00)) {
            assembly {log1(0, 0, "error:test_branch_storage")}
            revert();
        } else if ((branch == 1) && (sload(42) != 0x01)) {
            assembly {log1(0, 0, "error:test_branch_storage")}
            revert();
        }
        assembly {log1(0, 0, "success:test_branch_storage")}

        if ((branch == 0) && (mload(42) != 0x00)) {
            assembly {log1(0, 0, "error:test_branch_memory")}
            revert();
        } else if ((branch == 1) && (mload(42) != 0x01)) {
            assembly {log1(0, 0, "error:test_branch_memory")}
            revert();
        }
        assembly {log1(0, 0, "success:test_branch_memory")}


        assembly {log1(0, 0, "success:")}
    }
}
