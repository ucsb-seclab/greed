pragma solidity 0.8.7;

contract TestFork {
    //event Event(string message);

    function log(string memory message) private {
        //emit Event(message);
        assembly {
            // manually emit a technically invalid LOG1 that we
            // can then recognize and parse in the testing routine
            log1(0x0, 0x0, message)
        }
    }

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
            log("error:test_branch_storage");
            revert();
        } else if ((branch == 1) && (sload(42) != 0x01)) {
            log("error:test_branch_storage");
            revert();
        }
        log("success:test_branch_storage");

        if ((branch == 0) && (mload(42) != 0x00)) {
            log("error:test_branch_memory");
            revert();
        } else if ((branch == 1) && (mload(42) != 0x01)) {
            log("error:test_branch_memory");
            revert();
        }
        log("success:test_branch_memory");


        log("success:");
    }
}
