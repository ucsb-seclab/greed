pragma solidity 0.8.7;

contract TestMemory {
    event Event(string message);

    function log(string memory message) private {
        //emit Event(message);
        assembly {
            // manually emit a technically invalid LOG1 that we
            // can then recognize and parse in the testing routine
            log1(0x0, 0x0, message)
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

    function mstore8(uint offset, uint value) private pure {
        assembly {
            mstore8(offset, value)
        }
    }

    // function msize() private pure returns (uint value) {
    //     assembly {
    //         value := msize()
    //     }
    // }

    fallback() external {

        mstore(0, 0xFF);
        if (mload(0) != 0x00000000000000000000000000000000000000000000000000000000000000FF) {
            log("error:test_mstore_0");
            revert();
        }
        log("success:test_mstore_0");

        mstore(1, 0xFF);
        if (mload(0) != 0x0000000000000000000000000000000000000000000000000000000000000000) {
            log("error:test_mstore_1");
            revert();
        }
        if (mload(1) != 0x00000000000000000000000000000000000000000000000000000000000000FF) {
            log("error:test_mstore_1");
            revert();
        }
        log("success:test_mstore_1");

        mstore8(0, 0xFFFF);
        if (mload(0) != 0xFF00000000000000000000000000000000000000000000000000000000000000) {
            log("error:test_mstore8_0");
            revert();
        }
        log("success:test_mstore8_0");

        mstore8(1, 0xFF);
        if (mload(0) != 0xFFFF000000000000000000000000000000000000000000000000000000000000) {
            log("error:test_mstore8_1");
            revert();
        }
        log("success:test_mstore8_1");

        // probably hard to test msize
        // if (msize() != 0x180) {
        //     log("error:test_msize");
        //     revert();
        // }
        // log("success:test_msize");

        log("success:");
    }
}
