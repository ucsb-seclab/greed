pragma solidity 0.8.7;

contract TestStorage {
    event Event(string message);

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

    fallback() external {

        sstore(0, 0xFFFF);
        if (sload(0) != 0xFFFF) {
            log("error:test_sstore_0");
            revert();
        }
        log("success:test_sstore_0");

        sstore(8965, 0xFF);
        if (sload(0) != 0xFFFF) {
            log("error:test_sstore_8965");
            revert();
        }
        if (sload(8965) != 0xFF) {
            log("error:test_sstore_8965");
            revert();
        }
        log("success:test_sstore_8965");

        log("success:");
    }
}
