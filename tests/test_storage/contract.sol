pragma solidity 0.8.7;

contract TestStorage {

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
            assembly {log1(0, 0, "error:test_sstore_0")}
            revert();
        }
        assembly {log1(0, 0, "success:test_sstore_0")}

        sstore(8965, 0xFF);
        if (sload(0) != 0xFFFF) {
            assembly {log1(0, 0, "error:test_sstore_8965")}
            revert();
        }
        if (sload(8965) != 0xFF) {
            assembly {log1(0, 0, "error:test_sstore_8965")}
            revert();
        }
        assembly {log1(0, 0, "success:test_sstore_8965")}

        assembly {log1(0, 0, "success:")}
    }
}
