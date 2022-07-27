// SPDX-License-Identifier: GPL-3.0

pragma solidity 0.8.7;

contract TestShaOverlapping {

    fallback() external {
        uint addr1;
        uint addr2;

        assembly {
            mstore(1000, 42)
            mstore(2000, 43)
            addr1 := keccak256(1000, 32)
            addr2 := keccak256(2000, 32)
        }

        uint addr1plus100 = addr1 + 100;
        uint addr2plus200 = addr2 + 200;

        if (addr1plus100 == addr2plus200) {
            assembly {log1(0, 0, "error:test_sha_overlapping")}
            revert();
        } else {
            assembly {log1(0, 0, "success:test_sha_overlapping")}
        }

        assembly {log1(0, 0, "success:")}
    }

}
