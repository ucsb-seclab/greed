// SPDX-License-Identifier: GPL-3.0

pragma solidity 0.8.7;

contract TestSha {

    fallback() external {
        uint a;
        uint b;
        uint c;
        uint d;
        uint e;
        uint f;
        uint g;
        uint h;
        uint i;
        uint j;
        uint k;


        assembly {
            mstore(1000, 42)
            mstore(2000, 42)
            a := keccak256(1000, 32)
            b := keccak256(2000, 32)
        }

        if (a != b) {
            assembly {log1(0, 0, "error:test_sha_equal")}
            revert();
        } else {
            assembly {log1(0, 0, "success:test_sha_equal")}
        }


        assembly {
            mstore(3000, 42)
            c := keccak256(3000, 32)
        }

        if (a != c) {
            assembly {log1(0, 0, "error:test_sha_reuse_equal1")}
            revert();
        } else {
            assembly {log1(0, 0, "success:test_sha_reuse_equal1")}
        }

        if (b != c) {
            assembly {log1(0, 0, "error:test_sha_reuse_equal2")}
            revert();
        } else {
            assembly {log1(0, 0, "success:test_sha_reuse_equal2")}
        }


        assembly {
            mstore(4000, 43)
            d := keccak256(4000, 32)
        }

        if (a == d) {
            assembly {log1(0, 0, "error:test_sha_reuse_diff1")}
            revert();
        } else {
            assembly {log1(0, 0, "success:test_sha_reuse_diff1")}
        }

        if (b == d) {
            assembly {log1(0, 0, "error:test_sha_reuse_diff2")}
            revert();
        } else {
            assembly {log1(0, 0, "success:test_sha_reuse_diff2")}
        }


        assembly {
            mstore(5000, 0x0000000000000000000000000000000000000000000000000000000000000000ffffffff00000000)
            mstore(6000, 0x0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff)
            e := keccak256(5000, 29)
            f := keccak256(6000, 29)
        }

        if (e == f) {
            assembly {log1(0, 0, "error:test_sha_diff0xff")}
            revert();
        } else {
            assembly {log1(0, 0, "success:test_sha_diff0xff")}
        }


        assembly {
            g := keccak256(5000, 28)
            h := keccak256(6000, 28)
        }

        if (g != h) {
            assembly {log1(0, 0, "error:test_sha_diff0xffpartial")}
            revert();
        } else {
            assembly {log1(0, 0, "success:test_sha_diff0xffpartial")}
        }


        assembly {
            mstore(7000, 45)
            mstore(8000, 46)
            i := keccak256(7000, 32)
            j := keccak256(8000, 32)
        }

        if (i == j) {
            assembly {log1(0, 0, "error:test_sha_different")}
            revert();
        } else {
            assembly {log1(0, 0, "success:test_sha_different")}
        }

        assembly {log1(0, 0, "success:")}
    }

}
