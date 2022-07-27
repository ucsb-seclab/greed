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

        uint index1 = 1024*1;
        uint index2 = 1024*2;
        uint index3 = 1024*3;
        uint index4 = 1024*4;
        uint index5 = 1024*5;
        uint index6 = 1024*6;

        assembly {
            mstore(index1, 42)
            mstore(index2, 42)
            a := keccak256(index1, 32)
            b := keccak256(index2, 32)
        }

        if (a != b) {
            assembly {log1(0, 0, "error:test_sha_equal")}
            revert();
        } else {
            assembly {log1(0, 0, "success:test_sha_equal")}
        }


        assembly {
            mstore(index3, 42)
            c := keccak256(index3, 32)
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
            mstore(index4, 43)
            d := keccak256(index4, 32)
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
            mstore(index5, 45)
            mstore(index6, 46)
            e := keccak256(index5, 32)
            f := keccak256(index6, 32)
        }

        if (e == f) {
            assembly {log1(0, 0, "error:test_sha_different")}
            revert();
        } else {
            assembly {log1(0, 0, "success:test_sha_different")}
        }


        assembly {
            mstore(index6, 45)
            g := keccak256(index6, 32)
        }

        if (e != g) {
            assembly {log1(0, 0, "error:test_sha_rewrite")}
            revert();
        } else {
            assembly {log1(0, 0, "success:test_sha_rewrite")}
        }

        assembly {log1(0, 0, "success:")}
    }

}
