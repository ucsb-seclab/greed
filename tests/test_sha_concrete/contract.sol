pragma solidity 0.8.7;

contract TestMemory {

    function mload(uint offset) private pure returns (bytes32 value) {
        assembly {
            value := mload(offset)
        }
    }

    function sload(uint offset) private view returns (bytes32 value) {
        assembly {
            value := sload(offset)
        }
    }

    function test_1(string calldata _name) public{

        // this is the keccak of the "test_address" string
        uint256 test_address = 0xcf0b1b5014de87f401af85ff4516711708f22a5140af0526c338de218bd6b126;

        uint deadbeef = 0xdeadbeef;
        bytes32 deadbeef_b = bytes32(abi.encodePacked(deadbeef));
        uint cafebabe = 0xcafebabe;
        bytes32 cafebabe_b = bytes32(abi.encodePacked(cafebabe));

        assembly{
            sstore(test_address, deadbeef_b)
        }

        uint256 sha_res = uint256(keccak256(abi.encodePacked(_name)));

        if(sha_res != test_address){
            assembly {log1(0, 0, "error:test_lamb_sha_concrete1")}
            revert();
        } else {
            assembly {log1(0, 0, "success:test_lamb_sha_concrete1")}
        }


        bytes32 mem_data = sload(sha_res);

        // We can only check if this is possible, NOT that this MUST happen.
        if(mem_data == deadbeef_b){

            // If we are here, sha_res should be fixed to the address 
            // that loads 0xdeadbeef from storage

            // Now, if we overwrite that storage location we 
            // shouldn't be able to say that the two are equal! 
            assembly{
                sstore(test_address, cafebabe_b)
            }

            // Verify that I cannot load 0xdeadbeef from storage since 
            // I just overwritten it with 0xcafebabe
            mem_data = sload(test_address);
            if(mem_data == deadbeef_b){
                assembly {log1(0, 0, "error:test_lamb_sha_concrete2")}
                revert();
            } else {
                assembly {log1(0, 0, "success:test_lamb_sha_concrete2")}
            }


            if(mem_data != cafebabe_b){
                assembly {log1(0, 0, "error:test_lamb_sha_concrete3")}
                revert();
            } else {
                assembly {log1(0, 0, "success:test_lamb_sha_concrete3")}
            }


            // Now, since sha_res should be fixed (it was loading 0xdeadbeef before)
            // I should be able to verify that I cannot load 0xdeadbeef anymore

            // Try to load from the address calculated from user.
            mem_data = sload(sha_res);
            if(mem_data == deadbeef_b){
                assembly {log1(0, 0, "error:test_lamb_sha_concrete4")}
                revert();
            }else{
            assembly {log1(0, 0, "success:test_lamb_sha_concrete4")}
            assembly {log1(0, 0, "success:")}
            }
        }            
    }
}