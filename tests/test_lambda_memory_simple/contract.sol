pragma solidity 0.8.7;

contract TestMemory {

    function mload(uint offset) private pure returns (bytes32 value) {
        assembly {
            value := mload(offset)
        }
    }


    // memOffset: where to copy the calldata in memory 
    // cdataOffset: where to copy from 
    // size: the amount of bytes to copy from calldata 
    // unknown_index: where to do the 'store over copy' operation
    // unknown_val: what to store at 'unknown_index'
    // expects: the list of 32 bytes slots we expect to read with the load over memcpy
    function test_1(uint256 memOffset, uint256 cdataOffset, uint256 size, uint256 unknown_index, bytes32 unknown_val, bytes32 [] calldata expects) public{
        
        
        // Copy some data from calldata
        assembly{
            calldatacopy(memOffset, cdataOffset, size)
        }

        // We need to move this because of the function signature.
        memOffset += 4;

       
        // Checking that the stuff we just copied matches what we expected
        // (load over memcpy)
        uint slots = size/32;
        for(uint i=0; i<slots; i++){
            if(mload(memOffset+i*32) != expects[i]){
                assembly{log1(0,0, "error:test_load_over_memcopy")}
                revert();
            }
        }

        assembly {log1(0, 0, "success:test_load_over_memcopy")}
        assembly {log1(0, 0, "success:")}
    }
}
