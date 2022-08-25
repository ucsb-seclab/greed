
import ast
import itertools
import logging
import re

import eth_abi

from eth_abi.tools import get_abi_strategy

log = logging.getLogger("InitCtxGenerator")
log.setLevel(logging.INFO)


# Whenever there is an array, we put X elements
DYNAMIC_ARRAY_MAX_SIZE = 4

# Whenever there is bytes, we use X of them.
DYNAMIC_BYTES_MAX_SIZE = 8

def get_calldata_for(func):
    f_proto = func.name
    
    # Drop the function's name
    f_args = ''.join(list(itertools.dropwhile(lambda x: x != '(', f_proto)))
    
    # Convert the function prototype into a list of types
    f_args_original = [ arg.to_type_str() for arg in eth_abi.base.parse(f_args).components]

    # Void function, we skip it.
    if f_args == '()':
        log.warning(f"Function {func.name} has no args. Skipping")
        return None, None
    else:
        log.info(f"Generating CALLDATA for function {f_proto}")

        abi_strategy = get_abi_strategy(f_args)

        # I tweaked the strategy to let the example return:
        
        # TODO: create an API to use this withing eth_abi 

        #  - Fixed array sizes
        #  - Fixed bytes sizes
        #  - uint/int with min value that covers ALL their bits (i.e., a uint256 cannot be just 0x00)
        decoded = abi_strategy.example()

        # Creating the replacement dictionary to simbolize CALLDATA.
        
        # TODO flatten it! 
        decoded_flatten = decoded
        
        replacement_dict = {}

        for val in decoded_flatten:
            # This is an address
            if type(val) == str:
                addr = val.replace("0x",'').lower()
                replacement_dict[addr] = "SS" * (len(addr)//2)
            # This is an numeric constant
            elif type(val) == int:
                n_bits = len(bin(val).replace("0b",''))
                n_bytes = n_bits // 8
                num = hex(val).replace("0x",'').zfill(n_bytes).lower()
                replacement_dict[num] = "SS" * (len(num)//2)
            # This is raw bytes
            elif type(val) == bytes:
                repr_bytes = val.hex().lower()
                replacement_dict[repr_bytes] = "SS" * (len(repr_bytes)//2)

        import ipdb; ipdb.set_trace()

        # Encode it!
        calldata = eth_abi.encode(f_args_original, ast.literal_eval(str(decoded))).hex()

        # Replace our data with "SS"
        for replacement_who, replacement_what in replacement_dict.items():
            calldata = calldata.replace(replacement_who, replacement_what)
        
        calldata = func.signature + calldata
        
        return calldata,len(calldata)