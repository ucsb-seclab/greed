function __function_selector__() public {
    Begin block 0x0
    prev=[], succ=[0xb, 0xf]
    =================================
    0x0: v0(0x80) = CONST 
    0x2: v2(0x40) = CONST 
    0x4: MSTORE v2(0x40), v0(0x80)
    0x5: v5 = CALLVALUE 
    0x7: v7 = ISZERO v5
    0x8: v8(0xf) = CONST 
    0xa: JUMPI v8(0xf), v7

    Begin block 0xb
    prev=[0x0], succ=[]
    =================================
    0xb: vb(0x0) = CONST 
    0xe: REVERT vb(0x0), vb(0x0)

    Begin block 0xf
    prev=[0x0], succ=[0x3a, 0x63]
    =================================
    0x11: v11(0x0) = CONST 
    0x14: v14(0x0) = CONST 
    0x17: v17(0x2d) = CONST 
    0x19: v19(0xc18) = CONST 
    0x1c: MSTORE v19(0xc18), v17(0x2d)
    0x1d: v1d(0x2e) = CONST 
    0x1f: v1f(0x1000) = CONST 
    0x22: MSTORE v1f(0x1000), v1d(0x2e)
    0x23: v23(0x20) = CONST 
    0x25: v25(0xc18) = CONST 
    0x28: v28 = SHA3 v25(0xc18), v23(0x20)
    0x2b: v2b(0x20) = CONST 
    0x2d: v2d(0x2388) = CONST 
    0x30: v30 = SHA3 v2d(0x2388), v2b(0x20)
    0x35: v35 = EQ v28, v30
    0x36: v36 = ISZERO v35
    0x37: v37(0x63) = CONST 
    0x39: JUMPI v37(0x63), v36

    Begin block 0x3a
    prev=[0xf], succ=[]
    =================================
    0x3a: v3a(0x6572726f723a746573745f7368615f646966666572656e740000000000000000) = CONST 
    0x5b: v5b(0x0) = CONST 
    0x5e: LOG1 v5b(0x0), v5b(0x0), v3a(0x6572726f723a746573745f7368615f646966666572656e740000000000000000)
    0x5f: v5f(0x0) = CONST 
    0x62: REVERT v5f(0x0), v5f(0x0)

    Begin block 0x63
    prev=[0xf], succ=[]
    =================================
    0x64: v64(0x737563636573733a746573745f7368615f646966666572656e74000000000000) = CONST 
    0x85: v85(0x0) = CONST 
    0x88: LOG1 v85(0x0), v85(0x0), v64(0x737563636573733a746573745f7368615f646966666572656e74000000000000)
    0x8d: STOP 

}

