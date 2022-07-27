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
    prev=[0x0], succ=[0x36, 0x3a]
    =================================
    0x11: v11(0x0) = CONST 
    0x14: v14(0x2a) = CONST 
    0x16: v16(0x3e8) = CONST 
    0x19: MSTORE v16(0x3e8), v14(0x2a)
    0x1a: v1a(0x2a) = CONST 
    0x1c: v1c(0x7d0) = CONST 
    0x1f: MSTORE v1c(0x7d0), v1a(0x2a)
    0x20: v20(0x20) = CONST 
    0x22: v22(0x3e8) = CONST 
    0x25: v25 = SHA3 v22(0x3e8), v20(0x20)
    0x28: v28(0x20) = CONST 
    0x2a: v2a(0x7d0) = CONST 
    0x2d: v2d = SHA3 v2a(0x7d0), v28(0x20)
    0x32: v32 = EQ v25, v2d
    0x33: v33(0x3a) = CONST 
    0x35: JUMPI v33(0x3a), v32

    Begin block 0x36
    prev=[0xf], succ=[]
    =================================
    0x36: v36(0x0) = CONST 
    0x39: REVERT v36(0x0), v36(0x0)

    Begin block 0x3a
    prev=[0xf], succ=[0x50, 0x79]
    =================================
    0x3b: v3b(0x2b) = CONST 
    0x3d: v3d(0x3e8) = CONST 
    0x40: MSTORE v3d(0x3e8), v3b(0x2b)
    0x41: v41(0x20) = CONST 
    0x43: v43(0x3e8) = CONST 
    0x46: v46 = SHA3 v43(0x3e8), v41(0x20)
    0x4b: v4b = EQ v46, v2d
    0x4c: v4c = ISZERO v4b
    0x4d: v4d(0x79) = CONST 
    0x4f: JUMPI v4d(0x79), v4c

    Begin block 0x50
    prev=[0x3a], succ=[]
    =================================
    0x50: v50(0x6572726f723a746573745f7368615f7265777269746500000000000000000000) = CONST 
    0x71: v71(0x0) = CONST 
    0x74: LOG1 v71(0x0), v71(0x0), v50(0x6572726f723a746573745f7368615f7265777269746500000000000000000000)
    0x75: v75(0x0) = CONST 
    0x78: REVERT v75(0x0), v75(0x0)

    Begin block 0x79
    prev=[0x3a], succ=[]
    =================================
    0x7a: v7a(0x737563636573733a746573745f7368615f726577726974650000000000000000) = CONST 
    0x9b: v9b(0x0) = CONST 
    0x9e: LOG1 v9b(0x0), v9b(0x0), v7a(0x737563636573733a746573745f7368615f726577726974650000000000000000)
    0x9f: v9f(0x737563636573733a000000000000000000000000000000000000000000000000) = CONST 
    0xc0: vc0(0x0) = CONST 
    0xc3: LOG1 vc0(0x0), vc0(0x0), v9f(0x737563636573733a000000000000000000000000000000000000000000000000)
    0xc6: STOP 

}

