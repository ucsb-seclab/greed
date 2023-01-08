function __function_selector__() public {
    Begin block 0x0
    prev=[], succ=[0x11, 0x15]
    =================================
    0x0: v0(0x80) = CONST 
    0x2: v2(0x40) = CONST 
    0x4: MSTORE v2(0x40), v0(0x80)
    0x5: v5(0x0) = CONST 
    0x7: v7(0x1) = CONST 
    0x9: v9(0x0) = CONST 
    0xb: vb = SLOAD v9(0x0)
    0xc: vc = EQ vb, v7(0x1)
    0xd: vd = ISZERO vc
    0xe: ve(0x15) = CONST 
    0x10: JUMPI ve(0x15), vd

    Begin block 0x11
    prev=[0x0], succ=[0x15]
    =================================
    0x11: v11(0x1) = CONST 

    Begin block 0x15
    prev=[0x0, 0x11], succ=[0x1f, 0x27]
    =================================
    0x15_0x0: v15_0 = PHI v5(0x0), v11(0x1)
    0x16: v16(0x1) = CONST 
    0x19: v19 = EQ v15_0, v16(0x1)
    0x1b: v1b = ISZERO v19
    0x1c: v1c(0x27) = CONST 
    0x1e: JUMPI v1c(0x27), v1b

    Begin block 0x1f
    prev=[0x15], succ=[0x27]
    =================================
    0x20: v20(0x1) = CONST 
    0x22: v22(0x0) = CONST 
    0x24: v24 = SLOAD v22(0x0)
    0x25: v25 = EQ v24, v20(0x1)
    0x26: v26 = ISZERO v25

    Begin block 0x27
    prev=[0x15, 0x1f], succ=[0x2c, 0x55]
    =================================
    0x27_0x0: v27_0 = PHI v19, v26
    0x28: v28 = ISZERO v27_0
    0x29: v29(0x55) = CONST 
    0x2b: JUMPI v29(0x55), v28

    Begin block 0x2c
    prev=[0x27], succ=[]
    =================================
    0x2c: v2c(0x6572726f723a746573745f7068695f696d706f737369626c655f6272616e6368) = CONST 
    0x4d: v4d(0x0) = CONST 
    0x50: LOG1 v4d(0x0), v4d(0x0), v2c(0x6572726f723a746573745f7068695f696d706f737369626c655f6272616e6368)
    0x51: v51(0x0) = CONST 
    0x54: REVERT v51(0x0), v51(0x0)

    Begin block 0x55
    prev=[0x27], succ=[]
    =================================
    0x56: v56(0x737563636573733a000000000000000000000000000000000000000000000000) = CONST 
    0x77: v77(0x0) = CONST 
    0x7a: LOG1 v77(0x0), v77(0x0), v56(0x737563636573733a000000000000000000000000000000000000000000000000)
    0x7c: STOP 

}

