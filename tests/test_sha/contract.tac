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
    prev=[0x0], succ=[0x36, 0x5f]
    =================================
    0x11: v11(0x0) = CONST 
    0x14: v14(0x2a) = CONST 
    0x16: v16(0x400) = CONST 
    0x19: MSTORE v16(0x400), v14(0x2a)
    0x1a: v1a(0x2a) = CONST 
    0x1c: v1c(0x800) = CONST 
    0x1f: MSTORE v1c(0x800), v1a(0x2a)
    0x20: v20(0x20) = CONST 
    0x22: v22(0x400) = CONST 
    0x25: v25 = SHA3 v22(0x400), v20(0x20)
    0x28: v28(0x20) = CONST 
    0x2a: v2a(0x800) = CONST 
    0x2d: v2d = SHA3 v2a(0x800), v28(0x20)
    0x32: v32 = EQ v25, v2d
    0x33: v33(0x5f) = CONST 
    0x35: JUMPI v33(0x5f), v32

    Begin block 0x36
    prev=[0xf], succ=[]
    =================================
    0x36: v36(0x6572726f723a746573745f7368615f657175616c000000000000000000000000) = CONST 
    0x57: v57(0x0) = CONST 
    0x5a: LOG1 v57(0x0), v57(0x0), v36(0x6572726f723a746573745f7368615f657175616c000000000000000000000000)
    0x5b: v5b(0x0) = CONST 
    0x5e: REVERT v5b(0x0), v5b(0x0)

    Begin block 0x5f
    prev=[0xf], succ=[0xa8, 0xd1]
    =================================
    0x60: v60(0x737563636573733a746573745f7368615f657175616c00000000000000000000) = CONST 
    0x81: v81(0x0) = CONST 
    0x84: LOG1 v81(0x0), v81(0x0), v60(0x737563636573733a746573745f7368615f657175616c00000000000000000000)
    0x85: v85(0x2a) = CONST 
    0x87: v87(0x400) = CONST 
    0x8a: MSTORE v87(0x400), v85(0x2a)
    0x8b: v8b(0x2b) = CONST 
    0x8d: v8d(0x800) = CONST 
    0x90: MSTORE v8d(0x800), v8b(0x2b)
    0x91: v91(0x20) = CONST 
    0x93: v93(0x400) = CONST 
    0x96: v96 = SHA3 v93(0x400), v91(0x20)
    0x99: v99(0x20) = CONST 
    0x9b: v9b(0x800) = CONST 
    0x9e: v9e = SHA3 v9b(0x800), v99(0x20)
    0xa3: va3 = EQ v96, v9e
    0xa4: va4 = ISZERO va3
    0xa5: va5(0xd1) = CONST 
    0xa7: JUMPI va5(0xd1), va4

    Begin block 0xa8
    prev=[0x5f], succ=[]
    =================================
    0xa8: va8(0x6572726f723a746573745f7368615f646966666572656e740000000000000000) = CONST 
    0xc9: vc9(0x0) = CONST 
    0xcc: LOG1 vc9(0x0), vc9(0x0), va8(0x6572726f723a746573745f7368615f646966666572656e740000000000000000)
    0xcd: vcd(0x0) = CONST 
    0xd0: REVERT vcd(0x0), vcd(0x0)

    Begin block 0xd1
    prev=[0x5f], succ=[]
    =================================
    0xd2: vd2(0x737563636573733a746573745f7368615f646966666572656e74000000000000) = CONST 
    0xf3: vf3(0x0) = CONST 
    0xf6: LOG1 vf3(0x0), vf3(0x0), vd2(0x737563636573733a746573745f7368615f646966666572656e74000000000000)
    0xf9: STOP 

}

