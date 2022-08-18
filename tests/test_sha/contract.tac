function __function_selector__() public {
    Begin block 0x0
    prev=[], succ=[0xc, 0x10]
    =================================
    0x0: v0(0x80) = CONST 
    0x2: v2(0x40) = CONST 
    0x4: MSTORE v2(0x40), v0(0x80)
    0x5: v5 = CALLVALUE 
    0x7: v7 = ISZERO v5
    0x8: v8(0x10) = CONST 
    0xb: JUMPI v8(0x10), v7

    Begin block 0xc
    prev=[0x0], succ=[]
    =================================
    0xc: vc(0x0) = CONST 
    0xf: REVERT vc(0x0), vc(0x0)

    Begin block 0x10
    prev=[0x0], succ=[0x50, 0x79]
    =================================
    0x12: v12(0x0) = CONST 
    0x15: v15(0x0) = CONST 
    0x18: v18(0x0) = CONST 
    0x1a: v1a(0x400) = CONST 
    0x1f: v1f(0x0) = CONST 
    0x21: v21(0x800) = CONST 
    0x26: v26(0xffffffff00000000) = CONST 
    0x30: MSTORE v1a(0x400), v26(0xffffffff00000000)
    0x31: v31(0xffffffffffffffff) = CONST 
    0x3b: MSTORE v21(0x800), v31(0xffffffffffffffff)
    0x3c: v3c(0x20) = CONST 
    0x3f: v3f = SHA3 v1a(0x400), v3c(0x20)
    0x42: v42(0x20) = CONST 
    0x45: v45 = SHA3 v21(0x800), v42(0x20)
    0x4a: v4a = EQ v3f, v45
    0x4b: v4b = ISZERO v4a
    0x4c: v4c(0x79) = CONST 
    0x4f: JUMPI v4c(0x79), v4b

    Begin block 0x50
    prev=[0x10], succ=[]
    =================================
    0x50: v50(0x6572726f723a746573745f7368615f6469666630786666000000000000000000) = CONST 
    0x71: v71(0x0) = CONST 
    0x74: LOG1 v71(0x0), v71(0x0), v50(0x6572726f723a746573745f7368615f6469666630786666000000000000000000)
    0x75: v75(0x0) = CONST 
    0x78: REVERT v75(0x0), v75(0x0)

    Begin block 0x79
    prev=[0x10], succ=[0xb2, 0xdb]
    =================================
    0x7a: v7a(0x737563636573733a746573745f7368615f646966663078666600000000000000) = CONST 
    0x9b: v9b(0x0) = CONST 
    0x9e: LOG1 v9b(0x0), v9b(0x0), v7a(0x737563636573733a746573745f7368615f646966663078666600000000000000)
    0x9f: v9f(0x1c) = CONST 
    0xa2: va2 = SHA3 v1a(0x400), v9f(0x1c)
    0xa5: va5(0x1c) = CONST 
    0xa8: va8 = SHA3 v21(0x800), va5(0x1c)
    0xad: vad = EQ va2, va8
    0xae: vae(0xdb) = CONST 
    0xb1: JUMPI vae(0xdb), vad

    Begin block 0xb2
    prev=[0x79], succ=[]
    =================================
    0xb2: vb2(0x6572726f723a746573745f7368615f64696666307866667061727469616c0000) = CONST 
    0xd3: vd3(0x0) = CONST 
    0xd6: LOG1 vd3(0x0), vd3(0x0), vb2(0x6572726f723a746573745f7368615f64696666307866667061727469616c0000)
    0xd7: vd7(0x0) = CONST 
    0xda: REVERT vd7(0x0), vd7(0x0)

    Begin block 0xdb
    prev=[0x79], succ=[]
    =================================
    0xdc: vdc(0x737563636573733a746573745f7368615f64696666307866667061727469616c) = CONST 
    0xfd: vfd(0x0) = CONST 
    0x100: LOG1 vfd(0x0), vfd(0x0), vdc(0x737563636573733a746573745f7368615f64696666307866667061727469616c)
    0x101: v101(0x737563636573733a000000000000000000000000000000000000000000000000) = CONST 
    0x122: v122(0x0) = CONST 
    0x125: LOG1 v122(0x0), v122(0x0), v101(0x737563636573733a000000000000000000000000000000000000000000000000)
    0x12c: STOP 

}

