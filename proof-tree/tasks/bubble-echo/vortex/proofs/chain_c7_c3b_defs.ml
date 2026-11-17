(* C3b definitions: the 9 new definitions of chain_c3b_final.spec (frozen 296578ea), text verbatim, by new_definition *)
let va1_rbinit_b = new_definition
 `va1_rbinit_b (tbl:num->int32) (k:num) =
    let t0 = (word_sx (tbl (128 * k)):int64) in
    let t1 = (word_sx (tbl (128 * k + 1)):int64) in
    let x = word_add t0 (word_ishr (word_add (word_mul (word_sub t1 t0) (word 251658)) (word 262144)) 19) in
    let y = if ival x > &1 then x else word 1 in
    word_add (word_zx (word_ushr (word_add y (word 1)) 1)) (word 251658):int32`;;
let va1_zpseed_b = new_definition
 `va1_zpseed_b (mdl:num->int32) (k:num) =
    let h = word_xor (word_add (word_mul (mdl 2) (word 3266489909)) (word 2769733223))
                     (word_mul (word_xor (word k) (word 2654435769)) (word 2246822507)):int32 in
    let g = word_mul (word_xor (word_ushr h 15) h) (word 739982445):int32 in
    let u = word_xor (word_ushr g 12) g in
    word_zx (word_ishr (word_add (word_mul (word_zx u:int64) (word 329853)) (word 18446176457274163200)) 48):int32`;;
let va1_bad_b = new_definition
 `va1_bad_b (mdl:num->int32) (tbl:num->int32)
          (ps:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32) =
    word_add (SND(SND(SND(SND(SND(SND ps))))))
     (word (nsum (0..2047)
       (\k. bitval (~(FST ps k = word 251658)) +
            bitval (~(FST(SND(SND ps)) k = word 0)) +
            bitval (~(FST(SND(SND(SND ps))) k = word 0)) +
            bitval (~(FST(SND(SND(SND(SND ps)))) k = word 0)) +
            bitval (~(FST(SND ps) k = va1_rbinit_b tbl k)) +
            bitval (~(FST(SND(SND(SND(SND(SND ps))))) k = va1_zpseed_b mdl k))))):int32`;;
let va1_rd32 = new_definition
 `va1_rd32 (base:num) (m:int64->byte) (k:num) = read (bytes32 (word (base + 4 * k))) m`;;
let va1_punct_clean = new_definition
 `va1_punct_clean (m:int64->byte) <=>
    read (bytes32 (word 16396)) m = word 4294967295 /\ read (bytes32 (word 16400)) m = word 0 /\
    va1_w32s 16408 24 (\k. word 0) m /\ va1_w32s 1130496 208896 (\k. word 0) m`;;
let va1_f25_post = new_definition
 `va1_f25_post (t:int32) (mdl:num->int32) (tbl:num->int32) (a0:int32) (a1:int32) (a2:int32) (m:int64->byte) <=>
    read (bytes32 (word 16396)) m = t /\ read (bytes32 (word 16400)) m = word 0 /\
    read (bytes32 (word 16408)) m = a0 /\ read (bytes32 (word 16412)) m = a1 /\
    read (bytes32 (word 16416)) m = a2 /\
    va1_w32s 1130496 2048 (\k. word 251658) m /\ va1_w32s 1138688 2048 (va1_rbinit_b tbl) m /\
    va1_w32s 1146880 6144 (\k. word 0) m /\ va1_w32s 1171456 2048 (va1_zpseed_b mdl) m /\
    va1_w32s 1179648 196608 (\k. word 0) m`;;
let va1_f25_frame = new_definition
 `va1_f25_frame (m0:int64->byte) (m:int64->byte) <=>
    !a. a < 4194304 /\ ~(16396 <= a /\ a < 16404) /\ ~(16408 <= a /\ a < 16504) /\
        ~(1130496 <= a /\ a < 1966080)
        ==> read (bytes8 (word a)) m = read (bytes8 (word a)) m0`;;
let va1_unpunct_post = new_definition
 `va1_unpunct_post (m1:int64->byte) (m2:int64->byte) <=>
    read (bytes32 (word 16404)) m2 =
      word_add (read (bytes32 (word 16404)) m1)
               (va1_bad_b (va1_rd32 16640 m1) (va1_rd32 65536 m1)
                        (va1_rd32 1130496 m1, va1_rd32 1138688 m1, va1_rd32 1146880 m1,
                         va1_rd32 1155072 m1, va1_rd32 1163264 m1, va1_rd32 1171456 m1,
                         read (bytes32 (word 16400)) m1)) /\
    read (bytes32 (word 16396)) m2 = word 4294967295 /\ read (bytes32 (word 16400)) m2 = word 0 /\
    va1_w32s 16408 24 (\k. word 0) m2 /\ va1_w32s 1130496 208896 (\k. word 0) m2`;;
let va1_unpunct_frame = new_definition
 `va1_unpunct_frame (m1:int64->byte) (m2:int64->byte) <=>
    !a. a < 4194304 /\ ~(16396 <= a /\ a < 16504) /\ ~(1130496 <= a /\ a < 1966080)
        ==> read (bytes8 (word a)) m2 = read (bytes8 (word a)) m1`;;
