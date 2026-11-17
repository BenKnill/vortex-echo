(* ========================================================================= *)
(* Vortex pop R5, ripple (corrugation) kick: the explicit kick function      *)
(* va1_ck, the witness for the named premise va1_corrk_ok of                 *)
(* pop_design_defs.ml (SPEC-corr, Claude Opus 5.5, vortex-r5 2026-11-11).    *)
(*                                                                           *)
(* va1_ck is transcribed from the BYTES of vortex_a1.wasm function 17        *)
(* (ve_corr_kick; f18 ve_corr_unkick is byte-identical up to pc 1382), not   *)
(* from the C source: every operation is the WASM integer operation the      *)
(* bytes execute, in the bytes' operand order (i64 words: wrapping add, sub, *)
(* mul; word_ishr = i64.shr_s, word_ushr = i64.shr_u, word_udiv = div_u,     *)
(* iword (wtdiv ..) = div_s; i32 words for the phase and the hashes). Each   *)
(* select of the bytes is an if-then-else whose condition is the compare the *)
(* bytes perform (signed ival or unsigned val, constants reduced).           *)
(*                                                                           *)
(* f17 = loop 1 (pc 41-375): LAP[k] = va1_ck_lap rb zq k  (i64, scratch     *)
(*         2015232 + 8k), k < 2048;                                          *)
(*       loop 2 (pc 467-1348): KZ[k] = va1_ck_kk .. (va1_ck_lap rb zq) k    *)
(*         (i32, scratch 2007040 + 4k), k < 2048; it reads LAP, ZQ, RB, TBL, *)
(*         model word 2 (ZSEED, 16648), T (16392), P (16396), local 0 = sub; *)
(*       loop 3 (pc 1354-1485): ZP[k] += KZ[k] (f18: ZP[k] -= KZ[k]).        *)
(* So va1_corrk_ok va1_ck says: the kick adds, and the un-kick subtracts,    *)
(* exactly va1_ck mdl hp tbl t p sub rb zq k at every bead k < 2048.         *)
(*                                                                           *)
(* Bead index arithmetic of the bytes: (k + 1) & 2047 = (k + 1) MOD 2048 and *)
(* (k - 1) & 2047 = (k + 2047) MOD 2048 for k < 2048. The table row of bead  *)
(* k starts at word 128 k; the column is val ((r >>u 17) & 32764) DIV 4.     *)
(* hp (the pop header words 6..31) is not read by f17; it stays an argument *)
(* because va1_corrk_ok fixes the type of CK.                                *)
(* ========================================================================= *)

needs "ve_vort.ml";;
needs "ve_tick.ml";;
needs "ve_vk.ml";;
needs "va1_code.ml";;
needs "va1_seq_final2.ml";;
needs "pop_design_defs.ml";;

(* phase of a radius (u32 turns, 2^24 rad -> 2^-32 turn): x = sx r (loop 1, *)
(* pc 139-153) or zx r (loop 2, pc 992-1003)                                 *)
let va1_ck_ph = new_definition
 `va1_ck_ph (x:int64) = (word_zx (word_ushr (word_mul x (word 2670177)) 16):int32)`;;

(* one nested Taylor step t' = 2^30 - ((t * ((x2 * c) >>u 30)) >>u 30)        *)
let va1_ck_tstep = new_definition
 `va1_ck_tstep (x2:int64) (c:num) (t:int64) =
    word_sub (word 1073741824) (word_ushr (word_mul t (word_ushr (word_mul x2 (word c)) 30)) 30)`;;

(* |sin| of the phase, Q30, before the sign: quadrant fold (bit 30), x = f   *)
(* pi/2 in Q30, the Taylor series to x^13 (loop 1 pc 154-295, loop 2 pc      *)
(* 1004-1145; the same instructions)                                         *)
let va1_ck_sinmag = new_definition
 `va1_ck_sinmag (ph:int32) =
    let f = word_and ph (word 1073741823) in
    let ff = if word_and ph (word 1073741824) = word 0 then f else word_sub (word 1073741824) f in
    let x = word_ushr (word_mul (word_zx ff:int64) (word 1686629713)) 30 in
    let x2 = word_ushr (word_mul x x) 30 in
    let t1 = word_sub (word 1073741824) (word_ushr (word_mul x2 (word 6882960)) 30) in
    let t6 = va1_ck_tstep x2 178956971 (va1_ck_tstep x2 53687091 (va1_ck_tstep x2 25565282
               (va1_ck_tstep x2 14913081 (va1_ck_tstep x2 9761289 t1)))) in
    word_ushr (word_mul t6 x) 30`;;

(* sigma = 2^46 div_u ((s2 * s2) >>u 30), s2 the floored sine (Q16)          *)
let va1_ck_sig = new_definition
 `va1_ck_sig (s2:int64) =
    word_udiv (word 70368744177664) (word_ushr (word_mul s2 s2) 30)`;;

(* loop 1 (pc 41-375): LAP[k] = (dq * sigma(rb k)) >>s 12, with the signed  *)
(* sine (negated when the phase is negative) floored at SIN035 (signed)     *)
let va1_ck_lap = new_definition
 `va1_ck_lap (rb:num->int32) (zq:num->int32) (k:num) =
    let dq = word_add (word_sub (word_sx (zq ((k + 1) MOD 2048)))
                                (word_shl (word_sx (zq k)) 1))
                      (word_sx (zq ((k + 2047) MOD 2048))):int64 in
    let ph = va1_ck_ph (word_sx (rb k)) in
    let s = va1_ck_sinmag ph in
    let sv = if ival ph < &0 then word_sub (word 0) s else s in
    let s2 = if ival sv > &375809638 then sv else word 375809638 in
    word_ishr (word_mul dq (va1_ck_sig s2)) 12`;;

(* the hash finaliser of hash2: h ^= h >>u 15; h *= 0x2C1B3C6D; h ^= h >>u 12 *)
let va1_ck_hfin = new_definition
 `va1_ck_hfin (h:int32) =
    let h1 = word_mul (word_xor (word_ushr h 15) h) (word 739982445) in
    word_xor (word_ushr h1 12) h1`;;

(* the table speed at radius r of bead k (pc 496-555), clamped below at 1   *)
let va1_ck_spd = new_definition
 `va1_ck_spd (tbl:num->int32) (r:int32) (k:num) =
    let j = val (word_and (word_ushr r 17) (word 32764):int32) DIV 4 in
    let a = (word_sx (tbl (128 * k + j)):int64) in
    let b = (word_sx (tbl (128 * k + j + 1)):int64) in
    let v = word_add (word_ishr (word_add (word_mul (word_sub b a)
                                                     (word_zx (word_and r (word 524287)):int64))
                                           (word 262144)) 19) a in
    if ival v > &1 then v else word 1`;;

(* the corrugation envelope on16(r) (pc 808-939): the off smoothstep at      *)
(* pi - 0.30 (div_s, clamped to 0 .. 65536) and the on smoothstep at 0.10    *)
(* (div_u, clamped above at 65536), product >>s 16                           *)
let va1_ck_on = new_definition
 `va1_ck_on (r:int32) =
    let r16 = word_shl (word_zx r:int64) 16 in
    let t0 = iword (wtdiv (ival (word_add r16 (word 18446740949345370112))) (&3355443)):int64 in
    let t1 = if ival t0 > &0 then t0 else word 0 in
    let t2 = if ival t1 < &65536 then t1 else word 65536 in
    let off = word_ushr (word_mul (word_ushr (word_mul t2 t2) 16)
                                  (word_sub (word 196608) (word_shl t2 1))) 16 in
    let u0 = word_udiv (word_add r16 (word 18446743963758362624)) (word 3355443):int64 in
    let u1 = if val u0 < 65536 then u0 else word 65536 in
    let on = word_ushr (word_mul (word_ushr (word_mul u1 u1) 16)
                                 (word_sub (word 196608) (word_shl u1 1))) 16 in
    word_ishr (word_mul (word_sub (word 65536) off) on) 16`;;

(* the pinch-length quotient zp_of(k, spd) >> 3 of the bytes (pc 648-750):  *)
(* hash2(k, ZSEED + 1), its square, 2^24 fixed point, div_u by spd           *)
let va1_ck_zpq = new_definition
 `va1_ck_zpq (mdl:num->int32) (spd:int64) (k:num) =
    let h = va1_ck_hfin (word_xor (word_add (word_mul (mdl 2) (word 3266489909)) (word 1741255836))
                                  (word_mul (word_xor (word k) (word 2654435769)) (word 2246822507))) in
    let hz = (word_zx h:int64) in
    word_udiv (word_mul (word_ushr (word_add (word_mul (word_ushr (word_mul (word_ushr (word_mul hz hz) 32)
                                                                            (word 104858)) 32)
                                                       (word 1342177))
                                             (word 39582141907)) 16)
                        (word 421657))
              spd`;;

(* the jitter hash hash2(k ^ ZSEED, (T - P) * 8 + sub) of the bytes (pc     *)
(* 376-427 and 581-618)                                                      *)
let va1_ck_hj = new_definition
 `va1_ck_hj (mdl:num->int32) (t:int32) (p:int32) (sub:num) (k:num) =
    va1_ck_hfin (word_xor (word_mul (word_xor (word k) (word_xor (mdl 2) (word 2654435769)))
                                    (word 2246822507))
                          (word_add (word_mul (word_add (word_shl (word_sub t p) 3) (word sub))
                                              (word 3266489909))
                                    (word 2769733223)))`;;

(* loop 2 (pc 467-1348): KZ[k] for bead k, given the LAP contents lap.      *)
(* Outside [ON0, RIM_STOP) (the unsigned test (r - 1677722) >u 50693911 at  *)
(* pc 482-494) the kick is 0.                                                *)
let va1_ck_kk = new_definition
 `va1_ck_kk (mdl:num->int32) (tbl:num->int32) (t:int32) (p:int32) (sub:num)
            (rb:num->int32) (zq:num->int32) (lap:num->int64) (k:num) =
    let r = rb k in
    if val (word_add r (word 4293289574):int32) > 50693911 then (word 0:int32) else
    let spd = va1_ck_spd tbl r k in
    let sq13 = word_mul (word_mul spd spd) (word 13107) in
    let am = word_ishr sq13 24 in
    let jit = word_ishr (word_mul (word_ishr (word_mul am (word 8589935)) 32)
                                  (word_add (word_zx (va1_ck_hj mdl t p sub k))
                                            (word 18446744071562067968))) 32 in
    let z = (word_sx (zq k):int64) in
    let hi = if ival (word_mul z (word 5)) > ival (word_shl (va1_ck_zpq mdl spd k) 3)
             then word 0 else word_ishr sq13 25 in
    let l2 = word_add (word_sub (lap ((k + 1) MOD 2048)) (word_shl (lap k) 1))
                      (lap ((k + 2047) MOD 2048)) in
    let on = va1_ck_on r in
    let s = va1_ck_sinmag (va1_ck_ph (word_zx r)) in
    let sg = va1_ck_sig (if val s > 375809638 then s else word 375809638) in
    let b24 = word_ishr (iword (wtdiv (ival (word_mul (word_mul on sg) (word 11127432))) (ival spd))) 16 in
    let tb = word_ishr (word_mul l2 b24) 12 in
    let a32 = word_ishr (word_mul (word_ishr (word_mul (word_ushr (word_mul spd (word 56966666)) 16) on) 16)
                                  sg) 16 in
    let dq = word_add (word_sub (word_sx (zq ((k + 1) MOD 2048))) (word_shl z 1))
                      (word_sx (zq ((k + 2047) MOD 2048))) in
    let f = word_sub (word 0) (word_add tb (word_ishr (word_mul a32 dq) 16)) in
    let f1 = if ival hi < ival f then hi else f in
    let lo = word_sub (word 0) (word_ishr (word_mul am (word 22938)) 16) in
    let f2 = if ival f1 > ival lo then f1 else lo in
    word_zx (word_ushr (word_add (word_add jit f2) (word 131072)) 18)`;;

(* the witness: the kick of bead k (KZ[k] after loops 1 and 2)               *)
let va1_ck = new_definition
 `va1_ck (mdl:num->int32) (hp:num->int32) (tbl:num->int32) (t:int32) (p:int32) (sub:num)
         (rb:num->int32) (zq:num->int32) (k:num) =
    va1_ck_kk mdl tbl t p sub rb zq (va1_ck_lap rb zq) k`;;

(* the R5 statements as strings (pop_design_stmts.ml convention); pop_r5_corr.spec pins the same text *)
let pop_r5_spec_VA1_CORRK_OK = "va1_corrk_ok va1_ck";;
let pop_r5_spec_VA1_CORRK_SAT = "?CK. va1_corrk_ok CK";;
