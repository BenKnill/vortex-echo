(* ========================================================================= *)
(* Vortex chain C8a (vortex-chain-20261111-142342, Claude Opus 5.5,          *)
(* 2026-11-14): droplet birth as a named formula. va1_born is the list of    *)
(* records f13 (ve_birth_apply) of vortex_a1.wasm appends, as a closed       *)
(* function of what f13 reads: model word 2 (ZSEED), header words hp 3..11   *)
(* (bytes 16420..16452), T, the speed table, RA, RB, ZQ, ZP and ND.          *)
(*                                                                           *)
(* Transcribed from the BYTES of f13 (6097 B), not from the C source, in the *)
(* style of pop_r5_corr_defs.ml: every operation is the WASM integer         *)
(* operation the bytes execute, in the bytes' operand order (word_ishr =     *)
(* shr_s, word_ushr = shr_u, iword (wtdiv ..) = div_s, word_udiv = div_u,    *)
(* word_zx/word_sx = extend/wrap); each select or br_if is an if-then-else   *)
(* on the compare the bytes perform (constants reduced). The isqrt loops     *)
(* (32 rounds, counter 32 down to 1) are ve_isq 32 of ve_vk_defs.ml; the     *)
(* hash finaliser, table speed, pinch quotient, Taylor step and radius phase *)
(* are the frozen va1_ck_* helpers of pop_r5_corr_defs.ml (same instruction  *)
(* shapes). Pc numbers are body-relative (c8a/evidence/decomp-f13.txt).      *)
(*                                                                           *)
(* Loop 1 (pinch-off, pc 144-2610), loop 2 (spray, 2704-4390) and loop 3     *)
(* (antipode, 4491-6083) visit k = 0..2047 in order and stop when the count  *)
(* ND + LENGTH L reaches 16384 (f13 skips loop 1 when ND > 16383 and loops   *)
(* 2/3 when the count is > 16383). Loop 1 debits ZQ[k] and ZP[k] by the new  *)
(* record's words 8 and 9, and a later bead's local-maximum test reads the   *)
(* debited ZQ, so loop 1 is a left fold over (L, zq, zp). Loops 2 and 3 read *)
(* neither ZQ nor ZP. f13 reads no DI word (record words 10 and 11 are the   *)
(* old DI words, zero by va1_log_ok) and no scratch or VA/VB address.        *)
(* ========================================================================= *)

needs "pop_r5_corr_defs.ml";;

(* a 12-word record from its ten stored words; words 10 and 11 are zero      *)
let va1_rec12 = new_definition
 `va1_rec12 (w0:int32) (w1:int32) (w2:int32) (w3:int32) (w4:int32) (w5:int32)
            (w6:int32) (w7:int32) (w8:int32) (w9:int32) =
    (\i. if i = 0 then w0 else if i = 1 then w1 else if i = 2 then w2 else
         if i = 3 then w3 else if i = 4 then w4 else if i = 5 then w5 else
         if i = 6 then w6 else if i = 7 then w7 else if i = 8 then w8 else
         if i = 9 then w9 else word 0)`;;

(* the Taylor sine of a folded phase fraction ff (Q30 result, no sign): the  *)
(* instruction block that follows every quadrant fold in f13                 *)
let va1_b_sinf = new_definition
 `va1_b_sinf (ff:int32) =
    let x = word_ushr (word_mul (word_zx ff:int64) (word 1686629713)) 30 in
    let x2 = word_ushr (word_mul x x) 30 in
    let t1 = word_sub (word 1073741824) (word_ushr (word_mul x2 (word 6882960)) 30) in
    let t6 = va1_ck_tstep x2 178956971 (va1_ck_tstep x2 53687091 (va1_ck_tstep x2 25565282
               (va1_ck_tstep x2 14913081 (va1_ck_tstep x2 9761289 t1)))) in
    word_ushr (word_mul t6 x) 30`;;

(* sin and cos of the bead phase pk (= k << 21 in loops 1 and 2, the strength-reduced *)
(* 2097152 k in loop 3), with qb = k & 512 (bit 30 of pk); the bytes mask    *)
(* pk with 1071644672 (pc 689, 3180, 4794)                                   *)
let va1_b_bsin = new_definition
 `va1_b_bsin (pk:int32) (qb:int32) =
    let fa = word_and pk (word 1071644672) in
    let m = va1_b_sinf (if ~(qb = word 0) then word_sub (word 1073741824) fa else fa) in
    if ival pk < &0 then word_sub (word 0) m else m`;;

let va1_b_bcos = new_definition
 `va1_b_bcos (pk:int32) (qb:int32) =
    let fa = word_and pk (word 1071644672) in
    let m = va1_b_sinf (if ~(qb = word 0) then fa else word_sub (word 1073741824) fa) in
    if ival (word_add pk (word 1073741824)) < &0 then word_sub (word 0) m else m`;;

(* |sin| and cos of the radius phase pr = va1_ck_ph (word_zx r); loops 1 and *)
(* 2 use the unsigned sine magnitude (no sign step in the bytes), loop 3     *)
(* signs it (pc 5348)                                                        *)
let va1_b_rsinm = new_definition
 `va1_b_rsinm (pr:int32) =
    let fa = word_and pr (word 1073741823) in
    va1_b_sinf (if ~(word_and pr (word 1073741824) = word 0) then word_sub (word 1073741824) fa else fa)`;;

let va1_b_rcos = new_definition
 `va1_b_rcos (pr:int32) =
    let fa = word_and pr (word 1073741823) in
    let m = va1_b_sinf (if ~(word_and pr (word 1073741824) = word 0) then fa else word_sub (word 1073741824) fa) in
    if ival (word_add pr (word 1073741824)) < &0 then word_sub (word 0) m else m`;;

(* floor(sqrt(v)) as the bytes compute it: ve_isq 32 from (v, 0, 2^62)       *)
let va1_b_isqrt = new_definition
 `va1_b_isqrt (v:int64) = FST (SND (ve_isq 32 (v, word 0, word 4611686018427387904)))`;;

(* the tube-radius square-root argument (pc 411-467, 2848-2903): clamp(b) *  *)
(* clamp(a) with b = 11651972255721782 div_s spd^2, a = r * 5 div_u 1536     *)
let va1_b_tubearg = new_definition
 `va1_b_tubearg (r:int32) (spd:int64) =
    let bq = (iword (wtdiv (&11651972255721782) (ival (word_mul spd spd))):int64) in
    let aq = word_udiv (word_mul r (word 5)) (word 1536):int32 in
    word_mul (if ival bq < &163840 then bq else word 163840)
             (word_zx (if val aq < 98304 then aq else word 98304):int64)`;;

(* ---- loop 1, pinch-off: bead k is born iff it passes the band test (pc   *)
(* 174), is a strict local maximum of the current zq (pc 203, 225) and is at *)
(* least the pinch length (pc 401)                                           *)
let va1_b1_ok = new_definition
 `va1_b1_ok (mdl:num->int32) (tbl:num->int32) (rb:num->int32) (zq:num->int32) (k:num) <=>
    ~(val (word_add (rb k) (word 4244776699):int32) < 4248132142) /\
    ~(ival (zq k) <= ival (zq ((k + 2047) MOD 2048))) /\
    ~(ival (zq k) < ival (zq ((k + 1) MOD 2048))) /\
    ~(ival (va1_ck_zpq mdl (va1_ck_spd tbl (rb k) k) k) > ival (word_sx (zq k):int64))`;;

(* the loop-1 record of bead k (stores pc 2036-2543): words 0..5 position    *)
(* and velocity, 6 = T+1, 7 = k, 8 = dz (debited from ZQ[k]), 9 = de =       *)
(* max(ZP[k], 0) (debited from ZP[k])                                        *)
let va1_b1_rec = new_definition
 `va1_b1_rec (mdl:num->int32) (hp:num->int32) (tbl:num->int32) (t:int32) (rb:num->int32)
             (zq:num->int32) (zp:num->int32) (k:num) =
    let r = rb k in
    let spd = va1_ck_spd tbl r k in
    let zz = (word_sx (zq k):int64) in
    let sq1 = va1_b_isqrt (va1_b_tubearg r spd) in
    let h3 = (word_sx (hp 3):int64) in let h4 = (word_sx (hp 4):int64) in
    let h5 = (word_sx (hp 5):int64) in let h6 = (word_sx (hp 6):int64) in
    let h7 = (word_sx (hp 7):int64) in let h8 = (word_sx (hp 8):int64) in
    let h9 = (word_sx (hp 9):int64) in let h10 = (word_sx (hp 10):int64) in
    let h11 = (word_sx (hp 11):int64) in
    let pk = word_shl (word k:int32) 21 in
    let qb = word_and (word k:int32) (word 512) in
    let sk = va1_b_bsin pk qb in
    let ck = va1_b_bcos pk qb in
    let dy = word_ishr (word_add (word_mul sk h10) (word_mul ck h7)) 30 in
    let pr = va1_ck_ph (word_zx r) in
    let sr = va1_b_rsinm pr in
    let cr = va1_b_rcos pr in
    let ny = word_ishr (word_add (word_mul dy sr) (word_mul cr h4)) 30 in
    let ty = word_ishr (word_sub (word_mul dy cr) (word_mul sr h4)) 30 in
    let x = word_mul (word_xor (word k) (word 2654435769)) (word 2246822507):int32 in
    let c = word_mul (mdl 2) (word 3266489909):int32 in
    let b0 = word_ushr (word_add (word_mul (word_zx (va1_ck_hfin (word_xor x (word_add c (word 1074893945)))):int64)
                                           (word 11796)) (word 25331717111808)) 32 in
    let ey = word_ishr (word_sub (word_mul ck h10) (word_mul sk h7)) 30 in
    let sp = word_ishr (word_add (word_mul (word_zx (va1_ck_hfin (word_xor x (word_add c (word 2103371332)))):int64)
                                           (word 22938)) (word 18446694814729633792)) 32 in
    let p1 = word_add (word_sub ny (word_ishr (word_mul ty b0) 16)) (word_ishr (word_mul ey sp) 16) in
    let dx = word_ishr (word_add (word_mul sk h9) (word_mul ck h6)) 30 in
    let nx = word_ishr (word_add (word_mul dx sr) (word_mul cr h3)) 30 in
    let tx = word_ishr (word_sub (word_mul dx cr) (word_mul sr h3)) 30 in
    let ex = word_ishr (word_sub (word_mul ck h9) (word_mul sk h6)) 30 in
    let p0 = word_add (word_sub nx (word_ishr (word_mul tx b0) 16)) (word_ishr (word_mul ex sp) 16) in
    let dz = word_ishr (word_add (word_mul sk h11) (word_mul ck h8)) 30 in
    let nz = word_ishr (word_add (word_mul dz sr) (word_mul cr h5)) 30 in
    let tz = word_ishr (word_sub (word_mul dz cr) (word_mul sr h5)) 30 in
    let ez = word_ishr (word_sub (word_mul ck h11) (word_mul sk h8)) 30 in
    let p2 = word_add (word_sub nz (word_ishr (word_mul tz b0) 16)) (word_ishr (word_mul ez sp) 16) in
    let sqp = va1_b_isqrt (word_add (word_add (word_mul p1 p1) (word_mul p0 p0)) (word_mul p2 p2)) in
    let b1 = word_add (word_ushr (word_mul (word_zx (va1_ck_hfin (word_xor x (word_add c (word 46416558)))):int64)
                                           (word 39322)) 32) (word 29491) in
    let sp8 = word_shl sp 3 in
    let q1 = word_add (word_sub ny (word_ishr (word_mul ty b1) 16)) (iword (wtdiv (ival (word_mul ey sp8)) (&327680))) in
    let q0 = word_add (word_sub nx (word_ishr (word_mul tx b1) 16)) (iword (wtdiv (ival (word_mul ex sp8)) (&327680))) in
    let q2 = word_add (word_sub nz (word_ishr (word_mul tz b1) 16)) (iword (wtdiv (ival (word_mul ez sp8)) (&327680))) in
    let sqq = va1_b_isqrt (word_add (word_add (word_mul q1 q1) (word_mul q0 q0)) (word_mul q2 q2)) in
    let de = if ival (zp k) > &0 then zp k else word 0 in
    let dzw = (word_zx (word_ushr (word_add (word_mul zz (word 19661)) (word 32768)) 16):int32) in
    let tube = word_add (word_ishr (word_mul sq1 (word 5905580)) 16) (word 1076963049) in
    let lq = if ival sqq > &1 then sqq else word 1 in
    let lp = if ival sqp > &1 then sqp else word 1 in
    let q2n = (iword (wtdiv (ival (word_shl q2 30)) (ival lq)):int64) in
    let w2 = (word_zx (word_ushr (word_add (word_add (word_ishr (word_mul tube nz) 30)
               (word_ishr (word_mul (word_add q2n (iword (wtdiv (ival (word_shl p2 30)) (ival lp)))) zz) 25))
               (word 512)) 10):int32) in
    let q1n = (iword (wtdiv (ival (word_shl q1 30)) (ival lq)):int64) in
    let w1 = (word_zx (word_ushr (word_add (word_add (word_ishr (word_mul tube ny) 30)
               (word_ishr (word_mul (word_add q1n (iword (wtdiv (ival (word_shl p1 30)) (ival lp)))) zz) 25))
               (word 512)) 10):int32) in
    let q0n = (iword (wtdiv (ival (word_shl q0 30)) (ival lq)):int64) in
    let w0 = (word_zx (word_ushr (word_add (word_add (word_ishr (word_mul tube nx) 30)
               (word_ishr (word_mul (word_add q0n (iword (wtdiv (ival (word_shl p0 30)) (ival lp)))) zz) 25))
               (word 512)) 10):int32) in
    let y = word_mul (word_xor (word_add (word k) (word_shl (word_add t (word 1)) 12)) (word 2654435769))
                     (word 2246822507):int32 in
    let j1 = word_ishr (word_mul (word_ushr (word_mul spd (word 9175)) 16)
               (word_add (word_zx (va1_ck_hfin (word_xor y (word_add c (word 712778449)))):int64)
                         (word 18446744071562067968))) 32 in
    let vt = word_ushr (word_mul spd (word 57672)) 16 in
    let j2 = word_ishr (word_mul (word_ushr (word_mul spd (word 3932)) 16)
               (word_add (word_zx (va1_ck_hfin (word_xor y (word_add c (word 3979268358)))):int64)
                         (word 18446744071562067968))) 32 in
    let vn = word_add (word_ushr (word_mul (word_zx de:int64) (word 117964)) 16)
                      (word_ushr (word_mul spd (word 6554)) 16) in
    let w5 = (word_zx (word_ishr (word_add (word_add (word_add (word_add (word_mul ez j1) (word_mul tz vt))
               (word_mul nz j2)) (word_mul vn q2n)) (word 17179869184)) 35):int32) in
    let w4 = (word_zx (word_ishr (word_add (word_add (word_add (word_add (word_mul ey j1) (word_mul ty vt))
               (word_mul ny j2)) (word_mul vn q1n)) (word 17179869184)) 35):int32) in
    let w3 = (word_zx (word_ishr (word_add (word_add (word_add (word_add (word_mul ex j1) (word_mul tx vt))
               (word_mul nx j2)) (word_mul vn q0n)) (word 17179869184)) 35):int32) in
    va1_rec12 w0 w1 w2 w3 w4 w5 (word_add t (word 1)) (word k) dzw de`;;

(* ---- loop 2, spray: band test (pc 2732) and hash threshold (pc 2847)     *)
let va1_b2_ok = new_definition
 `va1_b2_ok (mdl:num->int32) (tbl:num->int32) (t:int32) (rb:num->int32) (k:num) <=>
    ~(val (word_add (rb k) (word 4245615560):int32) < 4249809864) /\
    ~(val (word_ushr (word_mul (va1_ck_spd tbl (rb k) k) (word 801053)) 16) <=
      val (word_zx (va1_ck_hfin (word_xor (word_mul (word_xor (word k) (word_xor (word_mul (mdl 2) (word 3)) (word 2654435769)))
                                                    (word 2246822507))
                                          (word_add (word_mul (word_add t (word 1)) (word 3266489909)) (word 2769733223)))):int64))`;;

(* the loop-2 record of bead k (stores pc 3072-4350): words 8, 9 = 0, 7 =    *)
(* 65536 | k, 6 = T+1                                                        *)
let va1_b2_rec = new_definition
 `va1_b2_rec (mdl:num->int32) (hp:num->int32) (tbl:num->int32) (t:int32) (rb:num->int32) (k:num) =
    let r = rb k in
    let spd = va1_ck_spd tbl r k in
    let tube = word_add (word_ishr (word_mul (va1_b_isqrt (va1_b_tubearg r spd)) (word 5905580)) 16) (word 1076963049) in
    let h3 = (word_sx (hp 3):int64) in let h4 = (word_sx (hp 4):int64) in
    let h5 = (word_sx (hp 5):int64) in let h6 = (word_sx (hp 6):int64) in
    let h7 = (word_sx (hp 7):int64) in let h8 = (word_sx (hp 8):int64) in
    let h9 = (word_sx (hp 9):int64) in let h10 = (word_sx (hp 10):int64) in
    let h11 = (word_sx (hp 11):int64) in
    let pk = word_shl (word k:int32) 21 in
    let qb = word_and (word k:int32) (word 512) in
    let sk = va1_b_bsin pk qb in
    let ck = va1_b_bcos pk qb in
    let dz = word_ishr (word_add (word_mul sk h11) (word_mul ck h8)) 30 in
    let pr = va1_ck_ph (word_zx r) in
    let sr = va1_b_rsinm pr in
    let cr = va1_b_rcos pr in
    let nz = word_ishr (word_add (word_mul dz sr) (word_mul cr h5)) 30 in
    let w2 = (word_zx (word_ushr (word_add (word_ishr (word_mul tube nz) 30) (word 512)) 10):int32) in
    let dy = word_ishr (word_add (word_mul sk h10) (word_mul ck h7)) 30 in
    let ny = word_ishr (word_add (word_mul dy sr) (word_mul cr h4)) 30 in
    let w1 = (word_zx (word_ushr (word_add (word_ishr (word_mul tube ny) 30) (word 512)) 10):int32) in
    let dx = word_ishr (word_add (word_mul sk h9) (word_mul ck h6)) 30 in
    let nx = word_ishr (word_add (word_mul dx sr) (word_mul cr h3)) 30 in
    let w0 = (word_zx (word_ushr (word_add (word_ishr (word_mul tube nx) 30) (word 512)) 10):int32) in
    let j1 = word_ishr (word_mul (word_ushr spd 2)
               (word_add (word_zx (va1_ck_hfin (word_xor (word_mul (word_xor (word k) (word 2654435769)) (word 2246822507))
                                                         (word_add (word_mul t (word 3266489909)) (word 3621415137)))):int64)
                         (word 18446744071562067968))) 32 in
    let hz = (word_zx (va1_ck_hfin (word_xor (word_add (word_mul (word k) (word 3266489909)) (word 2808445988))
                                             (word_mul (word_xor (word_add t (word 1)) (word 2654435769)) (word 2246822507)))):int64) in
    let vn = word_ushr (word_mul spd (word_add (word_ushr (word_mul hz (word 22938)) 32) (word 9830))) 16 in
    let vt = word_ushr (word_mul spd (word_add (word_ushr (word_mul hz (word 9830)) 32) (word 55706))) 16 in
    let tz = word_ishr (word_sub (word_mul dz cr) (word_mul sr h5)) 30 in
    let ez = word_ishr (word_sub (word_mul ck h11) (word_mul sk h8)) 30 in
    let ty = word_ishr (word_sub (word_mul dy cr) (word_mul sr h4)) 30 in
    let ey = word_ishr (word_sub (word_mul ck h10) (word_mul sk h7)) 30 in
    let tx = word_ishr (word_sub (word_mul dx cr) (word_mul sr h3)) 30 in
    let ex = word_ishr (word_sub (word_mul ck h9) (word_mul sk h6)) 30 in
    let w5 = (word_zx (word_ishr (word_add (word_add (word_add (word_mul ez j1) (word_mul nz vn)) (word_mul tz vt))
               (word 17179869184)) 35):int32) in
    let w4 = (word_zx (word_ishr (word_add (word_add (word_add (word_mul ey j1) (word_mul ny vn)) (word_mul ty vt))
               (word 17179869184)) 35):int32) in
    let w3 = (word_zx (word_ishr (word_add (word_add (word_add (word_mul ex j1) (word_mul nx vn)) (word_mul tx vt))
               (word 17179869184)) 35):int32) in
    va1_rec12 w0 w1 w2 w3 w4 w5 (word_add t (word 1)) (word_or (word k) (word 65536)) (word 0) (word 0)`;;

(* ---- loop 3, antipode: RA < ANT (pc 4506), RB >= ANT (4521), hash <=     *)
(* 2576980377 (4574)                                                         *)
let va1_b3_ok = new_definition
 `va1_b3_ok (mdl:num->int32) (ra:num->int32) (rb:num->int32) (k:num) <=>
    ~(ival (ra k) > &51029456) /\ ~(ival (rb k) < &51029457) /\
    ~(val (va1_ck_hfin (word_xor (word_mul (word_xor (word k) (word 2654435769)) (word 2246822507))
                                 (word_add (word_mul (mdl 2) (word 3266489909)) (word 1922313584)))) > 2576980377)`;;

(* the loop-3 record of bead k (stores pc 4709-6014): words 8, 9 = 0, 7 =    *)
(* 131072 + k, 6 = T+1; the table column of the clamped radius (pc 4602)     *)
let va1_b3_rec = new_definition
 `va1_b3_rec (mdl:num->int32) (hp:num->int32) (tbl:num->int32) (t:int32) (rb:num->int32) (k:num) =
    let rn = rb k in
    let rc = if val rn < 66584575 then rn else word 66584575 in
    let j = val (word_and (word_ushr rc 17) (word 508):int32) DIV 4 in
    let a = (word_sx (tbl (128 * k + j)):int64) in
    let b = (word_sx (tbl (128 * k + j + 1)):int64) in
    let h3 = (word_sx (hp 3):int64) in let h4 = (word_sx (hp 4):int64) in
    let h5 = (word_sx (hp 5):int64) in let h6 = (word_sx (hp 6):int64) in
    let h7 = (word_sx (hp 7):int64) in let h8 = (word_sx (hp 8):int64) in
    let h9 = (word_sx (hp 9):int64) in let h10 = (word_sx (hp 10):int64) in
    let h11 = (word_sx (hp 11):int64) in
    let pk = (word (2097152 * k):int32) in
    let qb = word_and (word k:int32) (word 512) in
    let sk = va1_b_bsin pk qb in
    let ck = va1_b_bcos pk qb in
    let dz = word_ishr (word_add (word_mul h11 sk) (word_mul h8 ck)) 30 in
    let pr = va1_ck_ph (word_zx rn) in
    let srm = va1_b_rsinm pr in
    let sr = if ival pr < &0 then word_sub (word 0) srm else srm in
    let cr = va1_b_rcos pr in
    let w2 = (word_zx (word_ushr (word_add (word_ishr (word_add (word_mul dz sr) (word_mul h5 cr)) 30) (word 512)) 10):int32) in
    let dy = word_ishr (word_add (word_mul sk h10) (word_mul ck h7)) 30 in
    let w1 = (word_zx (word_ushr (word_add (word_ishr (word_add (word_mul dy sr) (word_mul cr h4)) 30) (word 512)) 10):int32) in
    let dx = word_ishr (word_add (word_mul sk h9) (word_mul ck h6)) 30 in
    let w0 = (word_zx (word_ushr (word_add (word_ishr (word_add (word_mul dx sr) (word_mul cr h3)) 30) (word 512)) 10):int32) in
    let vv0 = word_add a (word_ishr (word_add (word_mul (word_sub b a)
                (word_zx (if val rn > 66584575 then word 524288 else word_and rn (word 524287)):int64)) (word 262144)) 19) in
    let vv = if ival vv0 > &210828 then vv0 else word 210828 in
    let x = word_mul (word_xor (word k) (word 2654435769)) (word 2246822507):int32 in
    let c = word_mul (mdl 2) (word 3266489909):int32 in
    let h6z = (word_zx (va1_ck_hfin (word_xor x (word_add c (word 893836197)))):int64) in
    let up = word_sub (word 0) (word_ushr (word_mul vv (word_add (word_ushr (word_mul (word_ushr (word_mul h6z h6z) 32)
                                                                                      (word 58982)) 32) (word 16384))) 16) in
    let lat = word_ushr (word_mul vv (word 36045)) 16 in
    let l2 = word_ishr (word_mul lat (word_add (word_zx (va1_ck_hfin (word_xor x (word_add c (word 4160326106)))):int64)
                                               (word 18446744071562067968))) 32 in
    let l3 = word_ishr (word_mul lat (word_add (word_zx (va1_ck_hfin (word_xor x (word_add c (word 3131848719)))):int64)
                                               (word 18446744071562067968))) 32 in
    let ez = word_ishr (word_sub (word_mul ck h11) (word_mul sk h8)) 30 in
    let tz = word_ishr (word_sub (word_mul dz cr) (word_mul sr h5)) 30 in
    let ey = word_ishr (word_sub (word_mul ck h10) (word_mul sk h7)) 30 in
    let ty = word_ishr (word_sub (word_mul dy cr) (word_mul sr h4)) 30 in
    let ex = word_ishr (word_sub (word_mul ck h9) (word_mul sk h6)) 30 in
    let tx = word_ishr (word_sub (word_mul dx cr) (word_mul sr h3)) 30 in
    let w5 = (word_zx (word_ishr (word_add (word_add (word_add (word_mul h5 up) (word_mul l2 ez)) (word_mul l3 tz))
               (word 17179869184)) 35):int32) in
    let w4 = (word_zx (word_ishr (word_add (word_add (word_add (word_mul up h4) (word_mul l2 ey)) (word_mul l3 ty))
               (word 17179869184)) 35):int32) in
    let w3 = (word_zx (word_ishr (word_add (word_add (word_add (word_mul up h3) (word_mul l2 ex)) (word_mul l3 tx))
               (word 17179869184)) 35):int32) in
    va1_rec12 w0 w1 w2 w3 w4 w5 (word_add t (word 1)) (word_add (word k) (word 131072)) (word 0) (word 0)`;;

(* ---- the three folds. A bead is visited only while the count             *)
(* val nd0 + LENGTH L is below 16384 (the loop exits at the cap).            *)
let va1_step1 = new_definition
 `va1_step1 (mdl:num->int32) (hp:num->int32) (tbl:num->int32) (t:int32) (rb:num->int32) (nd0:int32) (k:num)
            (st:(num->int32)list#(num->int32)#(num->int32)) =
    if 16384 <= val nd0 + LENGTH (FST st) \/ ~va1_b1_ok mdl tbl rb (FST (SND st)) k then st else
    let r = va1_b1_rec mdl hp tbl t rb (FST (SND st)) (SND (SND st)) k in
    (APPEND (FST st) [r],
     (\i. if i = k then word_sub (FST (SND st) i) (r 8) else FST (SND st) i),
     (\i. if i = k then word_sub (SND (SND st) i) (r 9) else SND (SND st) i))`;;

let va1_fold1 = new_recursive_definition num_RECURSION
 `(!mdl hp tbl t rb nd0 st. va1_fold1 mdl hp tbl t rb nd0 0 st = st) /\
  (!mdl hp tbl t rb nd0 k st. va1_fold1 mdl hp tbl t rb nd0 (SUC k) st =
       va1_step1 mdl hp tbl t rb nd0 k (va1_fold1 mdl hp tbl t rb nd0 k st))`;;

let va1_step2 = new_definition
 `va1_step2 (mdl:num->int32) (hp:num->int32) (tbl:num->int32) (t:int32) (rb:num->int32) (nd0:int32) (k:num)
            (L:(num->int32)list) =
    if 16384 <= val nd0 + LENGTH L \/ ~va1_b2_ok mdl tbl t rb k then L
    else APPEND L [va1_b2_rec mdl hp tbl t rb k]`;;

let va1_fold2 = new_recursive_definition num_RECURSION
 `(!mdl hp tbl t rb nd0 L. va1_fold2 mdl hp tbl t rb nd0 0 L = L) /\
  (!mdl hp tbl t rb nd0 k L. va1_fold2 mdl hp tbl t rb nd0 (SUC k) L =
       va1_step2 mdl hp tbl t rb nd0 k (va1_fold2 mdl hp tbl t rb nd0 k L))`;;

let va1_step3 = new_definition
 `va1_step3 (mdl:num->int32) (hp:num->int32) (tbl:num->int32) (t:int32) (ra:num->int32) (rb:num->int32)
            (nd0:int32) (k:num) (L:(num->int32)list) =
    if 16384 <= val nd0 + LENGTH L \/ ~va1_b3_ok mdl ra rb k then L
    else APPEND L [va1_b3_rec mdl hp tbl t rb k]`;;

let va1_fold3 = new_recursive_definition num_RECURSION
 `(!mdl hp tbl t ra rb nd0 L. va1_fold3 mdl hp tbl t ra rb nd0 0 L = L) /\
  (!mdl hp tbl t ra rb nd0 k L. va1_fold3 mdl hp tbl t ra rb nd0 (SUC k) L =
       va1_step3 mdl hp tbl t ra rb nd0 k (va1_fold3 mdl hp tbl t ra rb nd0 k L))`;;

(* the newborn list: loop 1 over all 2048 beads from ([], zq, zp), then      *)
(* loop 2, then loop 3, each continuing the list                             *)
let va1_born = new_definition
 `va1_born (mdl:num->int32) (hp:num->int32) (tbl:num->int32) (t:int32) (ra:num->int32) (rb:num->int32)
           (zq:num->int32) (zp:num->int32) (nd:int32) =
    va1_fold3 mdl hp tbl t ra rb nd 2048
      (va1_fold2 mdl hp tbl t rb nd 2048
        (FST (va1_fold1 mdl hp tbl t rb nd 2048 ([], zq, zp))))`;;

(* the C8a statement: va1_birth_ok (frozen text, pop_r5_birth.spec) with "exists L" replaced by the named
   list va1_born; precondition and frame are byte-identical *)
let va1_birth_eq = new_definition
 `va1_birth_eq <=>
   (!(mdl:num->int32) (hp:num->int32) (tbl:num->int32) (t:int32) (p:int32) (ap:int32)
       (ra:num->int32) (rb:num->int32) (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32) decls.
      va1_pop_window t p /\ va1_log_ok t di nd /\ wasm_decl_vals va1_f13_mc = SOME decls
      ==> ensures wasm
           (\s. read wcode s = va1_f13_mc /\ read wpc s = word 13 /\
                read wstatus s = WRunning /\ read wstack s = [] /\ read wlabels s = [] /\
                read warity s = 1 /\ read wmemsize s = 4194304 /\
                read wlocals s = wcall_locals [] decls /\
                va1_tick t (read wmem s) /\ va1_pop p ap (read wmem s) /\ va1_mdl mdl (read wmem s) /\
                va1_w32s 16408 26 hp (read wmem s) /\ va1_w32s 65536 262144 tbl (read wmem s) /\
                va1_w32s 1130496 2048 ra (read wmem s) /\ va1_w32s 1138688 2048 rb (read wmem s) /\
                va1_bs (di,zq,zp,nd) (read wmem s))
           (\s. read wstatus s = WDone /\ (?r. read wstack s = [I32 r]) /\
                va1_bs (va1_push (va1_born mdl hp tbl t ra rb zq zp nd) (di,zq,zp,nd)) (read wmem s))
           (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
            MAYCHANGE [wstatus] ,, MAYCHANGE [wlocal 0; wlocal 1; wlocal 2; wlocal 3; wlocal 4; wlocal 5; wlocal 6; wlocal 7; wlocal 8; wlocal 9; wlocal 10; wlocal 11; wlocal 12; wlocal 13; wlocal 14; wlocal 15; wlocal 16; wlocal 17; wlocal 18; wlocal 19; wlocal 20; wlocal 21; wlocal 22; wlocal 23; wlocal 24; wlocal 25; wlocal 26; wlocal 27; wlocal 28; wlocal 29; wlocal 30; wlocal 31; wlocal 32; wlocal 33; wlocal 34; wlocal 35; wlocal 36; wlocal 37; wlocal 38; wlocal 39; wlocal 40; wlocal 41] ,,
            MAYCHANGE [wmem :> bytes(word 16400,4)] ,,
            MAYCHANGE [wmem :> bytes(word 1163264,16384)] ,,
            MAYCHANGE [wmem :> bytes(word 1179648,786432)] ,,
            MAYCHANGE [wmem :> bytes(word 1966080,73728)]))`;;
