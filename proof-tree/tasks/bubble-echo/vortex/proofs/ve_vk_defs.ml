(* ========================================================================= *)
(* Vortex Echo v1: the field function ve_vk of the vortex export pair        *)
(* ve_vort_apply / ve_vort_unapply of vortex/core/ve_core.wasm (sha256       *)
(* 72fe0ba2), defined from the code's semantics (C source vk_normalise and   *)
(* vk_field in vortex/core/ve_core.c; the compiled prefix pc 21 .. 1305).    *)
(* All arithmetic is the WASM integer arithmetic of the bytes (i64 words,    *)
(* wrapping products and sums, arithmetic shifts, div_s / div_u).            *)
(*                                                                           *)
(*  normalise: for each vortex i < n, with x_c = sx(S[3i+c]) (i64),          *)
(*    s = y*y + x*x + z*z, r = the 32-step integer square root of s          *)
(*    (ve_isq), l = r if r > 1 else 1 (signed), XN[3i+c] = (x_c << 30) div_s l *)
(*    stored as an i32 (ve_vk_xn);                                           *)
(*  field: rows i = 0 .. n-1, partners j = i+1 .. n-1: the weight w_ij       *)
(*    (ve_vk_w), the cross product x_j x x_i (ve_vk_v), the term added to    *)
(*    acc[3j+c] (ve_vk_tj) and to the row sum of i (ve_vk_ti); acc after     *)
(*    row i (ve_vk_acc, summation order and operand order as compiled);       *)
(*  VD[m] = (acc[m] + 2^35) >>s 36 stored as an i32 (ve_vk_rnd).             *)
(* ========================================================================= *)

(* one step of the integer square root (s, r, b) as compiled (pc 144..195) *)
let ve_isq_step = new_definition
 `ve_isq_step (x:int64#int64#int64) =
    if val (FST x) < val (word_add (SND (SND x)) (FST (SND x)))
    then (FST x, word_ushr (FST (SND x)) 1, word_ushr (SND (SND x)) 2)
    else (word_sub (FST x) (word_add (SND (SND x)) (FST (SND x))),
          word_add (SND (SND x)) (word_ushr (FST (SND x)) 1),
          word_ushr (SND (SND x)) 2)`;;

let ve_isq = define
 `(ve_isq 0 (x:int64#int64#int64) = x) /\
  (ve_isq (SUC k) x = ve_isq_step (ve_isq k x))`;;

(* source coordinate c of vortex i, sign-extended to i64 *)
let ve_vk_sx = new_definition
 `ve_vk_sx (S:num->int32) i c = (word_sx (S (3 * i + c)):int64)`;;

(* |x|^2 as compiled: y*y + x*x + z*z (wrapping i64) *)
let ve_vk_ss = new_definition
 `ve_vk_ss (S:num->int32) i =
    word_add (word_add (word_mul (ve_vk_sx S i 1) (ve_vk_sx S i 1))
                       (word_mul (ve_vk_sx S i 0) (ve_vk_sx S i 0)))
             (word_mul (ve_vk_sx S i 2) (ve_vk_sx S i 2))`;;

(* the divisor: the square root r after 32 steps from (s, 0, 2^62), or 1 *)
let ve_vk_len = new_definition
 `ve_vk_len (S:num->int32) i =
    let r = FST (SND (ve_isq 32 (ve_vk_ss S i, word 0, word 4611686018427387904))) in
    if ival r > &1 then r else (word 1:int64)`;;

(* normalised coordinate XN[3i+c] (Q30), as stored by i64.store32 *)
let ve_vk_xn = new_definition
 `ve_vk_xn (S:num->int32) i c =
    (word_zx (iword (wtdiv (ival (word_shl (ve_vk_sx S i c) 30)) (ival (ve_vk_len S i))):int64)
     :int32)`;;

(* XN sign-extended to i64 (the pair loop operands) and the circulations *)
let ve_vk_X = new_definition
 `ve_vk_X (S:num->int32) i c = (word_sx (ve_vk_xn S i c):int64)`;;

let ve_vk_C = new_definition
 `ve_vk_C (mdl:num->int32) j = (word_sx (mdl (16 + j)):int64)`;;

(* pair (i, j): the regularised weight 2^54 div_u max(D2, 2^30 + D2 - dot) *)
let ve_vk_w = new_definition
 `ve_vk_w (X:num->num->int64) i j =
    let den = word_sub (word 1076426179)
                (word_ishr (word_add (word_add (word_mul (X j 1) (X i 1))
                                               (word_mul (X j 0) (X i 0)))
                                     (word_mul (X j 2) (X i 2))) 30) in
    word_udiv (word 18014398509481984) (if ival den > &2684355 then den else word 2684355)`;;

(* pair (i, j): component c of x_j x x_i (Q60, wrapping i64) *)
let ve_vk_v = new_definition
 `ve_vk_v (X:num->num->int64) i j c =
    if c = 0 then word_sub (word_mul (X j 1) (X i 2)) (word_mul (X j 2) (X i 1))
    else if c = 1 then word_sub (word_mul (X j 2) (X i 0)) (word_mul (X j 0) (X i 2))
    else word_sub (word_mul (X j 0) (X i 1)) (word_mul (X j 1) (X i 0))`;;

(* the term added to acc[3j+c] (partner j of row i) *)
let ve_vk_tj = new_definition
 `ve_vk_tj (X:num->num->int64) (C:num->int64) i j c =
    word_ishr (word_mul (word_ishr (word_mul (ve_vk_w X i j) (C i)) 20)
                        (word_ishr (word_sub (word 0) (ve_vk_v X i j c)) 36)) 12`;;

(* the term added to the row sum of i (component c) by partner j *)
let ve_vk_ti = new_definition
 `ve_vk_ti (X:num->num->int64) (C:num->int64) i j c =
    word_ishr (word_mul (word_ishr (word_mul (ve_vk_w X i j) (C j)) 20)
                        (word_ishr (ve_vk_v X i j c) 36)) 12`;;

(* acc[3j+c] after partner j of row i is added, operand order as compiled *)
let ve_vk_upd = new_definition
 `ve_vk_upd (X:num->num->int64) (C:num->int64) i j c (a:int64) =
    if c = 2 then word_add a (ve_vk_tj X C i j c) else word_add (ve_vk_tj X C i j c) a`;;

(* row sum of row i over the partners i+1 .. i+k *)
let ve_vk_rs = define
 `(ve_vk_rs (X:num->num->int64) (C:num->int64) i 0 c = (word 0:int64)) /\
  (ve_vk_rs X C i (SUC k) c = word_add (ve_vk_ti X C i (i + 1 + k) c) (ve_vk_rs X C i k c))`;;

(* the accumulators acc[3j+c] after rows 0 .. i-1 of n vortices *)
let ve_vk_acc = define
 `(ve_vk_acc (X:num->num->int64) (C:num->int64) n 0 j c = (word 0:int64)) /\
  (ve_vk_acc X C n (SUC i) j c =
     if j = i then word_add (ve_vk_acc X C n i j c) (ve_vk_rs X C i (n - 1 - i) c)
     else if i < j then ve_vk_upd X C i j c (ve_vk_acc X C n i j c)
     else ve_vk_acc X C n i j c)`;;

(* VD[m] = (acc[m] + 2^35) >>s 36, stored by i64.store32 *)
let ve_vk_rnd = new_definition
 `ve_vk_rnd (a:int64) = (word_zx (word_ishr (word_add a (word 34359738368)) 36):int32)`;;

(* the field function: VD = ve_vk mdl S for the source S (VB for apply, VA *)
(* for unapply), n = min(model word 1, 640) vortices                        *)
let ve_vk = new_definition
 `ve_vk (mdl:num->int32) (S:num->int32) m =
    ve_vk_rnd (ve_vk_acc (ve_vk_X S) (ve_vk_C mdl) (MIN (val (mdl 1)) 640)
                         (MIN (val (mdl 1)) 640) (m DIV 3) (m MOD 3))`;;
