(* C8p P5 v2 definitions, generated verbatim from c8p_f25h2.spec (Claude Opus 5.5, 2026-11-14) *)
let va1_isq_body = new_definition
 `va1_isq_body (s:int64#int64#int64) =
    let r = FST s in let b = FST (SND s) in let v = SND (SND s) in
    if val r < val (word_add b v) then (r,word_ushr b 2,word_ushr v 1)
    else (word_sub r (word_add b v),word_ushr b 2,word_add b (word_ushr v 1))`;;
let va1_isqrt = new_definition
 `va1_isqrt (x:int64) = SND (SND (ITER 32 va1_isq_body (x,word 4611686018427387904,word 0)))`;;
let va1_fix30 = new_definition
 `va1_fix30 (x:int64) (v:int64) = iword (wtdiv (ival (word_shl x 30)) (ival (if ival v > &1 then v else word 1))):int64`;;
let va1_pcross = new_definition
 `va1_pcross (n0:int64) (n1:int64) (n2:int64) (y0:int64) (y1:int64) (y2:int64) (v:int64) =
    let u0 = va1_fix30 y0 v in let u1 = va1_fix30 y1 v in let u2 = va1_fix30 y2 v in
    [n0; n1; n2; u0; u1; u2;
     word_ushr (word_sub (word_mul u2 n1) (word_mul u1 n2)) 30;
     word_ushr (word_sub (word_mul u0 n2) (word_mul u2 n0)) 30;
     word_ushr (word_sub (word_mul u1 n0) (word_mul u0 n1)) 30]`;;
let va1_pfrm = new_definition
 `va1_pfrm (a0:int32) (a1:int32) (a2:int32) =
    let x0 = (word_sx a0:int64) in let x1 = (word_sx a1:int64) in let x2 = (word_sx a2:int64) in
    let v1 = va1_isqrt (word_add (word_add (word_mul x1 x1) (word_mul x0 x0)) (word_mul x2 x2)) in
    let n0 = va1_fix30 x0 v1 in let n1 = va1_fix30 x1 v1 in let n2 = va1_fix30 x2 v1 in
    let c = val (word_sub (word_xor n1 (word_ishr n1 63)) (word_ishr n1 63)) < 1020054733 in
    let y0 = (if c then n2 else word 0) in
    let y1 = (if c then word 0 else word_sub (word 0) n2) in
    let y2 = (if c then word_sub (word 0) n0 else n1) in
    va1_pcross n0 n1 n2 y0 y1 y2 (va1_isqrt (word_add (word_add (word_mul y0 y0) (word_mul y1 y1)) (word_mul y2 y2)))`;;
let va1_hmix = new_definition
 `va1_hmix (x:int32) =
    let t = word_mul (word_xor (word_ushr x 15) x) (word_or x (word 1)) in
    let w = word_xor (word_add (word_mul (word_xor (word_ushr t 7) t) (word_or t (word 61))) t) t in
    word_xor (word_ushr w 14) w`;;
let va1_hjig = new_definition
 `va1_hjig (x:int32) =
    word_add (word_zx (word_ushr (word_mul (word_zx (va1_hmix (word_add x (word 1831565813))):int64) (word 52429)) 32):int32)
             (word 39322)`;;
let va1_hseed = new_definition
 `va1_hseed (a0:int32) (a1:int32) (a2:int32) (i:num) =
    ITER i (\s. word_add s (word 3663131626))
           (word_add (word_xor (word_xor (word_mul a1 (word 7)) (word_mul a2 (word 13))) a0) (word 1831565813))`;;
let va1_phdr = new_definition
 `va1_phdr (a0:int32) (a1:int32) (a2:int32) (k:num) =
    if k < 9 then (word_zx (EL k (va1_pfrm a0 a1 a2)):int32)
    else if k < 15 then va1_hmix (va1_hseed a0 a1 a2 (k - 9))
    else va1_hjig (va1_hseed a0 a1 a2 (k - 15))`;;
