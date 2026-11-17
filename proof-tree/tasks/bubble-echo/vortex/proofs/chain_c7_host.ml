needs "ve_vort.ml";;
needs "ve_tick.ml";;
needs "ve_vk.ml";;
needs "va1_code.ml";;
needs "va1_seq_final2.ml";;
needs "pop_design_defs.ml";;
needs "pop_design_stmts.ml";;
needs "pop_l2_cdrift.ml";;
needs "pop_l3_jdrift.ml";;
needs "pop_l4_drop.ml";;
needs "pop_l1_rimd.ml";;
needs "pop_l1_rim.ml";;
needs "pop_l5_unbirth.ml";;
needs "pop_h1_hol.ml";;
needs "pop_n1_sat.ml";;
needs "pop_q0_calls.ml";;
needs "pop_q1_untick.ml";;
needs "pop_q2_forward.ml";;
needs "pop_r5_jig_defs.ml";;
needs "pop_r5jig_dec.ml";;
needs "pop_r5jig_lem.ml";;
needs "pop_r5_corr_defs.ml";;
needs "pop_r5c_lem.ml";;
needs "pop_r5b_bdec.ml";;
needs "pop_r5bp_lem.ml";;
needs "pop_r5bp_lem2.ml";;
needs "pop_r5bp_lem3.ml";;
needs "pop_r5bp_lem4.ml";;
needs "pop_r5bp_lem5b.ml";;
needs "pop_r5bp_lem6.ml";;
needs "pop_s0_end.ml";;
needs "pop_r5_r4c_final.ml";;
needs "chain_c1_host.ml";;
needs "chain_c3a_defs.ml";;
needs "chain_c3a_f26a.ml";;
needs "chain_c3a_f26b.ml";;
needs "chain_c3a_f26c.ml";;
needs "chain_c3a_seq.ml";;
needs "chain_c3a_fin.ml";;
needs "chain_c2_host_pop.ml";;
needs "chain_c2_chain.ml";;
needs "chain_c1_np.ml";;
needs "chain_c1_frame.ml";;
needs "chain_c4_lem.ml";;
needs "chain_c4_film.ml";;
needs "chain_c3b_dec.ml";;
needs "chain_c7_c3b_defs.ml";;
needs "chain_c7_c3b_l1.ml";;
needs "chain_c7_c3b_pure.ml";;
needs "chain_c5_dec.ml";;
needs "chain_c5_tacs.ml";;
needs "chain_c5_leaves.ml";;
needs "chain_c5_punct_a.ml";;
needs "chain_c5_punct_b.ml";;
needs "chain_c5_punct_c.ml";;
needs "chain_c7_c6a_host.ml";;
needs "chain_c5p_frames.ml";;
needs "chain_c5p_rules.ml";;
needs "chain_c7_c6b_host.ml";;
needs "chain_c7_film.ml";;
(* ========================================================================= *)
(* Vortex chain, rung C7 (C7 agent, Claude Opus 5.5, 2026-11-13), layer     *)
(* "host": the C6a / C6b puncture calls as C1 host calls, the C3a/C3b       *)
(* bridge, and the C7b / C7a theorems. Pure HOL; no mk_thm / new_axiom.     *)
(* ========================================================================= *)

(* ---- the puncture calls as C1 host calls, from C6a (click, wasmc) and C6b (auto, wasmn) ---- *)
let C7_HCALL_CLICK = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (t:int32) (mdl:num->int32) (a0:int32) (a1:int32) (a2:int32) (m:int64->byte).
     fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\
     read (bytes32 (word 16396)) m = word 4294967295 /\ va1_tick t m /\ ~(t = word 0) /\ va1_mdl mdl m /\
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0) /\ gl 0 = I32 (word 16384)
     ==> va1_hcall (wasmc fs) va1_puncture_mc [I32 a2; I32 a1; I32 a0] (word 0)
           (\gl2 m2. va1_c6a_rel mdl gl m gl2 m2) gl m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[va1_hcall] THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `t:int32`; `mdl:num->int32`; `a0:int32`; `a1:int32`;
                `a2:int32`; `m:int64->byte`] VA1_HCALL_PUNCTURE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:num` (X_CHOOSE_THEN `decls:wval list` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`e:num`; `decls:wval list`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s0:wasmstate` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s0:wasmstate`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C1_EV_MONO THEN GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let C7_HCALL_AUTO = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (t:int32) (mdl:num->int32) (N:num) (x:(num->int32)#(num->int32)) (m0:int64->byte).
     fs 9 = (va1_f9_mc,0,0) /\ fs 27 = (va1_f27_mc,0,0) /\ fs 33 = (va1_puncture_mc,3,1) /\
     fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ gl 0 = I32 (word 16384) /\ ~(word_add t (word 1) = word 0) /\
     va1_tick t m0 /\ va1_pop (word 4294967295) (word_add t (word 1)) m0 /\ va1_mdl mdl m0 /\ va1_vab N x m0 /\
     ~(read (bytes32 (word 16516)) m0 = word 0 /\ read (bytes32 (word 16520)) m0 = word 0 /\
       read (bytes32 (word 16524)) m0 = word 0)
     ==> va1_hcall (wasmn fs) va1_tick_forward_mc [] (word 1)
           (\gl2 m2. gl2 = gl /\ ?m1. va1_tf_mid N mdl t x m0 m1 /\ va1_c6a_mem mdl m1 m2) gl m0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `t:int32`; `mdl:num->int32`; `N:num`;
                `x:(num->int32)#(num->int32)`; `read (bytes32 (word 16516)) (m0:int64->byte)`;
                `read (bytes32 (word 16520)) (m0:int64->byte)`; `read (bytes32 (word 16524)) (m0:int64->byte)`;
                `m0:int64->byte`] VA1_TICK_FORWARD_PUNCT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun lth ->
    let _,[step;pp;qq;cc] = strip_comb(concl lth) in
    let eth,dth = CONJ_PAIR VA1_TICKF_CALLEE in
    let code = rand(lhand(concl eth)) and e = rand(rand(concl eth)) and decls = rand(rand(concl dth)) in
    MATCH_MP_TAC (ISPECL [step; code; e; decls; `[]:wval list`; `word 1:int32`; pp; qq; cc] VA1_HCALL_ENSURES) THEN
    REWRITE_TAC[eth; dth; lth]) THEN
  CONJ_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[WCALL_ENTRY_READS];
    REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[]]);;

(* ---- bridge: C3b's renamed constants are C3a's ---- *)
let C7_RBINIT_B = prove
 (`va1_rbinit_b = va1_rbinit`,
  REWRITE_TAC[FUN_EQ_THM; va1_rbinit_b; va1_rbinit; va1_rbv; LET_DEF; LET_END_DEF] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ADD_SYM]);;
let C7_ZPSEED_B = prove
 (`va1_zpseed_b = va1_zpseed`,
  REWRITE_TAC[FUN_EQ_THM; va1_zpseed_b; va1_zpseed; va1_zpx0; va1_zpx1; LET_DEF; LET_END_DEF]);;
let C7_C6A_REL_PUNCT = prove
 (`!(mdl:num->int32) (gl:num->wval) (m:int64->byte) (gl':num->wval) (m':int64->byte).
     va1_c6a_rel mdl gl m gl' m' ==> va1_punct_rel mdl gl m gl' m'`,
  REWRITE_TAC[va1_c6a_rel; va1_c6a_mem; va1_c6a_frame; va1_punct_rel; va1_punct_frame; C7_RBINIT_B; C7_ZPSEED_B] THEN
  MESON_TAC[]);;

(* ---- the puncture hypotheses of the films, discharged ---- *)
let C7_CLICK_H = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (ap:int32) (x0:(num->int32)#(num->int32))
    (K:num) (m0:int64->byte) (a0:int32) (a1:int32) (a2:int32).
     fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\ gl 0 = I32 (word 16384) /\
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0) /\ 1 <= K /\ K + 520 < 4294967296
     ==> !m1. va1_np_st (word K) ap mdl N (ITER K (va1_swf mdl) x0) m1 /\ va1_np_frame m0 m1
              ==> va1_hcall (wasmc fs) va1_puncture_mc [I32 a2; I32 a1; I32 a0] (word 0)
                    (\gl2 m2. va1_punct_rel mdl gl m1 gl2 m2) gl m1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (ISPECL [`\(m1:int64->byte) (gl2:num->wval) (m2:int64->byte). va1_c6a_rel mdl gl m1 gl2 m2`;
                        `wasmc fs`] C7_CLICK_H_GEN) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC C7_C6A_REL_PUNCT THEN FIRST_ASSUM ACCEPT_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC C7_HCALL_CLICK THEN EXISTS_TAC `t:int32` THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC]);;

let C7_AUTO_H = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (x0:(num->int32)#(num->int32))
    (K:num) (m0:int64->byte).
     va1_fs_np fs /\ fs 33 = (va1_puncture_mc,3,1) /\
     fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\ gl 0 = I32 (word 16384) /\
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ 1 <= K /\ K + 520 < 4294967296 /\
     ~(read (bytes32 (word 16516)) m0 = word 0 /\ read (bytes32 (word 16520)) m0 = word 0 /\
       read (bytes32 (word 16524)) m0 = word 0)
     ==> !m1. va1_np_st (word (K - 1)) (word K) mdl N (ITER (K - 1) (va1_swf mdl) x0) m1 /\ va1_np_frame m0 m1
              ==> va1_hcall (wasmn fs) va1_tick_forward_mc [] (word 1)
                    (\gl2 m2. va1_autopunct_rel mdl N (ITER (K - 1) (va1_swf mdl) x0) gl m1 gl2 m2) gl m1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_fs_np] THEN STRIP_TAC THEN
  MATCH_MP_TAC (ISPECL [`\(m1:int64->byte) (gl2:num->wval) (m2:int64->byte). gl2 = gl /\ va1_c6a_mem mdl m1 m2`;
                        `wasmn fs`] C7_AUTO_H_GEN) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC C7_C6A_REL_PUNCT THEN ASM_REWRITE_TAC[va1_c6a_rel];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC VA1_HCALL_MONO THEN
    EXISTS_TAC `\(gl2:num->wval) (m2:int64->byte). gl2 = (gl:num->wval) /\ ?m1. va1_tf_mid N (mdl:num->int32) (t:int32) (x:(num->int32)#(num->int32)) (m:int64->byte) m1 /\ va1_c6a_mem mdl m1 m2` THEN
    CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`g2:num->wval`; `m2:int64->byte`] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `mm:int64->byte` MP_TAC)) THEN
      REWRITE_TAC[va1_tf_mid; va1_np_frame] THEN STRIP_TAC THEN EXISTS_TAC `mm:int64->byte` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC C7_HCALL_AUTO THEN ASM_REWRITE_TAC[]];
    FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC]);;

(* ---- the headlines ---- *)
let C7_ANTS_TAC (h:thm) : tactic =
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; MATCH_ACCEPT_TAC VA1_C5P_EVENTUALLY_WASMN;
         MATCH_MP_TAC h THEN ASM_REWRITE_TAC[]];;

let VA1_FILM_AUTO = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num)
   (x0:(num->int32)#(num->int32)) (K:num) (n:num) (m0:int64->byte).
     va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\ fs 33 = (va1_puncture_mc,3,1) /\
     fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\ gl 0 = I32 (word 16384) /\
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ 1 <= K /\ K + 520 < 4294967296 /\ n <= 520 /\
     va1_np_st (word 0) (word K) mdl N x0 m0 /\ va1_clean m0 /\
     ~(read (bytes32 (word 16516)) m0 = word 0 /\ read (bytes32 (word 16520)) m0 = word 0 /\
       read (bytes32 (word 16524)) m0 = word 0)
     ==> va1_hrun (wasmn fs) (APPEND (REPLICATE K T) (APPEND (REPLICATE n T) (REPLICATE (n + K) F)))
           (\gl3 m3. gl3 = gl /\ va1_np_st (word 0) (word K) mdl N x0 m3 /\ va1_clean m3 /\
                     read (bytes32 (word 16404)) m3 = read (bytes32 (word 16404)) m0 /\
                     va1_film_bytes N m0 m3) gl m0`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`wasmn fs`; `fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`;
                `x0:(num->int32)#(num->int32)`; `K:num`; `m0:int64->byte`] C7_FILM_AUTO_GEN) THEN
  ANTS_TAC THENL [C7_ANTS_TAC C7_AUTO_H; ALL_TAC] THEN
  DISCH_THEN(fun th -> ACCEPT_TAC(MP (SPEC `n:num` (CONJUNCT1 th)) (ASSUME `n <= 520`))));;

let VA1_FILM_AUTO_TO_END = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num)
   (x0:(num->int32)#(num->int32)) (K:num) (m0:int64->byte).
     va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\ fs 33 = (va1_puncture_mc,3,1) /\
     fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\ gl 0 = I32 (word 16384) /\
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ 1 <= K /\ K + 520 < 4294967296 /\
     va1_np_st (word 0) (word K) mdl N x0 m0 /\ va1_clean m0 /\
     ~(read (bytes32 (word 16516)) m0 = word 0 /\ read (bytes32 (word 16520)) m0 = word 0 /\
       read (bytes32 (word 16524)) m0 = word 0)
     ==> va1_hrun (wasmn fs) (APPEND (REPLICATE K T) (REPLICATE 520 T))
           (\gl3 m3. gl3 = gl /\
              va1_hcall (wasmn fs) va1_tick_forward_mc [] (word 0)
                (\gl4 m4. gl4 = gl3 /\ m4 = m3 /\
                   va1_hrun (wasmn fs) (REPLICATE (520 + K) F)
                     (\gl5 m5. gl5 = gl /\ va1_np_st (word 0) (word K) mdl N x0 m5 /\ va1_clean m5 /\
                        read (bytes32 (word 16404)) m5 = read (bytes32 (word 16404)) m0 /\
                        va1_film_bytes N m0 m5) gl4 m4) gl3 m3) gl m0`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`wasmn fs`; `fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`;
                `x0:(num->int32)#(num->int32)`; `K:num`; `m0:int64->byte`] C7_FILM_AUTO_GEN) THEN
  ANTS_TAC THENL [C7_ANTS_TAC C7_AUTO_H; ALL_TAC] THEN
  DISCH_THEN(ACCEPT_TAC o CONJUNCT2));;

let VA1_FILM_CLICK = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (ap:int32)
   (x0:(num->int32)#(num->int32)) (K:num) (n:num) (m0:int64->byte) (a0:int32) (a1:int32) (a2:int32).
     va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\
     fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\ gl 0 = I32 (word 16384) /\
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ 1 <= K /\ K + 520 < 4294967296 /\ n <= 520 /\
     (ap = word 0 \/ K < val ap) /\ va1_np_st (word 0) ap mdl N x0 m0 /\ va1_clean m0 /\
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0)
     ==> va1_hrun (wasmc fs) (REPLICATE K T)
           (\gl1 m1. va1_hcall (wasmc fs) va1_puncture_mc [I32 a2; I32 a1; I32 a0] (word 0)
              (va1_hrun (wasmc fs) (APPEND (REPLICATE n T) (REPLICATE (n + K) F))
                 (\gl3 m3. gl3 = gl /\ va1_np_st (word 0) ap mdl N x0 m3 /\ va1_clean m3 /\
                           read (bytes32 (word 16404)) m3 = read (bytes32 (word 16404)) m0 /\
                           va1_film_bytes N m0 m3)) gl1 m1) gl m0`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`; `ap:int32`;
                `x0:(num->int32)#(num->int32)`; `K:num`; `m0:int64->byte`; `[I32 a2; I32 a1; I32 a0]`] C7_FILM_CLICK_GEN) THEN
  ANTS_TAC THENL [C7_ANTS_TAC C7_CLICK_H; ALL_TAC] THEN
  DISCH_THEN(fun th -> ACCEPT_TAC(MP (SPEC `n:num` (CONJUNCT1 th)) (ASSUME `n <= 520`))));;

let VA1_FILM_CLICK_TO_END = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (ap:int32)
   (x0:(num->int32)#(num->int32)) (K:num) (m0:int64->byte) (a0:int32) (a1:int32) (a2:int32).
     va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\
     fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\ gl 0 = I32 (word 16384) /\
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ 1 <= K /\ K + 520 < 4294967296 /\
     (ap = word 0 \/ K < val ap) /\ va1_np_st (word 0) ap mdl N x0 m0 /\ va1_clean m0 /\
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0)
     ==> va1_hrun (wasmc fs) (REPLICATE K T)
           (\gl1 m1. va1_hcall (wasmc fs) va1_puncture_mc [I32 a2; I32 a1; I32 a0] (word 0)
              (va1_hrun (wasmc fs) (REPLICATE 520 T)
                 (\gl3 m3. gl3 = gl /\
                    va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 0)
                      (\gl4 m4. gl4 = gl3 /\ m4 = m3 /\
                         va1_hrun (wasmc fs) (REPLICATE (520 + K) F)
                           (\gl5 m5. gl5 = gl /\ va1_np_st (word 0) ap mdl N x0 m5 /\ va1_clean m5 /\
                              read (bytes32 (word 16404)) m5 = read (bytes32 (word 16404)) m0 /\
                              va1_film_bytes N m0 m5) gl4 m4) gl3 m3)) gl1 m1) gl m0`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`; `ap:int32`;
                `x0:(num->int32)#(num->int32)`; `K:num`; `m0:int64->byte`; `[I32 a2; I32 a1; I32 a0]`] C7_FILM_CLICK_GEN) THEN
  ANTS_TAC THENL [C7_ANTS_TAC C7_CLICK_H; ALL_TAC] THEN
  DISCH_THEN(ACCEPT_TAC o CONJUNCT2));;

(* ---- non-vacuity ---- *)
let c7_fs = mk_abs(`i:num`, mk_cond(`i = 25`, `(va1_f25_mc,3,1)`, mk_cond(`i = 32`, `(va1_f32_mc,2,1)`,
              mk_cond(`i = 33`, `(va1_puncture_mc,3,1)`, mk_cond(`i = 34`, `(va1_f34_mc,3,0)`, mk_comb(c4_fs, `i:num`))))));;
let C7_SAT_TAC (ap:term) : tactic =
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [ap; `\k:num. word 1:int32`; `1`; `((\i:num. word 0:int32),(\i:num. word 0:int32))`] C7_START_HDR) THEN
  REWRITE_TAC[ARITH_RULE `1 <= 640`] THEN DISCH_THEN(X_CHOOSE_THEN `m0:int64->byte` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [c7_fs; `\i:num. I32 (word 16384)`; `\k:num. word 1:int32`; `1`];;
let C7_SAT_FIN_TAC : tactic =
  REWRITE_TAC[va1_fs_np; va1_fs_pop] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV;;

let VA1_C7B_SAT = prove
 (`!K n. 1 <= K /\ K + 520 < 4294967296 /\ n <= 520
        ==> ?(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num)
             (x0:(num->int32)#(num->int32)) (m0:int64->byte).
              va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\ fs 33 = (va1_puncture_mc,3,1) /\
              fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\ gl 0 = I32 (word 16384) /\
              mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
              va1_np_st (word 0) (word K) mdl N x0 m0 /\ va1_clean m0 /\
              ~(read (bytes32 (word 16516)) m0 = word 0 /\ read (bytes32 (word 16520)) m0 = word 0 /\
                read (bytes32 (word 16524)) m0 = word 0)`,
  C7_SAT_TAC `word K:int32` THEN
  MAP_EVERY EXISTS_TAC [`((\i:num. word 0:int32),(\i:num. word 0:int32))`; `m0:int64->byte`] THEN
  C7_SAT_FIN_TAC);;

let VA1_C7A_SAT = prove
 (`!K n. 1 <= K /\ K + 520 < 4294967296 /\ n <= 520
        ==> ?(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (ap:int32)
             (x0:(num->int32)#(num->int32)) (m0:int64->byte) (a0:int32) (a1:int32) (a2:int32).
              va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\
              fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\ gl 0 = I32 (word 16384) /\
              mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
              (ap = word 0 \/ K < val ap) /\ va1_np_st (word 0) ap mdl N x0 m0 /\ va1_clean m0 /\
              ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0)`,
  C7_SAT_TAC `word 0:int32` THEN
  MAP_EVERY EXISTS_TAC [`word 0:int32`; `((\i:num. word 0:int32),(\i:num. word 0:int32))`; `m0:int64->byte`;
                        `word 1:int32`; `word 0:int32`; `word 0:int32`] THEN
  C7_SAT_FIN_TAC);;
