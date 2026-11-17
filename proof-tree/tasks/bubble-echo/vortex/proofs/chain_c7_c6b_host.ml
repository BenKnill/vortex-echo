needs "chain_c7_c6a_host.ml";;
needs "chain_c5p_rules.ml";;
(* Vortex chain rung C6b (vortex-chain-20261111-142342 c6b, Claude Opus 5.5, 2026-11-13): the auto puncture tick.        *)
(* tick_forward (f35) on the auto-pop branch under wasmn: prefix pc 3 -> 309 under wasmc with va1_seq_final2.ml's own   *)
(* call-site lemmas and VA1_RUN_TAC (stop pc 309), lifted by VA1_C5P_ENSURES_WASMN; the call at pc 309 by C5p's          *)
(* VA1_TF_CALL33_SITE fed with C6a's VA1_PUNCTURE_OK at the memory reached; the tail pc 315 -> WDone under wasmc, lifted; *)
(* glued with ENSURES_TRANS at wasmn fs. New definition va1_tf_mid. No new axioms.         Stable layer: never edit.  *)
let va1_tf_mid = new_definition
 `va1_tf_mid N (mdl:num->int32) (t:int32) (x:(num->int32)#(num->int32)) (m0:int64->byte) (m1:int64->byte) <=>
    va1_tick (word_add t (word 1)) m1 /\
    va1_vab N (ve_fredkin_fwdn (\i. ve_vk mdl) 16 x) m1 /\
    (!a. a < 4194304 /\ ~(16392 <= a /\ a < 16396) /\ ~(1114112 <= a /\ a < 1130496) /\
         ~(1966080 <= a /\ a < 2039808)
         ==> read (bytes8 (word a)) m1 = read (bytes8 (word a)) m0)`;;

let C6B_FR1 = `MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
           MAYCHANGE [wstatus] ,, MAYCHANGE [wlocal 0; wlocal 1; wlocal 2] ,,
           MAYCHANGE [wmem :> bytes(word 16392,4)] ,,
           MAYCHANGE [wmem :> bytes(word 1114112,16384)] ,,
           MAYCHANGE [wmem :> bytes(word 1966080,73728)]`;;
let C6B_FR1_BYTE = prove(mk_forall(`a:num`, mk_imp(
   `a < 4194304 /\ ~(16392 <= a /\ a < 16396) /\ ~(1114112 <= a /\ a < 1130496) /\ ~(1966080 <= a /\ a < 2039808)`,
   mk_forall(`s:wasmstate`, mk_forall(`s':wasmstate`, mk_imp(list_mk_comb(C6B_FR1, [`s:wasmstate`; `s':wasmstate`]),
     `read (wmem :> bytes8 (word a)) s' = read (wmem :> bytes8 (word a)) s`))))),
  GEN_TAC THEN STRIP_TAC THEN C3B_KEEPS_TAC C3B_BYTE_COMP_TAC);;

let C6B_MID_B32 = prove
 (`!N mdl t x (m0:int64->byte) m1 b.
     va1_tf_mid N mdl t x m0 m1 /\ b + 4 <= 4194304 /\ (b + 4 <= 16392 \/ 16396 <= b) /\
     (b + 4 <= 1114112 \/ 1130496 <= b) /\ (b + 4 <= 1966080 \/ 2039808 <= b)
     ==> read (bytes32 (word b)) m1 = read (bytes32 (word b)) m0`,
  REWRITE_TAC[va1_tf_mid] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC C6A_B32_KEEP THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let C6B_MID_MDL = prove
 (`!N mdl t x (m0:int64->byte) m1. va1_tf_mid N mdl t x m0 m1 /\ va1_mdl mdl m0 ==> va1_mdl mdl m1`,
  REWRITE_TAC[va1_mdl] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `mdl:num->int32`; `t:int32`; `x:(num->int32)#(num->int32)`; `m0:int64->byte`;
                `m1:int64->byte`; `16640 + 4 * k`] C6B_MID_B32) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let C6B_FR3 = `MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wmem]`;;
let C6B_KEEPS3 = end_itlist CONJ (map (c6a_keeps C6B_FR3)
  [`wlabels`; `warity`; `wlocal 2`; `wglobals`]);;


let c6b_W = `\w. if w = 4098 then (t:int32) else if w = 4099 then word 4294967295
   else if w = 4128 then word_add t (word 1) else if w = 4129 then (a0:int32) else if w = 4130 then (a1:int32)
   else if w = 4131 then (a2:int32) else if 4160 <= w /\ w < 5184 then (mdl:num->int32) (w - 4160)
   else if 278528 <= w /\ w < 278528 + 3 * N then FST (x:(num->int32)#(num->int32)) (w - 278528)
   else if 280576 <= w /\ w < 280576 + 3 * N then SND x (w - 280576) else word 0:int32`;;
let VA1_C6B_SAT = prove
 (`!(t:int32) (mdl:num->int32) (N:num) (x:(num->int32)#(num->int32)) (a0:int32) (a1:int32) (a2:int32).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ ~(word_add t (word 1) = word 0) /\
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0)
     ==> ?(fs:num->byte list#num#num) (gl:num->wval) (m0:int64->byte) (s:wasmstate).
           fs 9 = (va1_f9_mc,0,0) /\ fs 27 = (va1_f27_mc,0,0) /\ fs 33 = (va1_puncture_mc,3,1) /\
     fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\
           gl 0 = I32 (word 16384) /\
           va1_tick t m0 /\ va1_pop (word 4294967295) (word_add t (word 1)) m0 /\ va1_mdl mdl m0 /\ va1_vab N x m0 /\
     read (bytes32 (word 16516)) m0 = a0 /\ read (bytes32 (word 16520)) m0 = a1 /\ read (bytes32 (word 16524)) m0 = a2 /\
           read wcode s = va1_tick_forward_mc /\ read wpc s = word 3 /\ read wstatus s = WRunning /\
           read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
           read wmemsize s = 4194304 /\ read wglobals s = gl /\ read wmem s = m0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `\f:num. if f = 9 then (va1_f9_mc,0,0) else if f = 27 then (va1_f27_mc,0,0)
     else if f = 33 then (va1_puncture_mc,3,1) else if f = 25 then (va1_f25_mc,3,1)
     else if f = 32 then (va1_f32_mc,2,1) else (va1_f34_mc,3,0)` THEN
  EXISTS_TAC `\k:num. I32 (word 16384)` THEN
  EXISTS_TAC (mk_comb(c3b_memw, c6b_W)) THEN
  EXISTS_TAC (subst [mk_comb(c3b_memw, c6b_W), `mm:int64->byte`]
   `write wcode va1_tick_forward_mc (write wpc (word 3) (write wstatus WRunning (write wstack [] (write wlabels []
     (write warity 1 (write wmemsize 4194304 (write wglobals (\k:num. I32 (word 16384))
       (write wmem (mm:int64->byte) (ARB:wasmstate)))))))))`) THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  REWRITE_TAC[va1_tick; va1_pop; va1_mdl; va1_vab; ARITH_EQ] THEN REPEAT CONJ_TAC THEN C3B_MEMCONJ_TAC c6b_W);;
let c6b_mid pc stk memp = (mk_abs(`s:wasmstate`, list_mk_conj
  [mk_eq(`read wcode s`, `va1_tick_forward_mc`); mk_eq(`read wpc s`, mk_comb(`word:num->int64`, mk_small_numeral pc));
   `read wstatus s = WRunning`; mk_eq(`read wstack s`, stk); `read wlabels s = [0,317,0]`; `read warity s = 1`;
   `read (wlocal 2) s = I32 (word 1)`; `read wmemsize s = 4194304`; `read wglobals s = (gl:num->wval)`; memp]));;
let C6B_MIDP = `va1_tf_mid N mdl t x (m0:int64->byte) (read wmem s) /\
   read (bytes32 (word 16396)) (read wmem s) = word 4294967295 /\ va1_mdl mdl (read wmem s)`;;
let C6B_POSTM = `\m:int64->byte. ?m1. va1_tf_mid N mdl t x (m0:int64->byte) m1 /\ va1_c6a_mem mdl m1 m /\
   read (bytes32 (word 16408)) m = a0 /\ read (bytes32 (word 16412)) m = a1 /\ read (bytes32 (word 16416)) m = a2`;;
let C6B_MID309 = c6b_mid 309 `[I32 a2; I32 a1; I32 a0]` C6B_MIDP;;
let C6B_MID315 = c6b_mid 315 `[I32 (word 0)]` (rhs(concl(BETA_CONV(mk_comb(C6B_POSTM, `read wmem s`)))));;
let C6B_CALL = prove
 (list_mk_forall([`fs:num->byte list#num#num`; `gl:num->wval`; `t:int32`; `mdl:num->int32`; `N:num`;
    `x:(num->int32)#(num->int32)`; `m0:int64->byte`; `a0:int32`; `a1:int32`; `a2:int32`],
   mk_imp(`(fs:num->byte list#num#num) 33 = (va1_puncture_mc,3,1) /\ fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\
           fs 34 = (va1_f34_mc,3,0) /\ (gl:num->wval) 0 = I32 (word 16384) /\ ~(word_add (t:int32) (word 1) = word 0) /\
           ~((a0:int32) = word 0 /\ (a1:int32) = word 0 /\ (a2:int32) = word 0)`,
     list_mk_comb(`ensures (wasmn (fs:num->byte list#num#num))`, [C6B_MID309; C6B_MID315; C6B_FR3]))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ensures] THEN X_GEN_TAC `s:wasmstate` THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  ABBREV_TAC `m1 = read wmem (s:wasmstate)` THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `word_add t (word 1):int32`; `mdl:num->int32`; `a0:int32`; `a1:int32`;
                `a2:int32`; `m1:int64->byte`] VA1_PUNCTURE_OK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[va1_tf_mid]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun po ->
    let qq = rand(rator(concl po)) in
    MP_TAC(SPECL [`fs:num->byte list#num#num`; `a0:int32`; `a1:int32`; `a2:int32`; `[]:wval list`; `m1:int64->byte`;
      `word 0:int32`; `\m':int64->byte. va1_c6a_mem mdl m1 m' /\ read (bytes32 (word 16408)) m' = a0 /\
         read (bytes32 (word 16412)) m' = a1 /\ read (bytes32 (word 16416)) m' = a2`; qq] VA1_TF_CALL33_SITE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[po] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN MESON_TAC[]; ALL_TAC]) THEN
  REWRITE_TAC[ensures] THEN DISCH_THEN(MP_TAC o SPEC `s:wasmstate`) THEN
  ANTS_TAC THENL
   [CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[wglobal; READ_COMPONENT_COMPOSE; READ_ELEMENT];
    ALL_TAC] THEN
  MATCH_MP_TAC C6A_EV_MONO THEN X_GEN_TAC `s':wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> C6A_KEEPS_ON C6B_KEEPS3 th) THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `m1:int64->byte` THEN ASM_REWRITE_TAC[]);;
let C6B_PRE0 = `\s. read wcode s = va1_tick_forward_mc /\ read wpc s = word 3 /\
               read wstatus s = WRunning /\ read wstack s = [] /\
               read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\ read wglobals s = (gl:num->wval) /\
               va1_tick t (read wmem s) /\
               va1_pop (word 4294967295) (word_add t (word 1)) (read wmem s) /\
               va1_mdl mdl (read wmem s) /\ va1_vab N (x:(num->int32)#(num->int32)) (read wmem s)`;;
let c6b_post1 vk = subst [vk, `VK:(num->int32)->(num->int32)->num->int32`]
  (c6b_mid 309 `[I32 (read (bytes32 (word 16524)) (read wmem s)); I32 (read (bytes32 (word 16520)) (read wmem s));
                 I32 (read (bytes32 (word 16516)) (read wmem s))]`
   `va1_tick (word_add t (word 1)) (read wmem s) /\
    va1_pop (word 4294967295) (word_add t (word 1)) (read wmem s) /\
    va1_mdl mdl (read wmem s) /\
    va1_vab N (ve_fredkin_fwdn (\i. (VK:(num->int32)->(num->int32)->num->int32) mdl) 16 x) (read wmem s)`);;
let C6B_PREFIX_VK = prove
 (list_mk_forall([`VK:(num->int32)->(num->int32)->num->int32`; `fs:num->byte list#num#num`; `gl:num->wval`;
    `t:int32`; `mdl:num->int32`; `N:num`; `x:(num->int32)#(num->int32)`],
   mk_imp(`ve_vk_ok (VK:(num->int32)->(num->int32)->num->int32) /\ (mdl:num->int32) 1 = word N /\ 1 <= N /\ N <= 640 /\
     (fs:num->byte list#num#num) 9 = (ve_vort_apply_mc,0,0) /\ fs 27 = (ve_tick_inc_mc,0,0) /\ ~(word_add (t:int32) (word 1) = word 0)`,
     list_mk_comb(`ensures (wasmc (fs:num->byte list#num#num))`, [C6B_PRE0; c6b_post1 `VK:(num->int32)->(num->int32)->num->int32`; C6B_FR1]))),
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN VA1_MEMNAME_TAC "mm0" THEN
  VA1_RUN_TAC VA1_TICK_FORWARD_EXEC [9,VA1_CALL_VA; 27,VA1_CALL_TI] [309] THEN
  ENSURES_FINAL_STATE_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV VA1_ITER_CONV) THEN ASM_REWRITE_TAC[]);;
let C6B_PREFIX = prove
 (list_mk_forall([`fs:num->byte list#num#num`; `gl:num->wval`;
    `t:int32`; `mdl:num->int32`; `N:num`; `x:(num->int32)#(num->int32)`],
   mk_imp(`(mdl:num->int32) 1 = word N /\ 1 <= N /\ N <= 640 /\
     (fs:num->byte list#num#num) 9 = (va1_f9_mc,0,0) /\ fs 27 = (va1_f27_mc,0,0) /\ ~(word_add (t:int32) (word 1) = word 0)`,
     list_mk_comb(`ensures (wasmc (fs:num->byte list#num#num))`, [C6B_PRE0; c6b_post1 `ve_vk`; C6B_FR1]))),
  REWRITE_TAC[VA1_F9_IS_VORT_APPLY; VA1_F27_IS_TICK_INC] THEN VA1_VK_TAC C6B_PREFIX_VK);;

let C6B_PRE = `\s. read wcode s = va1_tick_forward_mc /\ read wpc s = word 3 /\ read wstatus s = WRunning /\
               read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\ read wglobals s = (gl:num->wval) /\ read wmem s = (m0:int64->byte)`;;
let C6B_PREFIX_MID = prove
 (list_mk_forall([`fs:num->byte list#num#num`; `gl:num->wval`; `t:int32`; `mdl:num->int32`; `N:num`;
    `x:(num->int32)#(num->int32)`; `m0:int64->byte`; `a0:int32`; `a1:int32`; `a2:int32`],
   mk_imp(`(fs:num->byte list#num#num) 9 = (va1_f9_mc,0,0) /\ fs 27 = (va1_f27_mc,0,0) /\
     (mdl:num->int32) 1 = word N /\ 1 <= N /\ N <= 640 /\ ~(word_add (t:int32) (word 1) = word 0) /\
     va1_tick t m0 /\ va1_pop (word 4294967295) (word_add t (word 1)) m0 /\ va1_mdl mdl m0 /\
     va1_vab N (x:(num->int32)#(num->int32)) m0 /\
     read (bytes32 (word 16516)) m0 = (a0:int32) /\ read (bytes32 (word 16520)) m0 = (a1:int32) /\
     read (bytes32 (word 16524)) m0 = (a2:int32)`,
     list_mk_comb(`ensures (wasmc (fs:num->byte list#num#num))`, [C6B_PRE; C6B_MID309; C6B_FR1]))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ensures] THEN X_GEN_TAC `s:wasmstate` THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `t:int32`; `mdl:num->int32`; `N:num`;
                `x:(num->int32)#(num->int32)`] C6B_PREFIX) THEN
  ASM_REWRITE_TAC[ensures] THEN DISCH_THEN(MP_TAC o SPEC `s:wasmstate`) THEN
  ANTS_TAC THENL [CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC C6A_EV_MONO THEN X_GEN_TAC `s':wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  SUBGOAL_THEN `va1_tf_mid N mdl t x m0 (read wmem (s':wasmstate))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[va1_tf_mid] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPEC `a:num` C6B_FR1_BYTE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`s:wasmstate`; `s':wasmstate`]) THEN ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE];
    ALL_TAC] THEN
  MAP_EVERY (fun b ->
    MP_TAC(SPECL [`N:num`; `mdl:num->int32`; `t:int32`; `x:(num->int32)#(num->int32)`; `m0:int64->byte`;
                  `read wmem (s':wasmstate)`; b] C6B_MID_B32) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC) [`16516`; `16520`; `16524`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[va1_pop]) THEN ASM_REWRITE_TAC[]);;

let C6B_FR4 = `MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus]`;;
let C6B_TAIL_W = prove
 (list_mk_forall([`fs:num->byte list#num#num`; `gl:num->wval`; `Rm:(int64->byte)->bool`],
   list_mk_comb(`ensures (wasmc (fs:num->byte list#num#num))`,
    [c6b_mid 315 `[I32 (word 0)]` `(Rm:(int64->byte)->bool) (read wmem s)`;
     `\s. read wstatus s = WDone /\ read wstack s = [I32 (word 1)] /\
          read wmemsize s = 4194304 /\ read wglobals s = (gl:num->wval) /\ (Rm:(int64->byte)->bool) (read wmem s)`;
     C6B_FR4])),
  REPEAT GEN_TAC THEN ENSURES_INIT_TAC "s0" THEN VA1_MEMNAME_TAC "mm0" THEN
  VA1_RUN_TAC VA1_TICK_FORWARD_EXEC [] [] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;
let VA1_TICK_FORWARD_PUNCT = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (t:int32) (mdl:num->int32) (N:num) (x:(num->int32)#(num->int32)) (a0:int32) (a1:int32) (a2:int32) (m0:int64->byte).
     fs 9 = (va1_f9_mc,0,0) /\ fs 27 = (va1_f27_mc,0,0) /\ fs 33 = (va1_puncture_mc,3,1) /\
     fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ gl 0 = I32 (word 16384) /\ ~(word_add t (word 1) = word 0) /\
     va1_tick t m0 /\ va1_pop (word 4294967295) (word_add t (word 1)) m0 /\ va1_mdl mdl m0 /\ va1_vab N x m0 /\
     read (bytes32 (word 16516)) m0 = a0 /\ read (bytes32 (word 16520)) m0 = a1 /\ read (bytes32 (word 16524)) m0 = a2 /\
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0)
     ==> ensures (wasmn fs)
          (\s. read wcode s = va1_tick_forward_mc /\ read wpc s = word 3 /\ read wstatus s = WRunning /\
               read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\ read wmem s = m0)
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 1)] /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               ?m1. va1_tf_mid N mdl t x m0 m1 /\ va1_c6a_mem mdl m1 (read wmem s) /\
                    read (bytes32 (word 16408)) (read wmem s) = a0 /\ read (bytes32 (word 16412)) (read wmem s) = a1 /\
                    read (bytes32 (word 16416)) (read wmem s) = a2)
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocal 0; wlocal 1; wlocal 2] ,, MAYCHANGE [wmem])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC (mk_binop `(,,):(wasmstate->wasmstate->bool)->(wasmstate->wasmstate->bool)->wasmstate->wasmstate->bool` C6B_FR1
     (mk_binop `(,,):(wasmstate->wasmstate->bool)->(wasmstate->wasmstate->bool)->wasmstate->wasmstate->bool` C6B_FR3 C6B_FR4)) THEN
  CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_TRANS THEN EXISTS_TAC C6B_MID309 THEN CONJ_TAC THENL
   [MATCH_MP_TAC VA1_C5P_ENSURES_WASMN THEN MATCH_MP_TAC C6B_PREFIX_MID THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_TRANS THEN EXISTS_TAC C6B_MID315 THEN CONJ_TAC THENL
   [MATCH_MP_TAC C6B_CALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC VA1_C5P_ENSURES_WASMN THEN
  MP_TAC(BETA_RULE(ISPECL [`fs:num->byte list#num#num`; `gl:num->wval`; C6B_POSTM] C6B_TAIL_W)) THEN
  REWRITE_TAC[]);;
