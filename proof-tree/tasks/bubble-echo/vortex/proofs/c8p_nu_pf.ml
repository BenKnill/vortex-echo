(* ========================================================================= *)
(* C8p rows P6 + P7 (lane vortex-chain-20261111-142342, role c8p, Claude     *)
(* Opus 5.5, 2026-11-15): the click puncture and the auto puncture tick with *)
(* the speed table (va1_ptbl, P4) and the 21 header words (va1_phdr, P5)     *)
(* named. C7 context (chain_c7_c6a_host.ml / chain_c7_c6b_host.ml / C8b's    *)
(* c8b_c6_u.ml), re-running their compositions with VA1_F33_TO_F25_V in      *)
(* place of VA1_F33_TO_F25 and VA1_F25_HDR in place of VA1_F25_OK.           *)
(* No axioms or cheats.                                                      *)
(* ========================================================================= *)
needs "c8b_c6_u.ml";;
needs "c8p_f25h2_pf.ml";;
needs "c8p7_f33_p.ml";;
needs "c8p_nu_stmts.ml";;

(* ---- f25's frame keeps the table ---- *)
let C8P_F25_TBL = prove
 (`!(m1:int64->byte) m2 f. va1_f25_frame m1 m2 /\ va1_w32s 65536 262144 f m1 ==> va1_w32s 65536 262144 f m2`,
  REWRITE_TAC[va1_w32s] THEN REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS `read (bytes32 (word (65536 + 4 * k))) (m1:int64->byte)` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
  MATCH_MP_TAC C6A_B32_KEEP THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[va1_f25_frame] o
    check (fun th -> can (find_term ((=) `va1_f25_frame`)) (concl th))) THEN ASM_ARITH_TAC);;

(* ---- the call at pc 1232 with the header ---- *)
let C6A_CALL25_N = prove
 (`!fs t mdl a0 a1 a2 (m1:int64->byte).
     fs 25 = (va1_f25_mc,3,1) /\
     va1_tick t m1 /\ read (bytes32 (word 16396)) m1 = word 4294967295 /\ va1_mdl mdl m1 /\
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0)
     ==> ensures (wasmc fs)
          (\s. read wcode s = va1_puncture_mc /\ read wpc s = word 1232 /\ read wstatus s = WRunning /\
               read wstack s = [I32 a2; I32 a1; I32 a0] /\ read wmemsize s = 4194304 /\ read wmem s = m1)
          (\s. read wcode s = va1_puncture_mc /\ read wpc s = word 1238 /\ read wstatus s = WRunning /\
               read wstack s = [I32 (word 0)] /\
               va1_f25_post t mdl (va1_rd32 65536 m1) a0 a1 a2 (read wmem s) /\ va1_f25_frame m1 (read wmem s) /\
               va1_w32s 16420 21 (va1_phdr a0 a1 a2) (read wmem s))
          (MAYCHANGE [wmem] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wpc])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a0:int32`; `a1:int32`; `a2:int32`; `t:int32`; `mdl:num->int32`; `va1_rd32 65536 m1`; C6A_D25]
    VA1_F25_HDR) THEN
  ASM_REWRITE_TAC[CONJUNCT2 VA1_F25_CALLEE] THEN
  DISCH_THEN(fun lth ->
    let _,largs = strip_comb(concl lth) in
    let pp = el 1 largs and qq = el 2 largs and cc = el 3 largs in
    MATCH_MP_TAC(ISPECL [`fs:num->byte list#num#num`; `25`; `va1_f25_mc`; `3`; `1`; `13`; C6A_D25; pp; qq; cc]
      WASMC_CALL_ENSURES) THEN
    EXISTS_TAC `6` THEN ASM_REWRITE_TAC[lth; VA1_F25_ENTRY; CONJUNCT2 VA1_F25_CALLEE]) THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN MESON_TAC[distinctness "wstat"];
    X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[LENGTH; ARITH_RULE `3 <= SUC(SUC(SUC 0))`] THEN
    REWRITE_TAC[WCALL_ENTRY_READS; VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[C6A_D1232] THEN CONV_TAC(ONCE_DEPTH_CONV CP_LOCALS_EVAL_CONV) THEN
    REWRITE_TAC[va1_w32s; va1_rd32];
    MAP_EVERY X_GEN_TAC [`s:wasmstate`; `c1:wasmstate`] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    STRIP_TAC THEN
    FIRST_ASSUM(fun th -> if can (term_match [] (list_mk_comb(C3B_FRAME,[`x:wasmstate`;`y:wasmstate`]))) (concl th)
      then MP_TAC(MATCH_MP C6A_F25_KEEPS th) THEN MP_TAC(MATCH_MP VA1_F25_FRAME_BYTES th) else NO_TAC) THEN
    REWRITE_TAC[WCALL_ENTRY_READS] THEN ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(SPECL [`1238`; `3`; `c1:wasmstate`; `s:wasmstate`] CP_WCALL_RETURN_N) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV CP_LOCALS_EVAL_CONV) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC C6A_SEQ3 THEN
    MAP_EVERY EXISTS_TAC [`write wmem (read wmem (c1:wasmstate)) s`;
                          `write wstack [I32 (word 0)] (write wmem (read wmem (c1:wasmstate)) s)`] THEN
    REWRITE_TAC[MAYCHANGE; SEQ_ID; ASSIGNS_THM] THEN MESON_TAC[]]);;

(* ---- pc 1232 -> 1238 with the table and the header ---- *)
let C6A_MID_N = prove
 (`!fs t mdl a0 a1 a2 (m:int64->byte).
     fs 25 = (va1_f25_mc,3,1) /\
     read (bytes32 (word 16396)) m = word 4294967295 /\ va1_tick t m /\ va1_mdl mdl m /\
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0)
     ==> ensures (wasmc fs)
          (\s. read wcode s = va1_puncture_mc /\ read wpc s = word 1232 /\ read wstatus s = WRunning /\
               read wstack s = [I32 a2; I32 a1; I32 a0] /\ read wmemsize s = 4194304 /\
               va1_f33_frame m (read wmem s) /\
               va1_w32s 65536 262144 (va1_ptbl a0 a1 a2 (mdl 2)) (read wmem s))
          (\s. read wcode s = va1_puncture_mc /\ read wpc s = word 1238 /\ read wstatus s = WRunning /\
               read wstack s = [I32 (word 0)] /\ va1_c6a_mem mdl m (read wmem s) /\
               read (bytes32 (word 16408)) (read wmem s) = a0 /\ read (bytes32 (word 16412)) (read wmem s) = a1 /\
               read (bytes32 (word 16416)) (read wmem s) = a2 /\
               va1_w32s 65536 262144 (va1_ptbl a0 a1 a2 (mdl 2)) (read wmem s) /\
               va1_w32s 16420 21 (va1_phdr a0 a1 a2) (read wmem s))
          (MAYCHANGE [wmem] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wpc])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ensures] THEN X_GEN_TAC `s:wasmstate` THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:int32`; `mdl:num->int32`; `m:int64->byte`; `read wmem s`] C6A_PRE_MEM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `t:int32`; `mdl:num->int32`; `a0:int32`; `a1:int32`; `a2:int32`;
                `read wmem s`] C6A_CALL25_N) THEN
  ASM_REWRITE_TAC[ensures] THEN DISCH_THEN(MP_TAC o SPEC `s:wasmstate`) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C6A_EV_MONO THEN X_GEN_TAC `s':wasmstate` THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  SUBGOAL_THEN `va1_w32s 65536 262144 (va1_ptbl a0 a1 a2 (mdl 2)) (read wmem (s':wasmstate))` ASSUME_TAC THENL
   [MATCH_MP_TAC C8P_F25_TBL THEN EXISTS_TAC `read wmem (s:wasmstate)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C6A_POST_MEM THEN EXISTS_TAC `t:int32` THEN EXISTS_TAC `read wmem s` THEN ASM_REWRITE_TAC[]);;

(* ---- the whole click call, ensures form ---- *)
let VA1_PUNCTURE_OK_N = prove(parse_term c8p_spec_VA1_PUNCTURE_OK_N,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ensures] THEN X_GEN_TAC `s0:wasmstate` THEN DISCH_TAC THEN
  SUBGOAL_THEN `read (bytes32 (word 16648)) (m:int64->byte) = mdl 2` ASSUME_TAC THENL
   [UNDISCH_TAC `va1_mdl mdl (m:int64->byte)` THEN REWRITE_TAC[va1_mdl] THEN
    DISCH_THEN(MP_TAC o SPEC `2`) THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `a0:int32`; `a1:int32`; `a2:int32`; `m:int64->byte`] C8P_F33_TO_F25_V) THEN
  ANTS_TAC THENL [RULE_ASSUM_TAC(REWRITE_RULE[va1_tick]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ensures; ASSUME `read (bytes32 (word 16648)) (m:int64->byte) = mdl 2`] THEN
  DISCH_THEN(MP_TAC o SPEC `s0:wasmstate`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP C6A_EV_CHAIN') THEN
  X_GEN_TAC `s1:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `t:int32`; `mdl:num->int32`; `a0:int32`; `a1:int32`; `a2:int32`;
                `m:int64->byte`] C6A_MID_N) THEN
  ASM_REWRITE_TAC[ensures] THEN DISCH_THEN(MP_TAC o SPEC `s1:wasmstate`) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP C6A_EV_CHAIN') THEN
  X_GEN_TAC `s2:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if can (term_match [] (list_mk_comb(C6A_FRAME_D,[`x:wasmstate`;`y:wasmstate`]))) (concl th)
    then C6A_KEEPS_ON C6A_D_KEEPS th else NO_TAC) THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `word 0:int32`] VA1_F33_EPILOGUE) THEN
  REWRITE_TAC[ensures] THEN DISCH_THEN(MP_TAC o SPEC `s2:wasmstate`) THEN
  ANTS_TAC THENL [REWRITE_TAC[va1_f33_epi_pre] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC C6A_EV_MONO THEN X_GEN_TAC `s3:wasmstate` THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if can (term_match [] (list_mk_comb(C6A_FRAME_E,[`x:wasmstate`;`y:wasmstate`]))) (concl th)
    then C6A_KEEPS_ON C6A_E_KEEPS th else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC C6A_FRAME_COMP THEN
  MAP_EVERY EXISTS_TAC [`s1:wasmstate`; `s2:wasmstate`] THEN ASM_REWRITE_TAC[]);;

(* ---- the click as a host call ---- *)
let VA1_HCALL_PUNCTURE_N = prove(parse_term c8p_spec_VA1_HCALL_PUNCTURE_N,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`17`; C6A_DECLS33] THEN REWRITE_TAC[VA1_PUNCTURE_CALLEE] THEN
  X_GEN_TAC `s0:wasmstate` THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH [I32 a2; I32 a1; I32 a0] = 3` SUBST1_TAC THENL
   [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC (mk_eq(`e0:wasmstate`,
    list_mk_comb(`wcall_entry`, [`va1_puncture_mc`; `3`; `1`; `[I32 a2; I32 a1; I32 a0]`; `17`; C6A_DECLS33; `s0:wasmstate`]))) THEN
  SUBGOAL_THEN `va1_f33_pre a0 a1 a2 m e0 /\ read wglobals e0 = gl` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e0" THEN REWRITE_TAC[WCALL_ENTRY_READS] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`a0:int32`; `a1:int32`; `a2:int32`; `s0:wasmstate`] VA1_F33_ENTRY) THEN
    ASM_REWRITE_TAC[wglobal; READ_COMPONENT_COMPOSE; READ_ELEMENT];
    ALL_TAC] THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `t:int32`; `mdl:num->int32`; `a0:int32`; `a1:int32`; `a2:int32`;
                `m:int64->byte`] VA1_PUNCTURE_OK_N) THEN
  ASM_REWRITE_TAC[ensures] THEN DISCH_THEN(MP_TAC o SPEC `e0:wasmstate`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C6A_EV_MONO THEN X_GEN_TAC `s:wasmstate` THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[va1_c6a_rel] THEN
  TRANS_TAC EQ_TRANS `read wglobals (e0:wasmstate)` THEN CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC C6A_GLOBALS THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[wglobal; READ_COMPONENT_COMPOSE; READ_ELEMENT]);;

(* ---- P7: the auto puncture tick (C8b's B8 proof with the named post) ---- *)
let C6B_POSTM_NU = `\m:int64->byte. va1_w32s 65536 262144 (va1_ptbl a0 a1 a2 (mdl 2)) m /\
   va1_w32s 16420 21 (va1_phdr a0 a1 a2) m /\
   ?m1. va1_tf_mid N mdl t x (m0:int64->byte) m1 /\ va1_c6a_mem mdl m1 m /\
   read (bytes32 (word 16408)) m = a0 /\ read (bytes32 (word 16412)) m = a1 /\ read (bytes32 (word 16416)) m = a2 /\
   va1_vabu N (uw:(num->int32)#(num->int32)) m`;;
let C6B_MID315_NU = c6b_mid 315 `[I32 (word 0)]` (rhs(concl(BETA_CONV(mk_comb(C6B_POSTM_NU, `read wmem s`)))));;

let C6B_CALL_NU = prove
 (list_mk_forall([`fs:num->byte list#num#num`; `gl:num->wval`; `t:int32`; `mdl:num->int32`; `N:num`;
    `x:(num->int32)#(num->int32)`; `m0:int64->byte`; `a0:int32`; `a1:int32`; `a2:int32`;
    `uw:(num->int32)#(num->int32)`],
   mk_imp(`(fs:num->byte list#num#num) 33 = (va1_puncture_mc,3,1) /\ fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\
           fs 34 = (va1_f34_mc,3,0) /\ (gl:num->wval) 0 = I32 (word 16384) /\ ~(word_add (t:int32) (word 1) = word 0) /\
           ~((a0:int32) = word 0 /\ (a1:int32) = word 0 /\ (a2:int32) = word 0)`,
     list_mk_comb(`ensures (wasmn (fs:num->byte list#num#num))`, [C6B_MID309_U; C6B_MID315_NU; C6B_FR3]))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ensures] THEN X_GEN_TAC `s:wasmstate` THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  ABBREV_TAC `m1 = read wmem (s:wasmstate)` THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `word_add t (word 1):int32`; `mdl:num->int32`; `a0:int32`; `a1:int32`;
                `a2:int32`; `m1:int64->byte`] VA1_PUNCTURE_OK_N) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[va1_tf_mid]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun po ->
    let qq = rand(rator(concl po)) in
    MP_TAC(SPECL [`fs:num->byte list#num#num`; `a0:int32`; `a1:int32`; `a2:int32`; `[]:wval list`; `m1:int64->byte`;
      `word 0:int32`; `\m':int64->byte. va1_c6a_mem mdl m1 m' /\ read (bytes32 (word 16408)) m' = a0 /\
         read (bytes32 (word 16412)) m' = a1 /\ read (bytes32 (word 16416)) m' = a2 /\
         va1_w32s 65536 262144 (va1_ptbl a0 a1 a2 (mdl 2)) m' /\ va1_w32s 16420 21 (va1_phdr a0 a1 a2) m'`; qq]
      VA1_TF_CALL33_SITE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[po] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN MESON_TAC[]; ALL_TAC]) THEN
  REWRITE_TAC[ensures] THEN DISCH_THEN(MP_TAC o SPEC `s:wasmstate`) THEN
  ANTS_TAC THENL
   [CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[wglobal; READ_COMPONENT_COMPOSE; READ_ELEMENT];
    ALL_TAC] THEN
  MATCH_MP_TAC C6A_EV_MONO THEN X_GEN_TAC `s':wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> C6A_KEEPS_ON C6B_KEEPS3 th) THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `m1:int64->byte` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C8B_C6A_VABU THEN EXISTS_TAC `mdl:num->int32` THEN EXISTS_TAC `m1:int64->byte` THEN
  ASM_REWRITE_TAC[]);;

let VA1_TICK_FORWARD_PUNCT_NU = prove(parse_term c8p_spec_VA1_TICK_FORWARD_PUNCT_NU,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `va1_vabu N (uw:(num->int32)#(num->int32)) m0` THENL
   [ALL_TAC;
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC `\s:wasmstate. F` THEN CONJ_TAC THENL
     [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_MESON_TAC[]; REWRITE_TAC[ensures]]] THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC (mk_binop `(,,):(wasmstate->wasmstate->bool)->(wasmstate->wasmstate->bool)->wasmstate->wasmstate->bool` C6B_FR1
     (mk_binop `(,,):(wasmstate->wasmstate->bool)->(wasmstate->wasmstate->bool)->wasmstate->wasmstate->bool` C6B_FR3 C6B_FR4)) THEN
  CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC C6B_PRE THEN CONJ_TAC THENL
   [GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_TRANS THEN EXISTS_TAC C6B_MID309_U THEN CONJ_TAC THENL
   [MATCH_MP_TAC VA1_C5P_ENSURES_WASMN THEN MATCH_MP_TAC C6B_PREFIX_MID_U THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_TRANS THEN EXISTS_TAC C6B_MID315_NU THEN CONJ_TAC THENL
   [MATCH_MP_TAC C6B_CALL_NU THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC VA1_C5P_ENSURES_WASMN THEN
  MP_TAC(BETA_RULE(ISPECL [`fs:num->byte list#num#num`; `gl:num->wval`; C6B_POSTM_NU] C6B_TAIL_W)) THEN
  REWRITE_TAC[]);;

let C8P_NU_CHECK = if forall (fun th -> hyp th = [])
  [C8P_F25_TBL; C6A_CALL25_N; C6A_MID_N; VA1_PUNCTURE_OK_N; VA1_HCALL_PUNCTURE_N; C6B_CALL_NU; VA1_TICK_FORWARD_PUNCT_NU]
  then TRUTH else failwith "C8P_NU_CHECK";;
