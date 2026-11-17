(* Vortex chain rung C5' (lane vortex-chain-20261111-142342 c5p, Claude Opus 5.5, 2026-11-13): layer R, the auto-  *)
(* puncture call rules. f33 (export "puncture") as a wasmn callee: its wasmc host-entry contract (C5/C6a frame,      *)
(* global 0 moved and restored) becomes a wfsum without wglobal 0 in the frame (VA1_F33_WFSUM, rule G3), and a      *)
(* caller's `call 33` becomes one ensures (wasmn fs) step (VA1_CALL33_WASMN / _FROM_WASMC), instantiated at the     *)
(* real site, tick_forward (f35) pc 309 (VA1_TF_CALL33_SITE). Transfer wasmc -> wasmn: VA1_C5P_ENSURES_WASMN and    *)
(* _EVENTUALLY_WASMN (re-bound from the shim). Stable layer: never edit (new files get new names).                    *)
needs "chain_c5_punct_a.ml";;
needs "va1_code.ml";;
needs "chain_c5p_frames.ml";;

let VA1_C5P_F6_KEEPS = prove
 (`!s s'. (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocals] ,, MAYCHANGE [wmem]) s s'
          ==> read wglobals s' = read wglobals s /\ read wmemsize s' = read wmemsize s /\
              read wcode s' = read wcode s /\ read warity s' = read warity s`,
  REWRITE_TAC[MAYCHANGE; SEQ_ID; seq; ASSIGNS; assign] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN REWRITE_TAC[]);;
let VA1_C5P_F7_SUB = prove
 (`(MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
    MAYCHANGE [wlocals] ,, MAYCHANGE [wglobal 0] ,, MAYCHANGE [wmem]) subsumed
   ((MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
     MAYCHANGE [wlocals] ,, MAYCHANGE [wmem]) ,, MAYCHANGE [wglobal 0])`,
  SUBSUMED_MAYCHANGE_TAC);;

let VA1_C5P_WTAKE_0 = prove(`!l:A list. wtake 0 l = []`, LIST_INDUCT_TAC THEN REWRITE_TAC[wtake]);;
let VA1_C5P_WDROP_0 = prove(`!l:A list. wdrop 0 l = l`, LIST_INDUCT_TAC THEN REWRITE_TAC[wdrop]);;
let c5p_decls33 = rand(rhs(concl(CONJUNCT2 VA1_PUNCTURE_CALLEE)));;
let VA1_F33_WFSUM = prove
 (`!fs a0 a1 a2 m (Q:wasmstate->bool).
     (!s. Q s ==> read (wglobal 0) s = I32 (word 16384)) /\
     ensures (wasmc fs) (va1_f33_pre a0 a1 a2 m) Q
       (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
        MAYCHANGE [wlocals] ,, MAYCHANGE [wglobal 0] ,, MAYCHANGE [wmem])
     ==> wfsum fs (va1_f33_pre a0 a1 a2 m) Q
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocals] ,, MAYCHANGE [wmem])`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WASMN_TO_WFSUM THEN
  MATCH_MP_TAC WASM_ENSURES_GLOBAL_RESTORED THEN EXISTS_TAC `0` THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[wglobal; READ_COMPONENT_COMPOSE] THEN
    ASM_MESON_TAC[VA1_C5P_F6_KEEPS];
    REWRITE_TAC[va1_f33_pre] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC `MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
        MAYCHANGE [wlocals] ,, MAYCHANGE [wglobal 0] ,, MAYCHANGE [wmem]` THEN
    REWRITE_TAC[VA1_C5P_F7_SUB] THEN MATCH_MP_TAC ENSURES_WASMC_WASMN THEN ASM_REWRITE_TAC[]]);;

let VA1_C5P_WRITE_BACK = prove
 (`!s c1:wasmstate. read wglobals c1 = read wglobals s /\ read wmemsize c1 = read wmemsize s ==>
     write wmemsize (read wmemsize c1) (write wglobals (read wglobals c1) s) = s`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[WGLOBALS_SVC; WMEMSIZE_SVC]);;
let VA1_CALL33_WASMN = prove
 (`!fs mc pc a0 a1 a2 (rest:wval list) m r (R:(int64->byte)->bool) (Q:wasmstate->bool).
     fs 33 = (va1_puncture_mc,3,1) /\ pc < 2 EXP 64 /\ wasm_decode mc pc = SOME (Wcall 33,6) /\
     wfsum fs (va1_f33_pre a0 a1 a2 m) Q
       (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
        MAYCHANGE [wlocals] ,, MAYCHANGE [wmem]) /\
     (!c. Q c ==> read wstatus c = WDone /\ read wstack c = [I32 r] /\ R (read wmem c))
     ==> ensures (wasmn fs)
          (\s. read wcode s = mc /\ read wpc s = word pc /\ read wstatus s = WRunning /\
               read wstack s = CONS (I32 a2) (CONS (I32 a1) (CONS (I32 a0) rest)) /\
               read wmemsize s = 4194304 /\ read (wglobal 0) s = I32 (word 16384) /\ read wmem s = m)
          (\s. read wcode s = mc /\ read wpc s = word (pc + 6) /\ read wstatus s = WRunning /\
               read wstack s = CONS (I32 r) rest /\
               read wmemsize s = 4194304 /\ read (wglobal 0) s = I32 (word 16384) /\ R (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wmem])`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC `MAYCHANGE [wmem] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wpc]` THEN
  CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
  MATCH_MP_TAC WASMN_CALL_ENSURES THEN
  MAP_EVERY EXISTS_TAC [`33`; `va1_puncture_mc`; `3`; `1`; `17`; c5p_decls33;
    `va1_f33_pre a0 a1 a2 m`; `Q:wasmstate->bool`;
    `MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
     MAYCHANGE [wlocals] ,, MAYCHANGE [wmem]`; `6`] THEN
  ASM_REWRITE_TAC[VA1_PUNCTURE_CALLEE] THEN REPEAT CONJ_TAC THENL
   [(* the callee's final states are not running *)
    X_GEN_TAC `c:wasmstate` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:wasmstate`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[distinctness "wstat"];
    (* the caller's precondition gives the call and f33's entry precondition *)
    X_GEN_TAC `s:wasmstate` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN ASM_SIMP_TAC[MOD_LT] THEN
    REWRITE_TAC[LENGTH] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     (mk_eq(mk_comb(list_mk_comb(`wcall_entry`, [`va1_puncture_mc`; `3`; `1`;
        `CONS (I32 a2) (CONS (I32 a1) (CONS (I32 a0) (rest:wval list)))`; `17`; c5p_decls33]), `s:wasmstate`),
            mk_comb(list_mk_comb(`wcall_entry`, [`va1_puncture_mc`; `3`; `1`;
        `[I32 a2; I32 a1; I32 a0]`; `17`; c5p_decls33]), `s:wasmstate`)))
     SUBST1_TAC THENL
     [REWRITE_TAC[wcall_entry; wtake] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[VA1_C5P_WTAKE_0];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `read wmem s = (m:int64->byte)`)) THEN
    MATCH_MP_TAC VA1_F33_ENTRY THEN ASM_REWRITE_TAC[];
    (* the return state *)
    MAP_EVERY X_GEN_TAC [`s:wasmstate`; `c1:wasmstate`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP VA1_C5P_F6_KEEPS) THEN
    REWRITE_TAC[WCALL_ENTRY_READS] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c1:wasmstate`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`s:wasmstate`; `c1:wasmstate`] VA1_C5P_WRITE_BACK) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[wcall_return] THEN
    ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN ASM_SIMP_TAC[MOD_LT] THEN
    REWRITE_TAC[wdrop; APPEND] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[VA1_C5P_WDROP_0] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[wglobal; READ_COMPONENT_COMPOSE]) THEN
    REWRITE_TAC[wglobal; READ_COMPONENT_COMPOSE] THEN
    CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MAYCHANGE; SEQ_ID; seq; ASSIGNS; assign] THEN MESON_TAC[]]);;

let VA1_CALL33_FROM_WASMC = prove
 (`!fs mc pc a0 a1 a2 (rest:wval list) m r (R:(int64->byte)->bool) (Q:wasmstate->bool).
     fs 33 = (va1_puncture_mc,3,1) /\ pc < 2 EXP 64 /\ wasm_decode mc pc = SOME (Wcall 33,6) /\
     ensures (wasmc fs) (va1_f33_pre a0 a1 a2 m) Q
       (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
        MAYCHANGE [wlocals] ,, MAYCHANGE [wglobal 0] ,, MAYCHANGE [wmem]) /\
     (!c. Q c ==> read wstatus c = WDone /\ read wstack c = [I32 r] /\
              read (wglobal 0) c = I32 (word 16384) /\ R (read wmem c))
     ==> ensures (wasmn fs)
          (\s. read wcode s = mc /\ read wpc s = word pc /\ read wstatus s = WRunning /\
               read wstack s = CONS (I32 a2) (CONS (I32 a1) (CONS (I32 a0) rest)) /\
               read wmemsize s = 4194304 /\ read (wglobal 0) s = I32 (word 16384) /\ read wmem s = m)
          (\s. read wcode s = mc /\ read wpc s = word (pc + 6) /\ read wstatus s = WRunning /\
               read wstack s = CONS (I32 r) rest /\
               read wmemsize s = 4194304 /\ read (wglobal 0) s = I32 (word 16384) /\ R (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wmem])`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VA1_CALL33_WASMN THEN
  EXISTS_TAC `Q:wasmstate->bool` THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC VA1_F33_WFSUM THEN ASM_SIMP_TAC[]);;

let c5p_dec309 = match (snd VA1_TICK_FORWARD_EXEC).(309) with Some th -> th | None -> failwith "c5p: no decode at 309";;
let VA1_TF_CALL33_SITE = prove
 (`!fs a0 a1 a2 (rest:wval list) m r (R:(int64->byte)->bool) (Q:wasmstate->bool).
     fs 33 = (va1_puncture_mc,3,1) /\
     ensures (wasmc fs) (va1_f33_pre a0 a1 a2 m) Q
       (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
        MAYCHANGE [wlocals] ,, MAYCHANGE [wglobal 0] ,, MAYCHANGE [wmem]) /\
     (!c. Q c ==> read wstatus c = WDone /\ read wstack c = [I32 r] /\
              read (wglobal 0) c = I32 (word 16384) /\ R (read wmem c))
     ==> ensures (wasmn fs)
          (\s. read wcode s = va1_tick_forward_mc /\ read wpc s = word 309 /\ read wstatus s = WRunning /\
               read wstack s = CONS (I32 a2) (CONS (I32 a1) (CONS (I32 a0) rest)) /\
               read wmemsize s = 4194304 /\ read (wglobal 0) s = I32 (word 16384) /\ read wmem s = m)
          (\s. read wcode s = va1_tick_forward_mc /\ read wpc s = word 315 /\ read wstatus s = WRunning /\
               read wstack s = CONS (I32 r) rest /\
               read wmemsize s = 4194304 /\ read (wglobal 0) s = I32 (word 16384) /\ R (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wmem])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`fs:num->byte list#num#num`; `va1_tick_forward_mc`; `309`; `a0:int32`; `a1:int32`; `a2:int32`;
    `rest:wval list`; `m:int64->byte`; `r:int32`; `R:(int64->byte)->bool`; `Q:wasmstate->bool`] VA1_CALL33_FROM_WASMC) THEN
  ASM_REWRITE_TAC[c5p_dec309] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[]);;
let VA1_C5P_SITE_SAT = prove
 (`!a0 a1 a2 (rest:wval list) m. ?s.
     read wcode s = va1_tick_forward_mc /\ read wpc s = word 309 /\ read wstatus s = WRunning /\
     read wstack s = CONS (I32 a2) (CONS (I32 a1) (CONS (I32 a0) rest)) /\
     read wmemsize s = 4194304 /\ read (wglobal 0) s = I32 (word 16384) /\ read wmem s = m`,
  REPEAT GEN_TAC THEN
  EXISTS_TAC `write wcode va1_tick_forward_mc (write wpc (word 309) (write wstatus WRunning
     (write wstack (CONS (I32 a2) (CONS (I32 a1) (CONS (I32 a0) rest))) (write wmemsize 4194304
     (write (wglobal 0) (I32 (word 16384)) (write wmem m (ARB:wasmstate)))))))` THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN REWRITE_TAC[]);;
let VA1_C5P_ENSURES_WASMN = prove(`!fs (P:wasmstate->bool) Q C. ensures (wasmc fs) P Q C ==> ensures (wasmn fs) P Q C`, ACCEPT_TAC ENSURES_WASMC_WASMN);;
let VA1_C5P_EVENTUALLY_WASMN = prove(`!fs P s. eventually (wasmc fs) P s ==> eventually (wasmn fs) P s`, ACCEPT_TAC EVENTUALLY_WASMC_WASMN);;
