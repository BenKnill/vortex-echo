needs "chain_c3b_pure.ml";;
needs "chain_c5_punct_c.ml";;
(* Vortex chain rung C6a (vortex-chain-20261111-142342 c6a, Claude Opus 5.5, 2026-11-13): the click puncture as one host *)
(* call. Composes C5's VA1_F33_TO_F25 / VA1_F33_EPILOGUE / VA1_F33_ENTRY with C3b's VA1_F25_OK through                 *)
(* WASMC_CALL_ENSURES at f33's `call 25` (pc 1232). New definitions va1_c6a_frame / va1_c6a_mem / va1_c6a_rel           *)
(* (C4's va1_punct_frame / va1_punct_rel in C3b's names). No axioms or cheats.      Stable layer: never edit. *)

let va1_c6a_frame = new_definition
 `va1_c6a_frame (m0:int64->byte) (m:int64->byte) <=>
    !a. a < 4194304 /\ ~(16288 <= a /\ a < 16384) /\ ~(16396 <= a /\ a < 16404) /\ ~(16408 <= a /\ a < 16504) /\
        ~(65536 <= a /\ a < 1114112) /\ ~(1130496 <= a /\ a < 1966080)
        ==> read (bytes8 (word a)) m = read (bytes8 (word a)) m0`;;
let va1_c6a_mem = new_definition
 `va1_c6a_mem (mdl:num->int32) (m:int64->byte) (m':int64->byte) <=>
    read (bytes32 (word 16396)) m' = read (bytes32 (word 16392)) m /\
    read (bytes32 (word 16400)) m' = word 0 /\
    (?tbl. va1_w32s 65536 262144 tbl m' /\ va1_w32s 1138688 2048 (va1_rbinit tbl) m') /\
    va1_w32s 1130496 2048 (\k. word 251658) m' /\
    va1_w32s 1146880 2048 (\k. word 0) m' /\ va1_w32s 1155072 2048 (\k. word 0) m' /\
    va1_w32s 1163264 2048 (\k. word 0) m' /\ va1_w32s 1171456 2048 (va1_zpseed mdl) m' /\
    va1_w32s 1179648 196608 (\k. word 0) m' /\
    va1_c6a_frame m m'`;;
let va1_c6a_rel = new_definition
 `va1_c6a_rel (mdl:num->int32) (gl:num->wval) (m:int64->byte) (gl':num->wval) (m':int64->byte) <=>
    gl' = gl /\ va1_c6a_mem mdl m m'`;;

(* ---- generic: eventually chaining, component keeps ---- *)
let C6A_EV_MONO = prove
 (`!(step:S->S->bool) P Q s. (!s'. P s' ==> Q s') ==> eventually step P s ==> eventually step Q s`,
  MESON_TAC[EVENTUALLY_MONO]);;

let C6A_EV_CHAIN = prove
 (`!(step:S->S->bool) P Q s.
     eventually step P s /\ (!s'. P s' ==> eventually step Q s') ==> eventually step Q s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`step:S->S->bool`; `P:S->bool`; `Q:S->bool`] EVENTUALLY_IMP_EVENTUALLY) THEN
  ASM_MESON_TAC[]);;

let C6A_KEEP_TAC = C3B_KEEPS_TAC C3B_COMP_TAC;;
let C6A_EV_CHAIN' = REWRITE_RULE[IMP_CONJ] C6A_EV_CHAIN;;
let C6A_KEEPS_ON keeps th = MAP_EVERY (fun k -> ASSUME_TAC(MATCH_MP k th)) (CONJUNCTS keeps);;

let C6A_FRAME_F = `MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
                   MAYCHANGE [wlocals] ,, MAYCHANGE [wglobal 0] ,, MAYCHANGE [wmem]`;;
let C6A_FRAME_D = `MAYCHANGE [wmem] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wpc]`;;
let C6A_FRAME_E = `MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
                   MAYCHANGE [wlocal 4] ,, MAYCHANGE [wglobal 0]`;;

let c6a_keeps fr comp = prove
 (mk_forall(`s:wasmstate`, mk_forall(`s':wasmstate`,
    mk_imp(list_mk_comb(fr,[`s:wasmstate`;`s':wasmstate`]),
           mk_eq(mk_comb(mk_comb(`read:(wasmstate,A)component->wasmstate->A`
                    |> inst [type_of comp |> dest_type |> snd |> el 1, `:A`], comp), `s':wasmstate`),
                 mk_comb(mk_comb(`read:(wasmstate,A)component->wasmstate->A`
                    |> inst [type_of comp |> dest_type |> snd |> el 1, `:A`], comp), `s:wasmstate`))))),
  C6A_KEEP_TAC);;

(* the call step D keeps everything but memory, stack and pc *)
let C6A_D_KEEPS = end_itlist CONJ (map (c6a_keeps C6A_FRAME_D)
  [`wcode`; `wstatus`; `wlabels`; `warity`; `wlocal 3`; `wmemsize`; `wglobal 0`]);;
(* the epilogue E keeps memory and memory size *)
let C6A_E_KEEPS = end_itlist CONJ (map (c6a_keeps C6A_FRAME_E) [`wmem`; `wmemsize`]);;
(* the whole frame F keeps memory size *)
let C6A_F_KEEPS = c6a_keeps C6A_FRAME_F `wmemsize`;;

(* F ,, D ,, E stays inside F *)
let C6A_FRAME_SUB = prove
 (`((MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
      MAYCHANGE [wlocals] ,, MAYCHANGE [wglobal 0] ,, MAYCHANGE [wmem]) ,, (MAYCHANGE [wmem] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wpc]) ,, (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
      MAYCHANGE [wlocal 4] ,, MAYCHANGE [wglobal 0])) subsumed
   (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
      MAYCHANGE [wlocals] ,, MAYCHANGE [wglobal 0] ,, MAYCHANGE [wmem])`,
  SUBSUMED_MAYCHANGE_TAC);;
let C6A_SEQ3 = prove
 (`!(A:S->S->bool) (B:S->S->bool) (C:S->S->bool) (x:S) (y:S) (z:S) (w:S). A x y /\ B y z /\ C z w ==> (A ,, B ,, C) x w`,
  REWRITE_TAC[seq] THEN MESON_TAC[]);;
let C6A_FRAME_COMP = prove
 (`!s0 s1 s2 s3:wasmstate.
     (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
      MAYCHANGE [wlocals] ,, MAYCHANGE [wglobal 0] ,, MAYCHANGE [wmem]) s0 s1 /\
     (MAYCHANGE [wmem] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wpc]) s1 s2 /\
     (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
      MAYCHANGE [wlocal 4] ,, MAYCHANGE [wglobal 0]) s2 s3
     ==> (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
      MAYCHANGE [wlocals] ,, MAYCHANGE [wglobal 0] ,, MAYCHANGE [wmem]) s0 s3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC C6A_FRAME_SUB THEN REWRITE_TAC[subsumed] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC C6A_SEQ3 THEN MAP_EVERY EXISTS_TAC [`s1:wasmstate`; `s2:wasmstate`] THEN ASM_REWRITE_TAC[]);;

(* globals: F with global 0 back at its start value keeps all globals *)
let C6A_GLOBALS = prove
 (mk_forall(`s:wasmstate`, mk_forall(`s':wasmstate`,
   mk_imp(mk_conj(list_mk_comb(C6A_FRAME_F,[`s:wasmstate`;`s':wasmstate`]),
                  `read (wglobal 0) s' = read (wglobal 0) (s:wasmstate)`),
          `read wglobals s' = read wglobals (s:wasmstate)`))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
  ASM_CASES_TAC `k = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `wglobal 0`)) (concl th) && is_eq (concl th))) THEN
    REWRITE_TAC[wglobal; READ_COMPONENT_COMPOSE; READ_ELEMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `read (wglobals :> element k) s' = read (wglobals :> element k) (s:wasmstate)` MP_TAC THENL
   [UNDISCH_TAC (list_mk_comb(C6A_FRAME_F,[`s:wasmstate`;`s':wasmstate`])) THEN
    SPEC_TAC(`s':wasmstate`,`s':wasmstate`) THEN SPEC_TAC(`s:wasmstate`,`s:wasmstate`) THEN
    REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
    REPEAT(MATCH_MP_TAC C3B_SEQ_KEEPS THEN CONJ_TAC) THEN
    MATCH_MP_TAC C3B_ASSIGNS_KEEPS THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[wglobal; wlocal; READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE] THEN
    CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
    REWRITE_TAC[element; read; write] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_ELEMENT]]);;

(* ---- memory lemmas ---- *)
let C6A_B32_KEEP = prove
 (`!b (m:int64->byte) m'. (!i. i < 4 ==> read (bytes8 (word (b + i))) m' = read (bytes8 (word (b + i))) m)
     ==> read (bytes32 (word b)) m' = read (bytes32 (word b)) m`,
  REWRITE_TAC[C3B_B8_B32]);;

let C6A_PRE_MEM = prove
 (`!t mdl (m:int64->byte) m1.
     va1_f33_frame m m1 /\ va1_tick t m /\ read (bytes32 (word 16396)) m = word 4294967295 /\ va1_mdl mdl m
     ==> va1_tick t m1 /\ read (bytes32 (word 16396)) m1 = word 4294967295 /\ va1_mdl mdl m1`,
  REWRITE_TAC[va1_f33_frame; va1_tick; va1_mdl] THEN REPEAT STRIP_TAC THENL
   [MP_TAC(SPECL [`16392`; `m:int64->byte`; `m1:int64->byte`] C6A_B32_KEEP);
    MP_TAC(SPECL [`16396`; `m:int64->byte`; `m1:int64->byte`] C6A_B32_KEEP);
    MP_TAC(SPECL [`16640 + 4 * k`; `m:int64->byte`; `m1:int64->byte`] C6A_B32_KEEP)] THEN
  (ANTS_TAC THENL [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC]) THEN
  ASM_SIMP_TAC[]);;

let C6A_W32S_SPLIT = prove
 (`!(m:int64->byte). va1_w32s 1146880 6144 (\k. word 0) m
     ==> va1_w32s 1146880 2048 (\k. word 0) m /\ va1_w32s 1155072 2048 (\k. word 0) m /\
         va1_w32s 1163264 2048 (\k. word 0) m`,
  REWRITE_TAC[va1_w32s] THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `k:num`);
    FIRST_X_ASSUM(MP_TAC o SPEC `k + 2048`);
    FIRST_X_ASSUM(MP_TAC o SPEC `k + 4096`)] THEN
  REWRITE_TAC[ARITH_RULE `1146880 + 4 * (k + 2048) = 1155072 + 4 * k`;
              ARITH_RULE `1146880 + 4 * (k + 4096) = 1163264 + 4 * k`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let C6A_POST_MEM = prove
 (`!t mdl a0 a1 a2 (m:int64->byte) m1 m2.
     va1_tick t m /\ va1_f33_frame m m1 /\
     va1_f25_post t mdl (va1_rd32 65536 m1) a0 a1 a2 m2 /\ va1_f25_frame m1 m2
     ==> va1_c6a_mem mdl m m2 /\
         read (bytes32 (word 16408)) m2 = a0 /\ read (bytes32 (word 16412)) m2 = a1 /\
         read (bytes32 (word 16416)) m2 = a2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_f25_post; va1_tick] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[va1_c6a_mem] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C6A_W32S_SPLIT) THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXISTS_TAC `va1_rd32 65536 m1` THEN ASM_REWRITE_TAC[va1_w32s; va1_rd32] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC C6A_B32_KEEP THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[va1_f25_frame] o
      check (fun th -> can (find_term ((=) `va1_f25_frame`)) (concl th))) THEN ASM_ARITH_TAC;
    REWRITE_TAC[va1_c6a_frame] THEN REPEAT STRIP_TAC THEN
    TRANS_TAC EQ_TRANS `read (bytes8 (word a)) (m1:int64->byte)` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[va1_f25_frame] o
        check (fun th -> can (find_term ((=) `va1_f25_frame`)) (concl th))) THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[va1_f33_frame] o
        check (fun th -> can (find_term ((=) `va1_f33_frame`)) (concl th))) THEN ASM_ARITH_TAC]]);;

(* ---- the call at pc 1232 ---- *)
let C6A_D1232 = match (snd C5_F33_EXEC).(1232) with Some th -> th | None -> failwith "C6A: no decode at 1232";;
let C6A_D25 = rand(rand(concl(CONJUNCT2 VA1_F25_CALLEE)));;

let C6A_F25_KEEPS = let th1 = c6a_keeps C3B_FRAME `wmemsize` and th2 = c6a_keeps C3B_FRAME `wglobals` in
  GEN_ALL(DISCH_ALL(CONJ (UNDISCH(SPEC_ALL th1)) (UNDISCH(SPEC_ALL th2))));;

let C6A_CALL25 = prove
 (`!fs t mdl a0 a1 a2 (m1:int64->byte).
     fs 25 = (va1_f25_mc,3,1) /\
     va1_tick t m1 /\ read (bytes32 (word 16396)) m1 = word 4294967295 /\ va1_mdl mdl m1 /\
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0)
     ==> ensures (wasmc fs)
          (\s. read wcode s = va1_puncture_mc /\ read wpc s = word 1232 /\ read wstatus s = WRunning /\
               read wstack s = [I32 a2; I32 a1; I32 a0] /\ read wmemsize s = 4194304 /\ read wmem s = m1)
          (\s. read wcode s = va1_puncture_mc /\ read wpc s = word 1238 /\ read wstatus s = WRunning /\
               read wstack s = [I32 (word 0)] /\
               va1_f25_post t mdl (va1_rd32 65536 m1) a0 a1 a2 (read wmem s) /\ va1_f25_frame m1 (read wmem s))
          (MAYCHANGE [wmem] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wpc])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a0:int32`; `a1:int32`; `a2:int32`; `t:int32`; `mdl:num->int32`; `va1_rd32 65536 m1`; C6A_D25]
    VA1_F25_OK) THEN
  ASM_REWRITE_TAC[CONJUNCT2 VA1_F25_CALLEE] THEN
  DISCH_THEN(fun lth ->
    let _,largs = strip_comb(concl lth) in
    let pp = el 1 largs and qq = el 2 largs and cc = el 3 largs in
    MATCH_MP_TAC(ISPECL [`fs:num->byte list#num#num`; `25`; `va1_f25_mc`; `3`; `1`; `13`; C6A_D25; pp; qq; cc]
      WASMC_CALL_ENSURES) THEN
    EXISTS_TAC `6` THEN ASM_REWRITE_TAC[lth; VA1_F25_ENTRY; CONJUNCT2 VA1_F25_CALLEE]) THEN
  REPEAT CONJ_TAC THENL
   [(* callee finishes *)
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN MESON_TAC[distinctness "wstat"];
    (* call site and callee entry *)
    X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[LENGTH; ARITH_RULE `3 <= SUC(SUC(SUC 0))`] THEN
    REWRITE_TAC[WCALL_ENTRY_READS; VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[C6A_D1232] THEN CONV_TAC(ONCE_DEPTH_CONV CP_LOCALS_EVAL_CONV) THEN
    REWRITE_TAC[va1_w32s; va1_rd32];
    (* return *)
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

(* ---- pc 1232 -> 1238, memory relative to the entry memory m ---- *)
let C6A_MID = prove
 (`!fs t mdl a0 a1 a2 (m:int64->byte).
     fs 25 = (va1_f25_mc,3,1) /\
     read (bytes32 (word 16396)) m = word 4294967295 /\ va1_tick t m /\ va1_mdl mdl m /\
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0)
     ==> ensures (wasmc fs)
          (\s. read wcode s = va1_puncture_mc /\ read wpc s = word 1232 /\ read wstatus s = WRunning /\
               read wstack s = [I32 a2; I32 a1; I32 a0] /\ read wmemsize s = 4194304 /\
               va1_f33_frame m (read wmem s))
          (\s. read wcode s = va1_puncture_mc /\ read wpc s = word 1238 /\ read wstatus s = WRunning /\
               read wstack s = [I32 (word 0)] /\ va1_c6a_mem mdl m (read wmem s) /\
               read (bytes32 (word 16408)) (read wmem s) = a0 /\ read (bytes32 (word 16412)) (read wmem s) = a1 /\
               read (bytes32 (word 16416)) (read wmem s) = a2)
          (MAYCHANGE [wmem] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wpc])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ensures] THEN X_GEN_TAC `s:wasmstate` THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:int32`; `mdl:num->int32`; `m:int64->byte`; `read wmem s`] C6A_PRE_MEM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `t:int32`; `mdl:num->int32`; `a0:int32`; `a1:int32`; `a2:int32`;
                `read wmem s`] C6A_CALL25) THEN
  ASM_REWRITE_TAC[ensures] THEN DISCH_THEN(MP_TAC o SPEC `s:wasmstate`) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C6A_EV_MONO THEN X_GEN_TAC `s':wasmstate` THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C6A_POST_MEM THEN EXISTS_TAC `t:int32` THEN EXISTS_TAC `read wmem s` THEN ASM_REWRITE_TAC[]);;

(* ---- the whole call, ensures form ---- *)
let VA1_PUNCTURE_OK = prove
 (`!(fs:num->byte list#num#num) (t:int32) (mdl:num->int32) (a0:int32) (a1:int32) (a2:int32) (m:int64->byte).
     fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\
     read (bytes32 (word 16396)) m = word 4294967295 /\ va1_tick t m /\ ~(t = word 0) /\ va1_mdl mdl m /\
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0)
     ==> ensures (wasmc fs) (va1_f33_pre a0 a1 a2 m)
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 0)] /\
               read (wglobal 0) s = I32 (word 16384) /\ read wmemsize s = 4194304 /\
               va1_c6a_mem mdl m (read wmem s) /\
               read (bytes32 (word 16408)) (read wmem s) = a0 /\ read (bytes32 (word 16412)) (read wmem s) = a1 /\
               read (bytes32 (word 16416)) (read wmem s) = a2)
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocals] ,, MAYCHANGE [wglobal 0] ,, MAYCHANGE [wmem])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ensures] THEN X_GEN_TAC `s0:wasmstate` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `a0:int32`; `a1:int32`; `a2:int32`; `m:int64->byte`] VA1_F33_TO_F25) THEN
  ANTS_TAC THENL [RULE_ASSUM_TAC(REWRITE_RULE[va1_tick]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ensures] THEN DISCH_THEN(MP_TAC o SPEC `s0:wasmstate`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP C6A_EV_CHAIN') THEN
  X_GEN_TAC `s1:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `t:int32`; `mdl:num->int32`; `a0:int32`; `a1:int32`; `a2:int32`;
                `m:int64->byte`] C6A_MID) THEN
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

(* ---- the whole call as a host call (C1's va1_hcall, unfolded) ---- *)
let C6A_DECLS33 = rand(rand(concl(CONJUNCT2 VA1_PUNCTURE_CALLEE)));;

let VA1_HCALL_PUNCTURE = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (t:int32) (mdl:num->int32) (a0:int32) (a1:int32) (a2:int32) (m:int64->byte).
     fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\
     read (bytes32 (word 16396)) m = word 4294967295 /\ va1_tick t m /\ ~(t = word 0) /\ va1_mdl mdl m /\
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0) /\
     gl 0 = I32 (word 16384)
     ==> ?e decls.
           wasm_entry va1_puncture_mc = SOME e /\ wasm_decl_vals va1_puncture_mc = SOME decls /\
           !s0. read wmemsize s0 = 4194304 /\ read wglobals s0 = gl /\ read wmem s0 = m
                ==> eventually (wasmc fs)
                      (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 0)] /\
                           read wmemsize s = 4194304 /\
                           va1_c6a_rel mdl gl m (read wglobals s) (read wmem s) /\
                           read (bytes32 (word 16408)) (read wmem s) = a0 /\ read (bytes32 (word 16412)) (read wmem s) = a1 /\
                           read (bytes32 (word 16416)) (read wmem s) = a2)
                      (wcall_entry va1_puncture_mc (LENGTH [I32 a2; I32 a1; I32 a0]) 1 [I32 a2; I32 a1; I32 a0] e decls s0)`,
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
                `m:int64->byte`] VA1_PUNCTURE_OK) THEN
  ASM_REWRITE_TAC[ensures] THEN DISCH_THEN(MP_TAC o SPEC `e0:wasmstate`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C6A_EV_MONO THEN X_GEN_TAC `s:wasmstate` THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[va1_c6a_rel] THEN
  TRANS_TAC EQ_TRANS `read wglobals (e0:wasmstate)` THEN CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC C6A_GLOBALS THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[wglobal; READ_COMPONENT_COMPOSE; READ_ELEMENT]);;

(* ---- operational reading ---- *)
let VA1_PUNCTURE_RUNS = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (t:int32) (mdl:num->int32) (a0:int32) (a1:int32) (a2:int32) (m:int64->byte) (s0:wasmstate).
     fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\
     read (bytes32 (word 16396)) m = word 4294967295 /\ va1_tick t m /\ ~(t = word 0) /\ va1_mdl mdl m /\
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0) /\
     gl 0 = I32 (word 16384) /\
     read wmemsize s0 = 4194304 /\ read wglobals s0 = gl /\ read wmem s0 = m
     ==> (?s. RTC (wasmc fs) (wcall_entry va1_puncture_mc 3 1 [I32 a2; I32 a1; I32 a0] 17
                [I32 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); I64 (word 0)] s0) s /\
              read wstatus s = WDone) /\
         (!s. RTC (wasmc fs) (wcall_entry va1_puncture_mc 3 1 [I32 a2; I32 a1; I32 a0] 17
                [I32 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); I64 (word 0)] s0) s /\
              ~(read wstatus s = WRunning)
              ==> read wstatus s = WDone /\ read wstack s = [I32 (word 0)] /\ read wmemsize s = 4194304 /\
                  va1_c6a_rel mdl gl m (read wglobals s) (read wmem s) /\
                  read (bytes32 (word 16408)) (read wmem s) = a0 /\ read (bytes32 (word 16412)) (read wmem s) = a1 /\
                  read (bytes32 (word 16416)) (read wmem s) = a2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `t:int32`; `mdl:num->int32`; `a0:int32`; `a1:int32`;
                `a2:int32`; `m:int64->byte`] VA1_HCALL_PUNCTURE) THEN
  ASM_REWRITE_TAC[VA1_PUNCTURE_CALLEE; option_INJ] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:num` (X_CHOOSE_THEN `decls:wval list` STRIP_ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    (rhs(concl th) = `e:num` || rhs(concl th) = `decls:wval list`)))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s0:wasmstate`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH [I32 a2; I32 a1; I32 a0] = 3` SUBST1_TAC THENL
   [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP EVENTUALLY_RTC_EXISTS) THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN MESON_TAC[];
    X_GEN_TAC `s:wasmstate` THEN STRIP_TAC THEN
    FIRST_ASSUM(fun ev -> if fst(strip_comb(concl ev)) = `eventually:(wasmstate->wasmstate->bool)->(wasmstate->bool)->wasmstate->bool`
      then MP_TAC(MATCH_MP (SPEC_ALL (MP (ISPECL [`wasmc fs`; rand(rator(concl ev))] EVENTUALLY_RTC_FINAL)
              (prove(mk_forall(`x:wasmstate`, mk_forall(`u:wasmstate`, mk_imp(mk_comb(rand(rator(concl ev)),`x:wasmstate`),
                 `~(wasmc fs x u)`))),
                 REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
                 MATCH_MP_TAC WASMC_FINAL THEN ASM_REWRITE_TAC[distinctness "wstat"])))) ev)
      else NO_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `s:wasmstate`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[WASMC_FINAL]; CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN SIMP_TAC[]]]);;

(* ---- non-vacuity ---- *)
let VA1_C6A_SAT = prove
 (`!(t:int32) (mdl:num->int32) (a0:int32) (a1:int32) (a2:int32).
     ~(t = word 0) /\ ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0)
     ==> ?(fs:num->byte list#num#num) (gl:num->wval) (m:int64->byte) (s0:wasmstate).
           fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\
           read (bytes32 (word 16396)) m = word 4294967295 /\ va1_tick t m /\ va1_mdl mdl m /\
           gl 0 = I32 (word 16384) /\
           read wmemsize s0 = 4194304 /\ read wglobals s0 = gl /\ read wmem s0 = m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a0:int32`; `a1:int32`; `a2:int32`; `t:int32`; `mdl:num->int32`; `\k:num. word 0:int32`] VA1_F25_SAT) THEN
  STRIP_TAC THEN
  EXISTS_TAC `\f:num. if f = 25 then (va1_f25_mc,3,1) else if f = 32 then (va1_f32_mc,2,1) else (va1_f34_mc,3,0)` THEN
  EXISTS_TAC `\k:num. I32 (word 16384)` THEN EXISTS_TAC `read wmem (s:wasmstate)` THEN
  EXISTS_TAC `write wglobals (\k:num. I32 (word 16384)) (s:wasmstate)` THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN ASM_REWRITE_TAC[]);;
