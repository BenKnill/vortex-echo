(* ========================================================================= *)
(* vortex-chain C8a (Claude Opus 5.5, 2026-11-14), row A2: the isqrt loops   *)
(* of f13 with values. Each of the four sites (pc 571, 1753, 1962, 3007) is  *)
(* 32 rounds of ve_isq_step on (v, r, bit) from the loop head with counter c *)
(* to the exit: (v, r, bit) at the exit = ve_isq 32 X when they were         *)
(* ve_isq (32 - c) X at the head. Every local the loop does not write keeps  *)
(* its (universally quantified) value y_i; the two scratch locals of the     *)
(* loop stay existential.                                                    *)
(* ========================================================================= *)
let C8A_ISQ_SUC = prove(`!c X. SUC c <= 32 ==> ve_isq (32 - c) X = ve_isq_step (ve_isq (32 - SUC c) X)`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `32 - c = SUC (32 - SUC c)` SUBST1_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[ve_isq]]);;
let C8A_ISQ32 = prove(`!X. ve_isq 32 X = ve_isq_step (ve_isq 31 X)`, REWRITE_TAC[num_CONV `32`; ve_isq]);;
let c8a_isq_tr q (vl,rl,bl) =
  [(vl, mk_comb(`FST:int64#int64#int64->int64`, q));
   (rl, mk_comb(`FST:int64#int64->int64`, mk_comb(`SND:int64#int64#int64->int64#int64`, q)));
   (bl, mk_comb(`SND:int64#int64->int64`, mk_comb(`SND:int64#int64#int64->int64#int64`, q)))];;
let c8a_keep (vl,rl,bl) ctr aux =
  map (fun i -> (i, mk_var("y" ^ string_of_int i, if r5b_ity i then `:int32` else `:int64`)))
      (filter (fun i -> not (mem i ([vl; rl; bl; ctr] @ aux))) (0--41));;
let c8a_isq_stmt lp ep ctr vrb aux outer =
  let bp = lp + 2 in
  let keep = c8a_keep vrb ctr aux in
  let pre = r5b_pred bp (Lp lp :: outer) ((ctr, `word c:int32`) :: c8a_isq_tr `ve_isq (32 - c) (X:int64#int64#int64)` vrb @ keep) [] in
  let post = r5b_pred ep outer (c8a_isq_tr `ve_isq 32 (X:int64#int64#int64)` vrb @ keep) [] in
  let e = r5b_ens pre post in
  let vs = subtract (frees e) [`c:num`] in
  mk_forall(`c:num`, mk_imp(`1 <= c /\ c <= 32`, list_mk_forall(vs, e)));;
let C8A_ISQ_CLOSE eqths : tactic =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[injectivity "wval"; R5B_EX_EQ] THEN
  REWRITE_TAC eqths THEN REWRITE_TAC[ve_isq_step] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0; WORD_SUB_0] THEN
  CONV_TAC(DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV)) THEN ASM_REWRITE_TAC[injectivity "wval"; R5B_EX_EQ];;
let C8A_ISQ_BRANCH lp ep ctr vrb aux outer : tactic = fun (asl,w) ->
  let bp = lp + 2 in
  let keep = c8a_keep vrb ctr aux in
  (ENSURES_SEQUENCE_TAC (mk_small_numeral bp)
     (r5b_rest (r5b_pred bp (Lp lp :: outer) ((ctr, `word c:int32`) :: c8a_isq_tr `ve_isq (32 - c) (X:int64#int64#int64)` vrb @ keep) [])) THEN
   CONJ_TAC THENL
    [MP_TAC(SPECL [`c:num`; `X:int64#int64#int64`] C8A_ISQ_SUC) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
     R5B_INIT_TAC THEN R5B_RUN1 R5B_EXEC [ep; bp] THEN
     FIRST_X_ASSUM(fun th -> if is_eq(concl th) && can (find_term ((=) `ve_isq_step`)) (concl th) then C8A_ISQ_CLOSE [th] else failwith "");
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && is_forall(rand(concl th)))) THEN
     ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN MATCH_ACCEPT_TAC]]) (asl,w);;
let C8A_ISQ_TAC lp ep ctr vrb aux outer : tactic =
  INDUCT_TAC THENL [ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC(SPEC `c:num` R5B_DEC1) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC)] THEN
  ASM_CASES_TAC `c = 0` THENL
   [R5B_INIT_TAC THEN R5B_RUN1 R5B_EXEC [ep; lp + 2] THEN C8A_ISQ_CLOSE [C8A_ISQ32];
    C8A_ISQ_BRANCH lp ep ctr vrb aux outer];;
let C8A_ISQV1 = prove(c8a_isq_stmt 571 627 13 (20,30,16) [31;15] r5b_L1B,
  C8A_ISQ_TAC 571 627 13 (20,30,16) [31;15] r5b_L1B);;
let C8A_ISQV2 = prove(c8a_isq_stmt 1753 1809 13 (31,20,16) [34;15] r5b_L1B,
  C8A_ISQ_TAC 1753 1809 13 (31,20,16) [34;15] r5b_L1B);;
let C8A_ISQV3 = prove(c8a_isq_stmt 1962 2018 13 (34,31,16) [36;15] r5b_L1B,
  C8A_ISQ_TAC 1962 2018 13 (34,31,16) [36;15] r5b_L1B);;
let C8A_ISQV4 = prove(c8a_isq_stmt 3007 3063 0 (31,20,16) [30;13] r5b_L2B,
  C8A_ISQ_TAC 3007 3063 0 (31,20,16) [30;13] r5b_L2B);;
