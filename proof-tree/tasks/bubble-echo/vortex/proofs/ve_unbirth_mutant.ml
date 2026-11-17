(* ========================================================================= *)
(* Vortex Echo v1 semantic control at model level (a REFUTED row): the      *)
(* mutant un-birth ve_pop1_mut forgets the stored rate deta, and does not   *)
(* invert the births. VE_UNBIRTH_MUTANT_REFUTED: the zero births state      *)
(* satisfies the premise ve_log_ok 0, and after one birth at tick 0 (bead 0, *)
(* dz = 0, deta = 1) the mutant backward at tick 1 does not give it back    *)
(* (bead 0's rate stays at word_sub (word 0) (word 1)). The shipped un-birth *)
(* restores every such state: LIFO_BIRTHS_INVERSE in ve_generic.ml.         *)
(* ========================================================================= *)

needs "ve_generic_defs.ml";;
needs "ve_mutant_defs.ml";;
needs "ve_mutant_stmts.ml";;

let VE_BETA_TAC = CONV_TAC(TOP_DEPTH_CONV BETA_CONV);;

let VE_MUT_CLAUSES = prove
 (parse_term ve_spec_VE_MUT_CLAUSES, REWRITE_TAC[ve_push; ve_unb_mut]);;

let VE_MUT_S1 = prove
 (`ve_cnt (ve_push1 0 (0,word 0,word 1,(\j. word 0)) ve_bzero) = 1 /\
   ve_rbirth (ve_slots (ve_push1 0 (0,word 0,word 1,(\j. word 0)) ve_bzero) 0) = 1 /\
   ve_zp (ve_push1 0 (0,word 0,word 1,(\j. word 0)) ve_bzero) 0 = word_sub (word 0) (word 1)`,
  REWRITE_TAC[ve_push1; LET_DEF; LET_END_DEF] THEN VE_BETA_TAC THEN
  REWRITE_TAC[ve_bzero; ve_zq; ve_zp; ve_dq; ve_dp; ve_cnt; ve_slots; ve_rbirth; FST; SND] THEN
  VE_BETA_TAC THEN REWRITE_TAC[ADD_CLAUSES]);;

let VE_ZP_POP1_MUT = prove
 (`!s. ve_zp (ve_pop1_mut s) = ve_zp s`,
  REWRITE_TAC[ve_pop1_mut; LET_DEF; LET_END_DEF] THEN VE_BETA_TAC THEN
  REWRITE_TAC[ve_zp; FST; SND]);;

let VE_UNB_MUT_ONE = REWRITE_RULE[GSYM ONE] (INST [`0`,`n:num`] (SPEC_ALL (CONJUNCT2 ve_unb_mut)));;

let VE_UNBIRTH_MUTANT_REFUTED = prove
 (parse_term ve_spec_VE_UNBIRTH_MUTANT_REFUTED,
  CONJ_TAC THENL
   [REWRITE_TAC[ve_log_ok; ve_free; ve_bzero; ve_cnt; ve_slots; ve_dq; ve_dp; FST; SND; LT] THEN
    VE_BETA_TAC THEN REWRITE_TAC[];
    REWRITE_TAC[ve_births_bwd_mut; ve_births_fwd] THEN VE_BETA_TAC THEN
    REWRITE_TAC[ve_push; VE_MUT_S1; VE_UNB_MUT_ONE] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[VE_MUT_S1; CONJUNCT1 ve_unb_mut] THEN
    DISCH_THEN(MP_TAC o C AP_THM `0` o AP_TERM `ve_zp`) THEN
    REWRITE_TAC[VE_ZP_POP1_MUT; VE_MUT_S1] THEN
    REWRITE_TAC[ve_bzero; ve_zp; FST; SND] THEN VE_BETA_TAC THEN
    CONV_TAC WORD_REDUCE_CONV]);;
