(* vortex-chain C8a (Claude Opus 5.5, 2026-11-14), row A4 support: pure lemmas on the folds *)
let C8A_REC1_W7 = prove(`!mdl hp tbl t rb zq zp k. va1_b1_rec mdl hp tbl t rb zq zp k 7 = word k`, C8A_REC_TAC va1_b1_rec);;
let C8A_FOLD1_PUSH = prove(
 `!mdl hp tbl t rb nd di zq zp k. k <= 2048 ==>
    FST (SND (va1_fold1 mdl hp tbl t rb nd k ([],zq,zp))) =
      FST (SND (va1_push (FST (va1_fold1 mdl hp tbl t rb nd k ([],zq,zp))) (di,zq,zp,nd))) /\
    SND (SND (va1_fold1 mdl hp tbl t rb nd k ([],zq,zp))) =
      FST (SND (SND (va1_push (FST (va1_fold1 mdl hp tbl t rb nd k ([],zq,zp))) (di,zq,zp,nd))))`,
  REPEAT GEN_TAC THEN SPEC_TAC(`k:num`,`k:num`) THEN
  INDUCT_TAC THENL [REWRITE_TAC[va1_fold1; va1_push]; ALL_TAC] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[va1_fold1] THEN
  SPEC_TAC(`va1_fold1 mdl hp tbl t rb nd k ([],zq,zp)`, `s:(num->int32)list#(num->int32)#(num->int32)`) THEN
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[va1_step1] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[R5B_PUSH_SNOC; R5B_PUSH1_ND; C8A_REC1_W7] THEN
  SUBGOAL_THEN `val (word k:int32) = k /\ k MOD 2048 = k /\ k < 65536` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;
let C8A_FOLD1_CAP = prove(
 `!mdl hp tbl t rb nd k st j. 16384 <= val nd + LENGTH (FST (va1_fold1 mdl hp tbl t rb nd k st))
    ==> va1_fold1 mdl hp tbl t rb nd (k + j) st = va1_fold1 mdl hp tbl t rb nd k st`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`j:num`,`j:num`) THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; va1_fold1; va1_step1]);;
let C8A_FOLD2_CAP = prove(
 `!mdl hp tbl t rb nd k L j. 16384 <= val nd + LENGTH (va1_fold2 mdl hp tbl t rb nd k L)
    ==> va1_fold2 mdl hp tbl t rb nd (k + j) L = va1_fold2 mdl hp tbl t rb nd k L`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`j:num`,`j:num`) THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; va1_fold2; va1_step2]);;
let C8A_FOLD3_CAP = prove(
 `!mdl hp tbl t ra rb nd k L j. 16384 <= val nd + LENGTH (va1_fold3 mdl hp tbl t ra rb nd k L)
    ==> va1_fold3 mdl hp tbl t ra rb nd (k + j) L = va1_fold3 mdl hp tbl t ra rb nd k L`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`j:num`,`j:num`) THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; va1_fold3; va1_step3]);;
