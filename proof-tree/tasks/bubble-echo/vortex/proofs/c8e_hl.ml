(* vortex-chain rung C8e row E4 pure part (c8e_hl), C8e PROVER (Claude Opus 5.5), 2026-11-15; loaded after c8e_defs.ml and c8e_decode.ml on the C8p dp layer. *)
let C8E_SNAP_SURJ = prove
 (`!sg:num->int32. (!w. 487424 <= w ==> sg w = word 0) ==> ?m. va1_snap m = sg`,
  REPEAT STRIP_TAC THEN EXISTS_TAC (mk_comb(c3b_memw, `\v:num. (sg:num->int32) (v - 4096)`)) THEN
  REWRITE_TAC[FUN_EQ_THM; va1_snap] THEN X_GEN_TAC `w:num` THEN COND_CASES_TAC THENL
   [REWRITE_TAC[ARITH_RULE `16384 + 4 * w = 4 * (4096 + w)`] THEN
    W(fun (asl,g) -> MP_TAC(BETA_RULE(ISPECL [`\v:num. (sg:num->int32) (v - 4096)`; `4096 + w`] C3B_MEMW_B32))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;
let C8E_SAT_TAC (s:term) : tactic =
  MP_TAC(SPEC s C8E_SNAP_SURJ) THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[va1_dom; va1_kind; va1_log_ok; va1_sg_clean] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;;
let VA1_DOM_SAT = prove
 (`!k. k < 4 ==> ?m:int64->byte. va1_dom (va1_snap m) /\ va1_kind (va1_snap m) = k`,
  REWRITE_TAC[ARITH_RULE `k < 4 <=> k = 0 \/ k = 1 \/ k = 2 \/ k = 3`] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [C8E_SAT_TAC `\w. if w = 3 then word 4294967295 else if w = 65 then word 1 else (word 0:int32)`;
    C8E_SAT_TAC `\w. if w = 65 then word 1 else (word 0:int32)`;
    C8E_SAT_TAC `\w. if w = 3 then word 4294967295 else if w = 32 \/ w = 33 \/ w = 65 then word 1 else (word 0:int32)`;
    C8E_SAT_TAC `\w. if w = 2 then word 520 else if w = 65 then word 1 else (word 0:int32)`]);;
let C8E_KIND_RANGE = prove
 (`!sg. va1_kind sg = 0 \/ va1_kind sg = 1 \/ va1_kind sg = 2 \/ va1_kind sg = 3 \/ va1_kind sg = 4`,
  GEN_TAC THEN REWRITE_TAC[va1_kind] THEN REPEAT COND_CASES_TAC THEN REWRITE_TAC[ARITH_EQ]);;
let VA1_INV = prove
 (`!(PT:(num->int32)->num->int32) sg. va1_dom sg /\ ~(va1_kind sg = 3) ==> va1_bwd (va1_fwdt PT sg) = sg`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(va1_kind sg = 4)` ASSUME_TAC THENL [ASM_MESON_TAC[va1_dom]; ALL_TAC] THEN
  MP_TAC(SPEC `sg:num->int32` C8E_KIND_RANGE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_MESON_TAC[VA1_INV_K0; VA1_INV_K1; VA1_INV_K2]);;
let VA1_BWD_FWD = prove
 (`!(PT:(num->int32)->num->int32) (sg:num->int32).
     va1_dom sg /\ ~(va1_kind sg = 3) ==> va1_imgt PT (va1_fwdt PT sg) /\ va1_bwd (va1_fwdt PT sg) = sg`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP VA1_INV) THEN
  ASM_REWRITE_TAC[va1_imgt]);;
let VA1_FWD_BWD = prove
 (`!(PT:(num->int32)->num->int32) (sg:num->int32).
     va1_imgt PT sg ==> va1_dom (va1_bwd sg) /\ ~(va1_kind (va1_bwd sg) = 3) /\ va1_fwdt PT (va1_bwd sg) = sg`,
  REWRITE_TAC[va1_imgt]);;
let VA1_FWD_INJ = prove
 (`!(PT:(num->int32)->num->int32) (sg1:num->int32) (sg2:num->int32).
     va1_dom sg1 /\ va1_dom sg2 /\ ~(va1_kind sg1 = 3) /\ ~(va1_kind sg2 = 3) /\
     va1_fwdt PT sg1 = va1_fwdt PT sg2 ==> sg1 = sg2`,
  MESON_TAC[VA1_INV]);;
let VA1_IMG_EXISTS = prove
 (`!(PT:(num->int32)->num->int32) (sg:num->int32).
     va1_imgt PT sg <=> ?sg0. va1_dom sg0 /\ ~(va1_kind sg0 = 3) /\ sg = va1_fwdt PT sg0`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[va1_imgt] THEN STRIP_TAC THEN EXISTS_TAC `va1_bwd sg` THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN ASM_MESON_TAC[VA1_BWD_FWD]]);;
