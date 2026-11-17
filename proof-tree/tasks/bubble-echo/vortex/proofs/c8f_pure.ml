(* c8f_pure.ml (vortex-chain C8f, Claude Opus 5.5, 2026-11-15): pure HOL facts about va1_fwd iterates along the films. *)
let C8F_ITER_ALT = prove
 (`!n (f:A->A) x. ITER (SUC n) f x = ITER n f (f x)`,
  REWRITE_TAC[ITER_ALT]);;
let C8F_ITER_ADD = prove
 (`!m n (f:A->A) x. ITER (m + n) f x = ITER n f (ITER m f x)`,
  REWRITE_TAC[ITER_ADD] THEN REWRITE_TAC[ADD_SYM]);;
let C8F_K0_STEP = prove
 (`!sg:num->int32. va1_dom sg /\ va1_kind sg = 0
     ==> va1_fwd sg 2 = word_add (sg 2) (word 1) /\
         (!w. ~(w = 2) /\ ~(274432 <= w /\ w < 278528) ==> va1_fwd sg w = sg w)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val ((sg:num->int32) 65) <= 640` ASSUME_TAC THENL [ASM_MESON_TAC[va1_dom]; ALL_TAC] THEN
  ASM_REWRITE_TAC[va1_fwd; va1_fwdt; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[va1_put_x; C8E_PUT_AP] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN REPEAT(COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN REFL_TAC);;
let C8F_ADD1_NZ = prove
 (`!(t:int32) (q:int32). val t < val q ==> ~(word_add t (word 1) = word 0)`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `q:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN
  REPEAT DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int32->num`) THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `(val (t:int32) + 1) MOD 4294967296 = val t + 1` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ARITH_TAC]);;
let C8F_LOG_EXT = prove
 (`!t di di' nd. va1_log_ok t di nd /\ (!w. w < 196608 ==> di' w = di w) ==> va1_log_ok t di' nd`,
  REWRITE_TAC[va1_log_ok] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `12 * i + 6 < 196608` (fun th -> ASM_SIMP_TAC[th]) THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[]]);;
let C8F_POP_LOG = prove
 (`!mdl hp tbl t p ra rb jq jp di zq zp nd (q:int32).
     va1_log_ok t di nd /\ val t < val q
     ==> va1_log_ok (word_add t (word 1))
           (FST(SND(SND(SND(SND(va1_pop_fwd va1_ck va1_jigk (va1_pop_births mdl hp tbl t p (ra,rb,jq,jp,di,zq,zp,nd))
                                  mdl hp tbl t p (ra,rb,jq,jp,di,zq,zp,nd)))))))
           (SND(SND(SND(SND(SND(SND(SND(va1_pop_fwd va1_ck va1_jigk (va1_pop_births mdl hp tbl t p (ra,rb,jq,jp,di,zq,zp,nd))
                                  mdl hp tbl t p (ra,rb,jq,jp,di,zq,zp,nd)))))))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC VA1_LOG_OK_POP_FWD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC C8F_ADD1_NZ THEN EXISTS_TAC `q:int32` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[va1_pop_births; LET_DEF; LET_END_DEF; FST; SND] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    MATCH_MP_TAC C8E_BORN_TAG THEN UNDISCH_TAC `va1_log_ok t di nd` THEN SIMP_TAC[va1_log_ok]]);;
let C8F_PF_EXISTS_TAC : tactic = fun (asl,w) ->
  let pf = find_term (fun t -> try fst(dest_const(repeat rator t)) = "va1_pop_fwd" && length(snd(strip_comb t)) = 9 with _ -> false) w in
  let sn t = mk_icomb(`SND:A#B->B`, t) in
  let di = mk_icomb(`FST:A#B->A`, sn(sn(sn(sn pf)))) in
  (MATCH_MP_TAC C8F_LOG_EXT THEN EXISTS_TAC di) (asl,w);;
let C8F_K1_STEP = prove
 (`!sg:num->int32. va1_dom sg /\ va1_kind sg = 1
     ==> va1_fwd sg 2 = word_add (sg 2) (word 1) /\ va1_fwd sg 3 = sg 3 /\ va1_fwd sg 65 = sg 65 /\
         va1_log_ok (word_add (sg 2) (word 1)) (\w. va1_fwd sg (290816 + w)) (va1_fwd sg 4)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `va1_log_ok (sg 2) (\w. (sg:num->int32) (290816 + w)) (sg 4) /\ val (sg 2) < val (word_add (sg 3) (word 520))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `va1_dom sg` THEN UNDISCH_TAC `va1_kind sg = 1` THEN REWRITE_TAC[va1_dom] THEN DISCH_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN UNDISCH_TAC `va1_kind sg = 1` THEN REWRITE_TAC[va1_kind] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[va1_fwd; va1_fwdt; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN REWRITE_TAC[va1_put_ps; va1_put_x; C8E_PUT_AP] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  C8F_PF_EXISTS_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[va1_sg_ps] THEN MATCH_MP_TAC C8F_POP_LOG THEN
    EXISTS_TAC `word_add ((sg:num->int32) 3) (word 520)` THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `~(4 <= 290816 + w /\ 290816 + w < 5) /\ (290816 <= 290816 + w /\ 290816 + w < 487424)`
      (fun th -> REWRITE_TAC[th; ADD_SUB2]) THEN
    UNDISCH_TAC `w < 196608` THEN ARITH_TAC]);;
let C8F_K2_STEP = prove
 (`!sg:num->int32. va1_kind sg = 2
     ==> va1_fwd sg 2 = word_add (sg 2) (word 1) /\ va1_fwd sg 3 = word_add (sg 2) (word 1) /\ va1_fwd sg 4 = word 0 /\
         va1_fwd sg 65 = sg 65 /\ (!w. w < 196608 ==> va1_fwd sg (290816 + w) = word 0)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[va1_fwd; va1_fwdt; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN REWRITE_TAC[va1_put_x; C8E_PUT_AP] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `278528 <= 290816 + w /\ 290816 + w < 487424 /\ ~((290816 + w) - 278528 < 2048) /\ ~((290816 + w) - 278528 < 4096) /\
                ~((290816 + w) - 278528 < 10240) /\ ~((290816 + w) - 278528 < 12288)` (fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `w < 196608` THEN ARITH_TAC);;
let C8F_CLK_FACTS = prove
 (`!a0 a1 a2 sg:num->int32.
     va1_clk a0 a1 a2 sg 2 = sg 2 /\ va1_clk a0 a1 a2 sg 3 = sg 2 /\ va1_clk a0 a1 a2 sg 4 = word 0 /\
     va1_clk a0 a1 a2 sg 65 = sg 65 /\ (!w. w < 196608 ==> va1_clk a0 a1 a2 sg (290816 + w) = word 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_clk; C8E_PUT_AP] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `278528 <= 290816 + w /\ 290816 + w < 487424 /\ ~((290816 + w) - 278528 < 2048) /\ ~((290816 + w) - 278528 < 4096) /\
                ~((290816 + w) - 278528 < 10240) /\ ~((290816 + w) - 278528 < 12288)` (fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `w < 196608` THEN ARITH_TAC);;
let C8F_VAL_ADD = prove
 (`!(x:int32) n. val x + n < 4294967296 ==> val (word_add x (word n)) = val x + n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `n MOD 4294967296 = n` SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;
let C8F_KIND_POP = prove
 (`!sg:num->int32. ~(sg 3 = word 4294967295) /\ val (sg 3) + 520 < 4294967296 /\ val (sg 3) <= val (sg 2)
     ==> (val (sg 2) < val (sg 3) + 520 ==> va1_kind sg = 1) /\ (val (sg 3) + 520 <= val (sg 2) ==> va1_kind sg = 3)`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[va1_kind] THEN ASM_SIMP_TAC[C8F_VAL_ADD] THEN
  REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;
let C8F_DOM_POP = prove
 (`!sg:num->int32. 1 <= val (sg 65) /\ val (sg 65) <= 640 /\
     (va1_kind sg = 1 /\ va1_log_ok (sg 2) (\w. sg (290816 + w)) (sg 4) \/ va1_kind sg = 3) ==> va1_dom sg`,
  GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[va1_dom; ARITH_EQ]);;
let C8F_POP_ITER = prove
 (`!sg:num->int32. va1_dom sg /\ va1_kind sg = 1 /\ val (sg 3) + 520 < 4294967296
     ==> !i. val (sg 2) + i <= val (sg 3) + 520
             ==> val (ITER i va1_fwd sg 2) = val (sg 2) + i /\ ITER i va1_fwd sg 3 = sg 3 /\
                 ITER i va1_fwd sg 65 = sg 65 /\ va1_dom (ITER i va1_fwd sg) /\
                 (val (sg 2) + i < val (sg 3) + 520 ==> va1_kind (ITER i va1_fwd sg) = 1) /\
                 (val (sg 2) + i = val (sg 3) + 520 ==> va1_kind (ITER i va1_fwd sg) = 3)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((sg:num->int32) 3 = word 4294967295) /\ val (sg 3) <= val (sg 2) /\ 1 <= val (sg 65) /\ val (sg 65) <= 640`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `va1_dom sg` THEN REWRITE_TAC[va1_dom] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `va1_kind sg = 1` THEN REWRITE_TAC[va1_kind] THEN REPEAT COND_CASES_TAC THEN
    REWRITE_TAC[ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ITER; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPEC `sg:num->int32` C8F_KIND_POP) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `s1 = ITER i va1_fwd (sg:num->int32)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `va1_kind (s1:num->int32) = 1` ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `s1:num->int32` C8F_K1_STEP) THEN ASM_REWRITE_TAC[ITER] THEN STRIP_TAC THEN
  SUBGOAL_THEN `val (va1_fwd (s1:num->int32) 2) = val ((sg:num->int32) 2) + SUC i` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL [`(s1:num->int32) 2`; `1`] C8F_VAL_ADD) THEN ANTS_TAC THENL
     [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC]; ALL_TAC] THEN
  MP_TAC(SPEC `va1_fwd (s1:num->int32)` C8F_KIND_POP) THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC C8F_DOM_POP THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `val ((sg:num->int32) 2) + SUC i < val (sg 3) + 520` THENL
     [DISJ1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;
let C8F_WORD_INJ = prove
 (`!a b. a < 4294967296 /\ b < 4294967296 ==> ((word a:int32) = word b <=> a = b)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT]);;
let C8F_KIND0 = prove
 (`!sg:num->int32 i. sg 3 = word 4294967295 /\ sg 2 = word i /\ i + 1 < 4294967296 /\
     (sg 32 = word 0 \/ ~(sg 32 = word (i + 1))) ==> va1_kind sg = 0 /\ ~(word_add (sg 2) (word 1) = word 0)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `~((word (i + 1):int32) = word 0)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`i + 1`; `0`] C8F_WORD_INJ) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ARITH_TAC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[va1_kind; GSYM WORD_ADD] THEN COND_CASES_TAC THEN ASM_MESON_TAC[]);;
let C8F_NP_ITER = prove
 (`!sg:num->int32 J. va1_dom sg /\ sg 2 = word 0 /\ sg 3 = word 4294967295 /\ J < 4294967296 /\
     (!i. i < J ==> sg 32 = word 0 \/ ~(sg 32 = word (i + 1)))
     ==> !i. i <= J
             ==> ITER i va1_fwd sg 2 = word i /\
                 (!w. ~(w = 2) /\ ~(274432 <= w /\ w < 278528) ==> ITER i va1_fwd sg w = sg w) /\
                 (i < J ==> va1_dom (ITER i va1_fwd sg) /\ va1_kind (ITER i va1_fwd sg) = 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= val ((sg:num->int32) 65) /\ val (sg 65) <= 640` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[va1_dom]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. i <= J ==> ITER i va1_fwd sg 2 = word i /\
                 (!w. ~(w = 2) /\ ~(274432 <= w /\ w < 278528) ==> ITER i va1_fwd (sg:num->int32) w = sg w)` ASSUME_TAC THENL
   [INDUCT_TAC THENL [ASM_REWRITE_TAC[ITER]; ALL_TAC] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `s1 = ITER i va1_fwd (sg:num->int32)` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`s1:num->int32`; `i:num`] C8F_KIND0) THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `~(3 = 2) /\ ~(274432 <= 3 /\ 3 < 278528) /\ ~(32 = 2) /\ ~(274432 <= 32 /\ 32 < 278528)`] THEN
      REPEAT CONJ_TAC THEN (ASM_ARITH_TAC ORELSE (FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC)); ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `va1_dom (s1:num->int32)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[va1_dom; ARITH_EQ] THEN
      ASM_SIMP_TAC[ARITH_RULE `~(65 = 2) /\ ~(274432 <= 65 /\ 65 < 278528)`]; ALL_TAC] THEN
    MP_TAC(SPEC `s1:num->int32` C8F_K0_STEP) THEN ASM_REWRITE_TAC[ITER] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[WORD_ADD; ADD1]; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`ITER i va1_fwd (sg:num->int32)`; `i:num`] C8F_KIND0) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[ARITH_RULE `~(3 = 2) /\ ~(274432 <= 3 /\ 3 < 278528) /\ ~(32 = 2) /\ ~(274432 <= 32 /\ 32 < 278528)`] THEN
    REPEAT CONJ_TAC THEN (ASM_ARITH_TAC ORELSE (FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC)); ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[va1_dom; ARITH_EQ] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(65 = 2) /\ ~(274432 <= 65 /\ 65 < 278528)`]);;
let C8F_W32S_SNAP = prove
 (`!(m:int64->byte) b n f. va1_w32s (16384 + 4 * b) n f m /\ b + n <= 487424 ==> !k. k < n ==> va1_snap m (b + k) = f k`,
  REWRITE_TAC[va1_w32s] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `b + k < 487424` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM C8E_SNAP_W] THEN REWRITE_TAC[ARITH_RULE `16384 + 4 * (b + k) = (16384 + 4 * b) + 4 * k`] THEN
  ASM_SIMP_TAC[]);;
let C8F_REG = fun b n f th ->
  let th1 = CONV_RULE (ONCE_DEPTH_CONV NUM_REDUCE_CONV) (SPECL [`m:int64->byte`; b; n; f] C8F_W32S_SNAP) in
  MP (CONV_RULE (RAND_CONV (ONCE_DEPTH_CONV NUM_REDUCE_CONV)) (REWRITE_RULE[] th1)) th;;
let C8F_REGION_TAC (bs:(term*term) list) : tactic =
  GEN_TAC THEN STRIP_TAC THEN
  EVERY (map (fun (b,hi) ->
    ASM_CASES_TAC (mk_binop `(<):num->num->bool` `w:num` hi) THENL
     [SUBGOAL_THEN (mk_eq(`w:num`, mk_binop `(+):num->num->num` b (mk_binop `(-):num->num->num` `w:num` b))) SUBST1_TAC
      THENL [ASM_ARITH_TAC; FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]; ALL_TAC]) bs) THEN ASM_ARITH_TAC;;
let C8F_START = prove
 (`!t ap mdl N x (m:int64->byte). va1_np_st t ap mdl N x m /\ va1_clean m /\ mdl 1 = word N /\ N <= 640
     ==> va1_snap m 2 = t /\ va1_snap m 3 = word 4294967295 /\ va1_snap m 32 = ap /\ va1_snap m 65 = word N /\
         va1_sg_clean (va1_snap m)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_np_st; va1_clean; va1_tick; va1_pop; va1_mdl; C8E_BS_ALT; FST; SND] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM(MATCH_MP C8E_SNAP_W (ARITH_RULE `2 < 487424`)); GSYM(MATCH_MP C8E_SNAP_W (ARITH_RULE `3 < 487424`));
              GSYM(MATCH_MP C8E_SNAP_W (ARITH_RULE `32 < 487424`)); GSYM(MATCH_MP C8E_SNAP_W (ARITH_RULE `65 < 487424`))] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[va1_sg_clean] THEN
  REWRITE_TAC[GSYM(MATCH_MP C8E_SNAP_W (ARITH_RULE `4 < 487424`))] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(C8F_REG `6` `26` `\k:num. word 0:int32` (ASSUME `va1_w32s 16408 26 (\k. word 0) (m:int64->byte)`)) THEN
  MP_TAC(C8F_REG `12288` `262144` `\k:num. word 0:int32` (ASSUME `va1_w32s 65536 262144 (\k. word 0) (m:int64->byte)`)) THEN
  MP_TAC(C8F_REG `278528` `2048` `\k:num. word 0:int32` (ASSUME `va1_w32s 1130496 2048 (\k. word 0) (m:int64->byte)`)) THEN
  MP_TAC(C8F_REG `280576` `2048` `\k:num. word 0:int32` (ASSUME `va1_w32s 1138688 2048 (\k. word 0) (m:int64->byte)`)) THEN
  MP_TAC(C8F_REG `282624` `2048` `\k:num. word 0:int32` (ASSUME `va1_w32s 1146880 2048 (\k. word 0) (m:int64->byte)`)) THEN
  MP_TAC(C8F_REG `284672` `2048` `\k:num. word 0:int32` (ASSUME `va1_w32s 1155072 2048 (\k. word 0) (m:int64->byte)`)) THEN
  MP_TAC(C8F_REG `286720` `2048` `\k:num. word 0:int32` (ASSUME `va1_w32s 1163264 2048 (\k. word 0) (m:int64->byte)`)) THEN
  MP_TAC(C8F_REG `288768` `2048` `\k:num. word 0:int32` (ASSUME `va1_w32s 1171456 2048 (\k. word 0) (m:int64->byte)`)) THEN
  MP_TAC(C8F_REG `290816` `196608` `\k:num. word 0:int32` (ASSUME `va1_w32s 1179648 196608 (\k. word 0) (m:int64->byte)`)) THEN
  REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    C8F_REGION_TAC [`278528`,`280576`; `280576`,`282624`; `282624`,`284672`; `284672`,`286720`; `286720`,`288768`;
                    `288768`,`290816`; `290816`,`487424`]]);;
let C8F_POPSTART = prove
 (`!sg:num->int32. sg 3 = sg 2 /\ val (sg 2) + 520 < 4294967296 /\ sg 4 = word 0 /\
     (!w. w < 196608 ==> sg (290816 + w) = word 0) /\ 1 <= val (sg 65) /\ val (sg 65) <= 640
     ==> va1_dom sg /\ va1_kind sg = 1`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((sg:num->int32) 3 = word 4294967295)` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
    CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `val ((sg:num->int32) 2) + 520 < 4294967296` THEN
    UNDISCH_TAC `(sg:num->int32) 3 = sg 2` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `sg:num->int32` C8F_KIND_POP) THEN ASM_REWRITE_TAC[LE_REFL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `va1_kind (sg:num->int32) = 1` ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC C8F_DOM_POP THEN ASM_REWRITE_TAC[va1_log_ok; VAL_WORD_0] THEN
  DISJ1_TAC THEN REWRITE_TAC[LT; LE_0; MULT_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[]);;
let C8F_DOM_START = prove
 (`!sg:num->int32. sg 2 = word 0 /\ sg 3 = word 4294967295 /\ 1 <= val (sg 65) /\ val (sg 65) <= 640 /\ va1_sg_clean sg /\
     (va1_kind sg = 2 ==> ~(sg 33 = word 0 /\ sg 34 = word 0 /\ sg 35 = word 0)) ==> va1_dom sg`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[va1_dom] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `va1_kind sg = 2 ==> ~((sg:num->int32) 33 = word 0 /\ sg 34 = word 0 /\ sg 35 = word 0)` THEN
  REWRITE_TAC[va1_kind] THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC WORD_REDUCE_CONV THEN COND_CASES_TAC THEN REWRITE_TAC[ARITH_EQ]);;
let C8F_FRAME_CLEAN = prove
 (`!sg s:num->int32. va1_sg_clean sg /\ (!w. ~(w = 2) /\ ~(274432 <= w /\ w < 278528) ==> s w = sg w) ==> va1_sg_clean s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_sg_clean] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[ARITH_RULE `~(4 = 2) /\ ~(274432 <= 4 /\ 4 < 278528)`];
    REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS `(sg:num->int32) (6 + k)` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ASM_SIMP_TAC[]];
    REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS `(sg:num->int32) (12288 + k)` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ASM_SIMP_TAC[]];
    REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS `(sg:num->int32) w` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ASM_SIMP_TAC[]]]);;
let C8F_AUTO_FACTS = prove
 (`!sg0:num->int32 K. sg0 2 = word 0 /\ sg0 3 = word 4294967295 /\ sg0 32 = word K /\ 1 <= K /\ K + 520 < 4294967296 /\
     1 <= val (sg0 65) /\ val (sg0 65) <= 640 /\ va1_sg_clean sg0 /\ ~(sg0 33 = word 0 /\ sg0 34 = word 0 /\ sg0 35 = word 0)
     ==> (!i. i < K ==> va1_dom (ITER i va1_fwd sg0) /\ ~(va1_kind (ITER i va1_fwd sg0) = 3)) /\
         ITER K va1_fwd sg0 2 = word K /\ ITER K va1_fwd sg0 3 = word K /\ ITER K va1_fwd sg0 4 = word 0 /\
         (!w. w < 196608 ==> ITER K va1_fwd sg0 (290816 + w) = word 0) /\ ITER K va1_fwd sg0 65 = sg0 65`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `va1_dom (sg0:num->int32)` ASSUME_TAC THENL
   [MATCH_MP_TAC C8F_DOM_START THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`sg0:num->int32`; `K - 1`] C8F_NP_ITER) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN DISJ2_TAC THEN
    MP_TAC(SPECL [`K:num`; `i + 1`] C8F_WORD_INJ) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `K - 1`) THEN REWRITE_TAC[LE_REFL; LT_REFL] THEN
  ABBREV_TAC `s = ITER (K - 1) va1_fwd (sg0:num->int32)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:num->int32) 3 = word 4294967295 /\ s 32 = word K /\ s 33 = sg0 33 /\ s 34 = sg0 34 /\ s 35 = sg0 35 /\ s 65 = sg0 65`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_X_ASSUM(fun th -> W(fun (_,w) -> if is_forall(concl th) then
       (TRANS_TAC EQ_TRANS (mk_comb(`sg0:num->int32`, rand(lhs w))) THEN CONJ_TAC THENL
         [MATCH_MP_TAC th THEN CONV_TAC NUM_REDUCE_CONV; ASM_REWRITE_TAC[]]) else failwith "")); ALL_TAC] THEN
  SUBGOAL_THEN `word_add ((s:num->int32) 2) (word 1) = word K` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~((word K:int32) = word 0) /\ ~((word K:int32) = word 4294967295)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`K:num`; `0`] C8F_WORD_INJ); MP_TAC(SPECL [`K:num`; `4294967295`] C8F_WORD_INJ)] THEN
    (ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC]); ALL_TAC] THEN
  SUBGOAL_THEN `va1_kind (s:num->int32) = 2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[va1_kind]; ALL_TAC] THEN
  SUBGOAL_THEN `va1_dom (s:num->int32)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[va1_dom; ARITH_EQ] THEN MATCH_MP_TAC C8F_FRAME_CLEAN THEN EXISTS_TAC `sg0:num->int32` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ITER K va1_fwd (sg0:num->int32) = va1_fwd s` SUBST1_TAC THENL
   [EXPAND_TAC "s" THEN SUBGOAL_THEN `K = SUC (K - 1)` (fun th -> GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV) [th]) THENL
     [ASM_ARITH_TAC; REWRITE_TAC[ITER]]; ALL_TAC] THEN
  MP_TAC(SPEC `s:num->int32` C8F_K2_STEP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_CASES_TAC `i = K - 1` THENL
   [ASM_REWRITE_TAC[ARITH_EQ]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) && can (find_term ((=) `ITER:num->((num->int32)->num->int32)->(num->int32)->num->int32`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[ARITH_EQ]]);;
let C8F_FB = prove
 (`!N (m0:int64->byte) m. va1_film_bytes N m0 m /\ va1_snap m = va1_snap m0 ==> va1_film_bytes_s m0 m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_film_bytes; va1_film_bytes_s] THEN STRIP_TAC THEN
  X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `16384 <= a /\ a < 1966080` THENL
   [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC] THEN
  MATCH_MP_TAC C4_W1_BYTES THEN EXISTS_TAC `16384 + 4 * ((a - 16384) DIV 4)` THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(a - 16384) DIV 4 < 487424` ASSUME_TAC THENL
     [REWRITE_TAC[RDIV_LT_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[C8E_SNAP_W];
    MP_TAC(SPECL [`a - 16384`; `4`] DIVISION) THEN ASM_ARITH_TAC;
    MP_TAC(SPECL [`a - 16384`; `4`] DIVISION) THEN ASM_ARITH_TAC;
    MP_TAC(SPECL [`a - 16384`; `4`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC]);;
let C8F_AUTO_ALL = prove
 (`!sg0:num->int32 K. sg0 2 = word 0 /\ sg0 3 = word 4294967295 /\ sg0 32 = word K /\ 1 <= K /\ K + 520 < 4294967296 /\
     1 <= val (sg0 65) /\ val (sg0 65) <= 640 /\ va1_sg_clean sg0 /\ ~(sg0 33 = word 0 /\ sg0 34 = word 0 /\ sg0 35 = word 0)
     ==> (!i. i < K + 520 ==> va1_dom (ITER i va1_fwd sg0) /\ ~(va1_kind (ITER i va1_fwd sg0) = 3)) /\
         val (ITER (K + 520) va1_fwd sg0 2) = K + 520 /\ ITER (K + 520) va1_fwd sg0 3 = word K /\
         val (ITER (K + 520) va1_fwd sg0 65) = val (sg0 65)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP C8F_AUTO_FACTS) THEN
  ABBREV_TAC `sK = ITER K va1_fwd (sg0:num->int32)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "A") STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  SUBGOAL_THEN `val (word K:int32) = K` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `sK:num->int32` C8F_POPSTART) THEN ASM_REWRITE_TAC[] THEN TRY(ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN STRIP_TAC THEN
  MP_TAC(SPEC `sK:num->int32` C8F_POP_ITER) THEN ASM_REWRITE_TAC[] THEN TRY(ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  DISCH_THEN(LABEL_TAC "P") THEN REWRITE_TAC[C8F_ITER_ADD] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_CASES_TAC `i < K` THENL [USE_THEN "A" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `i = K + (i - K)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[C8F_ITER_ADD] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "P" (MP_TAC o SPEC `i - K`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th] THEN MP_TAC th) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[ARITH_EQ]];
    USE_THEN "P" (MP_TAC o SPEC `520`) THEN REWRITE_TAC[LE_REFL] THEN SIMP_TAC[]]);;
let C8F_CLICK_FACTS = prove
 (`!sg0:num->int32 K. sg0 2 = word 0 /\ sg0 3 = word 4294967295 /\ (sg0 32 = word 0 \/ K < val (sg0 32)) /\
     1 <= K /\ K + 520 < 4294967296 /\ 1 <= val (sg0 65) /\ val (sg0 65) <= 640 /\ va1_sg_clean sg0
     ==> (!i. i < K ==> va1_dom (ITER i va1_fwd sg0) /\ va1_kind (ITER i va1_fwd sg0) = 0) /\
         va1_sg_clean (ITER (K - 1) va1_fwd sg0) /\ ITER (K - 1) va1_fwd sg0 2 = word (K - 1) /\
         ITER K va1_fwd sg0 2 = word K /\ ITER K va1_fwd sg0 3 = word 4294967295 /\ ITER K va1_fwd sg0 65 = sg0 65`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `!i. i < K ==> (sg0:num->int32) 32 = word 0 \/ ~(sg0 32 = word (i + 1))` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISJ2_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SUBGOAL_THEN `(i + 1) MOD 4294967296 = i + 1` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `va1_dom (sg0:num->int32)` ASSUME_TAC THENL
   [MATCH_MP_TAC C8F_DOM_START THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[va1_kind] THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_EQ]; ALL_TAC] THEN
  MP_TAC(SPECL [`sg0:num->int32`; `K:num`] C8F_NP_ITER) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `K:num`) THEN FIRST_ASSUM(MP_TAC o SPEC `K - 1`) THEN REWRITE_TAC[LE_REFL] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) && c8f_has "va1_kind" (concl th))) THEN
    ASM_SIMP_TAC[LT_IMP_LE];
    MATCH_MP_TAC C8F_FRAME_CLEAN THEN EXISTS_TAC `sg0:num->int32` THEN ASM_REWRITE_TAC[];
    TRANS_TAC EQ_TRANS `(sg0:num->int32) 3` THEN CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ASM_REWRITE_TAC[]];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;
let C8F_FWD_HIGH = prove
 (`!sg:num->int32 w. val (sg 65) <= 640 /\ 487424 <= w ==> va1_fwd sg w = sg w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[va1_fwd; va1_fwdt; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[va1_put_ps; va1_put_x; C8E_PUT_AP] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(COND_CASES_TAC THEN TRY(C8E_CONTRA_TAC THEN NO_TAC)) THEN REWRITE_TAC[]);;
