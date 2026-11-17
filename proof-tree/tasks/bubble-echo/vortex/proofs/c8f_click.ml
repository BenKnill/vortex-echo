let C8F_HP_TAC : tactic =
  REWRITE_TAC[LEFT_ADD_DISTRIB; ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_CASES_TAC `k < 3` THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST1_TAC (DISJ_CASES_THEN2 SUBST1_TAC SUBST1_TAC) o
      MATCH_MP (ARITH_RULE `k < 3 ==> k = 0 \/ k = 1 \/ k = 2`)) THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `~(k = 0) /\ ~(k = 1) /\ ~(k = 2)` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    C8E_USE_TAC `16420` `k - 3` THEN REFL_TAC];;
let C8F_DEC_CLK = prove
 (`!(m:int64->byte) (m':int64->byte) (sg:num->int32) a0 a1 a2.
     va1_snap m = sg /\ 1 <= val (sg 65) /\ val (sg 65) <= 640 /\
     va1_c6a_mem (\k. sg (64 + k)) m m' /\
     read (bytes32 (word 16408)) m' = a0 /\ read (bytes32 (word 16412)) m' = a1 /\ read (bytes32 (word 16416)) m' = a2 /\
     va1_w32s 65536 262144 (va1_ptbl a0 a1 a2 (sg 66)) m' /\ va1_w32s 16420 21 (va1_phdr a0 a1 a2) m'
     ==> va1_snap m' = va1_clk a0 a1 a2 sg`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_c6a_mem; va1_c6a_frame; va1_w32s] THEN STRIP_TAC THEN
  SUBGOAL_THEN `read (bytes32 (word 16392)) m = (sg:num->int32) 2` ASSUME_TAC THENL
   [EXPAND_TAC "sg" THEN REWRITE_TAC[va1_snap] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `!j. j < 262144 ==> (tbl:num->int32) j = va1_ptbl a0 a1 a2 ((sg:num->int32) 66) j` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[va1_clk] THEN MATCH_MP_TAC C8E_SNAP_EQ THEN CONJ_TAC THENL
   [MATCH_MP_TAC C8E_PEEL THEN CONJ_TAC THENL
     [REWRITE_TAC[LEFT_ADD_DISTRIB; ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN C8E_BIG_TAC;
      BETA_TAC] THEN
    MATCH_MP_TAC C8E_PEEL THEN CONJ_TAC THENL [C8E_REG_TAC; BETA_TAC] THEN
    MATCH_MP_TAC C8E_PEEL THEN CONJ_TAC THENL [C8F_HP_TAC; BETA_TAC] THEN
    MATCH_MP_TAC C8E_PEEL THEN CONJ_TAC THENL [C8E_P3_TAC; BETA_TAC] THEN
    GEN_TAC THEN STRIP_TAC THEN EXPAND_TAC "sg" THEN REWRITE_TAC[va1_snap] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC C4_KEEP_W32 THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN C8E_ARITH_TAC;
    C8E_OUT_TAC]);;
let C8F_CLK_HOST = prove
 (`!fs gl (m:int64->byte) a0 a1 a2.
     va1_fs_all fs /\ gl 0 = I32 (word 16384) /\ va1_snap m 3 = word 4294967295 /\ ~(va1_snap m 2 = word 0) /\
     1 <= val (va1_snap m 65) /\ val (va1_snap m 65) <= 640 /\ ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0)
     ==> va1_hcall (wasmc fs) va1_puncture_mc [I32 a2; I32 a1; I32 a0] (word 0)
           (\gl' m'. gl' = gl /\ va1_snap m' = va1_clk a0 a1 a2 (va1_snap m)) gl m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_fs_all] THEN STRIP_TAC THEN
  MP_TAC(SPEC `m:int64->byte` C8E_SNAP_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[va1_hcall] THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `va1_snap (m:int64->byte) 2`; `\k. va1_snap (m:int64->byte) (64 + k)`;
                `a0:int32`; `a1:int32`; `a2:int32`; `m:int64->byte`] VA1_HCALL_PUNCTURE_N) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_ASSUM(MP_TAC o check (c8f_has "va1_pop" o concl)) THEN
    REWRITE_TAC[va1_pop] THEN SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:num` (X_CHOOSE_THEN `decls:wval list` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`e:num`; `decls:wval list`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s0:wasmstate` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s0:wasmstate`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C1_EV_MONO THEN GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[va1_c6a_rel] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C8F_DEC_CLK THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV THENC NUM_REDUCE_CONV)) THEN ASM_REWRITE_TAC[]);;
let C8F_UNP_HOST = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (m:int64->byte).
     va1_fs_all fs /\ 1 <= val (va1_snap m 65) /\ val (va1_snap m 65) <= 640 /\
     ~(va1_snap m 2 = word 0) /\ ~(va1_snap m 2 = word 4294967295) /\ va1_snap m 3 = va1_snap m 2
     ==> va1_hcall (wasmc fs) va1_tick_backward_mc [] (word 1)
           (\gl' m'. gl' = gl /\ va1_snap m' = va1_bwd (va1_snap m)) gl m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_fs_all] THEN STRIP_TAC THEN
  MP_TAC(SPEC `m:int64->byte` C8E_SNAP_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[va1_sg_ps]) THEN
  MP_TAC(ISPECL ([`fs:num->byte list#num#num`; `gl:num->wval`; `va1_snap (m:int64->byte) 2`; `va1_snap (m:int64->byte) 32`;
                 `\k. va1_snap (m:int64->byte) (64 + k)`; `val (va1_snap (m:int64->byte) 65)`; `va1_sg_x (va1_snap (m:int64->byte))`;
                 `\k. va1_snap (m:int64->byte) (6 + k)`; `\k. va1_snap (m:int64->byte) (12288 + k)`] @ c8e_sgl @
                 [`va1_snap (m:int64->byte) 5`; `va1_sg_x (va1_snap (m:int64->byte))`; `m:int64->byte`]) C8E_H2B_RAW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[C8E_MDL1] THEN UNDISCH_TAC `va1_fs_np fs` THEN SIMP_TAC[va1_fs_np]; ALL_TAC] THEN
  DISCH_THEN(C8E_MONO_TAC
    (MATCH_MP_TAC VA1_DEC_UNPUNCT THEN MAP_EVERY EXISTS_TAC [`m:int64->byte`; `va1_snap (m:int64->byte) 32`; `va1_sg_x (va1_snap (m:int64->byte))`] THEN
     ASM_REWRITE_TAC[])));;
let c8f_clk_E = `!w. sg' w = va1_put 278528 208896
        (\w. if w < 2048 then word 251658 else if w < 4096 then va1_rbinit_b (va1_ptbl a0 a1 a2 ((sg:num->int32) 66)) (w - 2048)
             else if w < 10240 then word 0 else if w < 12288 then va1_zpseed_b (\k. sg (64 + k)) (w - 10240) else word 0)
       (va1_put 12288 262144 (va1_ptbl a0 a1 a2 (sg 66))
        (va1_put 6 24 (\k. if k = 0 then a0 else if k = 1 then a1 else if k = 2 then a2 else va1_phdr a0 a1 a2 (k - 3))
         (va1_put 3 2 (\k. if k = 0 then word_add (sg 2) (word 1) else word 0)
          (va1_put_x (3 * val (sg 65)) (ve_fredkin_fwdn (\i. ve_vk (\k. sg (64 + k))) 16 (va1_sg_x sg))
           (va1_put 2 1 (\i. word_add (sg 2) (word 1)) sg))))) w`;;
let VA1_CLICK_PAIR_INV = prove
 (`!(a0:int32) (a1:int32) (a2:int32) (sg:num->int32).
     va1_dom sg /\ va1_kind sg = 0 /\ va1_sg_clean sg /\ ~(word_add (sg 2) (word 1) = word 4294967295)
     ==> va1_bwd (va1_clk a0 a1 a2 (va1_fwd sg)) = sg`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `sg:num->int32` C8F_K0_STEP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[va1_dom]) THEN
  SUBGOAL_THEN `(sg:num->int32) 3 = word 4294967295 /\ ~(word_add (sg 2) (word 1) = word 0) /\ 1 <= val (sg 65) /\ val (sg 65) <= 640`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_CASES_TAC `(sg:num->int32) 3 = word 4294967295` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `va1_kind sg = 0` THEN ASM_REWRITE_TAC[va1_kind] THEN REPEAT COND_CASES_TAC THEN REWRITE_TAC[ARITH_EQ];
      ASM_MESON_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `va1_zpseed_b (\k. va1_fwd sg (64 + k)) = va1_zpseed_b (\k. (sg:num->int32) (64 + k))` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; C8E_ZPSEED_B] THEN GEN_TAC THEN MATCH_MP_TAC C8E_ZPSEED_MDL THEN BETA_TAC THEN
    CONV_TAC NUM_REDUCE_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `va1_fwd sg 66 = (sg:num->int32) 66` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `sg' = va1_clk a0 a1 a2 (va1_fwd sg)` THEN
  SUBGOAL_THEN c8f_clk_E (LABEL_TAC "E") THENL
   [EXPAND_TAC "sg'" THEN REWRITE_TAC[va1_clk] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[va1_fwd; va1_fwdt; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  (SUBGOAL_THEN `(sg':num->int32) 2 = word_add (sg 2) (word 1) /\ sg' 3 = word_add (sg 2) (word 1) /\ sg' 4 = word 0 /\
                sg' 5 = sg 5 /\ sg' 65 = sg 65 /\ sg' 66 = sg 66 /\
                (!k. k < 1024 ==> sg' (64 + k) = sg (64 + k)) /\
                (!k. k < 262144 ==> sg' (12288 + k) = va1_ptbl a0 a1 a2 (sg 66) k) /\
                (!k. k < 2048 ==> sg' (278528 + k) = word 251658 /\ sg' (280576 + k) = va1_rbinit_b (va1_ptbl a0 a1 a2 (sg 66)) k /\
                                  sg' (282624 + k) = word 0 /\ sg' (284672 + k) = word 0 /\ sg' (286720 + k) = word 0 /\
                                  sg' (288768 + k) = va1_zpseed_b (\k. sg (64 + k)) k) /\
                (!w. ~(274432 <= w /\ w < 274432 + 3 * val (sg 65)) /\ ~(276480 <= w /\ w < 276480 + 3 * val (sg 65)) /\
                     ~(2 <= w /\ w < 30) /\ ~(12288 <= w /\ w < 274432) /\ ~(278528 <= w) ==> sg' w = sg w)`
    STRIP_ASSUME_TAC THENL
   [USE_THEN "E" (fun th -> REWRITE_TAC[th]) THEN REPEAT STRIP_TAC THEN C8E_EVAL_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT(COND_CASES_TAC THEN TRY(C8E_CONTRA_TAC THEN NO_TAC)) THEN
    TRY(AP_TERM_TAC THEN C8E_ARITH_TAC); ALL_TAC]) THEN
  (SUBGOAL_THEN `(!w. 487424 <= w ==> (sg':num->int32) w = sg w) /\
                c8e_ag (3 * val ((sg:num->int32) 65)) (va1_sg_x sg') (ve_fredkin_fwdn (\i. ve_vk (\k. sg (64 + k))) 16 (va1_sg_x sg))`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c8e_ag; va1_sg_x] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT STRIP_TAC THEN
    USE_THEN "E" (fun th -> REWRITE_TAC[th]) THEN C8E_EVAL_TAC THEN REWRITE_TAC[va1_sg_x; ADD_SUB2]; ALL_TAC] THEN
  REMOVE_THEN "E" (K ALL_TAC)) THEN
  (SUBGOAL_THEN `va1_bad (\k. (sg':num->int32) (64 + k)) (\k. sg' (12288 + k))
                 ((\k. sg' (278528 + k)),(\k. sg' (280576 + k)),(\k. sg' (282624 + k)),(\k. sg' (284672 + k)),
                  (\k. sg' (286720 + k)),(\k. sg' (288768 + k)),sg' 4) = word 0` ASSUME_TAC THENL
   [MATCH_MP_TAC C8E_BAD0 THEN EXISTS_TAC `\k. (sg:num->int32) (64 + k)` THEN EXISTS_TAC `va1_ptbl a0 a1 a2 ((sg:num->int32) 66)` THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_SIMP_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(word_add ((sg:num->int32) 2) (word 1) = word 0)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  (REWRITE_TAC[va1_bwd; LET_DEF; LET_END_DEF; va1_sg_ps; FST; SND] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[C8E_ADDSUB1; WORD_ADD_0]) THEN
  (ASM_REWRITE_TAC[C8E_ADDSUB1] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[va1_sg_clean] o check (fun th -> concl th = `va1_sg_clean (sg:num->int32)`)) THEN
  SUBGOAL_THEN `c8e_lf (3 * val ((sg:num->int32) 65)) (ve_vk (\k. sg' (64 + k))) (ve_vk (\k. sg (64 + k)))` ASSUME_TAC THENL
   [MATCH_MP_TAC C8E_VK_LF THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `16 + j` o check(fun th -> is_forall(concl th) && can (find_term ((=) `1024`)) (concl th))) THEN
      REWRITE_TAC[ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN MATCH_MP_TAC THEN C8E_ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC]; ALL_TAC] THEN
  FIRST_ASSUM(fun lf -> if C8E_LF_TERM lf then
    MP_TAC(SPECL [`16`; `va1_sg_x sg'`; `ve_fredkin_fwdn (\i. ve_vk (\k. (sg:num->int32) (64 + k))) 16 (va1_sg_x sg)`]
      (MATCH_MP (BETA_RULE(ISPECL [`3 * val ((sg:num->int32) 65)`; `\i:num. ve_vk (\k. (sg':num->int32) (64 + k))`; `\i:num. ve_vk (\k. (sg:num->int32) (64 + k))`] C8E_FREDN_LOC)) (GEN `i:num` lf)))
    else failwith "") THEN
  ASM_REWRITE_TAC[FREDKIN_STEPS_INVERSE] THEN REWRITE_TAC[c8e_ag; va1_sg_x] THEN DISCH_THEN(LABEL_TAC "L" o CONJUNCT2)) THEN
  (REWRITE_TAC[FUN_EQ_THM; va1_put_x; va1_sg_x; C8E_PUT_AP] THEN X_GEN_TAC `w:num` THEN
  COND_CASES_TAC THENL [CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN C8E_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `w - 12288` o check(fun th -> is_forall(concl th) && can (find_term ((=) `262144`)) (concl th))) THEN
    ANTS_TAC THENL [C8E_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `12288 + (w - 12288) = w` SUBST1_TAC THENL [C8E_ARITH_TAC; MESON_TAC[]]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [COND_CASES_TAC THENL [SUBGOAL_THEN `w = 3` SUBST1_TAC THENL [C8E_ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
    COND_CASES_TAC THENL [SUBGOAL_THEN `w = 4` SUBST1_TAC THENL [C8E_ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
    COND_CASES_TAC THENL [SUBGOAL_THEN `w = 5` SUBST1_TAC THENL [C8E_ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `w - 6` o check(fun th -> is_forall(concl th) && can (find_term ((=) `24`)) (concl th))) THEN
    ANTS_TAC THENL [C8E_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `6 + (w - 6) = w` SUBST1_TAC THENL [C8E_ARITH_TAC; MESON_TAC[]]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [USE_THEN "L" (MP_TAC o SPEC `w - 276480`) THEN ANTS_TAC THENL [C8E_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN AP_TERM_TAC THEN C8E_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [USE_THEN "L" (MP_TAC o SPEC `w - 274432`) THEN ANTS_TAC THENL [C8E_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN AP_TERM_TAC THEN C8E_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL [SUBGOAL_THEN `w = 2` SUBST1_TAC THENL [C8E_ARITH_TAC; REWRITE_TAC[]]; ALL_TAC] THEN
  ASM_CASES_TAC `278528 <= w` THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check(fun th -> is_forall(concl th) && can (find_term ((=) `487424`)) (concl th) &&
                                              not (can (find_term ((=) `278528`)) (concl th)))) THEN
    MATCH_MP_TAC(ARITH_RULE `~(278528 <= w /\ w < 278528 + 208896) /\ 278528 <= w ==> 487424 <= w`) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MATCH_MP_TAC o check(fun th -> is_forall(concl th) && can (find_term ((=) `30`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN DISCH_TAC THEN C8E_CONTRA2_TAC));;
let C8F_CLICK_POP = prove
 (`!sg0:num->int32 K a0 a1 a2. sg0 2 = word 0 /\ sg0 3 = word 4294967295 /\ (sg0 32 = word 0 \/ K < val (sg0 32)) /\
     1 <= K /\ K + 520 < 4294967296 /\ 1 <= val (sg0 65) /\ val (sg0 65) <= 640 /\ va1_sg_clean sg0
     ==> (!i. i < K ==> va1_dom (ITER i va1_fwd sg0) /\ va1_kind (ITER i va1_fwd sg0) = 0) /\
         ITER K va1_fwd sg0 2 = word K /\ ITER K va1_fwd sg0 3 = word 4294967295 /\ ITER K va1_fwd sg0 65 = sg0 65 /\
         va1_bwd (va1_clk a0 a1 a2 (ITER K va1_fwd sg0)) = ITER (K - 1) va1_fwd sg0 /\
         (!i. i < 520 ==> va1_dom (ITER i va1_fwd (va1_clk a0 a1 a2 (ITER K va1_fwd sg0))) /\
                          va1_kind (ITER i va1_fwd (va1_clk a0 a1 a2 (ITER K va1_fwd sg0))) = 1) /\
         val (ITER 520 va1_fwd (va1_clk a0 a1 a2 (ITER K va1_fwd sg0)) 2) = K + 520 /\
         ITER 520 va1_fwd (va1_clk a0 a1 a2 (ITER K va1_fwd sg0)) 3 = word K /\
         val (ITER 520 va1_fwd (va1_clk a0 a1 a2 (ITER K va1_fwd sg0)) 65) = val (sg0 65)`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MP_TAC(MATCH_MP C8F_CLICK_FACTS th) THEN MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "A") STRIP_ASSUME_TAC) THEN
  USE_THEN "A" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `val (word K:int32) = K` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `sgc = va1_clk a0 a1 a2 (ITER K va1_fwd (sg0:num->int32))` THEN
  MP_TAC(SPECL [`a0:int32`; `a1:int32`; `a2:int32`; `ITER K va1_fwd (sg0:num->int32)`] C8F_CLK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `sgc:num->int32` C8F_POPSTART) THEN ASM_REWRITE_TAC[] THEN TRY(ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN STRIP_TAC THEN
  MP_TAC(SPEC `sgc:num->int32` C8F_POP_ITER) THEN ASM_REWRITE_TAC[] THEN TRY(ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  DISCH_THEN(LABEL_TAC "P") THEN CONJ_TAC THENL
   [EXPAND_TAC "sgc" THEN
    SUBGOAL_THEN `ITER K va1_fwd (sg0:num->int32) = va1_fwd (ITER (K - 1) va1_fwd sg0)` SUBST1_TAC THENL
     [SUBGOAL_THEN `K = SUC (K - 1)` (fun th -> GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV) [th]) THENL
       [ASM_ARITH_TAC; REWRITE_TAC[ITER]]; ALL_TAC] THEN
    USE_THEN "A" (MP_TAC o SPEC `K - 1`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    MATCH_MP_TAC VA1_CLICK_PAIR_INV THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
    SUBGOAL_THEN `K - 1 + 1 = K` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`K:num`; `4294967295`] C8F_WORD_INJ) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC];
    CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN USE_THEN "P" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      USE_THEN "P" (MP_TAC o SPEC `520`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN SIMP_TAC[] THEN ASM_ARITH_TAC]]);;
let C8F_END_C = prove
 (`!K fs gl (m:int64->byte). va1_snap m 3 = word K /\ val (va1_snap m 2) = K + 520 /\ K + 520 < 4294967296 /\
     val (va1_snap m 65) <= 640
     ==> va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 0) (\gl' m'. gl' = gl /\ m' = m) gl m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `m:int64->byte` C8E_SNAP_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC VA1_POP_HCALL_END THEN
  MAP_EVERY EXISTS_TAC [`va1_snap (m:int64->byte) 2`; `va1_snap (m:int64->byte) 3`; `va1_snap (m:int64->byte) 32`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `val (word K:int32) = K` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[C8F_VAL_ADD; ARITH_RULE `K + 520 < 4294967296 ==> K + 520 < 4294967296`] THEN
  CONJ_TAC THENL [DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;
let C8F_SG0C_TAC : tactic =
  MP_TAC(SPECL [`word 0:int32`; `ap:int32`; `mdl:num->int32`; `N:num`; `x0:(num->int32)#(num->int32)`; `m0:int64->byte`] C8F_START) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `val (word N:int32) = N` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC];;
(* the click film's backward half: from ITER n of the click state back to the start snapshot *)
let C8F_CLICK_BACK = prove
 (`!fs sg0 K n a0 a1 a2 gl (x:int64->byte).
     va1_fs_all fs /\ 1 <= K /\ n <= 520 /\
     (!i. i < K ==> va1_dom (ITER i va1_fwd sg0) /\ va1_kind (ITER i va1_fwd sg0) = 0) /\
     va1_bwd (va1_clk a0 a1 a2 (ITER K va1_fwd sg0)) = ITER (K - 1) va1_fwd sg0 /\
     (!i. i < 520 ==> va1_dom (ITER i va1_fwd (va1_clk a0 a1 a2 (ITER K va1_fwd sg0))) /\
                      va1_kind (ITER i va1_fwd (va1_clk a0 a1 a2 (ITER K va1_fwd sg0))) = 1) /\
     val (va1_clk a0 a1 a2 (ITER K va1_fwd sg0) 2) = K /\ K + 520 < 4294967296 /\
     va1_clk a0 a1 a2 (ITER K va1_fwd sg0) 3 = va1_clk a0 a1 a2 (ITER K va1_fwd sg0) 2 /\
     1 <= val (va1_clk a0 a1 a2 (ITER K va1_fwd sg0) 65) /\ val (va1_clk a0 a1 a2 (ITER K va1_fwd sg0) 65) <= 640 /\
     va1_snap x = ITER n va1_fwd (va1_clk a0 a1 a2 (ITER K va1_fwd sg0))
     ==> va1_hrun (wasmc fs) (REPLICATE (n + K) F) (\gl4 m4. gl4 = gl /\ va1_snap m4 = sg0) gl x`,
  REPEAT GEN_TAC THEN ABBREV_TAC `sgc = va1_clk a0 a1 a2 (ITER K va1_fwd (sg0:num->int32))` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM C8F_REP_APPEND; VA1_HRUN_APPEND] THEN
  MATCH_MP_TAC VA1_HRUN_MONO THEN EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\ va1_snap m' = (sgc:num->int32)` THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`g:num->wval`; `y:int64->byte`] THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `REPLICATE K F = CONS F (REPLICATE (K - 1) F)` SUBST1_TAC THENL
     [SUBGOAL_THEN `K = SUC (K - 1)` (fun th -> GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV) [th]) THENL
       [ASM_ARITH_TAC; REWRITE_TAC[REPLICATE]]; ALL_TAC] THEN
    REWRITE_TAC[VA1_HRUN_CLAUSES] THEN
    MATCH_MP_TAC VA1_HCALL_MONO THEN EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\ va1_snap m' = va1_bwd (va1_snap y)` THEN
    CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`g2:num->wval`; `z:int64->byte`] THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC C8F_BWD_RUN_C THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) && c8f_has "va1_kind" (concl th) &&
        not (c8f_has "va1_clk" (concl th)) && not (free_in `sgc:num->int32` (concl th)))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[ARITH_EQ]];
      MATCH_MP_TAC C8F_UNP_HOST THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC];
    MATCH_MP_TAC C8F_BWD_RUN_C THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) && c8f_has "va1_kind" (concl th) &&
        (c8f_has "va1_clk" (concl th) || free_in `sgc:num->int32` (concl th)))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[ARITH_EQ]]]);;
