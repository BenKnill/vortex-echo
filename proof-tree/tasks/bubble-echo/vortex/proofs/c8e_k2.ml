(* vortex-chain rung C8e row E4 pure part (c8e_k2), C8e PROVER (Claude Opus 5.5), 2026-11-15; loaded after c8e_defs.ml and c8e_decode.ml on the C8p dp layer. *)
let C8E_ZPSEED_MDL = prove
 (`!mdl mdl' k. mdl 2 = mdl' 2 ==> va1_zpseed mdl k = va1_zpseed mdl' k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[va1_zpseed; va1_zpx1; va1_zpx0] THEN ASM_REWRITE_TAC[]);;
let C8E_BAD0 = prove
 (`!mdl mdl' tbl tb ra rb jq jp zq zp nd.
     nd = word 0 /\ mdl 2 = mdl' 2 /\ (!k. k < 262144 ==> tbl k = tb k) /\
     (!k. k < 2048 ==> ra k = word 251658 /\ rb k = va1_rbinit_b tb k /\ jq k = word 0 /\ jp k = word 0 /\
                       zq k = word 0 /\ zp k = va1_zpseed_b mdl' k)
     ==> va1_bad mdl tbl (ra,rb,jq,jp,zq,zp,nd) = word 0`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[va1_bad; FST; SND; WORD_ADD_0] THEN
  SUBGOAL_THEN `nsum (0..2047) (\k. va1_mis mdl tbl (ra,rb,jq,jp,zq,zp) k) = 0` (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC NSUM_EQ_0 THEN REWRITE_TAC[IN_NUMSEG] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[va1_mis; FST; SND] THEN C8E_AGREEN_TAC `2048` [`k:num`] THEN
  REWRITE_TAC[C8E_ZPSEED_B] THEN
  SUBGOAL_THEN `va1_rbinit tbl k = va1_rbinit_b tb k /\ va1_zpseed mdl' k = va1_zpseed mdl k` (fun th -> REWRITE_TAC[th; BITVAL_CLAUSES; ADD_CLAUSES]) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC C8E_RBINIT_LOC THEN CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN C8E_ARITH_TAC;
    MATCH_MP_TAC C8E_ZPSEED_MDL THEN ASM_REWRITE_TAC[]]);;
let c8e_k2_E = `!w. sg' w = va1_put 278528 208896
        (\w. if w < 2048 then word 251658 else if w < 4096 then va1_rbinit_b (PT (sg:num->int32)) (w - 2048)
             else if w < 10240 then word 0 else if w < 12288 then va1_zpseed_b (\k. sg (64 + k)) (w - 10240) else word 0)
       (va1_put 12288 262144 (PT sg)
        (va1_put 6 24 (\k. if k < 3 then sg (33 + k) else va1_phdr (sg 33) (sg 34) (sg 35) (k - 3))
         (va1_put 3 2 (\k. if k = 0 then word_add (sg 2) (word 1) else word 0)
          (va1_put_x (3 * val (sg 65)) (ve_fredkin_fwdn (\i. ve_vk (\k. sg (64 + k))) 16 (va1_sg_x sg))
           (va1_put 2 1 (\i. word_add (sg 2) (word 1)) sg))))) w`;;
let C8E_CONTRA2_TAC : tactic = fun (asl,w) ->
  let simple,comps = c8e_numasms asl in
  let try1 hs = MAP_EVERY MP_TAC hs THEN ARITH_TAC in
  let pairs = List.concat (map (fun a -> map (fun b -> [a;b]) comps) comps) in
  (MATCH_MP_TAC(TAUT `F ==> p`) THEN
   FIRST (try1 simple :: map (fun h -> try1 (h :: simple)) comps @ map (fun hs -> try1 (hs @ simple)) pairs)) (asl,w);;
let VA1_INV_K2 = prove
 (`!(PT:(num->int32)->num->int32) sg. va1_dom sg /\ va1_kind sg = 2 ==> va1_bwd (va1_fwdt PT sg) = sg`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[va1_dom] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(sg:num->int32) 3 = word 4294967295 /\ ~(sg 32 = word 0) /\ word_add (sg 2) (word 1) = sg 32` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `(sg:num->int32) 3 = word 4294967295` THEN
    UNDISCH_TAC `va1_kind sg = 2` THEN ASM_REWRITE_TAC[va1_kind] THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `~(word_add ((sg:num->int32) 2) (word 1) = word 4294967295) /\ va1_sg_clean sg` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `sg' = va1_fwdt PT sg` THEN
  SUBGOAL_THEN c8e_k2_E (LABEL_TAC "E") THENL
   [EXPAND_TAC "sg'" THEN REWRITE_TAC[va1_fwdt; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    ASM_REWRITE_TAC[ARITH_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `(sg':num->int32) 2 = word_add (sg 2) (word 1) /\ sg' 3 = word_add (sg 2) (word 1) /\ sg' 4 = word 0 /\
                sg' 5 = sg 5 /\ sg' 65 = sg 65 /\ sg' 66 = sg 66 /\
                (!k. k < 1024 ==> sg' (64 + k) = sg (64 + k)) /\
                (!k. k < 262144 ==> sg' (12288 + k) = PT sg k) /\
                (!k. k < 2048 ==> sg' (278528 + k) = word 251658 /\ sg' (280576 + k) = va1_rbinit_b (PT sg) k /\
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
   [MATCH_MP_TAC C8E_BAD0 THEN EXISTS_TAC `\k. (sg:num->int32) (64 + k)` THEN EXISTS_TAC `(PT:(num->int32)->num->int32) sg` THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_SIMP_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(word_add ((sg:num->int32) 2) (word 1) = word 0)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  (REWRITE_TAC[va1_bwd; LET_DEF; LET_END_DEF; va1_sg_ps; FST; SND] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[C8E_ADDSUB1; WORD_ADD_0]) THEN
  (FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `word_add ((sg:num->int32) 2) (word 1) = sg 32`)) THEN
  ASM_REWRITE_TAC[C8E_ADDSUB1] THEN
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
