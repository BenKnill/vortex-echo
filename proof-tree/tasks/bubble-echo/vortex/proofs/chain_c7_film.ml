needs "ve_vort.ml";;
needs "ve_tick.ml";;
needs "ve_vk.ml";;
needs "va1_code.ml";;
needs "va1_seq_final2.ml";;
needs "pop_design_defs.ml";;
needs "pop_design_stmts.ml";;
needs "pop_l2_cdrift.ml";;
needs "pop_l3_jdrift.ml";;
needs "pop_l4_drop.ml";;
needs "pop_l1_rimd.ml";;
needs "pop_l1_rim.ml";;
needs "pop_l5_unbirth.ml";;
needs "pop_h1_hol.ml";;
needs "pop_n1_sat.ml";;
needs "pop_q0_calls.ml";;
needs "pop_q1_untick.ml";;
needs "pop_q2_forward.ml";;
needs "pop_r5_jig_defs.ml";;
needs "pop_r5jig_dec.ml";;
needs "pop_r5jig_lem.ml";;
needs "pop_r5_corr_defs.ml";;
needs "pop_r5c_lem.ml";;
needs "pop_r5b_bdec.ml";;
needs "pop_r5bp_lem.ml";;
needs "pop_r5bp_lem2.ml";;
needs "pop_r5bp_lem3.ml";;
needs "pop_r5bp_lem4.ml";;
needs "pop_r5bp_lem5b.ml";;
needs "pop_r5bp_lem6.ml";;
needs "pop_s0_end.ml";;
needs "pop_r5_r4c_final.ml";;
needs "chain_c1_host.ml";;
needs "chain_c3a_defs.ml";;
needs "chain_c3a_f26a.ml";;
needs "chain_c3a_f26b.ml";;
needs "chain_c3a_f26c.ml";;
needs "chain_c3a_seq.ml";;
needs "chain_c3a_fin.ml";;
needs "chain_c2_host_pop.ml";;
needs "chain_c2_chain.ml";;
needs "chain_c1_np.ml";;
needs "chain_c1_frame.ml";;
needs "chain_c4_lem.ml";;
needs "chain_c4_film.ml";;
needs "chain_c3b_dec.ml";;
needs "chain_c7_c3b_defs.ml";;
needs "chain_c7_c3b_l1.ml";;
needs "chain_c7_c3b_pure.ml";;
needs "chain_c5_dec.ml";;
needs "chain_c5_tacs.ml";;
needs "chain_c5_leaves.ml";;
needs "chain_c5_punct_a.ml";;
needs "chain_c5_punct_b.ml";;
needs "chain_c5_punct_c.ml";;
needs "chain_c7_c6a_host.ml";;
needs "chain_c5p_frames.ml";;
needs "chain_c5p_rules.ml";;
needs "chain_c7_c6b_host.ml";;
(* ========================================================================= *)
(* Vortex chain, rung C7 (C7 agent, Claude Opus 5.5, 2026-11-13), layer     *)
(* "film": the whole film with the REAL puncture step, generic in the       *)
(* puncture call. Pure HOL over C1/C2/C3a/C4 (chain_c4_film.ml internals);  *)
(* the puncture enters as a hypothesis about one host call, discharged in   *)
(* chain_c7_host.ml from C6a (click, wasmc) and C6b (auto, wasmn).          *)
(* No stepping; no mk_thm / new_axiom.                                      *)
(* ========================================================================= *)

(* ---- moving host calls to a super-relation of wasmc (wasmn: C5' EVENTUALLY_WASMC_WASMN) ---- *)
let C7_HCALL_TRANSFER = prove
 (`!(st1:wasmstate->wasmstate->bool) (st2:wasmstate->wasmstate->bool).
     (!P s. eventually st1 P s ==> eventually st2 P s)
     ==> !code args r (Q:(num->wval)->(int64->byte)->bool) gl m.
           va1_hcall st1 code args r Q gl m ==> va1_hcall st2 code args r Q gl m`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[va1_hcall] THEN
  ASM_MESON_TAC[]);;

let C7_HRUN_TRANSFER = prove
 (`!(st1:wasmstate->wasmstate->bool) (st2:wasmstate->wasmstate->bool).
     (!P s. eventually st1 P s ==> eventually st2 P s)
     ==> !cs (Q:(num->wval)->(int64->byte)->bool) gl m.
           va1_hrun st1 cs Q gl m ==> va1_hrun st2 cs Q gl m`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[VA1_HRUN_CLAUSES] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VA1_HCALL_MONO THEN
  EXISTS_TAC `va1_hrun (st1:wasmstate->wasmstate->bool) t (Q:(num->wval)->(int64->byte)->bool)` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`st1:wasmstate->wasmstate->bool`; `st2:wasmstate->wasmstate->bool`] C7_HCALL_TRANSFER) THEN
  ASM_MESON_TAC[]);;

let C7_REPLICATE_K = prove
 (`!K (x:A) (l:A list). 1 <= K ==> APPEND (REPLICATE K x) l = APPEND (REPLICATE (K - 1) x) (CONS x l)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `K = (K - 1) + 1` (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) [th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[C4_REPLICATE_ADD; GSYM APPEND_ASSOC; REPLICATE; num_CONV `1`; APPEND]);;

(* ---- after the K-th (puncture) step: C4's core, from the state mm right after the swirl part ---- *)
(* auto: the K-th tick_forward call is the auto puncture, given as one host call under st *)
let C7_AUTO_STEP = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num)
    (x0:(num->int32)#(num->int32)) (K:num) (m0:int64->byte) (m1:int64->byte) (gl2:num->wval) (m2:int64->byte) (n:num).
     va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ 1 <= K /\ K + 520 < 4294967296 /\ n <= 520 /\
     va1_np_st (word 0) (word K) mdl N x0 m0 /\ va1_clean m0 /\
     va1_np_st (word (K - 1)) (word K) mdl N (ITER (K - 1) (va1_swf mdl) x0) m1 /\ va1_np_frame m0 m1 /\
     va1_autopunct_rel mdl N (ITER (K - 1) (va1_swf mdl) x0) gl m1 gl2 m2
     ==> va1_hrun (wasmc fs) (APPEND (REPLICATE n T) (REPLICATE (n + K) F))
           (\gl3 m3. gl3 = gl /\ va1_np_st (word 0) (word K) mdl N x0 m3 /\ va1_clean m3 /\
                     read (bytes32 (word 16404)) m3 = read (bytes32 (word 16404)) m0 /\
                     va1_film_bytes N m0 m3) gl2 m2 /\
         va1_hrun (wasmc fs) (REPLICATE 520 T)
           (\gl3 m3. gl3 = gl /\
              va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 0)
                (\gl4 m4. gl4 = gl3 /\ m4 = m3 /\
                   va1_hrun (wasmc fs) (REPLICATE (520 + K) F)
                     (\gl5 m5. gl5 = gl /\ va1_np_st (word 0) (word K) mdl N x0 m5 /\ va1_clean m5 /\
                        read (bytes32 (word 16404)) m5 = read (bytes32 (word 16404)) m0 /\
                        va1_film_bytes N m0 m5) gl4 m4) gl3 m3) gl2 m2`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  C4_WK_TAC THEN
  SUBGOAL_THEN `va1_clean m1` ASSUME_TAC THENL
   [MATCH_MP_TAC C4_CLEAN_NP THEN EXISTS_TAC `m0:int64->byte` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) && (try fst(dest_const(fst(strip_comb(concl th)))) = "va1_autopunct_rel" with _ -> false))) THEN
  REWRITE_TAC[va1_autopunct_rel] THEN DISCH_THEN(X_CHOOSE_THEN `mm:int64->byte` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `va1_np_st (word K) (word K) mdl N (ITER K (va1_swf mdl) (x0:(num->int32)#(num->int32))) mm` ASSUME_TAC THENL
   [MATCH_MP_TAC C4_NPST_STEP THEN EXISTS_TAC `m1:int64->byte` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `va1_clean mm` ASSUME_TAC THENL
   [MATCH_MP_TAC C4_CLEAN_NP THEN EXISTS_TAC `m1:int64->byte` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[va1_np_frame] o check (fun th -> concl th = `va1_np_frame m0 m1`)) THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[va1_np_frame] o check (fun th -> concl th = `va1_np_frame m1 mm`)) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC C4_CORE_INV THEN EXISTS_TAC `mm:int64->byte` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN C4_HEAD_FIN_TAC;
    MATCH_MP_TAC C4_CORE_END THEN EXISTS_TAC `mm:int64->byte` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN C4_HEAD_FIN_TAC]);;

(* click: the puncture export called once after K no-pop ticks *)
let C7_CLICK_STEP = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (ap:int32)
    (x0:(num->int32)#(num->int32)) (K:num) (m0:int64->byte) (m1:int64->byte) (gl2:num->wval) (m2:int64->byte) (n:num).
     va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ 1 <= K /\ K + 520 < 4294967296 /\ n <= 520 /\
     (ap = word 0 \/ K < val ap) /\ va1_np_st (word 0) ap mdl N x0 m0 /\ va1_clean m0 /\
     va1_np_st (word K) ap mdl N (ITER K (va1_swf mdl) x0) m1 /\ va1_np_frame m0 m1 /\
     va1_punct_rel mdl gl m1 gl2 m2
     ==> va1_hrun (wasmc fs) (APPEND (REPLICATE n T) (REPLICATE (n + K) F))
           (\gl3 m3. gl3 = gl /\ va1_np_st (word 0) ap mdl N x0 m3 /\ va1_clean m3 /\
                     read (bytes32 (word 16404)) m3 = read (bytes32 (word 16404)) m0 /\
                     va1_film_bytes N m0 m3) gl2 m2 /\
         va1_hrun (wasmc fs) (REPLICATE 520 T)
           (\gl3 m3. gl3 = gl /\
              va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 0)
                (\gl4 m4. gl4 = gl3 /\ m4 = m3 /\
                   va1_hrun (wasmc fs) (REPLICATE (520 + K) F)
                     (\gl5 m5. gl5 = gl /\ va1_np_st (word 0) ap mdl N x0 m5 /\ va1_clean m5 /\
                        read (bytes32 (word 16404)) m5 = read (bytes32 (word 16404)) m0 /\
                        va1_film_bytes N m0 m5) gl4 m4) gl3 m3) gl2 m2`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  C4_WK_TAC THEN
  SUBGOAL_THEN `va1_clean m1` ASSUME_TAC THENL
   [MATCH_MP_TAC C4_CLEAN_NP THEN EXISTS_TAC `m0:int64->byte` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[va1_np_frame] o check (fun th -> concl th = `va1_np_frame m0 m1`)) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC C4_CORE_INV THEN EXISTS_TAC `m1:int64->byte` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN C4_HEAD_FIN_TAC;
    MATCH_MP_TAC C4_CORE_END THEN EXISTS_TAC `m1:int64->byte` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN C4_HEAD_FIN_TAC]);;

(* ---- the generic films ---- *)
let c7_qf ap = subst [ap, `ap:int32`]
 `\gl3 m3. gl3 = (gl:num->wval) /\ va1_np_st (word 0) (ap:int32) (mdl:num->int32) (N:num) (x0:(num->int32)#(num->int32)) m3 /\
           va1_clean m3 /\ read (bytes32 (word 16404)) m3 = read (bytes32 (word 16404)) (m0:int64->byte) /\
           va1_film_bytes N m0 m3`;;
let c7_qend st ap = subst [st, `st:wasmstate->wasmstate->bool`; c7_qf ap, `qf:(num->wval)->(int64->byte)->bool`]
 `\gl3 m3. gl3 = (gl:num->wval) /\
    va1_hcall (st:wasmstate->wasmstate->bool) va1_tick_forward_mc [] (word 0)
      (\gl4 m4. gl4 = gl3 /\ m4 = m3 /\ va1_hrun st (REPLICATE (520 + K) F) (qf:(num->wval)->(int64->byte)->bool) gl4 m4) gl3 m3`;;
let c7_np_post k ap = subst [k, `k:num`; ap, `ap:int32`]
 `\gl' m'. gl' = (gl:num->wval) /\ va1_np_st (word k) (ap:int32) (mdl:num->int32) (N:num) (ITER k (va1_swf mdl) (x0:(num->int32)#(num->int32))) m' /\
           va1_np_frame (m0:int64->byte) m'`;;

(* split off the last premise (the puncture hypothesis) under label "H"; transfer thms as "TR"/"TC" *)
let C7_INTRO_TAC (transfer:bool) : tactic =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
     MAP_EVERY ASSUME_TAC (butlast cs) THEN LABEL_TAC "H" (last cs) THEN
     (if transfer then
        let tr = hd cs in LABEL_TAC "TR" (MATCH_MP C7_HRUN_TRANSFER tr) THEN LABEL_TAC "TC" (MATCH_MP C7_HCALL_TRANSFER tr)
      else ALL_TAC)) THEN
  C4_WK_TAC;;
let C7_SUBST_TAC = REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var(lhs(concl th)))));;

let C7_FILM_AUTO_GEN = prove
 (mk_forall(`st:wasmstate->wasmstate->bool`, list_mk_forall([`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`;
    `x0:(num->int32)#(num->int32)`; `K:num`; `m0:int64->byte`],
   mk_imp(`(!P s. eventually (wasmc fs) P s ==> eventually (st:wasmstate->wasmstate->bool) P s) /\
     va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\
     (mdl:num->int32) 1 = word N /\ 1 <= N /\ N <= 640 /\ 1 <= K /\ K + 520 < 4294967296 /\
     va1_np_st (word 0) (word K) mdl N (x0:(num->int32)#(num->int32)) m0 /\ va1_clean m0 /\
     (!m1. va1_np_st (word (K - 1)) (word K) mdl N (ITER (K - 1) (va1_swf mdl) x0) m1 /\ va1_np_frame m0 m1
           ==> va1_hcall st va1_tick_forward_mc [] (word 1)
                 (\gl2 m2. va1_autopunct_rel mdl N (ITER (K - 1) (va1_swf mdl) x0) (gl:num->wval) m1 gl2 m2) gl m1)`,
   mk_conj(
    mk_forall(`n:num`, mk_imp(`n <= 520`,
      list_mk_comb(`va1_hrun (st:wasmstate->wasmstate->bool) (APPEND (REPLICATE K T) (APPEND (REPLICATE n T) (REPLICATE (n + K) F)))`,
                   [c7_qf `word K:int32`; `gl:num->wval`; `m0:int64->byte`]))),
    list_mk_comb(`va1_hrun (st:wasmstate->wasmstate->bool) (APPEND (REPLICATE K T) (REPLICATE 520 T))`,
                 [c7_qend `st:wasmstate->wasmstate->bool` `word K:int32`; `gl:num->wval`; `m0:int64->byte`]))))),
  C7_INTRO_TAC true THEN
  SUBGOAL_THEN (list_mk_comb(`va1_hrun (st:wasmstate->wasmstate->bool) (REPLICATE (K - 1) T)`,
                 [c7_np_post `K - 1` `word K:int32`; `gl:num->wval`; `m0:int64->byte`])) ASSUME_TAC THENL
   [USE_THEN "TR" MATCH_MP_TAC THEN MATCH_MP_TAC C4_NP_FWD THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MATCH_MP C7_REPLICATE_K (ASSUME `1 <= K`)] THEN REWRITE_TAC[VA1_HRUN_APPEND] THEN
  CONJ_TAC THENL [GEN_TAC THEN DISCH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC VA1_HRUN_MONO THEN EXISTS_TAC (c7_np_post `K - 1` `word K:int32`) THEN
  (CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC]) THEN
  MAP_EVERY X_GEN_TAC [`g1:num->wval`; `m1:int64->byte`] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[VA1_HRUN_CLAUSES] THEN
  MATCH_MP_TAC VA1_HCALL_MONO THEN
  EXISTS_TAC `\gl2 m2. va1_autopunct_rel mdl N (ITER (K - 1) (va1_swf mdl) (x0:(num->int32)#(num->int32))) gl m1 gl2 m2` THEN
  (CONJ_TAC THENL [ALL_TAC; USE_THEN "H" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]) THEN
  MAP_EVERY X_GEN_TAC [`g2:num->wval`; `m2:int64->byte`] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_TAC THENL
   [USE_THEN "TR" MATCH_MP_TAC THEN
    MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`; `x0:(num->int32)#(num->int32)`;
      `K:num`; `m0:int64->byte`; `m1:int64->byte`; `g2:num->wval`; `m2:int64->byte`; `n:num`] C7_AUTO_STEP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ACCEPT_TAC o CONJUNCT1)];
    MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`; `x0:(num->int32)#(num->int32)`;
      `K:num`; `m0:int64->byte`; `m1:int64->byte`; `g2:num->wval`; `m2:int64->byte`; `0`] C7_AUTO_STEP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LE_0]; DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
    USE_THEN "TR" (fun tr -> DISCH_THEN(MP_TAC o MATCH_MP tr)) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] VA1_HRUN_MONO) THEN
    MAP_EVERY X_GEN_TAC [`g3:num->wval`; `m3:int64->byte`] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    STRIP_TAC THEN C7_SUBST_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "TC" (fun tc -> FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP tc th))) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] VA1_HCALL_MONO) THEN
    MAP_EVERY X_GEN_TAC [`g4:num->wval`; `m4:int64->byte`] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    STRIP_TAC THEN C7_SUBST_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "TR" (fun tr -> FIRST_X_ASSUM(fun th -> ACCEPT_TAC(MATCH_MP tr th)))]);;

let C7_FILM_CLICK_GEN = prove
 (list_mk_forall([`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`; `ap:int32`;
    `x0:(num->int32)#(num->int32)`; `K:num`; `m0:int64->byte`; `args:wval list`],
   mk_imp(`va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\
     (mdl:num->int32) 1 = word N /\ 1 <= N /\ N <= 640 /\ 1 <= K /\ K + 520 < 4294967296 /\
     ((ap:int32) = word 0 \/ K < val ap) /\ va1_np_st (word 0) ap mdl N (x0:(num->int32)#(num->int32)) m0 /\ va1_clean m0 /\
     (!m1. va1_np_st (word K) ap mdl N (ITER K (va1_swf mdl) x0) m1 /\ va1_np_frame m0 m1
           ==> va1_hcall (wasmc fs) va1_puncture_mc args (word 0)
                 (\gl2 m2. va1_punct_rel mdl (gl:num->wval) m1 gl2 m2) gl m1)`,
   mk_conj(
    mk_forall(`n:num`, mk_imp(`n <= 520`,
      list_mk_comb(`va1_hrun (wasmc fs) (REPLICATE K T)`,
        [mk_abs(`gl1:num->wval`, mk_abs(`m1:int64->byte`,
           list_mk_comb(`va1_hcall (wasmc fs) va1_puncture_mc args (word 0)`,
             [mk_comb(`va1_hrun (wasmc fs) (APPEND (REPLICATE n T) (REPLICATE (n + K) F))`, c7_qf `ap:int32`);
              `gl1:num->wval`; `m1:int64->byte`])));
         `gl:num->wval`; `m0:int64->byte`]))),
    list_mk_comb(`va1_hrun (wasmc fs) (REPLICATE K T)`,
        [mk_abs(`gl1:num->wval`, mk_abs(`m1:int64->byte`,
           list_mk_comb(`va1_hcall (wasmc fs) va1_puncture_mc args (word 0)`,
             [mk_comb(`va1_hrun (wasmc fs) (REPLICATE 520 T)`, c7_qend `wasmc fs` `ap:int32`);
              `gl1:num->wval`; `m1:int64->byte`])));
         `gl:num->wval`; `m0:int64->byte`])))),
  C7_INTRO_TAC false THEN
  CONJ_TAC THENL [GEN_TAC THEN DISCH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC VA1_HRUN_MONO THEN EXISTS_TAC (c7_np_post `K:num` `ap:int32`) THEN
  (CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC C4_NP_FWD THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]) THEN
  MAP_EVERY X_GEN_TAC [`g1:num->wval`; `m1:int64->byte`] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MATCH_MP_TAC VA1_HCALL_MONO THEN
  EXISTS_TAC `\gl2 m2. va1_punct_rel mdl gl (m1:int64->byte) gl2 m2` THEN
  (CONJ_TAC THENL [ALL_TAC; USE_THEN "H" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]) THEN
  MAP_EVERY X_GEN_TAC [`g2:num->wval`; `m2:int64->byte`] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`; `ap:int32`; `x0:(num->int32)#(num->int32)`;
      `K:num`; `m0:int64->byte`; `m1:int64->byte`; `g2:num->wval`; `m2:int64->byte`] C7_CLICK_STEP) THENL
   [DISCH_THEN(MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ACCEPT_TAC o CONJUNCT1)];
    DISCH_THEN(MP_TAC o SPEC `0`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[LE_0]; DISCH_THEN(ACCEPT_TAC o CONJUNCT2)]]);;

(* ---- non-vacuity helper: a start memory of C4's shape whose auto-puncture header word 33 (16516) is 1 ---- *)
let c7_Wh = `\w. if w = 4129 then (word 1:int32) else read (bytes32 (word (4 * w))) (m:int64->byte)`;;
let c7_mh = rhs(concl(REDEPTH_CONV BETA_CONV (mk_comb(c4_memw, c7_Wh))));;
let C7_START_HDR = prove
 (`!(ap:int32) (mdl:num->int32) (N:num) (x0:(num->int32)#(num->int32)).
     N <= 640 ==> ?m0:int64->byte. va1_np_st (word 0) ap mdl N x0 m0 /\ va1_clean m0 /\
                                   read (bytes32 (word 16516)) m0 = word 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ap:int32`; `mdl:num->int32`; `N:num`; `x0:(num->int32)#(num->int32)`] C4_START_SAT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `m:int64->byte` MP_TAC) THEN
  REWRITE_TAC[C4_NPST_W; C4_CLEAN_W] THEN STRIP_TAC THEN
  EXISTS_TAC c7_mh THEN
  SUBGOAL_THEN (subst [c7_mh, `mh:int64->byte`]
    `!a. a < 4194304 /\ ~(16516 <= a /\ a < 16520) ==> read (bytes8 (word a)) mh = read (bytes8 (word a)) (m:int64->byte)`)
   ASSUME_TAC THENL
   [X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC (BETA_RULE (SPEC c7_Wh C4_MEMW_KEEP)) THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(SPECL [`a:num`; `4`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  FIRST [C4_WS_TAC `m:int64->byte`; C4_W_TAC `m:int64->byte`;
         MP_TAC (BETA_RULE (SPECL [c7_Wh; `4129`] C4_MEMW_B32)) THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]]);;

(* ---- the puncture hypotheses of the generic films, from a host-call contract of the puncture (generic in st, REL) ---- *)
let C7_CLICK_H_GEN = prove
 (`!(REL:(int64->byte)->(num->wval)->(int64->byte)->bool) (st:wasmstate->wasmstate->bool) (gl:num->wval)
    (mdl:num->int32) (N:num) (ap:int32) (x0:(num->int32)#(num->int32)) (K:num) (m0:int64->byte) (args:wval list).
     (!m1 gl2 m2. REL m1 gl2 m2 ==> va1_punct_rel mdl gl m1 gl2 m2) /\
     (!t m. read (bytes32 (word 16396)) m = word 4294967295 /\ va1_tick t m /\ ~(t = word 0) /\ va1_mdl mdl m
            ==> va1_hcall st va1_puncture_mc args (word 0) (\gl2 m2. REL m gl2 m2) gl m) /\
     1 <= K /\ K + 520 < 4294967296
     ==> !m1. va1_np_st (word K) ap mdl N (ITER K (va1_swf mdl) x0) m1 /\ va1_np_frame m0 m1
              ==> va1_hcall st va1_puncture_mc args (word 0) (\gl2 m2. va1_punct_rel mdl gl m1 gl2 m2) gl m1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `m1:int64->byte` THEN STRIP_TAC THEN C4_WK_TAC THEN
  MATCH_MP_TAC VA1_HCALL_MONO THEN EXISTS_TAC `\gl2 m2. (REL:(int64->byte)->(num->wval)->(int64->byte)->bool) m1 gl2 m2` THEN
  CONJ_TAC THENL [CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `word K:int32` THEN
  UNDISCH_TAC `va1_np_st (word K) ap mdl N (ITER K (va1_swf mdl) (x0:(num->int32)#(num->int32))) m1` THEN
  REWRITE_TAC[va1_np_st; va1_pop] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let C7_AUTO_H_GEN = prove
 (`!(REL:(int64->byte)->(num->wval)->(int64->byte)->bool) (st:wasmstate->wasmstate->bool) (gl:num->wval)
    (mdl:num->int32) (N:num) (x0:(num->int32)#(num->int32)) (K:num) (m0:int64->byte).
     (!m1 gl2 m2. REL m1 gl2 m2 ==> va1_punct_rel mdl gl m1 gl2 m2) /\
     (!t x m. va1_tick t m /\ va1_pop (word 4294967295) (word_add t (word 1)) m /\ ~(word_add t (word 1) = word 0) /\
              va1_mdl mdl m /\ va1_vab N x m /\
              ~(read (bytes32 (word 16516)) m = word 0 /\ read (bytes32 (word 16520)) m = word 0 /\
                read (bytes32 (word 16524)) m = word 0)
              ==> va1_hcall st va1_tick_forward_mc [] (word 1)
                    (\gl2 m2. ?m1. va1_tick (word_add t (word 1)) m1 /\ va1_vab N (ve_fredkin_fwdn (\i. ve_vk mdl) 16 x) m1 /\
                                   va1_np_frame m m1 /\ REL m1 gl2 m2) gl m) /\
     1 <= K /\ K + 520 < 4294967296 /\
     ~(read (bytes32 (word 16516)) m0 = word 0 /\ read (bytes32 (word 16520)) m0 = word 0 /\
       read (bytes32 (word 16524)) m0 = word 0)
     ==> !m1. va1_np_st (word (K - 1)) (word K) mdl N (ITER (K - 1) (va1_swf mdl) x0) m1 /\ va1_np_frame m0 m1
              ==> va1_hcall st va1_tick_forward_mc [] (word 1)
                    (\gl2 m2. va1_autopunct_rel mdl N (ITER (K - 1) (va1_swf mdl) x0) gl m1 gl2 m2) gl m1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `m1:int64->byte` THEN STRIP_TAC THEN C4_WK_TAC THEN
  SUBGOAL_THEN `word_add (word (K - 1)) (word 1):int32 = word K` ASSUME_TAC THENL
   [REWRITE_TAC[C1_WORD_ADD1] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[va1_np_frame] o check (fun th -> concl th = `va1_np_frame m0 m1`)) THEN
  SUBGOAL_THEN `read (bytes32 (word 16516)) m1 = read (bytes32 (word 16516)) (m0:int64->byte) /\
                read (bytes32 (word 16520)) m1 = read (bytes32 (word 16520)) (m0:int64->byte) /\
                read (bytes32 (word 16524)) m1 = read (bytes32 (word 16524)) (m0:int64->byte)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN C4_W_TAC `m0:int64->byte`; ALL_TAC] THEN
  UNDISCH_TAC `va1_np_st (word (K - 1)) (word K) mdl N (ITER (K - 1) (va1_swf mdl) (x0:(num->int32)#(num->int32))) m1` THEN
  REWRITE_TAC[va1_np_st] THEN STRIP_TAC THEN
  MATCH_MP_TAC VA1_HCALL_MONO THEN
  EXISTS_TAC `\gl2 m2. ?mm. va1_tick (word_add (word (K - 1)) (word 1)) mm /\
                 va1_vab N (ve_fredkin_fwdn (\i. ve_vk mdl) 16 (ITER (K - 1) (va1_swf mdl) (x0:(num->int32)#(num->int32)))) mm /\
                 va1_np_frame m1 mm /\ (REL:(int64->byte)->(num->wval)->(int64->byte)->bool) mm gl2 m2` THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`g2:num->wval`; `m2:int64->byte`] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN `mm:int64->byte` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[va1_autopunct_rel] THEN EXISTS_TAC `mm:int64->byte` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[va1_tick; GSYM va1_swf]) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(snd(dest_imp(snd(strip_forall(concl th)))))))) = "va1_punct_rel" with _ -> false)) THEN
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;
