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
(* ========================================================================= *)
(* Vortex chain, rung C4, layer 2 of 2 (C4 agent, Claude Opus 5.5,          *)
(* 2026-11-13). Spec chain_c4_final.spec. The whole film: K (click) or     *)
(* K - 1 (auto) no-pop forward calls (C1), the abstract puncture step, the  *)
(* pop forward and back (C2), the un-puncture call (C3a) and the no-pop     *)
(* backward calls to tick 0 (C1), with the byte frame carried through.      *)
(* Pure HOL; no stepping; no mk_thm / new_axiom.                            *)
(* ========================================================================= *)

let C4_REPLICATE_ADD = prove
 (`!n k (x:A). REPLICATE (n + k) x = APPEND (REPLICATE n x) (REPLICATE k x)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; APPEND; ADD_CLAUSES]);;
let C4_REPLICATE_SUC = prove
 (`!k (x:A). 1 <= k ==> REPLICATE k x = CONS x (REPLICATE (k - 1) x)`,
  INDUCT_TAC THEN REWRITE_TAC[REPLICATE; SUC_SUB1] THEN ARITH_TAC);;
let C4_WK = prove
 (`!K. 1 <= K /\ K + 520 < 4294967296
       ==> val(word K:int32) = K /\ ~(word K:int32 = word 4294967295) /\ ~(word K:int32 = word 0)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word K:int32) = K` ASSUME_TAC THENL
   [MATCH_MP_TAC C2_VAL_WORD_LT THEN ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  CONJ_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN
  ASM_REWRITE_TAC[VAL_WORD_0; VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;
let C4_AP_WEAK = prove
 (`!(ap:int32) K. (ap = word 0 \/ K < val ap) ==> (ap = word 0 \/ K - 1 < val ap)`,
  REPEAT GEN_TAC THEN DISCH_THEN DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN ASM_ARITH_TAC);;
let C4_UF_STEP : tactic =
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         MATCH_MP_TAC C4_UF_NP THEN FIRST_ASSUM ACCEPT_TAC; MATCH_MP_TAC C4_UF_PUNCT THEN FIRST_ASSUM ACCEPT_TAC;
         MATCH_MP_TAC C4_UF_POP THEN FIRST_ASSUM ACCEPT_TAC; MATCH_MP_TAC C4_UF_UNP THEN FIRST_ASSUM ACCEPT_TAC];;
let rec C4_UF_PATH (ms:term list) : tactic =
  match List.rev ms with
    [] -> C4_UF_STEP
  | last::revrest -> MATCH_MP_TAC C4_UF_TRANS THEN EXISTS_TAC last THEN
                     CONJ_TAC THENL [C4_UF_PATH (List.rev revrest); C4_UF_STEP];;
let C4_WK_TAC = MP_TAC(SPEC `K:num` C4_WK) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC;;

(* the post every film theorem ends with *)
let c4_qf = `\gl3 m3. gl3 = (gl:num->wval) /\ va1_np_st (word 0) (ap:int32) (mdl:num->int32) (N:num) (x0:(num->int32)#(num->int32)) m3 /\ va1_clean m3 /\
               read (bytes32 (word 16404)) m3 = read (bytes32 (word 16404)) (m0:int64->byte) /\
               va1_film_bytes N m0 m3`;;
let c4_s0 = `((\k. word 251658), va1_rbinit (tbl:num->int32), (\k. word 0), (\k. word 0), (\k. word 0), (\k. word 0),
              va1_zpseed (mdl:num->int32), word 0):(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32`;;
let c4_hp = `\k. read (bytes32 (word (16408 + 4 * k))) (m2:int64->byte)`;;

(* ---- the state right after the puncture ---- *)
let C4_AT_PUNCT = prove
 (`!(mdl:num->int32) N ap (x:(num->int32)#(num->int32)) K (gl1:num->wval) (m1:int64->byte) (gl2:num->wval) (m2:int64->byte).
     N <= 640 /\ va1_np_st (word K) ap mdl N x m1 /\ va1_clean m1 /\ va1_punct_rel mdl gl1 m1 gl2 m2
     ==> gl2 = gl1 /\ va1_punct_frame m1 m2 /\
         read (bytes32 (word 16404)) m2 = read (bytes32 (word 16404)) m1 /\
         ?tbl. va1_st (word K) (word K) ap mdl N x (\k. read (bytes32 (word (16408 + 4 * k))) (m2:int64->byte)) tbl ((\k. word 251658), va1_rbinit (tbl:num->int32), (\k. word 0), (\k. word 0), (\k. word 0), (\k. word 0), va1_zpseed (mdl:num->int32), word 0) m2 /\
               read (bytes32 (word 16504)) m2 = word 0 /\ read (bytes32 (word 16508)) m2 = word 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C4_NPST_W; C4_CLEAN_W; va1_punct_rel] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `read (bytes32 (word 16504)) (m1:int64->byte) = word 0 /\ read (bytes32 (word 16508)) m1 = word 0`
   STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `va1_w32s 16408 26 (\k. word 0) (m1:int64->byte)`)) THEN
    REWRITE_TAC[va1_w32s] THEN DISCH_THEN(fun th -> MP_TAC(SPEC `24` th) THEN MP_TAC(SPEC `25` th)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[va1_punct_frame] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "va1_punct_frame" with _ -> false)) THEN
  CONJ_TAC THENL [C4_W_TAC `m1:int64->byte`; ALL_TAC] THEN
  EXISTS_TAC `tbl:num->int32` THEN
  REWRITE_TAC[va1_st; va1_tick; va1_pop; C4_MDL_W32S; C4_VAB_W32S; va1_bs; FST; SND] THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; REWRITE_TAC[va1_w32s] THEN NO_TAC; ASM_REWRITE_TAC[] THEN NO_TAC;
         C4_WS_TAC `m1:int64->byte`; C4_W_TAC `m1:int64->byte`]);;

let C4_CLEAN_OF_UNP = prove
 (`!t p ap (mdl:num->int32) N (x:(num->int32)#(num->int32)) (hp:num->int32) (m:int64->byte).
     va1_st t p ap mdl N x (\k. if k < 24 then word 0 else hp k) (\k. word 0)
            ((\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),word 0) m /\
     hp 24 = word 0 /\ hp 25 = word 0
     ==> va1_clean m`,
  REWRITE_TAC[va1_st; va1_clean; va1_bs; FST; SND] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `va1_w32s 16408 26 (\k. if k < 24 then word 0 else (hp:num->int32) k) m` THEN
  REWRITE_TAC[va1_w32s] THEN DISCH_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `k < 24` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `k = 24 \/ k = 25` (DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]);;

let C4_ST_NP = prove
 (`!t ap (mdl:num->int32) N (x:(num->int32)#(num->int32)) (hp:num->int32) (tbl:num->int32)
    (S:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32) (m:int64->byte).
     va1_st t (word 4294967295) ap mdl N x hp tbl S m ==> va1_np_st t ap mdl N x m`,
  REWRITE_TAC[FORALL_PAIR_THM; va1_st; va1_np_st] THEN MESON_TAC[]);;

(* ---- the tail: the un-puncture call, then K - 1 no-pop backward calls to tick 0 ---- *)
let C4_TAIL = prove
 ((mk_forall(`fs:num->byte list#num#num`, list_mk_forall([`gl:num->wval`; `mdl:num->int32`; `N:num`; `ap:int32`;
     `x0:(num->int32)#(num->int32)`; `K:num`; `m0:int64->byte`; `hp:num->int32`; `tbl:num->int32`; `m:int64->byte`],
   mk_imp(list_mk_conj [`va1_fs_np fs /\ fs 26 = (va1_f26_mc,0,1) /\ (mdl:num->int32) 1 = word N /\ 1 <= N /\ N <= 640 /\
                          1 <= K /\ K + 520 < 4294967296 /\ ((ap:int32) = word 0 \/ K - 1 < val (ap:int32))`;
                         `va1_np_st (word 0) ap mdl N x0 m0 /\ va1_clean m0`;
                         `va1_st (word K) (word K) ap mdl N (ITER K (va1_swf mdl) x0) hp tbl ((\k. word 251658), va1_rbinit (tbl:num->int32), (\k. word 0), (\k. word 0), (\k. word 0), (\k. word 0), va1_zpseed (mdl:num->int32), word 0) m`;
                         `(hp:num->int32) 24 = word 0 /\ (hp:num->int32) 25 = word 0`;
                         `read (bytes32 (word 16404)) m = read (bytes32 (word 16404)) m0`;
                         c4_ufc `m0:int64->byte` `m:int64->byte`],
          `va1_hrun (wasmc fs) (REPLICATE K F) (\gl3 m3. gl3 = (gl:num->wval) /\ va1_np_st (word 0) (ap:int32) (mdl:num->int32) (N:num) (x0:(num->int32)#(num->int32)) m3 /\ va1_clean m3 /\ read (bytes32 (word 16404)) m3 = read (bytes32 (word 16404)) (m0:int64->byte) /\ va1_film_bytes N m0 m3) gl m`)))),
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  C4_WK_TAC THEN
  ASM_SIMP_TAC[C4_REPLICATE_SUC; VA1_HRUN_CLAUSES] THEN
  MP_TAC(ISPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `word K:int32`; `ap:int32`; `mdl:num->int32`; `N:num`;
    `ITER K (va1_swf mdl) (x0:(num->int32)#(num->int32))`; `hp:num->int32`; `tbl:num->int32`;
    `\k:num. word 251658:int32`; `va1_rbinit tbl`; `\k:num. word 0:int32`; `\k:num. word 0:int32`; `\k:num. word 0:int32`;
    `\k:num. word 0:int32`; `va1_zpseed mdl`; `word 0:int32`; `read (bytes32 (word 16404)) (m:int64->byte)`; `m:int64->byte`]
    VA1_HCALL_UNPUNCT) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `va1_fs_np fs` THEN REWRITE_TAC[va1_fs_np] THEN STRIP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC VA1_HCALL_MONO THEN
  FIRST_X_ASSUM(fun th -> EXISTS_TAC (rand(rator(rator(concl th)))) THEN REWRITE_TAC[th]) THEN
  MAP_EVERY X_GEN_TAC [`g1:num->wval`; `m1:int64->byte`] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[VA1_BAD_PUNCT; WORD_ADD_0] THEN STRIP_TAC THEN
  SUBGOAL_THEN `word_sub (word K) (word 1):int32 = word (K - 1) /\
    ve_fredkin_bwdn (\i. ve_vk mdl) 16 (ITER K (va1_swf mdl) (x0:(num->int32)#(num->int32))) = ITER (K - 1) (va1_swf mdl) x0`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [CONJ_TAC THENL [MATCH_MP_TAC C1_WORD_SUB1 THEN ASM_ARITH_TAC;
                    REWRITE_TAC[GSYM va1_swb] THEN MATCH_MP_TAC C1_SWB_ITER THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP C4_ST_NP) THEN
  SUBGOAL_THEN `va1_clean m1` ASSUME_TAC THENL
   [MATCH_MP_TAC C4_CLEAN_OF_UNP THEN
    MAP_EVERY EXISTS_TAC [`word (K - 1):int32`; `word 4294967295:int32`; `ap:int32`; `mdl:num->int32`; `N:num`;
      `ITER (K - 1) (va1_swf mdl) (x0:(num->int32)#(num->int32))`; `hp:num->int32`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`; `ap:int32`;
    `x0:(num->int32)#(num->int32)`; `K - 1`] VA1_NP_SCRUB_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`REPLICATE (K - 1) F`; `K - 1`; `m1:int64->byte`]) THEN
  ASM_REWRITE_TAC[C1_CMDS_OK_REPF; C1_CMDS_END_REPF; SUB_REFL; LE_REFL; ITER] THEN
  DISCH_TAC THEN MATCH_MP_TAC VA1_HRUN_MONO THEN
  FIRST_X_ASSUM(fun th -> EXISTS_TAC (rand(rator(rator(concl th)))) THEN REWRITE_TAC[th]) THEN
  MAP_EVERY X_GEN_TAC [`g3:num->wval`; `m3:int64->byte`] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `va1_clean m3` ASSUME_TAC THENL
   [MATCH_MP_TAC C4_CLEAN_NP THEN EXISTS_TAC `m1:int64->byte` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `read (bytes32 (word 16404)) m3 = read (bytes32 (word 16404)) (m0:int64->byte)` ASSUME_TAC THENL
   [FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[va1_np_frame] o
      check (fun th -> concl th = `va1_np_frame m1 m3`)) THEN
    C4_W_TAC `m1:int64->byte`;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC C4_FILM_BYTES_OF THEN
  MAP_EVERY EXISTS_TAC [`ap:int32`; `mdl:num->int32`; `x0:(num->int32)#(num->int32)`] THEN ASM_REWRITE_TAC[] THEN
  C4_UF_PATH [`m:int64->byte`; `m1:int64->byte`]);;

(* ---- the core after the puncture: n pop ticks forward and back, then the tail ---- *)
let c4_core_hyps = list_mk_conj
  [`va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\ (mdl:num->int32) 1 = word N /\ 1 <= N /\ N <= 640 /\
    1 <= K /\ K + 520 < 4294967296 /\ ((ap:int32) = word 0 \/ K - 1 < val (ap:int32))`;
   `va1_np_st (word 0) ap mdl N x0 m0 /\ va1_clean m0`;
   `va1_np_st (word K) ap mdl N (ITER K (va1_swf mdl) x0) m1 /\ va1_clean m1`;
   `read (bytes32 (word 16404)) m1 = read (bytes32 (word 16404)) m0`;
   c4_ufc `m0:int64->byte` `m1:int64->byte`;
   `va1_punct_rel mdl gl m1 gl2 m2`];;
let c4_core_vars = [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`; `ap:int32`;
  `x0:(num->int32)#(num->int32)`; `K:num`; `m0:int64->byte`; `m1:int64->byte`; `gl2:num->wval`; `m2:int64->byte`];;
let C4_CORE_START_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  C4_WK_TAC THEN
  MP_TAC(SPECL [`mdl:num->int32`; `N:num`; `ap:int32`; `ITER K (va1_swf mdl) (x0:(num->int32)#(num->int32))`; `K:num`;
    `gl:num->wval`; `m1:int64->byte`; `gl2:num->wval`; `m2:int64->byte`] C4_AT_PUNCT) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `tbl:num->int32` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN (mk_conj(subst [c4_s0, `s0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32`]
                           `va1_log_ok (word K) (va1_diof s0) (va1_ndof s0)`,
                         c4_ufc `m0:int64->byte` `m2:int64->byte`)) STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[va1_log_ok; va1_diof; va1_ndof; FST; SND; VAL_WORD_0; LE_0; LT; MULT_CLAUSES];
      C4_UF_PATH [`m1:int64->byte`]];
    ALL_TAC];;

let C4_CORE_INV = prove
 ((list_mk_forall(c4_core_vars @ [`n:num`], mk_imp(mk_conj(c4_core_hyps, `n <= 520`),
    `va1_hrun (wasmc fs) (APPEND (REPLICATE n T) (REPLICATE (n + K) F)) (\gl3 m3. gl3 = (gl:num->wval) /\ va1_np_st (word 0) (ap:int32) (mdl:num->int32) (N:num) (x0:(num->int32)#(num->int32)) m3 /\ va1_clean m3 /\ read (bytes32 (word 16404)) m3 = read (bytes32 (word 16404)) (m0:int64->byte) /\ va1_film_bytes N m0 m3) gl2 m2`))),
  C4_CORE_START_TAC THEN
  REWRITE_TAC[C4_REPLICATE_ADD; APPEND_ASSOC] THEN ONCE_REWRITE_TAC[VA1_HRUN_APPEND] THEN
  MP_TAC(ISPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`; `word K:int32`; `ap:int32`;
    `ITER K (va1_swf mdl) (x0:(num->int32)#(num->int32))`; c4_hp; `tbl:num->int32`; `word K:int32`; c4_s0;
    `n:num`; `m2:int64->byte`] VA1_POP_CHAIN_BYTES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC VA1_HRUN_MONO THEN
  FIRST_X_ASSUM(fun th -> EXISTS_TAC (rand(rator(rator(concl th)))) THEN REWRITE_TAC[th]) THEN
  MAP_EVERY X_GEN_TAC [`g3:num->wval`; `m3:int64->byte`] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C4_TAIL THEN
  MAP_EVERY EXISTS_TAC [c4_hp; `tbl:num->int32`] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[va1_pop_frame] o check (fun th -> concl th = `va1_pop_frame m2 m3`)) THEN
  CONJ_TAC THENL
   [C4_W_TAC `m2:int64->byte` THEN ASM_REWRITE_TAC[];
    C4_UF_PATH [`m2:int64->byte`]]);;

let C4_CORE_END = prove
 ((list_mk_forall(c4_core_vars, mk_imp(c4_core_hyps,
    `va1_hrun (wasmc fs) (REPLICATE 520 T)
       (\gl3 m3. gl3 = gl /\
          va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 0)
            (\gl4 m4. gl4 = gl3 /\ m4 = m3 /\ va1_hrun (wasmc fs) (REPLICATE (520 + K) F) (\gl3 m3. gl3 = (gl:num->wval) /\ va1_np_st (word 0) (ap:int32) (mdl:num->int32) (N:num) (x0:(num->int32)#(num->int32)) m3 /\ va1_clean m3 /\ read (bytes32 (word 16404)) m3 = read (bytes32 (word 16404)) (m0:int64->byte) /\ va1_film_bytes N m0 m3) gl4 m4) gl3 m3) gl2 m2`))),
  C4_CORE_START_TAC THEN
  MP_TAC(ISPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`; `word K:int32`; `ap:int32`;
    `ITER K (va1_swf mdl) (x0:(num->int32)#(num->int32))`; c4_hp; `tbl:num->int32`; `word K:int32`; c4_s0;
    `520`] VA1_POP_SCRUB_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "scrub") THEN
  MATCH_MP_TAC VA1_HRUN_MONO THEN
  EXISTS_TAC (subst [c4_hp, `hp:num->int32`; c4_s0, `s0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32`]
    `\gl' m'. gl' = (gl:num->wval) /\
       va1_pop_at mdl N (word K) ap (ITER K (va1_swf mdl) (x0:(num->int32)#(num->int32))) hp tbl (word K) s0 520 m' /\
       va1_pop_frame m2 m'`) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REMOVE_THEN "scrub" (MP_TAC o SPECL [`REPLICATE 520 T`; `0`; `m2:int64->byte`]) THEN
    ONCE_REWRITE_TAC[C2_REPT_NIL] THEN ASM_SIMP_TAC C2_FILM_SIMPS] THEN
  MAP_EVERY X_GEN_TAC [`g3:num->wval`; `m3:int64->byte`] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC VA1_HCALL_MONO THEN
  EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\ m' = (m3:int64->byte)` THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN REWRITE_TAC[C4_REPLICATE_ADD; VA1_HRUN_APPEND] THEN
    REMOVE_THEN "scrub" (MP_TAC o SPECL [`REPLICATE 520 F`; `520`; `m3:int64->byte`]) THEN
    ASM_SIMP_TAC C2_FILM_SIMPS THEN
    DISCH_TAC THEN MATCH_MP_TAC VA1_HRUN_MONO THEN
    FIRST_X_ASSUM(fun th -> EXISTS_TAC (rand(rator(rator(concl th)))) THEN REWRITE_TAC[th]) THEN
    MAP_EVERY X_GEN_TAC [`g5:num->wval`; `m5:int64->byte`] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC C4_TAIL THEN
    MAP_EVERY EXISTS_TAC [c4_hp; `tbl:num->int32`] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[va1_pop_frame] o check (fun th -> concl th = `va1_pop_frame m2 m3`)) THEN
    FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[va1_pop_frame] o check (fun th -> concl th = `va1_pop_frame m3 m5`)) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `read (bytes32 (word 16404)) (m3:int64->byte)` THEN CONJ_TAC THENL
       [C4_W_TAC `m3:int64->byte`; C4_W_TAC `m2:int64->byte` THEN ASM_REWRITE_TAC[]];
      C4_UF_PATH [`m2:int64->byte`; `m3:int64->byte`]];
    ALL_TAC] THEN
  UNDISCH_TAC (subst [c4_hp, `hp:num->int32`; c4_s0, `s0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32`]
    `va1_pop_at mdl N (word K) ap (ITER K (va1_swf mdl) (x0:(num->int32)#(num->int32))) hp tbl (word K) s0 520 m3`) THEN
  REWRITE_TAC[va1_pop_at] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C2_ST_TICK_POP) THEN
  MATCH_MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `word (val (word K:int32) + 520):int32`;
    `word K:int32`; `ap:int32`; `m3:int64->byte`] VA1_POP_HCALL_END) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[C2_VAL_P520; C2_VAL_WORD_LT; LE_REFL] THEN ASM_ARITH_TAC);;

(* ---- the forward no-pop run, and the auto step's intermediate state ---- *)
let C4_NP_FWD = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (ap:int32)
    (x0:(num->int32)#(num->int32)) (K:num) (m0:int64->byte).
     va1_fs_np fs /\ mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ K < 4294967296 /\ (ap = word 0 \/ K < val ap) /\
     va1_np_st (word 0) ap mdl N x0 m0
     ==> va1_hrun (wasmc fs) (REPLICATE K T)
           (\gl' m'. gl' = gl /\ va1_np_st (word K) ap mdl N (ITER K (va1_swf mdl) x0) m' /\ va1_np_frame m0 m') gl m0`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`; `ap:int32`;
    `x0:(num->int32)#(num->int32)`; `K:num`] VA1_NP_SCRUB_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`REPLICATE K T`; `0`; `m0:int64->byte`]) THEN
  ONCE_REWRITE_TAC[C2_REPT_NIL] THEN
  ASM_SIMP_TAC (C1_FILM_SIMPS @ [VA1_CMDS_OK_CLAUSES; VA1_CMDS_END_CLAUSES]));;

let C4_NPST_STEP = prove
 (`!(mdl:num->int32) N ap (x:(num->int32)#(num->int32)) K (m1:int64->byte) (mm:int64->byte).
     1 <= K /\ N <= 640 /\ va1_np_st (word (K - 1)) ap mdl N (ITER (K - 1) (va1_swf mdl) x) m1 /\
     read (bytes32 (word 16392)) mm = word_add (read (bytes32 (word 16392)) m1) (word 1) /\
     va1_vab N (va1_swf mdl (ITER (K - 1) (va1_swf mdl) x)) mm /\ va1_np_frame m1 mm
     ==> va1_np_st (word K) ap mdl N (ITER K (va1_swf mdl) x) mm`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C4_NPST_W; C4_VAB_W32S; va1_np_frame] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ITER K (va1_swf mdl) x = va1_swf mdl (ITER (K - 1) (va1_swf mdl) (x:(num->int32)#(num->int32))) /\
                word K:int32 = word_add (word (K - 1)) (word 1)` (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[C1_SWF_ITER; C1_WORD_ADD1] THEN CONJ_TAC THENL
     [AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC; AP_TERM_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; ASM_REWRITE_TAC[] THEN NO_TAC; C4_WS_TAC `m1:int64->byte`; C4_W_TAC `m1:int64->byte`]);;

(* ---- the headlines ---- *)
let C4_HEAD_FIN_TAC =
  FIRST [ASM_ARITH_TAC;
         MATCH_MP_TAC C4_AP_WEAK THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `read (bytes32 (word 16404)) (m1:int64->byte)` THEN
           CONJ_TAC THENL [C4_W_TAC `m1:int64->byte`; C4_W_TAC `m0:int64->byte`] THEN NO_TAC;
         C4_W_TAC `m0:int64->byte` THEN NO_TAC;
         C4_UF_PATH [`m1:int64->byte`] THEN NO_TAC;
         C4_UF_STEP THEN NO_TAC];;
let C4_HEAD_TAC (auto:bool) (core:thm) : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  C4_WK_TAC THEN
  MATCH_MP_TAC VA1_HRUN_MONO THEN
  EXISTS_TAC (if auto then
     `\gl' m'. gl' = (gl:num->wval) /\ va1_np_st (word (K - 1)) (word K) mdl N (ITER (K - 1) (va1_swf mdl) (x0:(num->int32)#(num->int32))) m' /\ va1_np_frame (m0:int64->byte) m'`
   else
     `\gl' m'. gl' = (gl:num->wval) /\ va1_np_st (word K) (ap:int32) mdl N (ITER K (va1_swf mdl) (x0:(num->int32)#(num->int32))) m' /\ va1_np_frame (m0:int64->byte) m'`) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC C4_NP_FWD THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC] THEN
  MAP_EVERY X_GEN_TAC [`g1:num->wval`; `m1:int64->byte`] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `va1_clean m1` ASSUME_TAC THENL
   [MATCH_MP_TAC C4_CLEAN_NP THEN EXISTS_TAC `m0:int64->byte` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`gl2:num->wval`; `m2:int64->byte`] THEN
  (if auto then
     REWRITE_TAC[va1_autopunct_rel] THEN DISCH_THEN(X_CHOOSE_THEN `mm:int64->byte` STRIP_ASSUME_TAC) THEN
     SUBGOAL_THEN `va1_np_st (word K) (word K) mdl N (ITER K (va1_swf mdl) (x0:(num->int32)#(num->int32))) mm` ASSUME_TAC THENL
      [MATCH_MP_TAC C4_NPST_STEP THEN EXISTS_TAC `m1:int64->byte` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     SUBGOAL_THEN `va1_clean mm` ASSUME_TAC THENL
      [MATCH_MP_TAC C4_CLEAN_NP THEN EXISTS_TAC `m1:int64->byte` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     MATCH_MP_TAC core THEN EXISTS_TAC `mm:int64->byte` THEN ASM_REWRITE_TAC[] THEN
     FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[va1_np_frame] o check (fun th -> concl th = `va1_np_frame m0 m1`)) THEN
     FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[va1_np_frame] o check (fun th -> concl th = `va1_np_frame m1 mm`)) THEN
     REPEAT CONJ_TAC THEN C4_HEAD_FIN_TAC
   else
     DISCH_TAC THEN
     MATCH_MP_TAC core THEN EXISTS_TAC `m1:int64->byte` THEN ASM_REWRITE_TAC[] THEN
     FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[va1_np_frame] o check (fun th -> concl th = `va1_np_frame m0 m1`)) THEN
     REPEAT CONJ_TAC THEN C4_HEAD_FIN_TAC);;

let VA1_FILM_INVERSE_CLICK = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (ap:int32)
   (x0:(num->int32)#(num->int32)) (K:num) (n:num) (m0:int64->byte).
     va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ 1 <= K /\ K + 520 < 4294967296 /\ n <= 520 /\
     (ap = word 0 \/ K < val ap) /\ va1_np_st (word 0) ap mdl N x0 m0 /\ va1_clean m0
     ==> va1_hrun (wasmc fs) (REPLICATE K T)
           (\gl1 m1. gl1 = gl /\ va1_np_st (word K) ap mdl N (ITER K (va1_swf mdl) x0) m1 /\ va1_clean m1 /\
              !gl2 m2. va1_punct_rel mdl gl1 m1 gl2 m2
                ==> va1_hrun (wasmc fs) (APPEND (REPLICATE n T) (REPLICATE (n + K) F))
                      (\gl3 m3. gl3 = gl /\ va1_np_st (word 0) ap mdl N x0 m3 /\ va1_clean m3 /\
                         read (bytes32 (word 16404)) m3 = read (bytes32 (word 16404)) m0 /\
                         va1_film_bytes N m0 m3) gl2 m2) gl m0`,
  C4_HEAD_TAC false C4_CORE_INV);;

let VA1_FILM_INVERSE_AUTO = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num)
   (x0:(num->int32)#(num->int32)) (K:num) (n:num) (m0:int64->byte).
     va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ 1 <= K /\ K + 520 < 4294967296 /\ n <= 520 /\
     va1_np_st (word 0) (word K) mdl N x0 m0 /\ va1_clean m0
     ==> va1_hrun (wasmc fs) (REPLICATE (K - 1) T)
           (\gl1 m1. gl1 = gl /\ va1_np_st (word (K - 1)) (word K) mdl N (ITER (K - 1) (va1_swf mdl) x0) m1 /\
              va1_clean m1 /\
              !gl2 m2. va1_autopunct_rel mdl N (ITER (K - 1) (va1_swf mdl) x0) gl1 m1 gl2 m2
                ==> va1_hrun (wasmc fs) (APPEND (REPLICATE n T) (REPLICATE (n + K) F))
                      (\gl3 m3. gl3 = gl /\ va1_np_st (word 0) (word K) mdl N x0 m3 /\ va1_clean m3 /\
                         read (bytes32 (word 16404)) m3 = read (bytes32 (word 16404)) m0 /\
                         va1_film_bytes N m0 m3) gl2 m2) gl m0`,
  C4_HEAD_TAC true C4_CORE_INV);;

let VA1_FILM_TO_END_CLICK = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (ap:int32)
   (x0:(num->int32)#(num->int32)) (K:num) (m0:int64->byte).
     va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ 1 <= K /\ K + 520 < 4294967296 /\
     (ap = word 0 \/ K < val ap) /\ va1_np_st (word 0) ap mdl N x0 m0 /\ va1_clean m0
     ==> va1_hrun (wasmc fs) (REPLICATE K T)
           (\gl1 m1. gl1 = gl /\ va1_np_st (word K) ap mdl N (ITER K (va1_swf mdl) x0) m1 /\ va1_clean m1 /\
              !gl2 m2. va1_punct_rel mdl gl1 m1 gl2 m2
                ==> va1_hrun (wasmc fs) (REPLICATE 520 T)
                      (\gl3 m3. gl3 = gl /\
                         va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 0)
                           (\gl4 m4. gl4 = gl3 /\ m4 = m3 /\
                              va1_hrun (wasmc fs) (REPLICATE (520 + K) F)
                                (\gl5 m5. gl5 = gl /\ va1_np_st (word 0) ap mdl N x0 m5 /\ va1_clean m5 /\
                                   read (bytes32 (word 16404)) m5 = read (bytes32 (word 16404)) m0 /\
                                   va1_film_bytes N m0 m5) gl4 m4) gl3 m3) gl2 m2) gl m0`,
  C4_HEAD_TAC false C4_CORE_END);;

let VA1_FILM_TO_END_AUTO = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num)
   (x0:(num->int32)#(num->int32)) (K:num) (m0:int64->byte).
     va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ 1 <= K /\ K + 520 < 4294967296 /\
     va1_np_st (word 0) (word K) mdl N x0 m0 /\ va1_clean m0
     ==> va1_hrun (wasmc fs) (REPLICATE (K - 1) T)
           (\gl1 m1. gl1 = gl /\ va1_np_st (word (K - 1)) (word K) mdl N (ITER (K - 1) (va1_swf mdl) x0) m1 /\
              va1_clean m1 /\
              !gl2 m2. va1_autopunct_rel mdl N (ITER (K - 1) (va1_swf mdl) x0) gl1 m1 gl2 m2
                ==> va1_hrun (wasmc fs) (REPLICATE 520 T)
                      (\gl3 m3. gl3 = gl /\
                         va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 0)
                           (\gl4 m4. gl4 = gl3 /\ m4 = m3 /\
                              va1_hrun (wasmc fs) (REPLICATE (520 + K) F)
                                (\gl5 m5. gl5 = gl /\ va1_np_st (word 0) (word K) mdl N x0 m5 /\ va1_clean m5 /\
                                   read (bytes32 (word 16404)) m5 = read (bytes32 (word 16404)) m0 /\
                                   va1_film_bytes N m0 m5) gl4 m4) gl3 m3) gl2 m2) gl m0`,
  C4_HEAD_TAC true C4_CORE_END);;
