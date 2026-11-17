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
needs "chain_c2_host_pop.ml";;
(* ========================================================================= *)
(* Vortex chain, rung C2, layer 2 of 2: the pop chain (PROVE-C2, Claude      *)
(* Opus 5.5, 2026-11-11). Spec chain_c2_final.spec (frozen c7a0c0a8...).    *)
(* History invariant (log_ok along va1_pop_reach), one step forward and back *)
(* on va1_pop_at, scrub in any order with the byte frame, the inverse chain, *)
(* the run to the end of the pop, non-vacuity. Pure HOL; no stepping.        *)
(* ========================================================================= *)

(* ---- arithmetic ---- *)

let C2_WADD1 = prove
 (`!a b. word_add (word (a + b)) (word 1):int32 = word (a + b + 1)`,
  REWRITE_TAC[GSYM WORD_ADD; ADD_ASSOC]);;

let C2_WSUC = prove
 (`!a u. word (a + SUC u):int32 = word (a + u + 1)`,
  REWRITE_TAC[ADD1]);;

let C2_VAL_WORD_LT = prove
 (`!n. n < 4294967296 ==> val(word n:int32) = n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let C2_WORD_NZ = prove
 (`!n. 0 < n /\ n < 4294967296 ==> ~(word n:int32 = word 0)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int32->num`) THEN
  ASM_SIMP_TAC[C2_VAL_WORD_LT; VAL_WORD_0] THEN ASM_ARITH_TAC);;

let C2_VAL_P520 = prove
 (`!p:int32. val p + 520 < 4294967296 ==> val(word_add p (word 520)) = val p + 520`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let C2_WINDOW = prove
 (`!(p:int32) (t0:int32) u.
     ~(p = word 4294967295) /\ val p <= val t0 /\ val t0 + u < val p + 520 /\ val p + 520 < 4294967296
     ==> va1_pop_window (word (val t0 + u)) p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[va1_pop_window] THEN
  ASM_SIMP_TAC[C2_VAL_P520] THEN
  SUBGOAL_THEN `val(word (val (t0:int32) + u):int32) = val t0 + u` SUBST1_TAC THENL
   [MATCH_MP_TAC C2_VAL_WORD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let C2_ALL_WEAK = prove
 (`!(L:(num->int32)list) (a:int32).
     ALL (\r. r 6 = a /\ r 10 = word 0 /\ r 11 = word 0) L ==> ALL (\r. r 6 = a) L`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL] THEN ASM_MESON_TAC[]);;

(* ---- the history invariant ---- *)

let C2_LOG_OK_FWD_S = prove
 (`!(L:(num->int32)list) (mdl:num->int32) (hp:num->int32) (tbl:num->int32) (t:int32) (p:int32)
    (S:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32).
     va1_log_ok t (va1_diof S) (va1_ndof S) /\ ~(word_add t (word 1) = word 0) /\
     ALL (\r. r 6 = word_add t (word 1)) L /\ val (va1_ndof S) + LENGTH L <= 16384
     ==> va1_log_ok (word_add t (word 1))
           (va1_diof (va1_pop_fwd va1_ck va1_jigk L mdl hp tbl t p S))
           (va1_ndof (va1_pop_fwd va1_ck va1_jigk L mdl hp tbl t p S))`,
  REPEAT GEN_TAC THEN C2_SPLIT_S_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC VA1_LOG_OK_POP_FWD THEN ASM_REWRITE_TAC[]);;

let VA1_POP_REACH_LOG_OK = prove
 (`!(mdl:num->int32) (hp:num->int32) (tbl:num->int32) (p:int32) (t0:int32)
   (S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32)
   (u:num)
   (S:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32).
     va1_log_ok t0 (va1_diof S0) (va1_ndof S0) /\ val t0 + u < 4294967296 /\
     va1_pop_reach mdl hp tbl p t0 S0 u S
     ==> va1_log_ok (word (val t0 + u)) (va1_diof S) (va1_ndof S)`,
  MAP_EVERY X_GEN_TAC
   [`mdl:num->int32`; `hp:num->int32`; `tbl:num->int32`; `p:int32`; `t0:int32`;
    `S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32`] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[VA1_POP_REACH_CLAUSES; ADD_CLAUSES; WORD_VAL] THEN MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `S:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32` THEN
  REWRITE_TAC[VA1_POP_REACH_CLAUSES] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `S':(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `val (t0:int32) + SUC u < 4294967296` THEN ARITH_TAC;
    DISCH_TAC] THEN
  ASM_REWRITE_TAC[C2_WSUC] THEN
  REWRITE_TAC[GSYM C2_WADD1] THEN MATCH_MP_TAC C2_LOG_OK_FWD_S THEN ASM_REWRITE_TAC[C2_WADD1] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC C2_WORD_NZ THEN UNDISCH_TAC `val (t0:int32) + SUC u < 4294967296` THEN ARITH_TAC;
    MATCH_MP_TAC C2_ALL_WEAK THEN ASM_REWRITE_TAC[]]);;

(* ---- generic tactic: weaken the postcondition of an hcall theorem ---- *)
let C2_MONO_FROM (th:thm) : tactic =
  MATCH_MP_TAC VA1_HCALL_MONO THEN EXISTS_TAC (rand(rator(rator(concl th)))) THEN
  CONJ_TAC THENL [ALL_TAC; ACCEPT_TAC th];;

(* ---- one step on va1_pop_at, with the frame ---- *)

let C2_POP_AT_FWD = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (p:int32) (ap:int32)
    (x0:(num->int32)#(num->int32)) (hp:num->int32) (tbl:num->int32) (t0:int32)
    (S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32)
    (kk:num) (u:num) (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_pop fs /\
     ~(p = word 4294967295) /\ val p <= val t0 /\ val t0 + kk <= val p + 520 /\ val p + 520 < 4294967296 /\
     va1_log_ok t0 (va1_diof S0) (va1_ndof S0) /\ u < kk /\ va1_pop_at mdl N p ap x0 hp tbl t0 S0 u m
     ==> va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 1)
           (\gl' m'. gl' = gl /\ va1_pop_at mdl N p ap x0 hp tbl t0 S0 (u + 1) m' /\
                     va1_pop_frame m m') gl m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_pop_at] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `word (val (t0:int32) + u):int32`;
    `p:int32`; `ap:int32`; `mdl:num->int32`; `N:num`;
    `ITER u (ve_fredkin_fwd (ve_vk mdl)) (x0:(num->int32)#(num->int32))`; `hp:num->int32`;
    `tbl:num->int32`;
    `S:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32`;
    `m:int64->byte`] C2_POP_HCALL_FWD_FRAME) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC C2_WINDOW THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC VA1_POP_REACH_LOG_OK THEN
      MAP_EVERY EXISTS_TAC [`mdl:num->int32`; `hp:num->int32`; `tbl:num->int32`; `p:int32`;
        `S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32`] THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> C2_MONO_FROM th) THEN
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `va1_pop_fwd va1_ck va1_jigk L mdl hp tbl (word (val (t0:int32) + u)) p
    (S:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32)` THEN
  REWRITE_TAC[GSYM ADD1] THEN REWRITE_TAC[VA1_POP_REACH_CLAUSES; ITER; C2_WSUC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C2_WADD1]) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC
   [`S:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32`;
    `L:(num->int32)list`] THEN
  ASM_REWRITE_TAC[]);;

let C2_POP_AT_BWD = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (p:int32) (ap:int32)
    (x0:(num->int32)#(num->int32)) (hp:num->int32) (tbl:num->int32) (t0:int32)
    (S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32)
    (kk:num) (u:num) (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_pop fs /\
     ~(p = word 4294967295) /\ val p <= val t0 /\ val t0 + kk <= val p + 520 /\ val p + 520 < 4294967296 /\
     va1_log_ok t0 (va1_diof S0) (va1_ndof S0) /\ 0 < u /\ u <= kk /\
     va1_pop_at mdl N p ap x0 hp tbl t0 S0 u m
     ==> va1_hcall (wasmc fs) va1_tick_backward_mc [] (word 1)
           (\gl' m'. gl' = gl /\ va1_pop_at mdl N p ap x0 hp tbl t0 S0 (u - 1) m' /\
                     va1_pop_frame m m') gl m`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `v:num` SUBST1_TAC) (SPEC `u:num` num_CASES) THEN
  REWRITE_TAC[LT_REFL] THEN
  REWRITE_TAC[SUC_SUB1; va1_pop_at; VA1_POP_REACH_CLAUSES; ITER; C2_WSUC] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `word (val (t0:int32) + v):int32`;
    `p:int32`; `ap:int32`; `mdl:num->int32`; `N:num`;
    `ITER v (ve_fredkin_fwd (ve_vk mdl)) (x0:(num->int32)#(num->int32))`; `hp:num->int32`;
    `tbl:num->int32`;
    `S':(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32`;
    `L:(num->int32)list`; `m:int64->byte`] C2_POP_HCALL_BWD_FRAME) THEN
  REWRITE_TAC[C2_WADD1] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `S = va1_pop_fwd va1_ck va1_jigk L mdl hp tbl (word (val (t0:int32) + v)) p S'` THEN
    DISCH_THEN(SUBST_ALL_TAC) THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC C2_WINDOW THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC VA1_POP_REACH_LOG_OK THEN
      MAP_EVERY EXISTS_TAC [`mdl:num->int32`; `hp:num->int32`; `tbl:num->int32`; `p:int32`;
        `S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32`] THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC C2_ALL_WEAK THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> C2_MONO_FROM th) THEN
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC
   `S':(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32` THEN
  ASM_REWRITE_TAC[]);;

(* ---- scrub with the frame, relative to any m0 framing the start memory ---- *)

let C2_POP_SCRUB_FRAME_GEN = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (p:int32) (ap:int32)
    (x0:(num->int32)#(num->int32)) (hp:num->int32) (tbl:num->int32) (t0:int32)
    (S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32)
    (kk:num) (m0:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_pop fs /\
     ~(p = word 4294967295) /\ val p <= val t0 /\ val t0 + kk <= val p + 520 /\ val p + 520 < 4294967296 /\
     va1_log_ok t0 (va1_diof S0) (va1_ndof S0)
     ==> !(cs:bool list) (u:num) (m:int64->byte).
           u <= kk /\ va1_cmds_ok kk u cs /\ va1_pop_at mdl N p ap x0 hp tbl t0 S0 u m /\
           va1_pop_frame m0 m
           ==> va1_hrun (wasmc fs) cs
                 (\gl' m'. gl' = gl /\
                    va1_pop_at mdl N p ap x0 hp tbl t0 S0 (va1_cmds_end u cs) m' /\
                    va1_pop_frame m0 m') gl m`,
  MAP_EVERY X_GEN_TAC
   [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`; `p:int32`; `ap:int32`;
    `x0:(num->int32)#(num->int32)`; `hp:num->int32`; `tbl:num->int32`; `t0:int32`;
    `S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32`;
    `kk:num`; `m0:int64->byte`] THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN ASSUME_TAC th) THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[VA1_HRUN_CLAUSES; VA1_CMDS_OK_CLAUSES; VA1_CMDS_END_CLAUSES] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[VA1_CMDS_END_CLAUSES] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:num`; `m:int64->byte`] THEN
  REWRITE_TAC[VA1_HRUN_CLAUSES; VA1_CMDS_OK_CLAUSES; VA1_CMDS_END_CLAUSES] THEN
  ASM_CASES_TAC `h:bool` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC VA1_HCALL_MONO THENL
   [EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\
       va1_pop_at mdl N p ap x0 hp tbl t0 S0 (u + 1) m' /\ va1_pop_frame m m'` THEN
    CONJ_TAC THENL
     [REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `u < kk` THEN ARITH_TAC;
        MATCH_MP_TAC VA1_POP_FRAME_TRANS THEN EXISTS_TAC `m:int64->byte` THEN
        ASM_REWRITE_TAC[]];
      MATCH_MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`;
        `p:int32`; `ap:int32`; `x0:(num->int32)#(num->int32)`; `hp:num->int32`; `tbl:num->int32`;
        `t0:int32`;
        `S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32`;
        `kk:num`; `u:num`; `m:int64->byte`] C2_POP_AT_FWD) THEN
      ASM_REWRITE_TAC[]];
    EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\
       va1_pop_at mdl N p ap x0 hp tbl t0 S0 (u - 1) m' /\ va1_pop_frame m m'` THEN
    CONJ_TAC THENL
     [REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `u <= kk` THEN ARITH_TAC;
        MATCH_MP_TAC VA1_POP_FRAME_TRANS THEN EXISTS_TAC `m:int64->byte` THEN
        ASM_REWRITE_TAC[]];
      MATCH_MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`;
        `p:int32`; `ap:int32`; `x0:(num->int32)#(num->int32)`; `hp:num->int32`; `tbl:num->int32`;
        `t0:int32`;
        `S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32`;
        `kk:num`; `u:num`; `m:int64->byte`] C2_POP_AT_BWD) THEN
      ASM_REWRITE_TAC[]]]);;

let VA1_POP_SCRUB_FRAME = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (p:int32) (ap:int32)
   (x0:(num->int32)#(num->int32)) (hp:num->int32) (tbl:num->int32) (t0:int32)
   (S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32)
   (K:num).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_pop fs /\
     ~(p = word 4294967295) /\ val p <= val t0 /\ val t0 + K <= val p + 520 /\ val p + 520 < 4294967296 /\
     va1_log_ok t0 (va1_diof S0) (va1_ndof S0)
     ==> !(cs:bool list) (u:num) (m:int64->byte).
           u <= K /\ va1_cmds_ok K u cs /\ va1_pop_at mdl N p ap x0 hp tbl t0 S0 u m
           ==> va1_hrun (wasmc fs) cs
                 (\gl' m'. gl' = gl /\
                    va1_pop_at mdl N p ap x0 hp tbl t0 S0 (va1_cmds_end u cs) m' /\
                    va1_pop_frame m m') gl m`,
  MAP_EVERY X_GEN_TAC
   [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`; `p:int32`; `ap:int32`;
    `x0:(num->int32)#(num->int32)`; `hp:num->int32`; `tbl:num->int32`; `t0:int32`;
    `S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32`;
    `kk:num`] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`cs:bool list`; `u:num`; `m:int64->byte`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`; `p:int32`;
    `ap:int32`; `x0:(num->int32)#(num->int32)`; `hp:num->int32`; `tbl:num->int32`; `t0:int32`;
    `S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32`;
    `kk:num`; `m:int64->byte`] C2_POP_SCRUB_FRAME_GEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`cs:bool list`; `u:num`; `m:int64->byte`]) THEN
  ASM_REWRITE_TAC[VA1_POP_FRAME_REFL]);;

let VA1_POP_SCRUB = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (p:int32) (ap:int32)
   (x0:(num->int32)#(num->int32)) (hp:num->int32) (tbl:num->int32) (t0:int32)
   (S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32)
   (K:num).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_pop fs /\
     ~(p = word 4294967295) /\ val p <= val t0 /\ val t0 + K <= val p + 520 /\ val p + 520 < 4294967296 /\
     va1_log_ok t0 (va1_diof S0) (va1_ndof S0)
     ==> !(cs:bool list) (u:num) (m:int64->byte).
           u <= K /\ va1_cmds_ok K u cs /\ va1_pop_at mdl N p ap x0 hp tbl t0 S0 u m
           ==> va1_hrun (wasmc fs) cs
                 (\gl' m'. gl' = gl /\
                    va1_pop_at mdl N p ap x0 hp tbl t0 S0 (va1_cmds_end u cs) m') gl m`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC VA1_HRUN_MONO THEN
  EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\
     va1_pop_at mdl N p ap x0 hp tbl t0 S0 (va1_cmds_end u cs) m' /\ va1_pop_frame m m'` THEN
  CONJ_TAC THENL
   [CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN MESON_TAC[];
    MP_TAC(SPEC_ALL VA1_POP_SCRUB_FRAME) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ---- command lists ---- *)

let C2_CMDS_OK_REPT = prove
 (`!j kk u cs. u <= kk
     ==> (va1_cmds_ok kk u (APPEND (REPLICATE j T) cs) <=>
          u + j <= kk /\ va1_cmds_ok kk (u + j) cs)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[REPLICATE; APPEND; ADD_CLAUSES] THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REPLICATE; APPEND; ADD_CLAUSES; VA1_CMDS_OK_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `u < kk` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`kk:num`; `u + 1`; `cs:bool list`]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[ARITH_RULE `(u + 1) + j = SUC (u + j)`];
    REWRITE_TAC[DE_MORGAN_THM] THEN DISJ1_TAC THEN ASM_ARITH_TAC]);;

let C2_CMDS_OK_REPF = prove
 (`!j kk u. va1_cmds_ok kk u (REPLICATE j F) <=> j <= u`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; VA1_CMDS_OK_CLAUSES; LE_0] THEN ARITH_TAC);;

let C2_CMDS_END_REPT = prove
 (`!j u cs. va1_cmds_end u (APPEND (REPLICATE j T) cs) = va1_cmds_end (u + j) cs`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[REPLICATE; APPEND; VA1_CMDS_END_CLAUSES; ADD_CLAUSES;
                  ARITH_RULE `!u j. (u + 1) + j = SUC (u + j)`]);;

let C2_CMDS_END_REPF = prove
 (`!j u. va1_cmds_end u (REPLICATE j F) = u - j`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; VA1_CMDS_END_CLAUSES; SUB_0] THEN ARITH_TAC);;

let C2_REPT_NIL = prove
 (`!j. REPLICATE j T = APPEND (REPLICATE j T) []`,
  REWRITE_TAC[APPEND_NIL]);;

let C2_POP_AT_0 = prove
 (`!(mdl:num->int32) (N:num) (p:int32) (ap:int32) (x0:(num->int32)#(num->int32))
    (hp:num->int32) (tbl:num->int32) (t0:int32)
    (S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32)
    (m:int64->byte).
     va1_pop_at mdl N p ap x0 hp tbl t0 S0 0 m <=> va1_st t0 p ap mdl N x0 hp tbl S0 m`,
  REWRITE_TAC[va1_pop_at; VA1_POP_REACH_CLAUSES; ITER; ADD_CLAUSES; WORD_VAL; UNWIND_THM2]);;

let C2_FILM_SIMPS =
  [LE_0; LE_REFL; ADD_CLAUSES; SUB_REFL; C2_CMDS_OK_REPT; C2_CMDS_OK_REPF;
   C2_CMDS_END_REPT; C2_CMDS_END_REPF; VA1_CMDS_OK_CLAUSES; VA1_CMDS_END_CLAUSES; C2_POP_AT_0];;

(* ---- corollaries ---- *)

let VA1_POP_CHAIN_BYTES = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (p:int32) (ap:int32)
   (x0:(num->int32)#(num->int32)) (hp:num->int32) (tbl:num->int32) (t0:int32)
   (S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32)
   (k:num) (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_pop fs /\
     ~(p = word 4294967295) /\ val p <= val t0 /\ val t0 + k <= val p + 520 /\ val p + 520 < 4294967296 /\
     va1_log_ok t0 (va1_diof S0) (va1_ndof S0) /\ va1_st t0 p ap mdl N x0 hp tbl S0 m
     ==> va1_hrun (wasmc fs) (APPEND (REPLICATE k T) (REPLICATE k F))
           (\gl' m'. gl' = gl /\ va1_st t0 p ap mdl N x0 hp tbl S0 m' /\ va1_pop_frame m m') gl m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`; `p:int32`;
    `ap:int32`; `x0:(num->int32)#(num->int32)`; `hp:num->int32`; `tbl:num->int32`; `t0:int32`;
    `S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32`;
    `k:num`] VA1_POP_SCRUB_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`APPEND (REPLICATE k T) (REPLICATE k F)`; `0`; `m:int64->byte`]) THEN
  ASM_SIMP_TAC C2_FILM_SIMPS);;

let VA1_POP_CHAIN_INVERSE = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (p:int32) (ap:int32)
   (x0:(num->int32)#(num->int32)) (hp:num->int32) (tbl:num->int32) (t0:int32)
   (S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32)
   (k:num) (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_pop fs /\
     ~(p = word 4294967295) /\ val p <= val t0 /\ val t0 + k <= val p + 520 /\ val p + 520 < 4294967296 /\
     va1_log_ok t0 (va1_diof S0) (va1_ndof S0) /\ va1_st t0 p ap mdl N x0 hp tbl S0 m
     ==> va1_hrun (wasmc fs) (APPEND (REPLICATE k T) (REPLICATE k F))
           (\gl' m'. gl' = gl /\ va1_st t0 p ap mdl N x0 hp tbl S0 m') gl m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`; `p:int32`;
    `ap:int32`; `x0:(num->int32)#(num->int32)`; `hp:num->int32`; `tbl:num->int32`; `t0:int32`;
    `S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32`;
    `k:num`; `m:int64->byte`] VA1_POP_CHAIN_BYTES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MATCH_MP_TAC VA1_HRUN_MONO THEN
  FIRST_X_ASSUM(fun th -> EXISTS_TAC (rand(rator(rator(concl th)))) THEN REWRITE_TAC[th]) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN MESON_TAC[]);;

let C2_ST_TICK_POP = prove
 (`!(t:int32) (p:int32) (ap:int32) (mdl:num->int32) (N:num) (x:(num->int32)#(num->int32))
    (hp:num->int32) (tbl:num->int32)
    (S:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32)
    (m:int64->byte).
     va1_st t p ap mdl N x hp tbl S m ==> va1_tick t m /\ va1_pop p ap m`,
  REWRITE_TAC[FORALL_PAIR_THM; va1_st] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let VA1_POP_CHAIN_TO_END = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (p:int32) (ap:int32)
   (x0:(num->int32)#(num->int32)) (hp:num->int32) (tbl:num->int32)
   (S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32)
   (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_pop fs /\
     ~(p = word 4294967295) /\ val p + 520 < 4294967296 /\
     va1_log_ok p (va1_diof S0) (va1_ndof S0) /\ va1_st p p ap mdl N x0 hp tbl S0 m
     ==> va1_hrun (wasmc fs) (REPLICATE 520 T)
           (\gl1 m1. gl1 = gl /\ va1_pop_at mdl N p ap x0 hp tbl p S0 520 m1 /\
              va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 0)
                (\gl2 m2. gl2 = gl1 /\ m2 = m1 /\
                   va1_hrun (wasmc fs) (REPLICATE 520 F)
                     (\gl3 m3. gl3 = gl /\ va1_st p p ap mdl N x0 hp tbl S0 m3) gl2 m2) gl1 m1) gl m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`; `p:int32`;
    `ap:int32`; `x0:(num->int32)#(num->int32)`; `hp:num->int32`; `tbl:num->int32`; `p:int32`;
    `S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32`;
    `520`] VA1_POP_SCRUB) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN DISCH_THEN(LABEL_TAC "scrub") THEN
  MATCH_MP_TAC VA1_HRUN_MONO THEN
  EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\
     va1_pop_at mdl N p ap x0 hp tbl p S0 520 m'` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REMOVE_THEN "scrub" (MP_TAC o SPECL [`REPLICATE 520 T`; `0`; `m:int64->byte`]) THEN
    ONCE_REWRITE_TAC[C2_REPT_NIL] THEN ASM_SIMP_TAC C2_FILM_SIMPS] THEN
  MAP_EVERY X_GEN_TAC [`g1:num->wval`; `m1:int64->byte`] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC VA1_HCALL_MONO THEN
  EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\ m' = (m1:int64->byte)` THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN REWRITE_TAC[] THEN
    REMOVE_THEN "scrub" (MP_TAC o SPECL [`REPLICATE 520 F`; `520`; `m1:int64->byte`]) THEN
    ASM_SIMP_TAC C2_FILM_SIMPS;
    ALL_TAC] THEN
  UNDISCH_TAC `va1_pop_at mdl N p ap x0 hp tbl p S0 520 m1` THEN
  REWRITE_TAC[va1_pop_at] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C2_ST_TICK_POP) THEN
  MATCH_MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `word (val (p:int32) + 520):int32`;
    `p:int32`; `ap:int32`; `m1:int64->byte`] VA1_POP_HCALL_END) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[C2_VAL_P520; C2_VAL_WORD_LT; LE_REFL] THEN ASM_ARITH_TAC);;

let VA1_POP_CHAIN_SAT = prove
 (`(!(t:int32) (p:int32) (ap:int32) (mdl:num->int32) (N:num) (x:(num->int32)#(num->int32))
    (hp:num->int32) (tbl:num->int32)
    (S:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32).
     N <= 640 ==> ?m:int64->byte. va1_st t p ap mdl N x hp tbl S m) /\
  (?(fs:num->byte list#num#num) (mdl:num->int32) (N:num) (p:int32) (ap:int32)
    (x0:(num->int32)#(num->int32)) (hp:num->int32) (tbl:num->int32)
    (S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32)
    (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_pop fs /\
     ~(p = word 4294967295) /\ val p + 520 < 4294967296 /\
     va1_log_ok p (va1_diof S0) (va1_ndof S0) /\ va1_st p p ap mdl N x0 hp tbl S0 m)`,
  CONJ_TAC THENL [MATCH_ACCEPT_TAC VA1_ST_SAT; ALL_TAC] THEN
  MP_TAC(ISPECL [`word 120:int32`; `word 120:int32`; `word 0:int32`; `\k:num. word 1:int32`; `1`;
    `((\i:num. word 0:int32),(\i:num. word 0:int32))`; `\i:num. word 0:int32`; `\i:num. word 0:int32`;
    `((\i:num. word 0:int32),(\i:num. word 0:int32),(\i:num. word 0:int32),(\i:num. word 0:int32),
      (\i:num. word 0:int32),(\i:num. word 0:int32),(\i:num. word 0:int32),(word 0:int32))`]
    VA1_ST_SAT) THEN
  REWRITE_TAC[ARITH_RULE `1 <= 640`] THEN DISCH_THEN(X_CHOOSE_TAC `m:int64->byte`) THEN
  MAP_EVERY EXISTS_TAC
   [`\i. if i = 9 then (va1_f9_mc,0,0) else if i = 10 then (va1_f10_mc,0,0)
         else if i = 11 then (va1_f11_mc,0,0) else if i = 12 then (va1_f12_mc,0,0)
         else if i = 13 then (va1_f13_mc,0,1) else if i = 14 then (va1_f14_mc,0,1)
         else if i = 15 then (va1_f15_mc,0,0) else if i = 16 then (va1_f16_mc,0,0)
         else if i = 17 then (va1_f17_mc,1,0) else if i = 18 then (va1_f18_mc,1,0)
         else if i = 19 then (va1_f19_mc,0,0) else if i = 20 then (va1_f20_mc,0,0)
         else if i = 21 then (va1_f21_mc,0,0) else if i = 22 then (va1_f22_mc,0,0)
         else if i = 23 then (va1_f23_mc,0,0) else if i = 24 then (va1_f24_mc,0,0)
         else if i = 27 then (va1_f27_mc,0,0) else (va1_f28_mc,0,0)`;
    `\k:num. word 1:int32`; `1`; `word 120:int32`; `word 0:int32`;
    `((\i:num. word 0:int32),(\i:num. word 0:int32))`; `\i:num. word 0:int32`; `\i:num. word 0:int32`;
    `((\i:num. word 0:int32),(\i:num. word 0:int32),(\i:num. word 0:int32),(\i:num. word 0:int32),
      (\i:num. word 0:int32),(\i:num. word 0:int32),(\i:num. word 0:int32),(word 0:int32))`;
    `m:int64->byte`] THEN
  ASM_REWRITE_TAC[va1_fs_pop; va1_log_ok; va1_diof; va1_ndof; FST; SND; VAL_WORD_0; LT; LE_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC(NUM_REDUCE_CONV THENC WORD_REDUCE_CONV) THEN REWRITE_TAC[]);;
