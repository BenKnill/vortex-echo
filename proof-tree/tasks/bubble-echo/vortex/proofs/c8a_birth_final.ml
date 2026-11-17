(* vortex-chain C8a final leaf (row A7), Claude Opus 5.5, 2026-11-15. Spec c8a_birth.spec (frozen sha256
   45a80dc635545cd09bfc37f9fb4faec174c1b004db539ce6d23597d580ac21c7, FROZEN-C8A.txt). VA1_BIRTH_EQ: f13 from pc 13 to WDone
   leaves ND' and the record log as va1_push (va1_born ...) of the entry state: prologue C8A_PRO, loop 1 C8A_LOOP1V (k = 0),
   C8A_T2 (route lemmas in c8a_final_lem.ml) (2612: loop 2 entry, C8A_LOOP2V, C8A_T3: loop 3 entry, C8A_LOOP3V, epilogue R5B_EPI, C8A_FINAL_MEMV), with the
   ND = 16384 and cap exits handled by the fold cap lemmas. VA1_BORN_SHAPE and VA1_BIRTH_EQ_OK are re-bound from the
   shape layer (c8a_shape_lem.ml); the fold CLAUSES, VA1_F13_ENTRY and VA1_PUSH_CLAUSES as in the A1 probe. *)
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
needs "c8a_born_defs.ml";;
needs "c8a_shape_lem.ml";;
needs "c8a_isqv.ml";;
needs "c8a_seg1v.ml";;
needs "c8a_fold_lem.ml";;
needs "c8a_iter1.ml";;
needs "c8a_loop2v.ml";;
needs "c8a_loop3v.ml";;
needs "c8a_final_lem.ml";;
let VA1_BIRTH_EQ = prove(`va1_birth_eq`,
  REWRITE_TAC[va1_birth_eq; va1_born] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `va1_log_ok t di nd` THEN REWRITE_TAC[va1_log_ok] THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC c8a_pre0 THEN CONJ_TAC THENL
   [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
    EXISTS_TAC `read wmem (s:wasmstate)` THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `wlocals`)) (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `wasm_decl_vals`)) (concl th))) THEN
    REWRITE_TAC[CONJUNCT2 VA1_F13_CALLEE; option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[wlocal; READ_COMPONENT_COMPOSE] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[wcall_locals; LENGTH; READ_ELEMENT] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    FIRST_ASSUM(fun th -> if concl th = `va1_mdl mdl (read wmem (s:wasmstate))` then
       MP_TAC(SPEC `2` (REWRITE_RULE[va1_mdl; va1_w32s] th)) else NO_TAC) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[va1_tick; va1_bs]) THEN ASM_REWRITE_TAC[R5B_EX_EQ; injectivity "wval"; va1_push; FST; SND];
    ALL_TAC] THEN
  R5B_EXISTS_TAC THEN X_GEN_TAC `m0:int64->byte` THEN R5B_PURE_TAC THEN
  W(fun (asl,w) -> C8A_THEN (r5b_inst2 asl (SPECL [`m0:int64->byte`; `nd:int32`; `t:int32`; `mdl:num->int32`] C8A_PRO))) THEN
  R5B_DISJ_TAC THEN CONJ_TAC THENL
   [R5B_PURE_TAC THEN
    W(fun (asl,w) -> C8A_THENM (c8a_inst3 asl (SPECL (`2047` :: `0` :: tl c8a_iter1v_vars) C8A_LOOP1V))) THEN
    R5B_PURE_TAC THEN
    W(fun (asl,w) -> C8A_THEN (c8a_inst3 asl (INST [c8a_Lf `2048`, `L:(num->int32)list`] (SPEC_ALL C8A_T2)))) THEN C8A_SAMEPOST;
    R5B_PURE_TAC THEN
    W(fun (asl,w) -> REWRITE_TAC[FST; r5b_inst2 asl (SPEC_ALL c8a_cap1)]) THEN
    W(fun (asl,w) -> C8A_THENM (c8a_inst3 asl (INST [`[]:(num->int32)list`, `L:(num->int32)list`] (SPEC_ALL C8A_T2)))) THEN
    C8A_SAMEPOST]);;
let VA1_BORN_SHAPE = prove(`!mdl hp tbl t ra rb zq zp nd. val nd <= 16384
    ==> ALL (\r. r 6 = word_add t (word 1) /\ r 10 = word 0 /\ r 11 = word 0) (va1_born mdl hp tbl t ra rb zq zp nd) /\
        val nd + LENGTH (va1_born mdl hp tbl t ra rb zq zp nd) <= 16384`, ACCEPT_TAC VA1_BORN_SHAPE);;
let VA1_BIRTH_EQ_OK = prove(`va1_birth_eq ==> va1_birth_ok`, ACCEPT_TAC VA1_BIRTH_EQ_OK);;
let VA1_FOLD1_CLAUSES = prove(`(!mdl hp tbl t rb nd0 st. va1_fold1 mdl hp tbl t rb nd0 0 st = st) /\
  (!mdl hp tbl t rb nd0 k st. va1_fold1 mdl hp tbl t rb nd0 (SUC k) st =
       va1_step1 mdl hp tbl t rb nd0 k (va1_fold1 mdl hp tbl t rb nd0 k st))`, REWRITE_TAC[va1_fold1]);;
let VA1_FOLD2_CLAUSES = prove(`(!mdl hp tbl t rb nd0 L. va1_fold2 mdl hp tbl t rb nd0 0 L = L) /\
  (!mdl hp tbl t rb nd0 k L. va1_fold2 mdl hp tbl t rb nd0 (SUC k) L =
       va1_step2 mdl hp tbl t rb nd0 k (va1_fold2 mdl hp tbl t rb nd0 k L))`, REWRITE_TAC[va1_fold2]);;
let VA1_FOLD3_CLAUSES = prove(`(!mdl hp tbl t ra rb nd0 L. va1_fold3 mdl hp tbl t ra rb nd0 0 L = L) /\
  (!mdl hp tbl t ra rb nd0 k L. va1_fold3 mdl hp tbl t ra rb nd0 (SUC k) L =
       va1_step3 mdl hp tbl t ra rb nd0 k (va1_fold3 mdl hp tbl t ra rb nd0 k L))`, REWRITE_TAC[va1_fold3]);;
let VA1_F13_ENTRY = prove(`wasm_entry va1_f13_mc = SOME 13`, ACCEPT_TAC VA1_F13_ENTRY);;
let VA1_PUSH_CLAUSES = prove(parse_term pop_spec_VA1_PUSH_CLAUSES, REWRITE_TAC[va1_push]);;
