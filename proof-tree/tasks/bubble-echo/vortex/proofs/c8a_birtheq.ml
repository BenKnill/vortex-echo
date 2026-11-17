(* vortex-chain C8a (Claude Opus 5.5, 2026-11-15): VA1_BIRTH_EQ as a stage lemma (verbatim the proof of the A7 leaf
   c8a_birth_final.ml, receipt runs/20261115T182425Z-3029081-c8a_birth_final-0d47d0), for the A9 layers on C8b s2. *)
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
