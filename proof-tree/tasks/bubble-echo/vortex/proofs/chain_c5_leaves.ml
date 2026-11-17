(* ========================================================================= *)
(* Vortex chain rung C5 part 1 "leaves" (lane vortex-chain-20261111-142342   *)
(* c5, Claude Opus 5.5, 2026-11-13): the trunc guard, f32 (sin/cos) and f34  *)
(* (frame) of vortex_a1.wasm, on hol-hearth 6adb41ce's wasm profile (H1     *)
(* exact float compares and trunc). Spec chain_c5_leaves.spec. Statements    *)
(* are filled from the spec by c5/spec/asm_leaves.py. Stable layer: never   *)
(* edit (new files get new names).                                           *)
(* ========================================================================= *)

needs "chain_c5_tacs.ml";;

let VA1_C5_WDECL_VALS_CLAUSES = prove
 (`(!code pc. wdecl_vals 0 (code:byte list) pc = SOME ([]:wval list)) /\
  (!k code pc. wdecl_vals (SUC k) code pc =
     wobind (wuleb (wdrop pc code)) (\p.
     wobind (whd (wdrop (pc + SND p) code)) (\t.
     wobind (wdecl_vals k code (pc + SND p + 1)) (\r.
       SOME (APPEND (REPLICATE (FST p) (wzero_of (val (t:byte)))) r)))))`,
  REWRITE_TAC[wdecl_vals]);;

(* ---- the trunc guard: proofs verbatim from hol-hearth 6adb41ce wasm/demos/f64_guard.ml ---- *)
let VA1_F64G_MAG_LT = prove
 (`!E Fr. E <= 1085 /\ Fr < 4503599627370496
         ==> (if 1075 <= (if E = 0 then 1 else E)
              then (if E = 0 then Fr else Fr + 4503599627370496) *
                   2 EXP ((if E = 0 then 1 else E) - 1075)
              else (if E = 0 then Fr else Fr + 4503599627370496) DIV
                   2 EXP (1075 - (if E = 0 then 1 else E))) < 9223372036854775808`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `sig = if E = 0 then Fr else Fr + 4503599627370496` THEN
  SUBGOAL_THEN `sig < 9007199254740992` ASSUME_TAC THENL
   [EXPAND_TAC "sig" THEN COND_CASES_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `ee = if E = 0 then 1 else E` THEN
  SUBGOAL_THEN `ee <= 1085` ASSUME_TAC THENL
   [EXPAND_TAC "ee" THEN COND_CASES_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [TRANS_TAC LET_TRANS `sig * 2 EXP 10` THEN CONJ_TAC THENL
     [REWRITE_TAC[LE_MULT_LCANCEL; LE_EXP] THEN ASM_ARITH_TAC;
      CONV_TAC(ONCE_DEPTH_CONV NUM_RED_CONV) THEN ASM_ARITH_TAC];
    TRANS_TAC LET_TRANS `sig:num` THEN REWRITE_TAC[DIV_LE] THEN ASM_ARITH_TAC]);;

let VA1_F64G_SPLIT = prove
 (`!x. x MOD 9223372036854775808 =
       ((x DIV 4503599627370496) MOD 2048) * 4503599627370496 + x MOD 4503599627370496`,
  GEN_TAC THEN
  MP_TAC(SPECL [`x MOD 9223372036854775808`; `4503599627370496`] DIVISION) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_RED_CONV) THEN
  REWRITE_TAC[ARITH_RULE `9223372036854775808 = 4503599627370496 * 2048`] THEN
  REWRITE_TAC[GSYM DIV_MOD] THEN
  REWRITE_TAC[ARITH_RULE `4503599627370496 * 2048 = 2 EXP 52 * 2 EXP 11`] THEN
  REWRITE_TAC[GSYM EXP_ADD; ARITH_RULE `4503599627370496 = 2 EXP 52`; MOD_MOD_EXP_MIN] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_RED_CONV) THEN ARITH_TAC);;

let VA1_F64_TRUNC_GUARD = prove
 (`!v:int64. wfrel 99 (word_and v (word 9223372036854775807)) (word 4890909195324358656)
             ==> ~wftrap 176 v`,
  GEN_TAC THEN
  SUBGOAL_THEN `val(word_and v (word 9223372036854775807):int64) = val(v:int64) MOD 9223372036854775808`
    ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `9223372036854775807 = 2 EXP 63 - 1`; VAL_WORD_AND_MASK_WORD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_RED_CONV) THEN REFL_TAC; ALL_TAC] THEN
  REWRITE_TAC[wfrel; wftrap; wf_nan; wf_inf; wf_key; wf_trunc; wf_mag; wf_exp; wf_frac; wf_sign;
              wf_ebits; wf_fbits; wf_tlo; wf_thi; wf_tbits; wf_tidx; DIMINDEX_64] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV ORELSEC INT_RED_CONV)) THEN
  ABBREV_TAC `x = val(v:int64)` THEN
  SUBGOAL_THEN `x < 18446744073709551616` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN MP_TAC(ISPEC `v:int64` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `E = (x DIV 4503599627370496) MOD 2048` THEN
  ABBREV_TAC `Fr = x MOD 4503599627370496` THEN
  SUBGOAL_THEN `x MOD 9223372036854775808 = E * 4503599627370496 + Fr` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["E"; "Fr"] THEN REWRITE_TAC[VA1_F64G_SPLIT]; ALL_TAC] THEN
  SUBGOAL_THEN `E < 2048 /\ Fr < 4503599627370496` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["E"; "Fr"] THEN REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(E * 4503599627370496 + Fr) DIV 4503599627370496 = E /\
                (E * 4503599627370496 + Fr) MOD 4503599627370496 = Fr /\
                (E * 4503599627370496 + Fr) DIV 9223372036854775808 = 0 /\
                (E * 4503599627370496 + Fr) MOD 9223372036854775808 = E * 4503599627370496 + Fr`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `Fr:num` THEN ASM_ARITH_TAC;
      MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `E:num` THEN ASM_ARITH_TAC;
      MATCH_MP_TAC DIV_LT THEN ASM_ARITH_TAC;
      MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `E MOD 2048 = E` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[ARITH_EQ; INT_OF_NUM_LT]) THEN
  SUBGOAL_THEN `E <= 1085` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(E = 2047)` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`E:num`; `Fr:num`] VA1_F64G_MAG_LT) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN COND_CASES_TAC THEN INT_ARITH_TAC);;

let va1_trunc_guard_ok = new_definition
 `va1_trunc_guard_ok <=>
    !v:int64. wfrel 99 (word_and v (word 9223372036854775807)) (word 4890909195324358656:int64) ==> ~wftrap 176 v`;;

let VA1_TRUNC_GUARD_OK = prove
 (`va1_trunc_guard_ok`,
  REWRITE_TAC[va1_trunc_guard_ok; VA1_F64_TRUNC_GUARD]);;

(* ---- helpers ---- *)
let VA1_C5_WTAKE_0 = prove(`!l:A list. wtake 0 l = []`, LIST_INDUCT_TAC THEN REWRITE_TAC[wtake]);;

let VA1_C5_AND3_CASES = prove
 (`!w:int32. word_and w (word 3) = word 0 \/ word_and w (word 3) = word 1 \/
             word_and w (word 3) = word 2 \/ word_and w (word 3) = word 3`,
  BITBLAST_TAC);;

let C5_ENTRY_TAC =
  REWRITE_TAC[wlocal; READ_COMPONENT_COMPOSE; WCALL_ENTRY_READS; READ_ELEMENT] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[wlocal; READ_COMPONENT_COMPOSE; WCALL_ENTRY_READS; READ_ELEMENT] THEN
  REWRITE_TAC[wcall_locals; wtake; VA1_C5_WTAKE_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[wtake; VA1_C5_WTAKE_0; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EL_CONS; HD; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[EL_CONS; HD];;

(* ---- f32: guard split + join at pc 100, then the 4-way br_table ---- *)
let VA1_F32_CORRECT = prove
 (`!x k. ensures wasm
 (\s. read wcode s = va1_f32_mc /\ read wpc s = word 5 /\ read wstatus s = WRunning /\
      read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
      read (wlocal 0) s = F64 x /\ read (wlocal 1) s = I32 k)
 (\s. read wstatus s = WDone /\ ?r. read wstack s = [F64 r])
 (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
  MAYCHANGE [wlocal 0; wlocal 2; wlocal 3])`,
  REPEAT GEN_TAC THEN
  WASM_F64_JOIN_TAC `100`
   `\s. read wcode s = va1_f32_mc /\ read wstatus s = WRunning /\
        read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
        read (wlocal 1) s = I32 k /\ (?a. read (wlocal 0) s = F64 a) /\
        (?b. read (wlocal 2) s = F64 b) /\ (?n. read (wlocal 3) s = I64 n)` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN WASM_STEPS_TAC C5_F32_EXEC (1--22) THEN
    WASM_F64_CASES_TAC THENL
     [WASM_STEPS_TAC C5_F32_EXEC (23--25) THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP VA1_F64_TRUNC_GUARD) THEN
      WASM_STEPS_TAC C5_F32_EXEC (26--28);
      WASM_STEPS_TAC C5_F32_EXEC (23--27)] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN REPEAT(FIRST_X_ASSUM(CHOOSE_TAC o check (is_exists o concl))) THEN
  WASM_STEPS_TAC C5_F32_EXEC (1--14) THEN
  MP_TAC(ISPEC `word_add k (word_zx (n:int64)):int32` VA1_C5_AND3_CASES) THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN MP_TAC th)) ORELSE
         DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))) THENL
  [WASM_STEPS_TAC C5_F32_EXEC (15--43); WASM_STEPS_TAC C5_F32_EXEC (15--47);
   WASM_STEPS_TAC C5_F32_EXEC (15--44); WASM_STEPS_TAC C5_F32_EXEC (15--48)] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let VA1_F32_ENTRY = prove
 (`!x k rest s.
     (\s. read wcode s = va1_f32_mc /\ read wpc s = word 5 /\ read wstatus s = WRunning /\
      read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
      read (wlocal 0) s = F64 x /\ read (wlocal 1) s = I32 k)
     (wcall_entry va1_f32_mc 2 1 (CONS (I32 k) (CONS (F64 x) rest)) 5 [F64 (word 0); I64 (word 0)] s)`,
  C5_ENTRY_TAC);;

let VA1_F32_PRE_SAT = prove
 (`!x k. ?s:wasmstate. (\s. read wcode s = va1_f32_mc /\ read wpc s = word 5 /\ read wstatus s = WRunning /\
      read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
      read (wlocal 0) s = F64 x /\ read (wlocal 1) s = I32 k) s`,
  REPEAT GEN_TAC THEN
  EXISTS_TAC `wcall_entry va1_f32_mc 2 1 (CONS (I32 k) (CONS (F64 x) [])) 5
                [F64 (word 0); I64 (word 0)] (ARB:wasmstate)` THEN
  REWRITE_TAC[VA1_F32_ENTRY]);;

(* ---- f34: one wfrel split before the selects, straight line ---- *)
let VA1_F34_CORRECT = prove
 (`ensures wasm
 (\s. read wcode s = va1_f34_mc /\ read wpc s = word 7 /\ read wstatus s = WRunning /\
      read wstack s = [] /\ read wlabels s = [] /\ read warity s = 0 /\ read wmemsize s = 4194304 /\
      read (wlocal 0) s = I32 (word 16352) /\ read (wlocal 1) s = I32 (word 16320) /\
      read (wlocal 2) s = I32 (word 16288))
 (\s. read wstatus s = WDone /\ read wstack s = [])
 (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
  MAYCHANGE [wlocal 3; wlocal 4; wlocal 5; wlocal 6; wlocal 7; wlocal 8; wlocal 9] ,,
  MAYCHANGE [wmem :> bytes64 (word 16320)] ,, MAYCHANGE [wmem :> bytes64 (word 16328)] ,,
  MAYCHANGE [wmem :> bytes64 (word 16336)] ,, MAYCHANGE [wmem :> bytes64 (word 16288)] ,,
  MAYCHANGE [wmem :> bytes64 (word 16296)] ,, MAYCHANGE [wmem :> bytes64 (word 16304)])`,
  ENSURES_INIT_TAC "s0" THEN WASM_STEPS_TAC C5_F34_EXEC (1--10) THEN WASM_F64_CASES_TAC THEN
  WASM_STEPS_TAC C5_F34_EXEC (11--104) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

let VA1_F34_ENTRY = prove
 (`!rest s. read wmemsize s = 4194304 ==>
     (\s. read wcode s = va1_f34_mc /\ read wpc s = word 7 /\ read wstatus s = WRunning /\
      read wstack s = [] /\ read wlabels s = [] /\ read warity s = 0 /\ read wmemsize s = 4194304 /\
      read (wlocal 0) s = I32 (word 16352) /\ read (wlocal 1) s = I32 (word 16320) /\
      read (wlocal 2) s = I32 (word 16288))
     (wcall_entry va1_f34_mc 3 0
        (CONS (I32 (word 16288)) (CONS (I32 (word 16320)) (CONS (I32 (word 16352)) rest))) 7
        [F64 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0)] s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C5_ENTRY_TAC THEN ASM_REWRITE_TAC[]);;

let VA1_F34_PRE_SAT = prove
 (`?s:wasmstate. (\s. read wcode s = va1_f34_mc /\ read wpc s = word 7 /\ read wstatus s = WRunning /\
      read wstack s = [] /\ read wlabels s = [] /\ read warity s = 0 /\ read wmemsize s = 4194304 /\
      read (wlocal 0) s = I32 (word 16352) /\ read (wlocal 1) s = I32 (word 16320) /\
      read (wlocal 2) s = I32 (word 16288)) s`,
  EXISTS_TAC `wcall_entry va1_f34_mc 3 0
     (CONS (I32 (word 16288)) (CONS (I32 (word 16320)) (CONS (I32 (word 16352)) []))) 7
     [F64 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0)]
     (write wmemsize 4194304 (ARB:wasmstate))` THEN
  MATCH_MP_TAC VA1_F34_ENTRY THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN REWRITE_TAC[]);;
