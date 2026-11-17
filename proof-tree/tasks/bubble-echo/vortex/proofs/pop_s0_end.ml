needs "ve_vort.ml";;
needs "ve_tick.ml";;
needs "ve_vk.ml";;
needs "va1_code.ml";;
needs "va1_seq_final2.ml";;
needs "pop_design_defs.ml";;
needs "pop_design_stmts.ml";;
(* ========================================================================= *)
(* Vortex pop effort, segment S0 (rung R0, pop end of run), prover S0       *)
(* (Claude Opus 5.5), 2026-11-11. Statements: pop_design_stmts.ml strings,  *)
(* spec pop_design_r0_end.spec (frozen, sha256 a58767df...).                 *)
(*                                                                           *)
(* tick_forward (f35) of vortex_a1.wasm, once the pop has run out: P set,   *)
(* T >=u P and T >=u P + 520 (wrapping add, as in the bytes). Path: pc 13    *)
(* load P, pc 22 eq -1 (false), pc 27 load T, pc 36 ge_u (true, br_if 1 to   *)
(* pc 133), local 2 := 0, pc 145 ge_u against P + 520 (true, br_if 1 to the  *)
(* outer block end), return local 2 = 0. No call, no store.                  *)
(* No definitions, no parser changes in this file (spec-locked leaf).        *)
(* ========================================================================= *)

(* A step that also rewrites with the state-free hypotheses: the branch     *)
(* tests at pc 22, 36 and 145 need ~(p = -1), val p <= val t and             *)
(* val (p + 520) <= val t; GE turns the stepper output (val t >= ..) into   *)
(* the hypothesis form.                                                      *)
let POP_S0_MSTEP_TAC execth sname (asl,w) =
  let notstate th =
    not (exists (fun v -> type_of v = `:wasmstate`) (frees (concl th))) in
  let mths = filter (fun th -> is_memfact (concl th) || notstate th) (map snd asl) in
  (CAPC_STEP_TAC execth
     (READ_COMPONENT_COMPOSE :: VA1_GTU_MAX :: GE :: BITVAL_CLAUSES :: mths) sname THEN
   CAP_DISCARD_OLD_TAC sname) (asl,w);;

(* step until WDone (this path has no call) *)
let rec POP_S0_RUN_TAC execth : tactic = fun (asl,w) ->
  let s = rand w in
  let ths = map snd asl in
  let is_done = exists (fun th ->
    concl th = mk_eq(mk_comb(`read wstatus`,s),`WDone`)) ths in
  if is_done then ALL_TAC (asl,w) else
  let n = fst(dest_var s) in
  let k = int_of_string(String.sub n 1 (String.length n - 1)) + 1 in
  let sname = "s"^string_of_int k in
  (POP_S0_MSTEP_TAC execth sname THEN POP_S0_RUN_TAC execth) (asl,w);;

let VA1_TICK_FORWARD_POP_END = prove
 (parse_term pop_spec_VA1_TICK_FORWARD_POP_END,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN VA1_MEMNAME_TAC "mm0" THEN
  POP_S0_RUN_TAC VA1_TICK_FORWARD_EXEC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

(* two disjoint 4-byte cells: a bytes32 write leaves the other read alone *)
let POP_S0_B32_B32_OTHER = prove
 (`!a b (y:int32) (m:int64->byte).
     (a + 4 <= b \/ b + 4 <= a) /\ a + 4 < 2 EXP 64 /\ b + 4 < 2 EXP 64
     ==> read (bytes32 (word a)) (write (bytes32 (word b)) y m) =
         read (bytes32 (word a)) m`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC READ_WRITE_ORTHOGONAL_COMPONENTS THEN
  REWRITE_TAC[bytes32] THEN MATCH_MP_TAC ORTHOGONAL_COMPONENTS_SUB_LEFT THEN
  MATCH_MP_TAC ORTHOGONAL_COMPONENTS_SUB_RIGHT THEN
  REWRITE_TAC[ORTHOGONAL_COMPONENTS_BYTES; DIMINDEX_64] THEN
  MATCH_MP_TAC NONOVERLAPPING_MODULO_SIMPLE THEN
  SUBGOAL_THEN `val(word a:int64) = a /\ val(word b:int64) = b`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

(* the R0 precondition memory facts hold together: write T, P and AUTO *)
let VA1_TICK_POP_SAT = prove
 (parse_term pop_spec_VA1_TICK_POP_SAT,
  REPEAT GEN_TAC THEN
  EXISTS_TAC `write (bytes32 (word 16512)) (ap:int32)
               (write (bytes32 (word 16396)) (p:int32)
                 (write (bytes32 (word 16392)) (t:int32) (\a:int64. word 0:byte)))` THEN
  REWRITE_TAC[va1_tick; va1_pop] THEN
  SIMP_TAC[READ_WRITE_VALID_COMPONENT; VALID_COMPONENT_BYTES32;
           POP_S0_B32_B32_OTHER; ARITH]);;

(* the real end state P = 120, T = 640 meets the numeric hypotheses *)
let VA1_POP_END_SAT = prove
 (parse_term pop_spec_VA1_POP_END_SAT,
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;
