(* ========================================================================= *)
(* Vortex Echo v1 control on the exact bytes of vortex/core/ve_core.wasm     *)
(* (sha256 72fe0ba2): the named premise ve_vk_ok as merged in PR #72 is      *)
(* unsatisfiable. ve_vk_ok_pc3 (ve_vk_pc3_defs.ml) is that definition        *)
(* verbatim apart from the name. It starts the prefix of ve_vort_apply at    *)
(* pc 3, inside the local declarations: byte 3 decodes as nop and byte 4 as  *)
(* i64.mul, which has no operands on the empty stack, so the state at pc 4   *)
(* has no successor and never reaches pc 1305.                               *)
(*                                                                           *)
(* VE_VK_OK_PC3_UNSAT: no VK satisfies ve_vk_ok_pc3. Proof: an explicit      *)
(* state S3 (writes over ARB) with N = 1 and the model / VA / VB read from   *)
(* S3 meets the precondition; its only successor S4 (pc 4) is stuck, and     *)
(* neither is at pc 1305.                                                    *)
(* ========================================================================= *)

needs "ve_vort_code.ml";;
needs "ve_vk_pc3_defs.ml";;
needs "ve_vk_pc3_stmts.ml";;

(* the decode window pc 3 .. 5 of ve_vort_apply (inside the local declarations) *)
let VK_PC3_EXEC = FAST_MK_EXEC_RANGES ve_vort_apply_mc [3, 5];;

(* a state S3 at pc 3 with model word 1 = 1 (writes over ARB), and S4 = S3 with pc 4 *)
let vk_s3 = `write wpc (word 3) (write wcode ve_vort_apply_mc (write wstatus WRunning
   (write wstack [] (write wlabels [] (write warity 0 (write wmemsize 2097152
   (write (wmem :> bytes32 (word 16644)) (word 1:int32) (ARB:wasmstate))))))))`;;
let vk_s4 = mk_comb(mk_comb(mk_comb(`write:(wasmstate,int64)component->int64->wasmstate->wasmstate`, `wpc`), `word 4:int64`), vk_s3);;

let VK_READS_CONV = DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV;;

let VK_S3_READS = prove
 (subst [vk_s3,`s3:wasmstate`]
  `read wpc s3 = word 3 /\ read wcode s3 = ve_vort_apply_mc /\ read wstatus s3 = WRunning /\
   read wstack s3 = [] /\ read wlabels s3 = [] /\ read warity s3 = 0 /\ read wmemsize s3 = 2097152 /\
   read (wmem :> bytes32 (word 16644)) s3 = word 1`,
  REPEAT CONJ_TAC THEN CONV_TAC(LAND_CONV VK_READS_CONV) THEN REWRITE_TAC[]);;

let VK_S4_READS = prove
 (subst [vk_s4,`s4:wasmstate`]
  `read wpc s4 = word 4 /\ read wcode s4 = ve_vort_apply_mc /\ read wstatus s4 = WRunning /\
   read wstack s4 = []`,
  REPEAT CONJ_TAC THEN CONV_TAC(LAND_CONV VK_READS_CONV) THEN REWRITE_TAC[]);;

(* byte 3 is a nop: the only successor of S3 is S4 *)
let VK_STEP3 = WASM_CONV (snd VK_PC3_EXEC) [] (CONJUNCTS VK_S3_READS)
   (mk_comb(mk_comb(`wasm`, vk_s3), `s':wasmstate`));;

(* byte 4 is i64.mul, with no operands on the empty stack: S4 has no successor *)
let VK_STEP4 = WASM_CONV (snd VK_PC3_EXEC) [] (CONJUNCTS VK_S4_READS)
   (mk_comb(mk_comb(`wasm`, vk_s4), `s':wasmstate`));;


(* no state that is not a final state and has no successor eventually satisfies P; *)
(* one deterministic step from a non-final state to such a state does not either   *)
let VK_EV_TWO = prove
 (`!P (s:wasmstate) s1.
     ~(P s) /\ (!s'. wasm s s' <=> s1 = s') /\ ~(P s1) /\ (!s'. ~(wasm s1 s'))
     ==> ~(eventually wasm P s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(eventually wasm P (s1:wasmstate))` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[eventually_CASES] THEN ASM_REWRITE_TAC[EXISTS_SIMP]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[eventually_CASES] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FORALL_UNWIND_THM1] THEN ASM_REWRITE_TAC[]);;

(* the model, VA and VB of the counterexample are the words of S3 *)
let vk_mdl3 = subst [vk_s3,`s3:wasmstate`] `\k. read (wmem :> bytes32 (word (16640 + 4 * k))) s3:int32`;;
let vk_va3 = subst [vk_s3,`s3:wasmstate`] `\m. read (wmem :> bytes32 (word (1114112 + 4 * m))) s3:int32`;;
let vk_vb3 = subst [vk_s3,`s3:wasmstate`] `\m. read (wmem :> bytes32 (word (1122304 + 4 * m))) s3:int32`;;

let VE_VK_OK_PC3_UNSAT = prove
 (parse_term ve_spec_VE_VK_OK_PC3_UNSAT,
  GEN_TAC THEN REWRITE_TAC[ve_vk_ok_pc3] THEN
  DISCH_THEN(MP_TAC o SPECL [`1`; vk_mdl3; vk_va3; vk_vb3] o CONJUNCT1) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[VK_S3_READS; ensures] THEN
  DISCH_THEN(MP_TAC o SPEC vk_s3) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[VK_S3_READS] THEN
  MATCH_MP_TAC VK_EV_TWO THEN EXISTS_TAC vk_s4 THEN REPEAT CONJ_TAC THENL
   [CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[VK_S3_READS] THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[];
    REWRITE_TAC[VK_STEP3];
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[VK_S4_READS] THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[];
    REWRITE_TAC[VK_STEP4]]);;
