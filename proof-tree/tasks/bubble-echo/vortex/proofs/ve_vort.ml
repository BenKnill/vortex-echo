(* ========================================================================= *)
(* Vortex Echo v1: the vortex Fredkin export pair ve_vort_apply /            *)
(* ve_vort_unapply on the exact bytes of vortex/core/ve_core.wasm (sha256   *)
(* 72fe0ba2; bindings in ve_vort_code.ml, decode window pc 1305 .. end).     *)
(*                                                                           *)
(* VE_VORT_APPLY_LOOP_CORRECT / VE_VORT_UNAPPLY_LOOP_CORRECT: the Fredkin    *)
(* loop of each body (pc 1305 to the end), unconditionally, for N = 1..640   *)
(* (model word 1): apply VA' = VB, VB' = VD + VA; unapply VA' = VB - VD,     *)
(* VB' = VA (m < 3N), no trap.                                               *)
(* VE_VORT_APPLY_CORRECT / VE_VORT_UNAPPLY_CORRECT (and the _FREDKIN forms   *)
(* in terms of ve_fredkin_fwd / ve_fredkin_bwd of ve_generic_defs.ml): the   *)
(* whole exports from their entry, under the NAMED premise ve_vk_ok VK       *)
(* (ve_vort_defs.ml: the field phase pc 21..1305 leaves VD = VK(model,       *)
(* source)), composed with the loop theorems.                                *)
(* VE_VORT_INVERSE: unapply on the state apply leaves restores VA and VB, an *)
(* instance of FREDKIN_STEP_INVERSE. VE_VORT_STEPS_INVERSE: n substeps with  *)
(* this VK, an instance of FREDKIN_STEPS_INVERSE (model level).             *)
(* ========================================================================= *)

needs "ve_vort_code.ml";;
needs "../../capillary/proofs/cap_helpers.ml";;
needs "ve_generic.ml";;
needs "ve_vort_defs.ml";;
needs "ve_vort_tacs.ml";;
needs "ve_vort_stmts.ml";;

let VE_VORT_APPLY_LOOP_CORRECT = prove
 (parse_term ve_spec_VE_VORT_APPLY_LOOP_CORRECT,
  VORT_TAC `ve_vort_apply_mc` VE_VORT_APPLY_EXEC `1122304` `1114112`
    `\m:num. word_add ((vd:num->int32) m) ((va:num->int32) m)` `vb:num->int32`
    `vb:num->int32` `va:num->int32`);;

let VE_VORT_UNAPPLY_LOOP_CORRECT = prove
 (parse_term ve_spec_VE_VORT_UNAPPLY_LOOP_CORRECT,
  VORT_TAC `ve_vort_unapply_mc` VE_VORT_UNAPPLY_EXEC `1114112` `1122304`
    `\m:num. word_sub ((vb:num->int32) m) ((vd:num->int32) m)` `va:num->int32`
    `va:num->int32` `vb:num->int32`);;

(* compose the premise's prefix (selected conjunct of ve_vk_ok) with a loop  *)
(* theorem (instantiated at vd = VK mdl source), then weaken to the stated   *)
(* postcondition (close with post_tac) and frame.                            *)
let VE_VORT_COMPOSE_TAC sel loopth src post_tac =
  GEN_TAC THEN DISCH_THEN(MP_TAC o sel o REWRITE_RULE[ve_vk_ok]) THEN
  DISCH_THEN(fun pth ->
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`N:num`; `mdl:num->int32`; `va:num->int32`; `vb:num->int32`] pth) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`N:num`; `va:num->int32`; `vb:num->int32`;
                  mk_comb(`(VK:(num->int32)->(num->int32)->num->int32) mdl`, src)] loopth) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
  (fun (asl,w) ->
     let th2 = snd(hd asl) and th1 = snd(hd(tl asl)) in
     let _,[_;_;q1;_] = strip_comb(concl th1) in
     let _,[_;p2;r2;_] = strip_comb(concl th2) in
     let x = `s:wasmstate` in
     let pimp = TAC_PROOF((asl, mk_forall(x, mk_imp(mk_comb(q1,x), mk_comb(p2,x)))),
       X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
       ASM_REWRITE_TAC[] THEN
       FIRST_X_ASSUM(fun th -> if can (find_term ((=) `16640`)) (concl th)
                               then MP_TAC(SPEC `1` th) else NO_TAC) THEN
       CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[]) in
     let th2a = MATCH_MP ENSURES_PRECONDITION_THM (CONJ pimp th2) in
     let th12 = MATCH_MP ENSURES_TRANS (CONJ th1 th2a) in
     (MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC (rand(concl th12)) THEN
      CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC r2 THEN CONJ_TAC THENL
       [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
        (X_GEN_TAC `m:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN post_tac);
        ACCEPT_TAC th12]) (asl,w));;

let VE_VORT_APPLY_CORRECT = prove
 (parse_term ve_spec_VE_VORT_APPLY_CORRECT,
  VE_VORT_COMPOSE_TAC CONJUNCT1 VE_VORT_APPLY_LOOP_CORRECT `vb:num->int32`
    (REWRITE_TAC[WORD_ADD_SYM]));;

let VE_VORT_UNAPPLY_CORRECT = prove
 (parse_term ve_spec_VE_VORT_UNAPPLY_CORRECT,
  VE_VORT_COMPOSE_TAC CONJUNCT2 VE_VORT_UNAPPLY_LOOP_CORRECT `va:num->int32` ALL_TAC);;

let VE_VORT_APPLY_FREDKIN = prove
 (parse_term ve_spec_VE_VORT_APPLY_FREDKIN,
  REWRITE_TAC[ve_fredkin_fwd; FST; SND] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[VE_VORT_APPLY_CORRECT]);;

let VE_VORT_UNAPPLY_FREDKIN = prove
 (parse_term ve_spec_VE_VORT_UNAPPLY_FREDKIN,
  REWRITE_TAC[ve_fredkin_bwd; FST; SND] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[VE_VORT_UNAPPLY_CORRECT]);;

(* unapply after apply: the unapply theorem at the state apply leaves, i.e. *)
(* (va', vb') = ve_fredkin_fwd (VK mdl) (va, vb); FREDKIN_STEP_INVERSE      *)
(* turns its postcondition ve_fredkin_bwd (VK mdl) (va', vb') into (va, vb). *)
let VE_VORT_INVERSE = prove
 (parse_term ve_spec_VE_VORT_INVERSE,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `mdl:num->int32`;
                `FST (ve_fredkin_fwd ((VK:(num->int32)->(num->int32)->num->int32) mdl) (va,vb))`;
                `SND (ve_fredkin_fwd ((VK:(num->int32)->(num->int32)->num->int32) mdl) (va,vb))`]
         (MP (SPEC `VK:(num->int32)->(num->int32)->num->int32` VE_VORT_UNAPPLY_FREDKIN)
             (ASSUME `ve_vk_ok (VK:(num->int32)->(num->int32)->num->int32)`))) THEN
  ASM_REWRITE_TAC[PAIR; FREDKIN_STEP_INVERSE] THEN
  REWRITE_TAC[ve_fredkin_fwd; FST; SND] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[]);;

let VE_FREDKIN_FWDN_CLAUSES = VE_FREDKIN_FWDN_CLAUSES;;
let VE_FREDKIN_BWDN_CLAUSES = VE_FREDKIN_BWDN_CLAUSES;;

let VE_VORT_STEPS_INVERSE = prove
 (parse_term ve_spec_VE_VORT_STEPS_INVERSE,
  REWRITE_TAC[FREDKIN_STEPS_INVERSE]);;
