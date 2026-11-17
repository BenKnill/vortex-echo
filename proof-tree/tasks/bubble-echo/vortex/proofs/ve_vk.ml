(* ========================================================================= *)
(* Vortex Echo v1: the field phase of the vortex export pair ve_vort_apply / *)
(* ve_vort_unapply on the exact bytes of vortex/core/ve_core.wasm (sha256    *)
(* 72fe0ba2; bindings in ve_vort_code.ml, decode windows pc 21 .. 1305 in    *)
(* ve_vk_code.ml).                                                            *)
(*                                                                           *)
(* VE_VK_OK: the named premise ve_vk_ok of ve_vort.ml holds for the explicit *)
(* field function ve_vk (ve_vk_defs.ml). Each prefix, run from its first     *)
(* instruction (pc 21) with N = 1 .. 640, reaches pc 1305 without trap with  *)
(* VD = ve_vk(model, source), leaving the model, VA and VB unchanged and     *)
(* writing only locals and scratch. Proof: four segments per export (see     *)
(* ve_vk_tacs.ml), composed with the frame lemma VK_ENSURES_SEG. Segments    *)
(* 2-4 (pc 266 .. 1305, the same bytes in both bodies) are proved once for a *)
(* code variable under its decode facts and instantiated for each export by *)
(* that export's decode theorems; segment 1 (it reads VB or VA) per export. *)
(* Corollaries without premise: VE_VORT_APPLY_CORRECT_VK,                    *)
(* VE_VORT_UNAPPLY_CORRECT_VK, VE_VORT_INVERSE_VK, VE_VORT_STEPS_INVERSE_VK. *)
(* Witnesses of the model-level named premises: VE_LOG_OK_SAT,               *)
(* VE_RUN_OK_SAT.                                                             *)
(* ========================================================================= *)

needs "ve_vort.ml";;
needs "ve_vk_tacs.ml";;
needs "ve_vk_stmts.ml";;

(* ------------------------------------------------------------------------- *)
(* The segments of both exports (the prefixes differ only in the source base *)
(* of the three loads of the normalisation loop: VB 1122304 for apply, VA    *)
(* 1114112 for unapply).                                                      *)
(* ------------------------------------------------------------------------- *)


let VK_E2_GEN = vk_gen_prove (vk_e2_stmt vk_mcv) (VK_E2_TAC vk_mcv VK_GEN_EXEC);;
let VK_SEG4_GEN = vk_gen_prove (vk_seg4_stmt vk_mcv)
  (VK_SEG4_TAC vk_mcv VK_GEN_EXEC (UNDISCH VK_E2_GEN));;
let VK_B2_GEN = vk_gen_prove (vk_b2_stmt vk_mcv) (VK_B2_TAC vk_mcv VK_GEN_EXEC);;
let VK_SEG2_GEN = vk_gen_prove (vk_seg2_stmt vk_mcv)
  (VK_SEG2_TAC vk_mcv VK_GEN_EXEC (UNDISCH VK_B2_GEN));;
let VK_SEG3_GEN = vk_gen_prove (vk_seg3_stmt vk_mcv) (VK_SEG3_TAC vk_mcv VK_GEN_EXEC);;

let VK_SEG4_APPLY = vk_inst_code `ve_vort_apply_mc` VE_VK_APPLY_EXEC VK_SEG4_GEN;;
let VK_SEG4_UNAPPLY = vk_inst_code `ve_vort_unapply_mc` VE_VK_UNAPPLY_EXEC VK_SEG4_GEN;;
let VK_SEG2_APPLY = vk_inst_code `ve_vort_apply_mc` VE_VK_APPLY_EXEC VK_SEG2_GEN;;
let VK_SEG2_UNAPPLY = vk_inst_code `ve_vort_unapply_mc` VE_VK_UNAPPLY_EXEC VK_SEG2_GEN;;
let VK_SEG3_APPLY = vk_inst_code `ve_vort_apply_mc` VE_VK_APPLY_EXEC VK_SEG3_GEN;;
let VK_SEG3_UNAPPLY = vk_inst_code `ve_vort_unapply_mc` VE_VK_UNAPPLY_EXEC VK_SEG3_GEN;;

let VK_SEG1_APPLY = prove(vk_seg1_stmt `ve_vort_apply_mc` `1122304`,
  VK_SEG1_TAC `ve_vort_apply_mc` `1122304` VE_VK_APPLY_EXEC);;
let VK_SEG1_UNAPPLY = prove(vk_seg1_stmt `ve_vort_unapply_mc` `1114112`,
  VK_SEG1_TAC `ve_vort_unapply_mc` `1114112` VE_VK_UNAPPLY_EXEC);;


(* ------------------------------------------------------------------------- *)
(* The named premise holds for ve_vk, and the corollaries without premise.   *)
(* ------------------------------------------------------------------------- *)

let VE_VK_OK = prove
 (parse_term ve_spec_VE_VK_OK,
  REWRITE_TAC[ve_vk_ok] THEN CONJ_TAC THENL
   [VK_EXPORT_TAC `vb:num->int32` VK_SEG1_APPLY VK_SEG2_APPLY VK_SEG3_APPLY VK_SEG4_APPLY;
    VK_EXPORT_TAC `va:num->int32` VK_SEG1_UNAPPLY VK_SEG2_UNAPPLY VK_SEG3_UNAPPLY VK_SEG4_UNAPPLY]);;

let VE_VK_OK_SAT = prove
 (parse_term ve_spec_VE_VK_OK_SAT,
  EXISTS_TAC `ve_vk` THEN ACCEPT_TAC VE_VK_OK);;

let VE_VORT_APPLY_CORRECT_VK = prove
 (parse_term ve_spec_VE_VORT_APPLY_CORRECT_VK,
  MP_TAC(MATCH_MP VE_VORT_APPLY_CORRECT VE_VK_OK) THEN REWRITE_TAC[]);;

let VE_VORT_UNAPPLY_CORRECT_VK = prove
 (parse_term ve_spec_VE_VORT_UNAPPLY_CORRECT_VK,
  MP_TAC(MATCH_MP VE_VORT_UNAPPLY_CORRECT VE_VK_OK) THEN REWRITE_TAC[]);;

let VE_VORT_INVERSE_VK = prove
 (parse_term ve_spec_VE_VORT_INVERSE_VK,
  MP_TAC(MATCH_MP VE_VORT_INVERSE VE_VK_OK) THEN REWRITE_TAC[]);;

let VE_VORT_STEPS_INVERSE_VK = prove
 (parse_term ve_spec_VE_VORT_STEPS_INVERSE_VK,
  REWRITE_TAC[FREDKIN_STEPS_INVERSE]);;

let VE_ISQ_CLAUSES = prove
 (parse_term ve_spec_VE_ISQ_CLAUSES, REWRITE_TAC[ve_isq]);;
let VE_VK_RS_CLAUSES = prove
 (parse_term ve_spec_VE_VK_RS_CLAUSES, REWRITE_TAC[ve_vk_rs]);;
let VE_VK_ACC_CLAUSES = prove
 (parse_term ve_spec_VE_VK_ACC_CLAUSES, REWRITE_TAC[ve_vk_acc]);;

(* satisfiability witnesses of the model-level named premises *)
let vk_zbs = `((\m. word 0),(\m. word 0),(\m. word 0),(\m. word 0),0,(\i. ve_zrec))
   :(num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))`;;
let VE_LOG_OK_SAT = prove
 (parse_term ve_spec_VE_LOG_OK_SAT,
  REWRITE_TAC[ve_log_ok; ve_free; ve_cnt; ve_slots; ve_dq; ve_dp; FST; SND; LT; LE_0]);;
let vk_zs = `(0,1,(\m. word 0),(\m. word 0),(\m. word 0),(\m. word 0),(\m. word 0),(\m. word 0),(\m. word 0),
   (\m. word 0),(\m. word 0),(\m. word 0),(\m. word 0),0,(\i. ve_zrec))
   :num#num#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#
    (num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))`;;
let VE_RUN_OK_SAT = prove
 (parse_term ve_spec_VE_RUN_OK_SAT,
  EXISTS_TAC vk_zs THEN
  SUBGOAL_THEN (mk_comb(`ve_run_ok`, vk_zs)) (fun th -> REWRITE_TAC[th; MATCH_MP VE_RUN_OK_STEP_OK th]) THEN
  MATCH_MP_TAC VE_RUN_OK_INIT THEN
  REWRITE_TAC[ve_t; ve_pt; ve_pop_zero; ve_hm; ve_ra; ve_rb; ve_jq; ve_jp; ve_bs; FST; SND] THEN ARITH_TAC);;
