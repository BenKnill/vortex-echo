(* ========================================================================= *)
(* Vortex Echo v1: the header tick pair of vortex/core/ve_core.wasm (sha256  *)
(* 72fe0ba2) on the exact bytes. Header word 2 (tick T) is byte 16392       *)
(* (HDR 0x4000 + 8). ve_tick_inc: T := T + 1; ve_tick_dec: T := T - 1       *)
(* (words mod 2^32), nothing else in memory changes; VE_TICK_INVERSE: dec   *)
(* after inc restores T.                                                     *)
(* ========================================================================= *)

needs "ve_tick_code.ml";;
needs "../../capillary/proofs/cap_helpers.ml";;
needs "ve_tick_stmts.ml";;

let VE_TICK_ADDM1 = prove
 (`!x:int32. word_add x (word 4294967295) = word_sub x (word 1)`,
  GEN_TAC THEN BITBLAST_TAC);;

let VE_TICK_TAC exec =
  GEN_TAC THEN ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `read (bytes32 (word 16392)) (read wmem s0) = t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ABBREV_TAC `mm = read wmem (s0:wasmstate)` THEN
  CAP_MSTEPS_TAC exec (1--7) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[CAP_B32_SAME; VE_TICK_ADDM1];;

let VE_TICK_INC_CORRECT = prove
 (parse_term ve_spec_VE_TICK_INC_CORRECT, VE_TICK_TAC VE_TICK_INC_EXEC);;

let VE_TICK_DEC_CORRECT = prove
 (parse_term ve_spec_VE_TICK_DEC_CORRECT, VE_TICK_TAC VE_TICK_DEC_EXEC);;

let VE_TICK_INVERSE = prove
 (parse_term ve_spec_VE_TICK_INVERSE,
  GEN_TAC THEN MP_TAC(SPEC `word_add t (word 1):int32` VE_TICK_DEC_CORRECT) THEN
  REWRITE_TAC[WORD_RULE `word_sub (word_add (t:int32) (word 1)) (word 1) = t`]);;
