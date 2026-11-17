(* PARKED 2026-10-20 (lead, relaying Ben): the pop is being redesigned, so the  *)
(* droplet leaf is on hold and UNPROVED. State when parked: in sessions the     *)
(* setup, the N = 0 path, the loop entry and the 48 body steps of ve_drop_apply *)
(* went through; the per-cell memory step was not yet run end to end (a THENL  *)
(* arity bug in the cell split was fixed here, untested); back and exit tactics *)
(* untested. No prove run, no receipt.                                          *)
(* ========================================================================= *)
(* Vortex Echo v1: tactics for the droplet export pair ve_drop_apply /      *)
(* ve_drop_unapply of vortex/core/ve_core.wasm (sha256 72fe0ba2), adapted   *)
(* from capillary/proofs/drift_tacs.ml. Body pc map (both exports):          *)
(*   3 block; 5..15 load nd (header word 4, byte 16400), exit if 0;          *)
(*   17..31 local1 := select(nd, 16384, nd <u 16384); 33..38 local0 := DI;  *)
(*   40 loop; 42..135 one record (6 loads, 4 stores); 137 br_if (counter);   *)
(*   139 end loop; 140 end block; 141 end.                                   *)
(* Labels inside the loop: [0,40,0; 0,141,0].                                *)
(* ========================================================================= *)

let VE_MOD12 = prove
 (`!q c. c < 12 ==> (12 * q + c) MOD 12 = c`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT]);;

let VE_MOD12_0 = prove
 (`!q. (12 * q) MOD 12 = 0`,
  GEN_TAC THEN MP_TAC(SPECL [`q:num`; `0`] VE_MOD12) THEN REWRITE_TAC[ADD_CLAUSES; ARITH]);;

let VE_ADDM1 = prove
 (`!x:int32. word_add x (word 4294967295) = word_sub x (word 1)`,
  GEN_TAC THEN BITBLAST_TAC);;

(* ve_drec_fwd / ve_drec_bwd on the cells of record i *)
let VE_DREC_CELLS_TAC fdef =
  REPEAT GEN_TAC THEN REWRITE_TAC[fdef; VE_MOD12_0] THEN
  SIMP_TAC[VE_MOD12; ARITH; GSYM ADD_ASSOC] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VE_MOD12];;

let VE_DREC_FWD_CELLS = prove
 (`!d i. ve_drec_fwd d (12 * i) = word_add (d (12 * i)) (d (12 * i + 3)) /\
         ve_drec_fwd d (12 * i + 1) = word_add (d (12 * i + 1)) (word_sub (d (12 * i + 4)) (word 1)) /\
         ve_drec_fwd d (12 * i + 2) = word_add (d (12 * i + 2)) (d (12 * i + 5)) /\
         ve_drec_fwd d (12 * i + 4) = word_sub (d (12 * i + 4)) (word 1) /\
         (!c. c < 12 /\ ~(c = 0) /\ ~(c = 1) /\ ~(c = 2) /\ ~(c = 4)
              ==> ve_drec_fwd d (12 * i + c) = d (12 * i + c))`,
  VE_DREC_CELLS_TAC ve_drec_fwd);;

let VE_DREC_BWD_CELLS = prove
 (`!d i. ve_drec_bwd d (12 * i) = word_sub (d (12 * i)) (d (12 * i + 3)) /\
         ve_drec_bwd d (12 * i + 1) = word_sub (d (12 * i + 1)) (d (12 * i + 4)) /\
         ve_drec_bwd d (12 * i + 2) = word_sub (d (12 * i + 2)) (d (12 * i + 5)) /\
         ve_drec_bwd d (12 * i + 4) = word_add (d (12 * i + 4)) (word 1) /\
         (!c. c < 12 /\ ~(c = 0) /\ ~(c = 1) /\ ~(c = 2) /\ ~(c = 4)
              ==> ve_drec_bwd d (12 * i + c) = d (12 * i + c))`,
  VE_DREC_CELLS_TAC ve_drec_bwd);;

let ve_drop_inv mc fdef = subst [mc,`MC:byte list`; fdef,`FD:(num->int32)->num->int32`]
 `\i s. read wcode s = MC /\ read wstatus s = WRunning /\
        read wmemsize s = 2097152 /\ read warity s = 0 /\
        read wlabels s = [0,40,0; 0,141,0] /\
        read (wlocal 0) s = I32 (word (1179648 + 48 * i)) /\
        read (wlocal 1) s = I32 (word (N - i)) /\
        read wstack s = (if read wpc s = word 42 then [] else [I32 (word (N - i))]) /\
        (!m. m < 12 * N ==> read (wmem :> bytes32 (word (1179648 + 4 * m))) s =
                            (if m < 12 * i then FD (d:num->int32) m else d m))`;;

let VE_HDR_TAC =
  SUBGOAL_THEN `read (bytes32 (word 16400)) mm = word N` ASSUME_TAC THENL
   [EXPAND_TAC "mm" THEN REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    FIRST_ASSUM ACCEPT_TAC; ALL_TAC];;

let VE_DROP_ZERO_TAC exec =
  ENSURES_INIT_TAC "s0" THEN MEMNAME_TAC THEN VE_HDR_TAC THEN
  CAP_MSTEPS_TAC exec (1--7) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; LT];;

let VE_DROP_ENTRY_TAC exec =
  ENSURES_INIT_TAC "s0" THEN MEMNAME_TAC THEN VE_HDR_TAC THEN
  CAP_MSTEPS_TAC exec (1--16) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LT; SUB_0] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;;

let ve_off k = if k = 0 then `1179648 + 48 * i`
  else mk_binop `(+):num->num->num` `1179648 + 48 * i` (mk_small_numeral (4 * k));;
let ve_idx k = if k = 0 then `12 * i`
  else mk_binop `(+):num->num->num` `12 * i` (mk_small_numeral k);;

(* the six loads of record i, in the address forms the steps produce *)
let VE_LOADFACTS_TAC =
  MAP_EVERY (fun k ->
    let a = ve_off k and j = ve_idx k in
    SUBGOAL_THEN (subst [a,`aa:num`; j,`jj:num`] `read (bytes32 (word aa)) mm = (d:num->int32) jj`)
      ASSUME_TAC THENL
     [SUBGOAL_THEN (subst [a,`aa:num`; j,`jj:num`] `aa = 1179648 + 4 * jj`) SUBST1_TAC THENL
       [ARITH_TAC;
        SUBGOAL_THEN (subst [j,`jj:num`] `jj < 12 * N /\ ~(jj < 12 * i)`) STRIP_ASSUME_TAC THENL
         [ASM_ARITH_TAC; ASM_SIMP_TAC[]]];
      ALL_TAC]) [0;1;2;3;4;5];;

(* loads after stores in one record: every (read cell, written cell) pair *)
let VE_B32O_FACTS_TAC =
  MAP_EVERY (fun (r,w) -> B32O_TAC (ve_off r) (ve_off w))
   (filter (fun (r,w) -> r <> w)
     (allpairs (fun r w -> (r,w)) [0;1;2;3;4;5] [0;1;2;4]));;

let VE_DROP_CELL_TAC cells =
  REPEAT B32_PEEL_TAC THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `!i c. 12 * i + c < 12 * i <=> F`; LT_REFL] THEN
  SIMP_TAC[ARITH_RULE `!i c. c < 12 ==> (12 * i + c < 12 * (i + 1) <=> T)`;
           ARITH_RULE `12 * i < 12 * (i + 1)`; ARITH] THEN
  ASM_SIMP_TAC[cells; VE_ADDM1; ARITH];;

let VE_DROP_BODY_TAC exec cells =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MAP_EVERY (fun k ->
     let t = if k = 0 then `val(word (1179648 + 48 * i):int32) = 1179648 + 48 * i`
       else subst [ve_off k,`aa:num`; mk_small_numeral (4 * k),`kk:num`]
         `val(word_add (word (1179648 + 48 * i)) (word kk):int32) = aa` in
     VAL_TAC t) [0;1;2;3;4;5] THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  VE_LOADFACTS_TAC THEN VE_B32O_FACTS_TAC THEN
  CAP_MSTEPS_TAC exec (1--48) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  ASM_SIMP_TAC[injectivity "wval"; CONS_11; CAP_DEC] THEN
  REPEAT CONJ_TAC THEN TRY(WORD_NUM_EQ_TAC THEN NO_TAC) THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `12 * i <= m /\ m < 12 * i + 12` THENL
     [SUBGOAL_THEN `?c. c < 12 /\ m = 12 * i + c`
        (CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THENL
       [EXISTS_TAC `m - 12 * i` THEN ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `c = 0 \/ c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/
                    c = 8 \/ c = 9 \/ c = 10 \/ c = 11` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
      VE_DROP_CELL_TAC cells;
      REPEAT B32_PEEL_TAC THEN ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN `(m < 12 * (i + 1) <=> m < 12 * i)` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[]]];;

let VE_DROP_BACK_TAC exec =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(word (N - i):int32 = word 0) <=> F` ASSUME_TAC THENL
   [REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN
    SUBGOAL_THEN `val(word (N - i):int32) = N - i` SUBST1_TAC THENL
     [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC;
      REWRITE_TAC[VAL_WORD_0] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  CAP_MSTEPS_TAC exec (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[];;

let VE_DROP_EXIT_TAC exec =
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUB_REFL]) THEN
  CAP_MSTEPS_TAC exec (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[];;

let VE_DROP_TAC mc exec fdef cells =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word N:int32) = N` ASSUME_TAC THENL
   [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `N = 0` THENL [VE_DROP_ZERO_TAC exec; ALL_TAC] THEN
  SUBGOAL_THEN `~(word N:int32 = word 0)` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN ASM_REWRITE_TAC[VAL_WORD_0]; ALL_TAC] THEN
  ENSURES_WHILE_UP_TAC `N:num` `42` `137` (ve_drop_inv mc fdef) THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC; VE_DROP_ENTRY_TAC exec; VE_DROP_BODY_TAC exec cells;
    VE_DROP_BACK_TAC exec; VE_DROP_EXIT_TAC exec];;
