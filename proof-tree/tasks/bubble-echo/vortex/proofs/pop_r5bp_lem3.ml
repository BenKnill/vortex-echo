(* ========================================================================= *)
(* Vortex pop R5 droplet birth (vortex-r5birth PROVE-birth r1, Claude Opus   *)
(* 5.5, 2026-11-11): lemma layer 3 on pop_r5bp_lem2.ml: the prologue R5B_PRO  *)
(* 13->146|2612 and the first loop-3 segment R5B_SEGI 4493->4700|6027.       *)
(* ========================================================================= *)
let () = r5b_extra := [VK_COND_I64; VK_COND_I32; R5B_SEL1_NZ; R5B_SPD_NZ; R5B_SHL2; R5B_ADDZQ; R5B_MUL48; R5B_INC1];;
(* 13 -> 146 (loop-1 head, k = 0, n = ND) | 2612 (ND = 16384) *)
let R5B_PRO = prove(list_mk_forall([`m0:int64->byte`;`nd:int32`;`t:int32`],
   mk_imp(`read (bytes32 (word 16400)) (m0:int64->byte) = nd /\ read (bytes32 (word 16392)) m0 = t /\ val (nd:int32) <= 16384`,
    r5b_ens (r5b_pred 13 [] [] [])
     (mk_abs(`s:wasmstate`, mk_disj(
        r5b_body 146 r5b_L1 [0,`word 0:int32`; 1,`word (val (nd:int32)):int32`; 3,`word_add t (word 1):int32`] [`val (nd:int32) < 16384`],
        r5b_body 2612 [] [1,`word (val (nd:int32)):int32`; 3,`word_add t (word 1):int32`] [`val (nd:int32) <= 16384`]))))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(if val (nd:int32) < 16384 then nd else word 16384) = word (val nd) /\
                (if ~(val (nd:int32) < 16384) then word 16384 else nd) = word (val nd)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[WORD_VAL] THEN CONJ_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `val (nd:int32) = 16384` (fun th -> REWRITE_TAC[GSYM th; WORD_VAL]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  R5B_INIT_TAC THEN r5b_time "pro" (R5B_RUN R5B_EXEC [146; 2612]) THEN ENSURES_FINAL_STATE_TAC THEN
  FIRST [DISJ1_TAC THEN R5B_CLOSE_TAC THEN REWRITE_TAC[WORD_VAL] THEN TRY(REPEAT CONJ_TAC THEN ASM_ARITH_TAC) THEN NO_TAC;
         DISJ2_TAC THEN R5B_CLOSE_TAC THEN REWRITE_TAC[WORD_VAL] THEN TRY(REPEAT CONJ_TAC THEN ASM_ARITH_TAC) THEN NO_TAC]);;

(* 4493 -> 4700 (live) | 6027 (continues 4506, 4521 band, 4574 hash) *)
let R5B_SEGI = r5b_with_thresh 0 (fun () -> prove(r5b_seg3 (r5b_pred 4493 r5b_L3 (r5b_trk3 `k:num` `n:num`) [])
     (mk_abs(`s:wasmstate`, mk_disj(r5b_body 4700 r5b_L3B (r5b_trk3 `k:num` `n:num`) [], r5b_body 6027 r5b_L3 (r5b_trk3 `k:num` `n:num`) []))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN r5b_val3_tac THEN R5B_INIT_TAC THEN
  r5b_time "segI" (R5B_RUN R5B_EXEC [4700; 6027]) THEN R5B_FIN_TAC)) ();;
