(* ========================================================================= *)
(* Vortex pop R5 droplet birth (vortex-r5birth PROVE-birth r2, Claude Opus   *)
(* 5.5, 2026-11-11): lemma layer 4 on pop_r5bp_lem3.ml: spray/antipode born *)
(* record r5b_born2, R5B_ENS_TRANS (ensures transitivity at R5B_FRAME),      *)
(* R5B_BIRTH_APPEND2 (spray birth keeps the invariant), R5B_FINAL_MEM.       *)
(* ========================================================================= *)
(* ---- R5 PROVE-birth: spray/antipode birth (word 7 >= 65536: no parent debit) *)
let r5b_born2 =
  `\(m0:int64->byte) (m:int64->byte).
   (!w. w < 196608 /\ ~(12 * n <= w /\ w < 12 * n + 10) ==>
        read (bytes32 (word (1179648 + 4 * w))) m = read (bytes32 (word (1179648 + 4 * w))) m0) /\
   read (bytes32 (word (1179648 + 4 * (12 * n + 6)))) m = word_add t (word 1) /\
   65536 <= val (read (bytes32 (word (1179648 + 4 * (12 * n + 7)))) m) /\
   (!i. i < 2048 ==> read (bytes32 (word (1163264 + 4 * i))) m = read (bytes32 (word (1163264 + 4 * i))) m0) /\
   (!i. i < 2048 ==> read (bytes32 (word (1171456 + 4 * i))) m = read (bytes32 (word (1171456 + 4 * i))) m0) /\
   read (bytes32 (word 16400)) m = read (bytes32 (word 16400)) m0`;;
let r5b_born2_at m0 m = rhs(concl(TOP_DEPTH_CONV BETA_CONV (list_mk_comb(r5b_born2, [m0; m]))));;

let r5b_trans_stmt = list_mk_forall([`P:wasmstate->bool`;`Q:wasmstate->bool`;`R:wasmstate->bool`],
  mk_imp(mk_conj(r5b_ens `P:wasmstate->bool` `Q:wasmstate->bool`, r5b_ens `Q:wasmstate->bool` `R:wasmstate->bool`),
         r5b_ens `P:wasmstate->bool` `R:wasmstate->bool`));;
let R5B_ENS_TRANS = prove(r5b_trans_stmt,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN EXISTS_TAC `Q:wasmstate->bool` THEN
  ASM_REWRITE_TAC[] THEN MAYCHANGE_IDEMPOT_TAC);;
let r5b_frame2 = hd(conjuncts(r5b_born2_at `m0:int64->byte` `m:int64->byte`));;
let R5B_W10_TAC2 j = MP_TAC(SPEC j (ASSUME r5b_frame2)) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPEC j (ASSUME r5b_w32di)) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC(ASSUME r5b_beyond) THEN ASM_ARITH_TAC;;
let r5b_ba2 = list_mk_forall([`t:int32`;`di:num->int32`;`zq:num->int32`;`zp:num->int32`;`nd:int32`;`n:num`;`m0:int64->byte`;`m:int64->byte`],
   mk_imp(list_mk_conj [r5b_mi `n:num` `m0:int64->byte`; `n < 16384`; r5b_zero_beyond;
                        r5b_born2_at `m0:int64->byte` `m:int64->byte`],
          r5b_mi `n + 1` `m:int64->byte`));;
let R5B_BIRTH_APPEND2 = prove(r5b_ba2,
  (REPEAT GEN_TAC THEN STRIP_TAC) THEN
  (EXISTS_TAC `APPEND (L:(num->int32)list) [\i. read (bytes32 (word (1179648 + 4 * (12 * n + i)))) (m:int64->byte)]`) THEN
  (REWRITE_TAC[ALL_APPEND; ALL; LENGTH_APPEND; LENGTH; R5B_PUSH_SNOC; R5B_PUSH1_ND; R5B_PUSH_ND]) THEN
  (REWRITE_TAC[va1_w32s] THEN RULE_ASSUM_TAC(REWRITE_RULE[va1_w32s])) THEN
  (SUBGOAL_THEN `val (word_add nd (word (LENGTH (L:(num->int32)list))):int32) = n` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`nd:int32`; `LENGTH (L:(num->int32)list)`] R5B_VAL_INC) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC]) THEN
  (SUBGOAL_THEN `!j. 12 * n <= j /\ j < 196608 ==> FST (va1_push L (di,zq,zp,nd)) j = word 0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`L:(num->int32)list`; `(di,zq,zp,nd):(num->int32)#(num->int32)#(num->int32)#int32`; `j:num`] R5B_PUSH_DI_BEYOND) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN `~(val (read (bytes32 (word (1179648 + 4 * (12 * n + 7)))) (m:int64->byte)) < 65536)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC]) THEN
  (ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  (ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [R5B_W10_TAC2 `12 * n + 10`; R5B_W10_TAC2 `12 * n + 11`; ASM_ARITH_TAC;
    X_GEN_TAC `w:num` THEN DISCH_TAC THEN COND_CASES_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `12 * n <= w ==> 12 * n + (w - 12 * n) = w`];
      MP_TAC(SPEC `w:num` (ASSUME r5b_frame2)) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      ASM_SIMP_TAC[]];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[]]));;
let R5B_FINAL_MEM = prove(list_mk_forall([`n:num`;`m0:int64->byte`],
   mk_imp(mk_conj(r5b_mi `n:num` `m0:int64->byte`, `n <= 16384`),
     `?L. ALL (\r. r 6 = word_add t (word 1) /\ r 10 = word 0 /\ r 11 = word 0) L /\
          val nd + LENGTH L <= 16384 /\
          va1_bs (va1_push L (di,zq,zp,nd)) (write (bytes32 (word 16400)) (word n) (m0:int64->byte))`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC `L:(num->int32)list` THEN ASM_REWRITE_TAC[PL5_BS_R5B] THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST [ASM_ARITH_TAC;
         MATCH_MP_TAC R5B_W32S_W32 THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]) THEN
  REWRITE_TAC[CAP_B32_SAME; R5B_PUSH_ND] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `val (nd:int32) + LENGTH (L:(num->int32)list) = n` then SUBST1_TAC(SYM th) else NO_TAC) THEN
  REWRITE_TAC[WORD_ADD; WORD_VAL]);;
