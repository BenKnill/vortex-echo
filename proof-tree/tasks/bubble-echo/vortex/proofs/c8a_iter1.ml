(* vortex-chain C8a (Claude Opus 5.5, 2026-11-14/15), row A4: loop-1 value invariant. SEGE2 (SEGE + input regions survive),
   APPEND1V (memory invariant after one record), ISQT1-3 (isqrt loops with tracked values), CORE1 (one bead with the
   push ZQ/ZP of a list L), STEP1_FST/TO2048 (fold facts), ITER1V (one bead on the fold), LOOP1V (head k -> exit 2612). *)
let c8a_inputs m = list_mk_conj (map (fun t -> subst [m,`m:int64->byte`] t)
  [`va1_w32s 1138688 2048 rb (m:int64->byte)`; `va1_w32s 65536 262144 tbl (m:int64->byte)`; `va1_mdl mdl (m:int64->byte)`;
   `va1_w32s 16408 26 hp (m:int64->byte)`; `va1_w32s 1130496 2048 ra (m:int64->byte)`]);;
let c8a_segE2 = list_mk_forall([`m0:int64->byte`;`k:num`;`n:num`;`t:int32`;`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;
   `rb:num->int32`;`zq:num->int32`;`zp:num->int32`;`ra:num->int32`],
  mk_imp(list_mk_conj [`k < 2048 /\ n < 16384`; c8a_mem1; `va1_w32s 1130496 2048 ra m0`],
   r5b_ens (r5b_pred 2018 r5b_L1B c8a_e_pre [`va1_b1_ok mdl tbl rb zq k`])
   (mk_abs(`s:wasmstate`, r5b_body_m 2586 r5b_L1 c8a_base1n1
      (mk_conj(c8a_born1v `m0:int64->byte` `read wmem (s:wasmstate)`, c8a_inputs `read wmem (s:wasmstate)`))))));;
let C8A_INPUT_CLOSE =
  REWRITE_TAC[va1_w32s; va1_mdl] THEN GEN_TAC THEN DISCH_TAC THEN REPEAT R5B_PEEL_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];;
let C8A_SEGE2 = prove(c8a_segE2,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN `val (word (48 * n):int32) = 48 * n /\ val (word (4 * k):int32) = 4 * k /\
                val (word (4 * k + 1163264):int32) = 4 * k + 1163264` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  C8A_LOAD_TAC `4 * k + 1171456` `k:num` `zp:num->int32` 1171456 `va1_w32s 1171456 2048 zp m0` THEN
  R5B_INIT_TAC THEN C8A_RUN R5B_EXEC [2586] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[injectivity "wval"; R5B_EX_EQ] THEN R5C_EXPAND_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[va1_w32s; va1_mdl]) THEN
  REPEAT CONJ_TAC THEN FIRST [R5B_MEMCLOSE_TAC; C8A_WORD_CLOSE; C8A_EXPAND_ALL THEN R5B_MEMCLOSE_TAC; C8A_INPUT_CLOSE]);;
let c8a_miv L m = list_mk_conj (map (fun t -> subst [L,`L:(num->int32)list`; m,`m:int64->byte`] t)
  [`va1_w32s 1179648 196608 (FST (va1_push (L:(num->int32)list) (di,zq,zp,nd))) (m:int64->byte)`;
   `va1_w32s 1163264 2048 (FST (SND (va1_push (L:(num->int32)list) (di,zq,zp,nd)))) (m:int64->byte)`;
   `va1_w32s 1171456 2048 (FST (SND (SND (va1_push (L:(num->int32)list) (di,zq,zp,nd))))) (m:int64->byte)`;
   `read (bytes32 (word 16400)) (m:int64->byte) = nd`]) ;;
let c8a_cz = `FST (SND (va1_push (L:(num->int32)list) (di,zq,zp,nd)))`;;
let c8a_cp = `FST (SND (SND (va1_push (L:(num->int32)list) (di,zq,zp,nd))))`;;
let C8A_REC1_EQ = prove(list_mk_forall([`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;`t:int32`;`rb:num->int32`;`zq:num->int32`;`zp:num->int32`;`k:num`],
   mk_eq(`va1_b1_rec mdl hp tbl t rb zq zp k`, list_mk_comb(`va1_rec12`, c8a_w1))),
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_b1_rec] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REFL_TAC);;
let c8a_b1v_cur = subst [c8a_cz,`zq:num->int32`; c8a_cp,`zp:num->int32`] (c8a_born1v `m0:int64->byte` `m1:int64->byte`);;
let c8a_rec_cur = subst [c8a_cz,`zq:num->int32`; c8a_cp,`zp:num->int32`] `va1_b1_rec mdl hp tbl t rb zq zp k`;;
let c8a_app1v = mk_imp(list_mk_conj [c8a_miv `L:(num->int32)list` `m0:int64->byte`; `val (nd:int32) + LENGTH (L:(num->int32)list) = n`;
   `n < 16384`; `k < 2048`; r5b_zero_beyond; c8a_b1v_cur],
   c8a_miv (mk_comb(mk_comb(`APPEND:(num->int32)list->(num->int32)list->(num->int32)list`, `L:(num->int32)list`),
                    mk_list([c8a_rec_cur], `:num->int32`))) `m1:int64->byte`);;
let c8a_b1v_cs = conjuncts c8a_b1v_cur;;
let c8a_frame_th () = ASSUME (el 0 c8a_b1v_cs);;
let c8a_mdi_th () = REWRITE_RULE[va1_w32s] (ASSUME `va1_w32s 1179648 196608 (FST (va1_push (L:(num->int32)list) (di,zq,zp,nd))) m0`);;
let C8A_DI_FRAME_TAC =
  MP_TAC(SPEC `w:num` (c8a_frame_th ())) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPEC `w:num` (c8a_mdi_th ())) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN REFL_TAC;;
let C8A_DI_ZERO_TAC jj =
  let wj = subst [jj,`j:num`] `12 * n + j` in
  MP_TAC(SPEC wj (c8a_frame_th ())) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPEC wj (c8a_mdi_th ())) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`L:(num->int32)list`; `(di,zq,zp,nd):(num->int32)#(num->int32)#(num->int32)#int32`; wj] R5B_PUSH_DI_BEYOND) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;;
let C8A_ZQZP_TAC idx base =
  let mth = REWRITE_RULE[va1_w32s] (ASSUME (subst [mk_small_numeral base,`b:num`; (if base = 1163264 then c8a_cz else c8a_cp),`f:num->int32`]
              `va1_w32s b 2048 (f:num->int32) m0`)) in
  MP_TAC(SPEC `w:num` (ASSUME (el idx c8a_b1v_cs))) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPEC `w:num` mth) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ASSUME (el 9 c8a_b1v_cs); ASSUME (el 10 c8a_b1v_cs)] THEN ASM_REWRITE_TAC[];;
let C8A_J12 = prove(`!j. j < 12 ==> j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11`, ARITH_TAC);;
let C8A_DI_SLOT_TAC =
  SUBGOAL_THEN `w = 12 * n + (w - 12 * n)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `w - 12 * n` C8A_J12) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`w - 12 * n`,`j:num`) THEN GEN_TAC THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC)) THEN TRY (DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[ADD_SUB2; ARITH_RULE `(12 * n + j) - 12 * n = j`] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THEN FIRST [C8A_DI_ZERO_TAC `10`; C8A_DI_ZERO_TAC `11`];;
let C8A_APPEND1V = prove(c8a_app1v,
  STRIP_TAC THEN REWRITE_TAC[R5B_PUSH_SNOC; R5B_PUSH1_ND; C8A_REC1_EQ; va1_rec12] THEN
  SUBGOAL_THEN `val (word_add nd (word (LENGTH (L:(num->int32)list))):int32) = n` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`nd:int32`; `LENGTH (L:(num->int32)list)`] R5B_VAL_INC) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `val (word k:int32) = k /\ k MOD 2048 = k /\ k < 65536` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[R5B_PUSH_ND] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[va1_w32s] THEN REPEAT CONJ_TAC THEN X_GEN_TAC `w:num` THEN DISCH_TAC THENL
   [COND_CASES_TAC THENL [C8A_DI_SLOT_TAC; C8A_DI_FRAME_TAC]; C8A_ZQZP_TAC 11 1163264; C8A_ZQZP_TAC 12 1171456]);;
let c8a_isqt_stmt lp ep ctr vrb trk extra outer =
  let bp = lp + 2 in
  let pre = r5b_pred bp (Lp lp :: outer) ((ctr, `word c:int32`) :: c8a_isq_tr `ve_isq (32 - c) (X:int64#int64#int64)` vrb @ trk) extra in
  let post = r5b_pred ep outer (c8a_isq_tr `ve_isq 32 (X:int64#int64#int64)` vrb @ trk) extra in
  let e = r5b_ens pre post in
  let vs = subtract (frees e) [`c:num`] in
  mk_forall(`c:num`, mk_imp(`1 <= c /\ c <= 32`, list_mk_forall(vs, e)));;
let C8A_ISQT_BRANCH lp ep ctr vrb trk extra outer : tactic = fun (asl,w) ->
  let bp = lp + 2 in
  (ENSURES_SEQUENCE_TAC (mk_small_numeral bp)
     (r5b_rest (r5b_pred bp (Lp lp :: outer) ((ctr, `word c:int32`) :: c8a_isq_tr `ve_isq (32 - c) (X:int64#int64#int64)` vrb @ trk) extra)) THEN
   CONJ_TAC THENL
    [MP_TAC(SPECL [`c:num`; `X:int64#int64#int64`] C8A_ISQ_SUC) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
     R5B_INIT_TAC THEN R5B_RUN1 R5B_EXEC [ep; bp] THEN
     FIRST_X_ASSUM(fun th -> if is_eq(concl th) && can (find_term ((=) `ve_isq_step`)) (concl th) then C8A_ISQ_CLOSE [th] else failwith "");
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && is_forall(rand(concl th)))) THEN
     ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN MATCH_ACCEPT_TAC]]) (asl,w);;
let C8A_ISQT_TAC lp ep ctr vrb trk extra outer : tactic =
  INDUCT_TAC THENL [ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC(SPEC `c:num` R5B_DEC1) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC)] THEN
  ASM_CASES_TAC `c = 0` THENL
   [R5B_INIT_TAC THEN R5B_RUN1 R5B_EXEC [ep; lp + 2] THEN C8A_ISQ_CLOSE [C8A_ISQ32];
    C8A_ISQT_BRANCH lp ep ctr vrb trk extra outer];;
let c8a_okx = [`va1_b1_ok mdl tbl rb zq k`];;
let c8a_t1 = filter (fun (l,_) -> l <> 20) (c8a_trk1v @ c8a_hpl);;
let c8a_t2 = filter (fun (l,_) -> not (mem l [31;20;16;13])) c8a_c_post;;
let c8a_t3 = filter (fun (l,_) -> not (mem l [34;31;16;13])) c8a_d_post;;
let C8A_ISQT1 = prove(c8a_isqt_stmt 571 627 13 (20,30,16) c8a_t1 c8a_okx r5b_L1B, C8A_ISQT_TAC 571 627 13 (20,30,16) c8a_t1 c8a_okx r5b_L1B);;
let C8A_ISQT2 = prove(c8a_isqt_stmt 1753 1809 13 (31,20,16) c8a_t2 c8a_okx r5b_L1B, C8A_ISQT_TAC 1753 1809 13 (31,20,16) c8a_t2 c8a_okx r5b_L1B);;
let C8A_ISQT3 = prove(c8a_isqt_stmt 1962 2018 13 (34,31,16) c8a_t3 c8a_okx r5b_L1B, C8A_ISQT_TAC 1962 2018 13 (34,31,16) c8a_t3 c8a_okx r5b_L1B);;
let c8a_L1k kk = subst [kk,`K:num`] `FST (va1_fold1 mdl hp tbl t rb nd K ([],zq,zp))`;;
let c8a_n1 kk = mk_binop `(+):num->num->num` `val (nd:int32)` (mk_comb(`LENGTH:(num->int32)list->num`, c8a_L1k kk));;
let c8a_mivk kk m = mk_conj(subst [c8a_L1k kk,`L:(num->int32)list`] (c8a_miv `L:(num->int32)list` m), c8a_inputs m);;
let c8a_setn l v trk = map (fun (i,x) -> if i = l then (i,v) else (i,x)) trk;;
let c8a_wn x = mk_comb(`word:num->int32`, x);;
let c8a_head1v kk = mk_abs(`s:wasmstate`, r5b_body_m 146 r5b_L1 (c8a_setn 1 (c8a_wn (c8a_n1 kk)) (c8a_setn 0 (c8a_wn kk) c8a_base1))
                                            (c8a_mivk kk `read wmem (s:wasmstate)`));;
let c8a_exit1v = mk_abs(`s:wasmstate`, mk_conj(r5b_body_m 2612 [] (c8a_setn 1 (c8a_wn (c8a_n1 `2048`)) (tl c8a_base1))
                                            (c8a_mivk `2048` `read wmem (s:wasmstate)`), mk_binop `(<=):num->num->bool` (c8a_n1 `2048`) `16384`));;
let c8a_iter1v_post = mk_abs(`s:wasmstate`, mk_disj(
   list_mk_conj [r5b_bd (c8a_head1v `k + 1`); `k + 1 < 2048`; mk_binop `(<):num->num->bool` (c8a_n1 `k + 1`) `16384`],
   r5b_bd c8a_exit1v));;
let c8a_zb = r5b_zero_beyond;;
let c8a_iter1v = list_mk_forall([`k:num`;`t:int32`;`di:num->int32`;`zq:num->int32`;`zp:num->int32`;`nd:int32`;`mdl:num->int32`;
   `hp:num->int32`;`tbl:num->int32`;`rb:num->int32`;`ra:num->int32`],
  mk_imp(list_mk_conj [`k < 2048`; mk_binop `(<):num->num->bool` (c8a_n1 `k:num`) `16384`; c8a_zb],
    r5b_ens (c8a_head1v `k:num`) c8a_iter1v_post));;
let c8a_Lf k = subst [k,`K:num`] `FST (va1_fold1 mdl hp tbl t rb nd K ([],zq,zp))`;;
let c8a_L1n = `if va1_b1_ok mdl tbl rb (FST (SND (va1_push (L:(num->int32)list) (di,zq,zp,nd)))) k
   then APPEND L [va1_b1_rec mdl hp tbl t rb (FST (SND (va1_push (L:(num->int32)list) (di,zq,zp,nd))))
                   (FST (SND (SND (va1_push (L:(num->int32)list) (di,zq,zp,nd))))) k] else L`;;
let c8a_step1_stmt = list_mk_forall([`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;`t:int32`;`rb:num->int32`;`nd:int32`;
   `di:num->int32`;`zq:num->int32`;`zp:num->int32`;`k:num`],
  mk_imp(mk_conj(`k < 2048`, mk_binop `(<):num->num->bool` (c8a_n1 `k:num`) `16384`),
    mk_eq(c8a_Lf `k + 1`, subst [c8a_Lf `k:num`,`L:(num->int32)list`] c8a_L1n)));;
let C8A_STEP1_FST = prove(c8a_step1_stmt,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;`t:int32`;`rb:num->int32`;`nd:int32`;
     `di:num->int32`;`zq:num->int32`;`zp:num->int32`;`k:num`] C8A_FOLD1_PUSH) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC (mk_binop `(<):num->num->bool` (c8a_n1 `k:num`) `16384`) THEN REWRITE_TAC[GSYM ADD1; va1_fold1] THEN
  SPEC_TAC(`va1_fold1 mdl hp tbl t rb nd k ([],zq,zp)`, `st:(num->int32)list#(num->int32)#(num->int32)`) THEN
  GEN_TAC THEN DISCH_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `~(16384 <= val (nd:int32) + LENGTH (FST (st:(num->int32)list#(num->int32)#(num->int32))))` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[va1_step1] THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;
let c8a_to2048_stmt = list_mk_forall([`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;`t:int32`;`rb:num->int32`;`nd:int32`;
   `zq:num->int32`;`zp:num->int32`;`k:num`],
  mk_imp(mk_conj(`k < 2048`, mk_disj(`k = 2047`, mk_binop `(<=):num->num->bool` `16384` (c8a_n1 `k + 1`))),
    `va1_fold1 mdl hp tbl t rb nd 2048 ([],zq,zp) = va1_fold1 mdl hp tbl t rb nd (k + 1) ([],zq,zp)`));;
let C8A_TO2048 = prove(c8a_to2048_stmt,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC) THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    MP_TAC(SPECL [`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;`t:int32`;`rb:num->int32`;`nd:int32`;`k + 1`;
                  `([],zq,zp):(num->int32)list#(num->int32)#(num->int32)`; `2047 - k`] C8A_FOLD1_CAP) THEN
    ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `(k + 1) + (2047 - k) = 2048` SUBST1_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]]]);;
let c8a_nn = mk_binop `(+):num->num->num` `val (nd:int32)` (mk_comb(`LENGTH:(num->int32)list->num`, c8a_L1n));;
let c8a_mivL L m = mk_conj(c8a_miv L m, c8a_inputs m);;
let c8a_core1_post = mk_abs(`s:wasmstate`, mk_disj(
   list_mk_conj [r5b_body_m 146 r5b_L1 (c8a_setn 1 (c8a_wn c8a_nn) (c8a_setn 0 (c8a_wn `k + 1`) c8a_base1))
                    (c8a_mivL c8a_L1n `read wmem (s:wasmstate)`); `k + 1 < 2048`; mk_binop `(<):num->num->bool` c8a_nn `16384`],
   list_mk_conj [r5b_body_m 2612 [] (c8a_setn 1 (c8a_wn c8a_nn) (tl c8a_base1)) (c8a_mivL c8a_L1n `read wmem (s:wasmstate)`);
                 mk_disj(`k = 2047`, mk_eq(c8a_nn, `16384`)); mk_binop `(<=):num->num->bool` c8a_nn `16384`]));;
let c8a_core1 = list_mk_forall([`m0:int64->byte`;`L:(num->int32)list`;`n:num`;`k:num`;`t:int32`;`di:num->int32`;`zq:num->int32`;
   `zp:num->int32`;`nd:int32`;`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;`rb:num->int32`;`ra:num->int32`],
  mk_imp(list_mk_conj [`k < 2048`; `n < 16384`; `val (nd:int32) + LENGTH (L:(num->int32)list) = n`; c8a_zb;
                       c8a_mivL `L:(num->int32)list` `m0:int64->byte`],
    r5b_ens (r5b_pred 146 r5b_L1 c8a_base1 []) c8a_core1_post));;
(* lemma instance: zq/zp := the current push ZQ/ZP, extra instantiation first *)
let c8a_li xi asl th =
  r5b_inst2 asl (INST [c8a_cz,`zq:num->int32`; c8a_cp,`zp:num->int32`] (INST xi (SPEC_ALL th)));;
let c8a_lisq x asl th = c8a_li [x,`X:int64#int64#int64`] asl (SPEC_ALL (MP (SPEC `32` th) (ARITH_RULE `1 <= 32 /\ 32 <= 32`)));;
let C8A_WK : tactic =
  X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  FIRST [DISCH_THEN ACCEPT_TAC;
         STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[va1_b_isqrt]) THEN
         REWRITE_TAC[va1_b_isqrt; ARITH_RULE `32 - 32 = 0`; ve_isq] THEN
         ASM_REWRITE_TAC[injectivity "wval"; R5B_EX_EQ] THEN NO_TAC];;
let C8A_THEN th : tactic = fun (asl,w) ->
  let p', q', _ = r5b_dest_ens (concl th) in
  (MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC p' THEN CONJ_TAC THENL
    [C8A_WK; MATCH_MP_TAC R5B_ENS_TRANS THEN EXISTS_TAC q' THEN CONJ_TAC THENL [ACCEPT_TAC th; ALL_TAC]]) (asl,w);;
let C8A_USE xi th : tactic = fun (asl,w) -> C8A_THEN (c8a_li xi asl th) (asl,w);;
let C8A_USEQ x th : tactic = fun (asl,w) -> C8A_THEN (c8a_lisq x asl th) (asl,w);;
let c8a_X1 = mk_pair(assoc 20 c8a_trk1v, mk_pair(assoc 30 c8a_isq0, assoc 16 c8a_isq0));;
let c8a_X2 = mk_pair(assoc 31 c8a_c_post, mk_pair(assoc 20 c8a_c_post, assoc 16 c8a_c_post));;
let c8a_X3 = mk_pair(assoc 34 c8a_d_post, mk_pair(assoc 31 c8a_d_post, assoc 16 c8a_d_post));;
let c8a_b1v_m1 = subst [`m1:int64->byte`,`m1:int64->byte`] c8a_b1v_cur;;
let C8A_FINW : tactic =
  X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN(DISJ_CASES_THEN (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THENL [DISJ1_TAC; DISJ2_TAC] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_ARITH_TAC;;
let c8a_m1pre = mk_abs(`s:wasmstate`, mk_exists(`m1:int64->byte`,
   mk_conj(subst [`m1:int64->byte`,`m0:int64->byte`] (r5b_bd(r5b_pred 2586 r5b_L1 c8a_base1n1 [])),
           mk_conj(c8a_b1v_cur, c8a_inputs `m1:int64->byte`))));;
let C8A_LIVE1_TAC : tactic =
  R5B_PURE_TAC THEN
  C8A_USE [] C8A_SEGB THEN C8A_USEQ c8a_X1 C8A_ISQT1 THEN C8A_USE [] C8A_SEGC THEN C8A_USEQ c8a_X2 C8A_ISQT2 THEN
  C8A_USE [] C8A_SEGD THEN C8A_USEQ c8a_X3 C8A_ISQT3 THEN C8A_USE [] C8A_SEGE2 THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC c8a_m1pre THEN CONJ_TAC THENL
   [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_TAC THEN
    EXISTS_TAC `read wmem (s:wasmstate)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  R5B_EXISTS_TAC THEN X_GEN_TAC `m1:int64->byte` THEN MATCH_MP_TAC R5B_ENS_PRE_CONJ THEN STRIP_TAC THEN
  W(fun (asl,w) -> ASSUME_TAC (MP C8A_APPEND1V (TAC_PROOF((asl, lhand(concl C8A_APPEND1V)),
                     REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC)))) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> mem (concl th) c8a_b1v_cs))) THEN
  SUBGOAL_THEN (mk_eq(mk_binop `(+):num->num->num` `val (nd:int32)` (mk_comb(`LENGTH:(num->int32)list->num`,
       mk_comb(mk_comb(`APPEND:(num->int32)list->(num->int32)list->(num->int32)list`, `L:(num->int32)list`), mk_list([c8a_rec_cur], `:num->int32`)))),
       `n + 1`)) ASSUME_TAC THENL [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  W(fun (asl,w) -> C8A_THEN (r5b_inst2 asl (INST [`m1:int64->byte`,`m0:int64->byte`; `n + 1`,`n:num`] (SPEC_ALL C8A_BACK1)))) THEN
  MATCH_MP_TAC R5B_ENS_NOW THEN C8A_FINW;;
let C8A_SKIP1_TAC : tactic =
  R5B_PURE_TAC THEN
  W(fun (asl,w) -> C8A_THEN (r5b_inst2 asl (SPEC_ALL C8A_BACK1))) THEN
  MATCH_MP_TAC R5B_ENS_NOW THEN C8A_FINW;;
let C8A_CORE1 = prove(c8a_core1,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C8A_USE [] C8A_SEGA THEN R5B_DISJ_TAC THEN CONJ_TAC THENL [C8A_LIVE1_TAC; C8A_SKIP1_TAC]);;
let C8A_ITER1V_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  EXISTS_TAC (mk_abs(`s:wasmstate`, mk_exists(`m0:int64->byte`,
     mk_conj(r5b_bd(r5b_pred 146 r5b_L1 (c8a_setn 1 (c8a_wn (c8a_n1 `k:num`)) c8a_base1) []), c8a_mivk `k:num` `m0:int64->byte`)))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_TAC THEN
    EXISTS_TAC `read wmem (s:wasmstate)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  R5B_EXISTS_TAC THEN X_GEN_TAC `m0:int64->byte` THEN
  MATCH_MP_TAC R5B_ENS_PRE_CONJ THEN STRIP_TAC THEN
  W(fun (asl,w) -> C8A_THEN (r5b_inst2 asl (INST [c8a_Lf `k:num`, `L:(num->int32)list`; c8a_n1 `k:num`, `n:num`] (SPEC_ALL C8A_CORE1)))) THEN
  MATCH_MP_TAC R5B_ENS_NOW THEN X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  W(fun (asl,w) -> let e = r5b_inst2 asl (SPEC_ALL C8A_STEP1_FST) in REWRITE_TAC[GSYM e]) THEN
  DISCH_THEN(DISJ_CASES_THEN (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THENL
   [DISJ1_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISJ2_TAC THEN W(fun (asl,w) -> SUBST1_TAC (r5b_inst2 asl (SPEC_ALL C8A_TO2048))) THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];;
let C8A_ITER1V = prove(c8a_iter1v, C8A_ITER1V_TAC);;
let c8a_iter1v_vars = [`k:num`;`t:int32`;`di:num->int32`;`zq:num->int32`;`zp:num->int32`;`nd:int32`;`mdl:num->int32`;
   `hp:num->int32`;`tbl:num->int32`;`rb:num->int32`;`ra:num->int32`];;
let c8a_loop1v = mk_forall(`d:num`, list_mk_forall(c8a_iter1v_vars,
  mk_imp(list_mk_conj [`k + d = 2047`; mk_binop `(<):num->num->bool` (c8a_n1 `k:num`) `16384`; c8a_zb],
    r5b_ens (c8a_head1v `k:num`) c8a_exit1v)));;
let C8A_LOOP1V = prove(c8a_loop1v,
  INDUCT_TAC THEN (REPEAT GEN_TAC THEN STRIP_TAC THEN
  W(fun (asl,w) -> let it = r5b_inst2 asl C8A_ITER1V in
    MATCH_MP_TAC R5B_ENS_TRANS THEN EXISTS_TAC (rand(rator(concl it))) THEN CONJ_TAC THENL [ACCEPT_TAC it; ALL_TAC]) THEN
  R5B_DISJ_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC R5B_ENS_PRE_CONJ THEN STRIP_TAC THEN
    FIRST [MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC;
           FIRST_X_ASSUM(MP_TAC o SPECL (`k + 1` :: tl c8a_iter1v_vars)) THEN
           ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; REWRITE_TAC[]]];
    MATCH_MP_TAC R5B_ENS_NOW THEN REWRITE_TAC[]]));;
