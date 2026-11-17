(* vortex-chain C8a (Claude Opus 5.5, 2026-11-15), row A5: loop 2 (spray) with values. SEGF 2706->2905|4363 (band + hash
   tests, skip iff ~va1_b2_ok), SEGG 2905->3009 (hp loads), ISQT4 (isqrt loop 4), SEGH 3063->4363 (record stores, words 8-9
   by the i64 zero store), BACK2 4363->2706|4391, APPEND2V (memory invariant after one loop-2 record), CORE2 (one bead on a
   list L), STEP2/TO2048B (fold facts), ITER2V, LOOP2V (head k -> exit 4391, list starting at L0). *)
let c8a_base2 = [15,`word k:int32`; 1,`word n:int32`; 2,`word_add (word_mul t (word 3266489909)) (word 3621415137):int32`;
  3,`word_add t (word 1):int32`; 4,`(mdl:num->int32) 2`;
  5,`word_mul (word_xor (word_add t (word 1)) (word 2654435769)) (word 2246822507):int32`;
  14,`word_xor (word_mul ((mdl:num->int32) 2) (word 3)) (word 2654435769):int32`;
  19,`word_add (word_mul (word_add t (word 1)) (word 3266489909)) (word 2769733223):int32`];;
let c8a_mem2 = `va1_w32s 1138688 2048 rb m0 /\ va1_w32s 65536 262144 tbl m0 /\ va1_w32s 16408 26 hp m0`;;
let c8a_seg2v p q = list_mk_forall([`m0:int64->byte`;`k:num`;`n:num`;`t:int32`;`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;
   `rb:num->int32`], mk_imp(mk_conj(`k < 2048 /\ n < 16384`, c8a_mem2), r5b_ens p q));;
let c8a_V2 = c8a_letvals va1_b2_rec;;
let c8a_v2 n = assoc n c8a_V2;;
let c8a_ok2 = `va1_b2_ok mdl tbl t rb k`;;
let c8a_trk2v = c8a_base2 @ [11, `(rb:num->int32) k`; 34, c8a_v2 "spd"; 31, `va1_b_tubearg (rb k) (va1_ck_spd tbl (rb k) k)`];;
let c8a_segF = c8a_seg2v (r5b_pred 2706 r5b_L2 c8a_base2 [])
   (mk_abs(`s:wasmstate`, mk_disj(r5b_body 2905 r5b_L2B c8a_trk2v [c8a_ok2], r5b_body 4363 r5b_L2 c8a_base2 [mk_neg c8a_ok2])));;
let C8A_BAND2 = prove(`!r:int32. ~(val (word_add r (word 4245615560)) < 4249809864) ==> 4194304 <= val r /\ val r <= 49351735`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `r:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MOD_ADD_CASES; ARITH_RULE `4245615560 < 4294967296`] THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;
let C8A_TBL_LOADS_G band bandth : tactic = fun (asl,w) ->
  try let bth = find (fun th -> concl th = band) (map snd asl) in
    (ASSUME_TAC (MATCH_MP bandth bth) THEN
     SUBGOAL_THEN `val ((rb:num->int32) k) <= 52371633` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     MP_TAC(SPECL [`k:num`; `(rb:num->int32) k`] C8A_TBLADDR) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
     FIRST_ASSUM(ASSUME_TAC o CONJUNCT2 o MATCH_MP R5C_J) THEN
     C8A_LOAD_TAC `val (word_add (word_shl (word k) 9) (word_and (word_ushr ((rb:num->int32) k) 17) (word 32764)):int32) + 65536`
        (mk_binop `(+):num->num->num` `128 * k` c8a_jj) `tbl:num->int32` 65536 `va1_w32s 65536 262144 tbl m0` THEN
     C8A_LOAD_TAC `val (word_add (word_shl (word k) 9) (word_and (word_ushr ((rb:num->int32) k) 17) (word 32764)):int32) + 65540`
        (mk_binop `(+):num->num->num` `128 * k` (mk_binop `(+):num->num->num` c8a_jj `1`)) `tbl:num->int32` 65536 `va1_w32s 65536 262144 tbl m0`) (asl,w)
  with Failure _ -> ALL_TAC (asl,w);;
let C8A_SEGF_DEFS = [va1_b2_ok; va1_ck_spd; va1_ck_hfin; va1_b_tubearg];;
let c8a_band2 = `~(val (word_add ((rb:num->int32) k) (word 4245615560)) < 4249809864)`;;
let C8A_SEGF = prove(c8a_segF,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN R5B_INIT_TAC THEN VK_VAL_TAC `4 * k` THEN
  C8A_LOAD_TAC `4 * k + 1138688` `k:num` `rb:num->int32` 1138688 `va1_w32s 1138688 2048 rb m0` THEN
  R5B_RUN R5B_EXEC [2750; 4363] THEN C8A_TBL_LOADS_G c8a_band2 C8A_BAND2 THEN
  R5B_RUN R5B_EXEC [2905; 4363] THEN C8A_FIN C8A_SEGF_DEFS);;
let c8a_hpl2 = map (fun (l,i) -> (l, subst [mk_small_numeral i,`i:num`] `word_sx ((hp:num->int32) i):int64`))
  [36,11; 17,10; 18,9; 37,8; 22,7; 25,6; 23,5; 21,4; 24,3];;
let c8a_isq02 = [0,`word 32:int32`; 20,`word 0:int64`; 16,`word 4611686018427387904:int64`];;
let c8a_segG = c8a_seg2v (r5b_pred 2905 r5b_L2B c8a_trk2v [c8a_ok2])
   (r5b_pred 3009 (Lp 3007 :: r5b_L2B) (c8a_trk2v @ c8a_isq02 @ c8a_hpl2) [c8a_ok2]);;
let C8A_SEGG = prove(c8a_segG,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN R5B_INIT_TAC THEN C8A_HP_LOADS THEN R5B_RUN R5B_EXEC [3009] THEN
  ENSURES_FINAL_STATE_TAC THEN C8A_CLOSE1 []);;
let c8a_t4 = filter (fun (l,_) -> not (mem l [31;20;16;0])) (c8a_trk2v @ c8a_hpl2);;
let C8A_ISQT4 = prove(c8a_isqt_stmt 3007 3063 0 (31,20,16) c8a_t4 [c8a_ok2] r5b_L2B, C8A_ISQT_TAC 3007 3063 0 (31,20,16) c8a_t4 [c8a_ok2] r5b_L2B);;
let c8a_h_pre = c8a_base2 @ [11, `(rb:num->int32) k`; 34, c8a_v2 "spd"; 20, c8a_v2 "tube" |> lhand |> lhand |> lhand] @ c8a_hpl2;;
let c8a_w2 = [c8a_v2 "w0"; c8a_v2 "w1"; c8a_v2 "w2"; c8a_v2 "w3"; c8a_v2 "w4"; c8a_v2 "w5"; `word_add t (word 1):int32`;
              `word_or (word k) (word 65536):int32`; `word 0:int32`; `word 0:int32`];;
let c8a_born2v m0 m =
  let b = r5b_born2_at m0 m in
  let cs = conjuncts b in
  let words = map (fun (j,v) -> subst [mk_small_numeral j,`j:num`; v,`V:int32`; m,`m:int64->byte`]
                     `read (bytes32 (word (1179648 + 4 * (12 * n + j)))) (m:int64->byte) = V`) (zip (0--9) c8a_w2) in
  list_mk_conj([el 0 cs] @ words @ [el 3 cs; el 4 cs; el 5 cs]);;
let c8a_base2n1 = map (fun (l,v) -> if l = 1 then (1, `word (n + 1):int32`) else (l,v)) c8a_base2;;
let c8a_segH = list_mk_forall([`m0:int64->byte`;`k:num`;`n:num`;`t:int32`;`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;
   `rb:num->int32`;`ra:num->int32`],
  mk_imp(list_mk_conj [`k < 2048 /\ n < 16384`; c8a_mem2; `va1_mdl mdl m0`; `va1_w32s 1130496 2048 ra m0`],
   r5b_ens (r5b_pred 3063 r5b_L2B c8a_h_pre [c8a_ok2])
   (mk_abs(`s:wasmstate`, r5b_body_m 4363 r5b_L2 c8a_base2n1
      (mk_conj(c8a_born2v `m0:int64->byte` `read wmem (s:wasmstate)`, c8a_inputs `read wmem (s:wasmstate)`))))));;
let C8A_W64Z_TAC = REPEAT R5B_PEEL_TAC THEN CONV_TAC(ONCE_DEPTH_CONV R5B_ADDR_NORM_CONV) THEN
  FIRST [REWRITE_TAC[PL5_R32_W64_ZERO] THEN NO_TAC;
         REWRITE_TAC[ARITH_RULE `48 * n + 1179684 = (48 * n + 1179680) + 4`] THEN REWRITE_TAC[WORD_ADD; PL5_R32_W64_ZERO] THEN NO_TAC];;
let c8a_b2v_cur = c8a_born2v `m0:int64->byte` `m1:int64->byte`;;
let c8a_b2v_cs = conjuncts c8a_b2v_cur;;
let c8a_rec2 = `va1_b2_rec mdl hp tbl t rb k`;;
let C8A_REC2_EQ = prove(list_mk_forall([`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;`t:int32`;`rb:num->int32`;`k:num`],
   mk_eq(c8a_rec2, list_mk_comb(`va1_rec12`, c8a_w2))),
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_b2_rec] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REFL_TAC);;
let c8a_app2v = mk_imp(list_mk_conj [c8a_miv `L:(num->int32)list` `m0:int64->byte`; `val (nd:int32) + LENGTH (L:(num->int32)list) = n`;
   `n < 16384`; `k < 2048`; r5b_zero_beyond; c8a_b2v_cur],
   c8a_miv (mk_comb(mk_comb(`APPEND:(num->int32)list->(num->int32)list->(num->int32)list`, `L:(num->int32)list`),
                    mk_list([c8a_rec2], `:num->int32`))) `m1:int64->byte`);;
let C8A_DI_FRAME_TAC_G cs =
  MP_TAC(SPEC `w:num` (ASSUME (el 0 cs))) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPEC `w:num` (c8a_mdi_th ())) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN REFL_TAC;;
let C8A_DI_ZERO_TAC_G cs jj =
  let wj = subst [jj,`j:num`] `12 * n + j` in
  MP_TAC(SPEC wj (ASSUME (el 0 cs))) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPEC wj (c8a_mdi_th ())) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`L:(num->int32)list`; `(di,zq,zp,nd):(num->int32)#(num->int32)#(num->int32)#int32`; wj] R5B_PUSH_DI_BEYOND) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;;
let C8A_DI_SLOT_TAC_G cs =
  SUBGOAL_THEN `w = 12 * n + (w - 12 * n)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `w - 12 * n` C8A_J12) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`w - 12 * n`,`j:num`) THEN GEN_TAC THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC)) THEN TRY (DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[ADD_SUB2; ARITH_RULE `(12 * n + j) - 12 * n = j`] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THEN FIRST [C8A_DI_ZERO_TAC_G cs `10`; C8A_DI_ZERO_TAC_G cs `11`];;
let C8A_ZQZP2_TAC cs idx base =
  let mth = REWRITE_RULE[va1_w32s] (ASSUME (subst [mk_small_numeral base,`b:num`; (if base = 1163264 then c8a_cz else c8a_cp),`f:num->int32`]
              `va1_w32s b 2048 (f:num->int32) m0`)) in
  MP_TAC(SPEC `w:num` (ASSUME (el idx cs))) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPEC `w:num` mth) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[WORD_SUB_0; COND_ID];;
let C8A_SEGH = prove(c8a_segH,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN `val (word (48 * n):int32) = 48 * n` ASSUME_TAC THENL [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  R5B_INIT_TAC THEN C8A_RUN R5B_EXEC [4363] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[injectivity "wval"; R5B_EX_EQ] THEN R5C_EXPAND_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[va1_w32s; va1_mdl]) THEN
  REPEAT CONJ_TAC THEN FIRST [R5B_MEMCLOSE_TAC; C8A_WORD_CLOSE; C8A_EXPAND_ALL THEN R5B_MEMCLOSE_TAC; C8A_INPUT_CLOSE; C8A_W64Z_TAC]);;
let c8a_base2k1 = c8a_setn 15 `word (k + 1):int32` c8a_base2;;
let c8a_base2x = filter (fun (l,_) -> l <> 15) c8a_base2;;
let c8a_back2 = list_mk_forall([`m0:int64->byte`;`k:num`;`n:num`;`t:int32`;`mdl:num->int32`],
   mk_imp(`k < 2048 /\ n <= 16384`,
    r5b_ens (r5b_pred 4363 r5b_L2 c8a_base2 [])
     (mk_abs(`s:wasmstate`, mk_disj(
        r5b_body 2706 r5b_L2 c8a_base2k1 [`k + 1 < 2048`; `n < 16384`],
        r5b_body 4391 [Blk 6084] c8a_base2x [`k = 2047 \/ n = 16384`])))));;
let C8A_BACK2 = prove(c8a_back2,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val (word k:int32) = k /\ val (word n:int32) = n` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  R5B_INIT_TAC THEN R5B_RUN R5B_EXEC [2706; 4391] THEN
  ENSURES_FINAL_STATE_TAC THEN FIRST [DISJ1_TAC THEN R5B_CLOSE1; DISJ2_TAC THEN R5B_CLOSE1;
     DISJ1_TAC THEN C8A_CLOSE1 [] ; DISJ2_TAC THEN C8A_CLOSE1 []] );;
let C8A_APPEND2V = prove(c8a_app2v,
  STRIP_TAC THEN REWRITE_TAC[R5B_PUSH_SNOC; R5B_PUSH1_ND; C8A_REC2_EQ; va1_rec12] THEN
  SUBGOAL_THEN `val (word_add nd (word (LENGTH (L:(num->int32)list))):int32) = n` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`nd:int32`; `LENGTH (L:(num->int32)list)`] R5B_VAL_INC) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[R5B_PUSH_ND] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_SUB_0; COND_ID; va1_w32s] THEN REPEAT CONJ_TAC THEN X_GEN_TAC `w:num` THEN DISCH_TAC THENL
   [COND_CASES_TAC THENL [C8A_DI_SLOT_TAC_G c8a_b2v_cs; C8A_DI_FRAME_TAC_G c8a_b2v_cs];
    C8A_ZQZP2_TAC c8a_b2v_cs 11 1163264; C8A_ZQZP2_TAC c8a_b2v_cs 12 1171456]);;
let c8a_L2n = `if va1_b2_ok mdl tbl t rb k then APPEND (L:(num->int32)list) [va1_b2_rec mdl hp tbl t rb k] else L`;;
let c8a_nn2 = mk_binop `(+):num->num->num` `val (nd:int32)` (mk_comb(`LENGTH:(num->int32)list->num`, c8a_L2n));;
let c8a_core2_post = mk_abs(`s:wasmstate`, mk_disj(
   list_mk_conj [r5b_body_m 2706 r5b_L2 (c8a_setn 1 (c8a_wn c8a_nn2) c8a_base2k1)
                    (c8a_mivL c8a_L2n `read wmem (s:wasmstate)`); `k + 1 < 2048`; mk_binop `(<):num->num->bool` c8a_nn2 `16384`],
   list_mk_conj [r5b_body_m 4391 [Blk 6084] (c8a_setn 1 (c8a_wn c8a_nn2) c8a_base2x) (c8a_mivL c8a_L2n `read wmem (s:wasmstate)`);
                 mk_disj(`k = 2047`, mk_eq(c8a_nn2, `16384`)); mk_binop `(<=):num->num->bool` c8a_nn2 `16384`]));;
let c8a_core2 = list_mk_forall([`m0:int64->byte`;`L:(num->int32)list`;`n:num`;`k:num`;`t:int32`;`di:num->int32`;`zq:num->int32`;
   `zp:num->int32`;`nd:int32`;`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;`rb:num->int32`;`ra:num->int32`],
  mk_imp(list_mk_conj [`k < 2048`; `n < 16384`; `val (nd:int32) + LENGTH (L:(num->int32)list) = n`; c8a_zb;
                       c8a_mivL `L:(num->int32)list` `m0:int64->byte`],
    r5b_ens (r5b_pred 2706 r5b_L2 c8a_base2 []) c8a_core2_post));;
let c8a_X4 = mk_pair(assoc 31 c8a_trk2v, mk_pair(`word 0:int64`, `word 4611686018427387904:int64`));;
let c8a_m2pre = mk_abs(`s:wasmstate`, mk_exists(`m1:int64->byte`,
   mk_conj(subst [`m1:int64->byte`,`m0:int64->byte`] (r5b_bd(r5b_pred 4363 r5b_L2 c8a_base2n1 [])),
           mk_conj(c8a_b2v_cur, c8a_inputs `m1:int64->byte`))));;
let C8A_LIVE2_TAC : tactic =
  R5B_PURE_TAC THEN
  C8A_USE [] C8A_SEGG THEN C8A_USEQ c8a_X4 C8A_ISQT4 THEN C8A_USE [] C8A_SEGH THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC c8a_m2pre THEN CONJ_TAC THENL
   [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_TAC THEN
    EXISTS_TAC `read wmem (s:wasmstate)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  R5B_EXISTS_TAC THEN X_GEN_TAC `m1:int64->byte` THEN MATCH_MP_TAC R5B_ENS_PRE_CONJ THEN STRIP_TAC THEN
  W(fun (asl,w) -> ASSUME_TAC (MP C8A_APPEND2V (TAC_PROOF((asl, lhand(concl C8A_APPEND2V)),
                     REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC)))) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> mem (concl th) c8a_b2v_cs))) THEN
  SUBGOAL_THEN (mk_eq(mk_binop `(+):num->num->num` `val (nd:int32)` (mk_comb(`LENGTH:(num->int32)list->num`,
       mk_comb(mk_comb(`APPEND:(num->int32)list->(num->int32)list->(num->int32)list`, `L:(num->int32)list`), mk_list([c8a_rec2], `:num->int32`)))),
       `n + 1`)) ASSUME_TAC THENL [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  W(fun (asl,w) -> C8A_THEN (r5b_inst2 asl (INST [`m1:int64->byte`,`m0:int64->byte`; `n + 1`,`n:num`] (SPEC_ALL C8A_BACK2)))) THEN
  MATCH_MP_TAC R5B_ENS_NOW THEN C8A_FINW;;
let C8A_SKIP2_TAC : tactic =
  R5B_PURE_TAC THEN
  W(fun (asl,w) -> C8A_THEN (r5b_inst2 asl (SPEC_ALL C8A_BACK2))) THEN
  MATCH_MP_TAC R5B_ENS_NOW THEN C8A_FINW;;
let C8A_CORE2 = prove(c8a_core2,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C8A_USE [] C8A_SEGF THEN R5B_DISJ_TAC THEN CONJ_TAC THENL [C8A_LIVE2_TAC; C8A_SKIP2_TAC]);;
(* loop 2 on the fold: the list starts at L0 (loop 1's output) *)
let c8a_L2f k = subst [k,`K:num`] `va1_fold2 mdl hp tbl t rb nd K (L0:(num->int32)list)`;;
let c8a_n2 kk = mk_binop `(+):num->num->num` `val (nd:int32)` (mk_comb(`LENGTH:(num->int32)list->num`, c8a_L2f kk));;
let c8a_mivk2 kk m = c8a_mivL (c8a_L2f kk) m;;
let c8a_head2v kk = mk_abs(`s:wasmstate`, r5b_body_m 2706 r5b_L2 (c8a_setn 1 (c8a_wn (c8a_n2 kk)) (c8a_setn 15 (c8a_wn kk) c8a_base2))
                                            (c8a_mivk2 kk `read wmem (s:wasmstate)`));;
let c8a_exit2v = mk_abs(`s:wasmstate`, mk_conj(r5b_body_m 4391 [Blk 6084] (c8a_setn 1 (c8a_wn (c8a_n2 `2048`)) c8a_base2x)
                                            (c8a_mivk2 `2048` `read wmem (s:wasmstate)`), mk_binop `(<=):num->num->bool` (c8a_n2 `2048`) `16384`));;
let c8a_iter2v_post = mk_abs(`s:wasmstate`, mk_disj(
   list_mk_conj [r5b_bd (c8a_head2v `k + 1`); `k + 1 < 2048`; mk_binop `(<):num->num->bool` (c8a_n2 `k + 1`) `16384`],
   r5b_bd c8a_exit2v));;
let c8a_iter2v_vars = [`k:num`;`t:int32`;`di:num->int32`;`zq:num->int32`;`zp:num->int32`;`nd:int32`;`mdl:num->int32`;
   `hp:num->int32`;`tbl:num->int32`;`rb:num->int32`;`ra:num->int32`;`L0:(num->int32)list`];;
let c8a_iter2v = list_mk_forall(c8a_iter2v_vars,
  mk_imp(list_mk_conj [`k < 2048`; mk_binop `(<):num->num->bool` (c8a_n2 `k:num`) `16384`; c8a_zb],
    r5b_ens (c8a_head2v `k:num`) c8a_iter2v_post));;
let c8a_step2_stmt = list_mk_forall([`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;`t:int32`;`rb:num->int32`;`nd:int32`;
   `L0:(num->int32)list`;`k:num`],
  mk_imp(mk_conj(`k < 2048`, mk_binop `(<):num->num->bool` (c8a_n2 `k:num`) `16384`),
    mk_eq(c8a_L2f `k + 1`, subst [c8a_L2f `k:num`,`L:(num->int32)list`] c8a_L2n)));;
let C8A_STEP2 = prove(c8a_step2_stmt,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM ADD1; va1_fold2; va1_step2] THEN
  SUBGOAL_THEN (mk_neg(mk_binop `(<=):num->num->bool` `16384` (c8a_n2 `k:num`))) (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;
let c8a_to2048b_stmt = list_mk_forall([`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;`t:int32`;`rb:num->int32`;`nd:int32`;
   `L0:(num->int32)list`;`k:num`],
  mk_imp(mk_conj(`k < 2048`, mk_disj(`k = 2047`, mk_binop `(<=):num->num->bool` `16384` (c8a_n2 `k + 1`))),
    mk_eq(c8a_L2f `2048`, c8a_L2f `k + 1`)));;
let C8A_TO2048B = prove(c8a_to2048b_stmt,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC) THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    MP_TAC(SPECL [`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;`t:int32`;`rb:num->int32`;`nd:int32`;`k + 1`;
                  `L0:(num->int32)list`; `2047 - k`] C8A_FOLD2_CAP) THEN
    ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `(k + 1) + (2047 - k) = 2048` SUBST1_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]]]);;
let C8A_ITER2V = prove(c8a_iter2v,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  EXISTS_TAC (mk_abs(`s:wasmstate`, mk_exists(`m0:int64->byte`,
     mk_conj(r5b_bd(r5b_pred 2706 r5b_L2 (c8a_setn 1 (c8a_wn (c8a_n2 `k:num`)) c8a_base2) []), c8a_mivk2 `k:num` `m0:int64->byte`)))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_TAC THEN
    EXISTS_TAC `read wmem (s:wasmstate)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  R5B_EXISTS_TAC THEN X_GEN_TAC `m0:int64->byte` THEN
  MATCH_MP_TAC R5B_ENS_PRE_CONJ THEN STRIP_TAC THEN
  W(fun (asl,w) -> C8A_THEN (r5b_inst2 asl (INST [c8a_L2f `k:num`, `L:(num->int32)list`; c8a_n2 `k:num`, `n:num`] (SPEC_ALL C8A_CORE2)))) THEN
  MATCH_MP_TAC R5B_ENS_NOW THEN X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  W(fun (asl,w) -> let e = r5b_inst2 asl (SPEC_ALL C8A_STEP2) in REWRITE_TAC[GSYM e]) THEN
  DISCH_THEN(DISJ_CASES_THEN (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THENL
   [DISJ1_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISJ2_TAC THEN W(fun (asl,w) -> SUBST1_TAC (r5b_inst2 asl (SPEC_ALL C8A_TO2048B))) THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;
let c8a_loop2v = mk_forall(`d:num`, list_mk_forall(c8a_iter2v_vars,
  mk_imp(list_mk_conj [`k + d = 2047`; mk_binop `(<):num->num->bool` (c8a_n2 `k:num`) `16384`; c8a_zb],
    r5b_ens (c8a_head2v `k:num`) c8a_exit2v)));;
let C8A_LOOP2V = prove(c8a_loop2v,
  INDUCT_TAC THEN (REPEAT GEN_TAC THEN STRIP_TAC THEN
  W(fun (asl,w) -> let it = r5b_inst2 asl C8A_ITER2V in
    MATCH_MP_TAC R5B_ENS_TRANS THEN EXISTS_TAC (rand(rator(concl it))) THEN CONJ_TAC THENL [ACCEPT_TAC it; ALL_TAC]) THEN
  R5B_DISJ_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC R5B_ENS_PRE_CONJ THEN STRIP_TAC THEN
    FIRST [MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC;
           FIRST_X_ASSUM(MP_TAC o SPECL (`k + 1` :: tl c8a_iter2v_vars)) THEN
           ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; REWRITE_TAC[]]];
    MATCH_MP_TAC R5B_ENS_NOW THEN REWRITE_TAC[]]));;
