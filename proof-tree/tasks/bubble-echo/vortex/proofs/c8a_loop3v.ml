(* vortex-chain C8a (Claude Opus 5.5, 2026-11-15), row A6: loop 3 (antipode) with values. SEGI 4493->4700|6027 (RA/RB
   band, hash; loads RA[k], RB[k], the TBL pair at the clamped-radius column via C8A_TBLADDR3/C8A_J3BOUND, hp), SEGJ
   4700->6027 (record stores), BACK3 6027->4493|6085, APPEND3V, CORE3, STEP3/TO2048C, ITER3V, LOOP3V (head k -> exit 6085). *)
let c8a_base3 = [0,`word k:int32`; 14,`word n:int32`; 3,`word_add t (word 1):int32`;
  5,`word_add (word_mul ((mdl:num->int32) 2) (word 3266489909)) (word 1922313584):int32`;
  7,`word_add (word_mul ((mdl:num->int32) 2) (word 3266489909)) (word 3131848719):int32`;
  8,`word_add (word_mul ((mdl:num->int32) 2) (word 3266489909)) (word 4160326106):int32`;
  9,`word_add (word_mul ((mdl:num->int32) 2) (word 3266489909)) (word 893836197):int32`;
  11,`word (2097152 * k):int32`; 12,`word (65536 + 512 * k):int32`; 13,`word (1130496 + 4 * k):int32`; 15,`word (1138688 + 4 * k):int32`];;
let c8a_mem3 = `va1_w32s 1138688 2048 rb m0 /\ va1_w32s 1130496 2048 ra m0 /\ va1_w32s 65536 262144 tbl m0 /\ va1_w32s 16408 26 hp m0`;;
let c8a_seg3v p q = list_mk_forall([`m0:int64->byte`;`k:num`;`n:num`;`t:int32`;`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;
   `rb:num->int32`;`ra:num->int32`], mk_imp(mk_conj(`k < 2048 /\ n < 16384`, c8a_mem3), r5b_ens p q));;
let c8a_V3 = c8a_letvals va1_b3_rec;;
let c8a_v3 n = assoc n c8a_V3;;
let c8a_ok3 = `va1_b3_ok mdl ra rb k`;;
let c8a_hpl3 = map (fun (l,i) -> (l, subst [mk_small_numeral i,`i:num`] `word_sx ((hp:num->int32) i):int64`))
  [34,3; 37,9; 22,6; 36,4; 25,10; 23,7; 17,5; 21,11; 24,8];;
let c8a_trk3v = c8a_base3 @ [19, `(rb:num->int32) k`; 32, `word_mul (word_xor (word k) (word 2654435769)) (word 2246822507):int32`;
   18, c8a_v3 "a"; 27, c8a_v3 "b"] @ c8a_hpl3;;
let c8a_segI = c8a_seg3v (r5b_pred 4493 r5b_L3 c8a_base3 [])
   (mk_abs(`s:wasmstate`, mk_disj(r5b_body 4700 r5b_L3B c8a_trk3v [c8a_ok3], r5b_body 6027 r5b_L3 c8a_base3 [mk_neg c8a_ok3])));;
let C8A_SEGI_DEFS = [va1_b3_ok; va1_ck_hfin];;
let C8A_AND508 = prove(`!x:int32. word_and x (word 508) = word (4 * (val (word_and x (word 508):int32) DIV 4)) /\
                                  val (word_and x (word 508):int32) DIV 4 <= 127`,
  GEN_TAC THEN
  SUBGOAL_THEN `val (word_and x (word 508):int32) MOD 4 = 0 /\ val (word_and x (word 508):int32) < 512` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`word_and x (word 508):int32`; `2`] VAL_WORD_AND_MASK_WORD) THEN
    MP_TAC(ISPECL [`word_and x (word 508):int32`; `9`] VAL_WORD_AND_MASK_WORD) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_BLAST `word_and (word_and x (word 508)) (word 3):int32 = word 0`;
                WORD_BLAST `word_and (word_and x (word 508)) (word 511):int32 = word_and x (word 508)`; VAL_WORD_0] THEN
    MP_TAC(SPECL [`val (word_and x (word 508):int32)`; `512`] MOD_LT_EQ) THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`val (word_and x (word 508):int32)`; `4`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  CONJ_TAC THENL [GEN_REWRITE_TAC LAND_CONV [GSYM WORD_VAL] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;
let C8A_TBLADDR3 = prove(`!k x:int32. k < 2048 ==>
   val (word_add (word (65536 + 512 * k)) (word_and x (word 508)):int32) = 65536 + 4 * (128 * k + val (word_and x (word 508):int32) DIV 4) /\
   val (word_add (word_add (word (65536 + 512 * k)) (word_and x (word 508))) (word 4):int32) =
     65536 + 4 * (128 * k + val (word_and x (word 508):int32) DIV 4 + 1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPEC `x:int32` C8A_AND508) THEN
  ABBREV_TAC `J = val (word_and x (word 508):int32) DIV 4` THEN STRIP_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `65536 + 4 * (128 * k + J) = (65536 + 512 * k) + 4 * J`;
              ARITH_RULE `65536 + 4 * (128 * k + J + 1) = ((65536 + 512 * k) + 4 * J) + 4`] THEN
  CONJ_TAC THEN MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC);;
let C8A_J3BOUND = prove(`!r:int32. val r <= 66584575 ==> val (word_and (word_ushr r 17) (word 508):int32) DIV 4 <= 126`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`word_ushr r 17:int32`; `word 508:int32`] (CONJUNCT1 VAL_WORD_AND_LE)) THEN REWRITE_TAC[VAL_WORD_USHR] THEN
  MP_TAC(SPECL [`val (r:int32)`; `66584575`; `2 EXP 17`] DIV_MONO) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`val (word_and (word_ushr r 17) (word 508):int32)`; `4`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;
let c8a_rc3 = `if ~(val ((rb:num->int32) k) < 66584575) then word 66584575 else rb k`;;
let c8a_jj3 = subst [c8a_rc3,`rcx:int32`] `val (word_and (word_ushr (rcx:int32) 17) (word 508):int32) DIV 4`;;
let C8A_TBL3_LOADS : tactic =
  SUBGOAL_THEN (mk_binop `(<=):num->num->bool` (mk_comb(`val:int32->num`, c8a_rc3)) `66584575`) ASSUME_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; mk_comb(mk_comb(`word_ushr:int32->num->int32`, c8a_rc3), `17`)] C8A_TBLADDR3) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(fun th -> if is_binary "<=" (concl th) && lhand(concl th) = mk_comb(`val:int32->num`, c8a_rc3)
                        then ASSUME_TAC (MATCH_MP C8A_J3BOUND th) else failwith "") THEN
  C8A_LOAD_TAC (subst [c8a_jj3,`J:num`] `65536 + 4 * (128 * k + J)`) (subst [c8a_jj3,`J:num`] `128 * k + J`)
     `tbl:num->int32` 65536 `va1_w32s 65536 262144 tbl m0` THEN
  C8A_LOAD_TAC (subst [c8a_jj3,`J:num`] `65536 + 4 * (128 * k + J + 1)`) (subst [c8a_jj3,`J:num`] `128 * k + J + 1`)
     `tbl:num->int32` 65536 `va1_w32s 65536 262144 tbl m0`;;
let C8A_SEGI_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN `val (word (1130496 + 4 * k):int32) = 1130496 + 4 * k /\ val (word (1138688 + 4 * k):int32) = 1138688 + 4 * k /\
                val (word (65536 + 512 * k):int32) = 65536 + 512 * k` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  C8A_LOAD_TAC `1130496 + 4 * k` `k:num` `ra:num->int32` 1130496 `va1_w32s 1130496 2048 ra m0` THEN
  C8A_LOAD_TAC `1138688 + 4 * k` `k:num` `rb:num->int32` 1138688 `va1_w32s 1138688 2048 rb m0` THEN
  C8A_TBL3_LOADS THEN C8A_HP_LOADS THEN
  R5B_INIT_TAC THEN R5B_RUN R5B_EXEC [4700; 6027] THEN C8A_FIN C8A_SEGI_DEFS;;
let C8A_SEGI = prove(c8a_segI, C8A_SEGI_TAC);;
let c8a_bornv ws m0 m =
  let b = r5b_born2_at m0 m in
  let cs = conjuncts b in
  let words = map (fun (j,v) -> subst [mk_small_numeral j,`j:num`; v,`V:int32`; m,`m:int64->byte`]
                     `read (bytes32 (word (1179648 + 4 * (12 * n + j)))) (m:int64->byte) = V`) (zip (0--9) ws) in
  list_mk_conj([el 0 cs] @ words @ [el 3 cs; el 4 cs; el 5 cs]);;
let c8a_w3 = [c8a_v3 "w0"; c8a_v3 "w1"; c8a_v3 "w2"; c8a_v3 "w3"; c8a_v3 "w4"; c8a_v3 "w5"; `word_add t (word 1):int32`;
              `word_add (word k) (word 131072):int32`; `word 0:int32`; `word 0:int32`];;
let c8a_born3v = c8a_bornv c8a_w3;;
let c8a_base3n1 = c8a_setn 14 `word (n + 1):int32` c8a_base3;;
let c8a_segJ = list_mk_forall([`m0:int64->byte`;`k:num`;`n:num`;`t:int32`;`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;
   `rb:num->int32`;`ra:num->int32`],
  mk_imp(list_mk_conj [`k < 2048 /\ n < 16384`; c8a_mem3; `va1_mdl mdl m0`],
   r5b_ens (r5b_pred 4700 r5b_L3B c8a_trk3v [c8a_ok3])
   (mk_abs(`s:wasmstate`, r5b_body_m 6027 r5b_L3 c8a_base3n1
      (mk_conj(c8a_born3v `m0:int64->byte` `read wmem (s:wasmstate)`, c8a_inputs `read wmem (s:wasmstate)`))))));;
let C8A_SEGJ = prove(c8a_segJ,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN `val (word (48 * n):int32) = 48 * n` ASSUME_TAC THENL [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  R5B_INIT_TAC THEN C8A_RUN R5B_EXEC [6027] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[injectivity "wval"; R5B_EX_EQ] THEN R5C_EXPAND_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[va1_w32s; va1_mdl]) THEN
  REPEAT CONJ_TAC THEN FIRST [R5B_MEMCLOSE_TAC; C8A_WORD_CLOSE; C8A_EXPAND_ALL THEN R5B_MEMCLOSE_TAC; C8A_INPUT_CLOSE; C8A_W64Z_TAC]);;
let c8a_base3_at kk = map (fun (l,v) -> (l, subst [kk,`k:num`] v)) c8a_base3;;
let c8a_base3k1 = c8a_base3_at `k + 1`;;
let c8a_base3x = filter (fun (l,_) -> mem l [3;14]) c8a_base3;;
let c8a_back3 = list_mk_forall([`m0:int64->byte`;`k:num`;`n:num`;`t:int32`;`mdl:num->int32`],
   mk_imp(`k < 2048 /\ n <= 16384`,
    r5b_ens (r5b_pred 6027 r5b_L3 c8a_base3 [])
     (mk_abs(`s:wasmstate`, mk_disj(
        r5b_body 4493 r5b_L3 c8a_base3k1 [`k + 1 < 2048`; `n < 16384`],
        r5b_body 6085 [] c8a_base3x [`k = 2047 \/ n = 16384`])))));;
let C8A_BACK3 = prove(c8a_back3,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val (word k:int32) = k /\ val (word n:int32) = n` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_add (word (2097152 * k)) (word 2097152):int32 = word (2097152 * (k + 1)) /\
                word_add (word (65536 + 512 * k)) (word 512):int32 = word (65536 + 512 * (k + 1)) /\
                word_add (word (1130496 + 4 * k)) (word 4):int32 = word (1130496 + 4 * (k + 1)) /\
                word_add (word (1138688 + 4 * k)) (word 4):int32 = word (1138688 + 4 * (k + 1))` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  R5B_INIT_TAC THEN R5B_RUN R5B_EXEC [4493; 6085] THEN
  ENSURES_FINAL_STATE_TAC THEN FIRST [DISJ1_TAC THEN R5B_CLOSE1; DISJ2_TAC THEN R5B_CLOSE1;
     DISJ1_TAC THEN C8A_CLOSE1 [] ; DISJ2_TAC THEN C8A_CLOSE1 []] );;
let c8a_b3v_cur = c8a_born3v `m0:int64->byte` `m1:int64->byte`;;
let c8a_b3v_cs = conjuncts c8a_b3v_cur;;
let c8a_rec3 = `va1_b3_rec mdl hp tbl t rb k`;;
let C8A_REC3_EQ = prove(list_mk_forall([`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;`t:int32`;`rb:num->int32`;`k:num`],
   mk_eq(c8a_rec3, list_mk_comb(`va1_rec12`, c8a_w3))),
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_b3_rec] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REFL_TAC);;
let c8a_app3v = mk_imp(list_mk_conj [c8a_miv `L:(num->int32)list` `m0:int64->byte`; `val (nd:int32) + LENGTH (L:(num->int32)list) = n`;
   `n < 16384`; `k < 2048`; r5b_zero_beyond; c8a_b3v_cur],
   c8a_miv (mk_comb(mk_comb(`APPEND:(num->int32)list->(num->int32)list->(num->int32)list`, `L:(num->int32)list`),
                    mk_list([c8a_rec3], `:num->int32`))) `m1:int64->byte`);;
let C8A_APPEND3V = prove(c8a_app3v,
  STRIP_TAC THEN REWRITE_TAC[R5B_PUSH_SNOC; R5B_PUSH1_ND; C8A_REC3_EQ; va1_rec12] THEN
  SUBGOAL_THEN `val (word_add nd (word (LENGTH (L:(num->int32)list))):int32) = n` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`nd:int32`; `LENGTH (L:(num->int32)list)`] R5B_VAL_INC) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[R5B_PUSH_ND] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_SUB_0; COND_ID; va1_w32s] THEN REPEAT CONJ_TAC THEN X_GEN_TAC `w:num` THEN DISCH_TAC THENL
   [COND_CASES_TAC THENL [C8A_DI_SLOT_TAC_G c8a_b3v_cs; C8A_DI_FRAME_TAC_G c8a_b3v_cs];
    C8A_ZQZP2_TAC c8a_b3v_cs 11 1163264; C8A_ZQZP2_TAC c8a_b3v_cs 12 1171456]);;
let c8a_L3n = `if va1_b3_ok mdl ra rb k then APPEND (L:(num->int32)list) [va1_b3_rec mdl hp tbl t rb k] else L`;;
let c8a_nn3 = mk_binop `(+):num->num->num` `val (nd:int32)` (mk_comb(`LENGTH:(num->int32)list->num`, c8a_L3n));;
let c8a_core3_post = mk_abs(`s:wasmstate`, mk_disj(
   list_mk_conj [r5b_body_m 4493 r5b_L3 (c8a_setn 14 (c8a_wn c8a_nn3) c8a_base3k1)
                    (c8a_mivL c8a_L3n `read wmem (s:wasmstate)`); `k + 1 < 2048`; mk_binop `(<):num->num->bool` c8a_nn3 `16384`],
   list_mk_conj [r5b_body_m 6085 [] (c8a_setn 14 (c8a_wn c8a_nn3) c8a_base3x) (c8a_mivL c8a_L3n `read wmem (s:wasmstate)`);
                 mk_disj(`k = 2047`, mk_eq(c8a_nn3, `16384`)); mk_binop `(<=):num->num->bool` c8a_nn3 `16384`]));;
let c8a_core3 = list_mk_forall([`m0:int64->byte`;`L:(num->int32)list`;`n:num`;`k:num`;`t:int32`;`di:num->int32`;`zq:num->int32`;
   `zp:num->int32`;`nd:int32`;`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;`rb:num->int32`;`ra:num->int32`],
  mk_imp(list_mk_conj [`k < 2048`; `n < 16384`; `val (nd:int32) + LENGTH (L:(num->int32)list) = n`; c8a_zb;
                       c8a_mivL `L:(num->int32)list` `m0:int64->byte`],
    r5b_ens (r5b_pred 4493 r5b_L3 c8a_base3 []) c8a_core3_post));;
let c8a_m3pre = mk_abs(`s:wasmstate`, mk_exists(`m1:int64->byte`,
   mk_conj(subst [`m1:int64->byte`,`m0:int64->byte`] (r5b_bd(r5b_pred 6027 r5b_L3 c8a_base3n1 [])),
           mk_conj(c8a_b3v_cur, c8a_inputs `m1:int64->byte`))));;
let C8A_LIVE3_TAC : tactic =
  R5B_PURE_TAC THEN
  C8A_USE [] C8A_SEGJ THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC c8a_m3pre THEN CONJ_TAC THENL
   [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_TAC THEN
    EXISTS_TAC `read wmem (s:wasmstate)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  R5B_EXISTS_TAC THEN X_GEN_TAC `m1:int64->byte` THEN MATCH_MP_TAC R5B_ENS_PRE_CONJ THEN STRIP_TAC THEN
  W(fun (asl,w) -> ASSUME_TAC (MP C8A_APPEND3V (TAC_PROOF((asl, lhand(concl C8A_APPEND3V)),
                     REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC)))) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> mem (concl th) c8a_b3v_cs))) THEN
  SUBGOAL_THEN (mk_eq(mk_binop `(+):num->num->num` `val (nd:int32)` (mk_comb(`LENGTH:(num->int32)list->num`,
       mk_comb(mk_comb(`APPEND:(num->int32)list->(num->int32)list->(num->int32)list`, `L:(num->int32)list`), mk_list([c8a_rec3], `:num->int32`)))),
       `n + 1`)) ASSUME_TAC THENL [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  W(fun (asl,w) -> C8A_THEN (r5b_inst2 asl (INST [`m1:int64->byte`,`m0:int64->byte`; `n + 1`,`n:num`] (SPEC_ALL C8A_BACK3)))) THEN
  MATCH_MP_TAC R5B_ENS_NOW THEN C8A_FINW;;
let C8A_SKIP3_TAC : tactic =
  R5B_PURE_TAC THEN
  W(fun (asl,w) -> C8A_THEN (r5b_inst2 asl (SPEC_ALL C8A_BACK3))) THEN
  MATCH_MP_TAC R5B_ENS_NOW THEN C8A_FINW;;
let C8A_CORE3 = prove(c8a_core3,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C8A_USE [] C8A_SEGI THEN R5B_DISJ_TAC THEN CONJ_TAC THENL [C8A_LIVE3_TAC; C8A_SKIP3_TAC]);;
(* loop 2 on the fold: the list starts at L0 (loop 1's output) *)
let c8a_L3f k = subst [k,`K:num`] `va1_fold3 mdl hp tbl t ra rb nd K (L0:(num->int32)list)`;;
let c8a_n3 kk = mk_binop `(+):num->num->num` `val (nd:int32)` (mk_comb(`LENGTH:(num->int32)list->num`, c8a_L3f kk));;
let c8a_mivk3 kk m = c8a_mivL (c8a_L3f kk) m;;
let c8a_head3v kk = mk_abs(`s:wasmstate`, r5b_body_m 4493 r5b_L3 (c8a_setn 14 (c8a_wn (c8a_n3 kk)) (c8a_base3_at kk))
                                            (c8a_mivk3 kk `read wmem (s:wasmstate)`));;
let c8a_exit3v = mk_abs(`s:wasmstate`, mk_conj(r5b_body_m 6085 [] (c8a_setn 14 (c8a_wn (c8a_n3 `2048`)) c8a_base3x)
                                            (c8a_mivk3 `2048` `read wmem (s:wasmstate)`), mk_binop `(<=):num->num->bool` (c8a_n3 `2048`) `16384`));;
let c8a_iter3v_post = mk_abs(`s:wasmstate`, mk_disj(
   list_mk_conj [r5b_bd (c8a_head3v `k + 1`); `k + 1 < 2048`; mk_binop `(<):num->num->bool` (c8a_n3 `k + 1`) `16384`],
   r5b_bd c8a_exit3v));;
let c8a_iter3v_vars = [`k:num`;`t:int32`;`di:num->int32`;`zq:num->int32`;`zp:num->int32`;`nd:int32`;`mdl:num->int32`;
   `hp:num->int32`;`tbl:num->int32`;`rb:num->int32`;`ra:num->int32`;`L0:(num->int32)list`];;
let c8a_iter3v = list_mk_forall(c8a_iter3v_vars,
  mk_imp(list_mk_conj [`k < 2048`; mk_binop `(<):num->num->bool` (c8a_n3 `k:num`) `16384`; c8a_zb],
    r5b_ens (c8a_head3v `k:num`) c8a_iter3v_post));;
let c8a_step3_stmt = list_mk_forall([`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;`t:int32`;`ra:num->int32`;`rb:num->int32`;`nd:int32`;
   `L0:(num->int32)list`;`k:num`],
  mk_imp(mk_conj(`k < 2048`, mk_binop `(<):num->num->bool` (c8a_n3 `k:num`) `16384`),
    mk_eq(c8a_L3f `k + 1`, subst [c8a_L3f `k:num`,`L:(num->int32)list`] c8a_L3n)));;
let C8A_STEP3 = prove(c8a_step3_stmt,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM ADD1; va1_fold3; va1_step3] THEN
  SUBGOAL_THEN (mk_neg(mk_binop `(<=):num->num->bool` `16384` (c8a_n3 `k:num`))) (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;
let c8a_to2048c_stmt = list_mk_forall([`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;`t:int32`;`ra:num->int32`;`rb:num->int32`;`nd:int32`;
   `L0:(num->int32)list`;`k:num`],
  mk_imp(mk_conj(`k < 2048`, mk_disj(`k = 2047`, mk_binop `(<=):num->num->bool` `16384` (c8a_n3 `k + 1`))),
    mk_eq(c8a_L3f `2048`, c8a_L3f `k + 1`)));;
let C8A_TO2048C = prove(c8a_to2048c_stmt,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC) THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    MP_TAC(SPECL [`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;`t:int32`;`ra:num->int32`;`rb:num->int32`;`nd:int32`;`k + 1`;
                  `L0:(num->int32)list`; `2047 - k`] C8A_FOLD3_CAP) THEN
    ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `(k + 1) + (2047 - k) = 2048` SUBST1_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]]]);;
let C8A_ITER3V = prove(c8a_iter3v,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  EXISTS_TAC (mk_abs(`s:wasmstate`, mk_exists(`m0:int64->byte`,
     mk_conj(r5b_bd(r5b_pred 4493 r5b_L3 (c8a_setn 14 (c8a_wn (c8a_n3 `k:num`)) c8a_base3) []), c8a_mivk3 `k:num` `m0:int64->byte`)))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_TAC THEN
    EXISTS_TAC `read wmem (s:wasmstate)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  R5B_EXISTS_TAC THEN X_GEN_TAC `m0:int64->byte` THEN
  MATCH_MP_TAC R5B_ENS_PRE_CONJ THEN STRIP_TAC THEN
  W(fun (asl,w) -> C8A_THEN (r5b_inst2 asl (INST [c8a_L3f `k:num`, `L:(num->int32)list`; c8a_n3 `k:num`, `n:num`] (SPEC_ALL C8A_CORE3)))) THEN
  MATCH_MP_TAC R5B_ENS_NOW THEN X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  W(fun (asl,w) -> let e = r5b_inst2 asl (SPEC_ALL C8A_STEP3) in REWRITE_TAC[GSYM e]) THEN
  DISCH_THEN(DISJ_CASES_THEN (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THENL
   [DISJ1_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISJ2_TAC THEN W(fun (asl,w) -> SUBST1_TAC (r5b_inst2 asl (SPEC_ALL C8A_TO2048C))) THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;
let c8a_loop3v = mk_forall(`d:num`, list_mk_forall(c8a_iter3v_vars,
  mk_imp(list_mk_conj [`k + d = 2047`; mk_binop `(<):num->num->bool` (c8a_n3 `k:num`) `16384`; c8a_zb],
    r5b_ens (c8a_head3v `k:num`) c8a_exit3v)));;
let C8A_LOOP3V = prove(c8a_loop3v,
  INDUCT_TAC THEN (REPEAT GEN_TAC THEN STRIP_TAC THEN
  W(fun (asl,w) -> let it = r5b_inst2 asl C8A_ITER3V in
    MATCH_MP_TAC R5B_ENS_TRANS THEN EXISTS_TAC (rand(rator(concl it))) THEN CONJ_TAC THENL [ACCEPT_TAC it; ALL_TAC]) THEN
  R5B_DISJ_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC R5B_ENS_PRE_CONJ THEN STRIP_TAC THEN
    FIRST [MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC;
           FIRST_X_ASSUM(MP_TAC o SPECL (`k + 1` :: tl c8a_iter3v_vars)) THEN
           ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; REWRITE_TAC[]]];
    MATCH_MP_TAC R5B_ENS_NOW THEN REWRITE_TAC[]]));;
