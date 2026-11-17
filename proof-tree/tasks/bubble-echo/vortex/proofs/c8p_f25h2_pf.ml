(* ========================================================================= *)
(* c8p_f25h2_pf.ml (vortex-chain-20261111-142342 c8p, Claude Opus 5.5,        *)
(* 2026-11-14): C8p row P5, VA1_F25_HDR = VA1_F25_OK plus the 21 header words *)
(* va1_w32s 16420 21 (va1_phdr a0 a1 a2), on the exact f25 bytes. Spec       *)
(* c8p_f25h2.spec (v2)    . Reuses the C3b driver and tactics of      *)
(* chain_c3b_l1.ml (in the basis) unchanged: value-tracking isqrt loops      *)
(* (ITER induction), PRO/MID/HDRA segments with named locals, loop 3 by      *)
(* induction (C8P_IT3/C8P_LOOP3), C8P_FOLD, and copies of C3b's IT4/LOOP4/   *)
(* IT5/LOOP5/TAIL carrying va1_w32s 16420 21 h. No axioms, no cheats.      *)
(* ========================================================================= *)
needs "c8p_f25h2_defs.ml";;
(* ---- C8p P5: generic isqrt loop with values ---- *)
let C8P_ISQ_BODY_EQ = prove
 (`!r b v:int64. va1_isq_body (r,b,v) =
     (word_sub r (if ~(val r < val (word_add b v)) then word_add b v else word 0), word_ushr b 2,
      word_add (if ~(val r < val (word_add b v)) then b else word 0) (word_ushr v 1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_isq_body] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[FST; SND] THEN COND_CASES_TAC THEN
  REWRITE_TAC[WORD_SUB_0; WORD_ADD_0; WORD_ADD_SYM] THEN REWRITE_TAC[WORD_ADD_0]);;
let c8p_it c = list_mk_icomb "ITER" [c; `va1_isq_body`; `(r:int64,b:int64,v:int64)`];;
let c8p_isq_post_trk c = [6, mk_icomb(`FST:int64#int64#int64->int64`, c8p_it c);
                          7, mk_icomb(`FST:int64#int64->int64`, mk_icomb(`SND:int64#int64#int64->int64#int64`, c8p_it c));
                          9, mk_icomb(`SND:int64#int64->int64`, mk_icomb(`SND:int64#int64#int64->int64#int64`, c8p_it c))];;
let c8p_isq_stmt lp ep trk =
  let bp = lp + 2 in
  let pre = c3b_pred bp [Lp lp] ((8,`word c:int32`) :: (6,`r:int64`) :: (7,`b:int64`) :: (9,`v:int64`) :: trk) [] in
  let post = c3b_pred ep [] (c8p_isq_post_trk `c:num` @ trk) [] in
  let e = c3b_ens pre post in
  let vs = subtract (frees e) [`c:num`] in
  mk_forall(`c:num`, mk_imp(`1 <= c /\ c <= 32`, list_mk_forall(vs, e)));;
let c8p_rbv' = [6, `word_sub (r:int64) (if ~(val r < val (word_add (b:int64) (v:int64))) then word_add b v else word 0)`;
                7, `word_ushr (b:int64) 2`; 9, `word_add (if ~(val (r:int64) < val (word_add (b:int64) (v:int64))) then b else word 0) (word_ushr v 1)`];;
let C8P_ISQ_TAC name lp ep trk : tactic =
  let bp = lp + 2 in
  INDUCT_TAC THENL [ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ITER_ALT; C8P_ISQ_BODY_EQ] THEN
  MP_TAC(SPEC `c:num` C3B_DEC1) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC)] THEN
  ASM_CASES_TAC `c = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[ITER_ALT] THEN
    C3B_INIT_TAC THEN c3b_time name (C3B_RUN1 C3B_EXEC [ep; bp]) THEN C3B_FIN_TAC;
    ENSURES_SEQUENCE_TAC (mk_small_numeral bp) (c3b_rest (c3b_pred bp [Lp lp] ((8, `word c:int32`) :: c8p_rbv' @ trk) [])) THEN
    CONJ_TAC THENL
     [C3B_INIT_TAC THEN c3b_time name (C3B_RUN1 C3B_EXEC [ep; bp]) THEN C3B_FIN_TAC;
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && is_forall(rand(concl th)))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(fun th -> MATCH_ACCEPT_TAC th)]]];;
let c8p_trk1 = [0,`a0:int32`; 1,`a1:int32`; 2,`a2:int32`; 3,`x3:int64`; 4,`x4:int64`; 5,`x5:int64`];;
let c8p_trk2 = c8p_trk1 @ [12,`x12:int64`; 13,`x13:int64`; 14,`x14:int64`];;

let C8P_ISQ1 = prove(c8p_isq_stmt 96 152 c8p_trk1, C8P_ISQ_TAC "isq1" 96 152 c8p_trk1);;
let C8P_ISQ2 = prove(c8p_isq_stmt 273 329 c8p_trk2, C8P_ISQ_TAC "isq2" 273 329 c8p_trk2);;

let c8p_sq3 a b c = list_mk_icomb "word_add" [list_mk_icomb "word_add" [list_mk_icomb "word_mul" [a;a]; list_mk_icomb "word_mul" [b;b]]; list_mk_icomb "word_mul" [c;c]];;
let c8p_trkPRO = [8,`word 32:int32`; 0,`a0:int32`; 1,`a1:int32`; 2,`a2:int32`; 3,`word_sx (a1:int32):int64`; 4,`word_sx (a0:int32):int64`;
   5,`word_sx (a2:int32):int64`; 6, c8p_sq3 `word_sx (a1:int32):int64` `word_sx (a0:int32):int64` `word_sx (a2:int32):int64`;
   7,`word 4611686018427387904:int64`; 9,`word 0:int64`];;
let C8P_VCLOSE_TAC = ASM_REWRITE_TAC[injectivity "wval"; C3B_EX_EQ] THEN REWRITE_TAC[va1_fix30; COND_SWAP] THEN
  CONV_TAC(DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV)) THEN ASM_REWRITE_TAC[injectivity "wval"; C3B_EX_EQ];;
let C8P_VSEG_TAC name stops : tactic =
  REPEAT GEN_TAC THEN TRY(DISCH_THEN STRIP_ASSUME_TAC) THEN C3B_INIT_TAC THEN
  c3b_time name (C3B_RUN C3B_EXEC stops) THEN ENSURES_FINAL_STATE_TAC THEN C8P_VCLOSE_TAC;;
let C8P_PRO = prove(c3b_seg `read (bytes32 (word 16396)) m0 = word 4294967295 /\ ~(word_or (word_or (a1:int32) a0) a2 = word 0)`
   (c3b_pred 13 [] c3b_trk0 []) (c3b_pred 98 [Lp 96] c8p_trkPRO []),
  C8P_VSEG_TAC "pro" [98]);;
let c8p_n1 = `va1_fix30 x3 v` and c8p_n0 = `va1_fix30 x4 v` and c8p_n2 = `va1_fix30 x5 v`;;
let c8p_c = `val (word_sub (word_xor (va1_fix30 x3 v) (word_ishr (va1_fix30 x3 v) 63)) (word_ishr (va1_fix30 x3 v) 63)) < 1020054733`;;
let c8p_y0 = mk_cond(c8p_c, c8p_n2, `word 0:int64`) and c8p_y1 = mk_cond(c8p_c, `word 0:int64`, mk_icomb(mk_icomb(`word_sub:int64->int64->int64`, `word 0:int64`), c8p_n2))
and c8p_y2 = mk_cond(c8p_c, mk_icomb(mk_icomb(`word_sub:int64->int64->int64`, `word 0:int64`), c8p_n0), c8p_n1);;
let c8p_trkMIDpre = [0,`a0:int32`; 1,`a1:int32`; 2,`a2:int32`; 3,`x3:int64`; 4,`x4:int64`; 5,`x5:int64`; 6,`x6:int64`; 7,`x7:int64`; 9,`v:int64`];;
let c8p_trkMIDpost = [8,`word 32:int32`; 0,`a0:int32`; 1,`a1:int32`; 2,`a2:int32`; 3,c8p_n1; 4,c8p_n0; 5,c8p_n2;
   6, c8p_sq3 c8p_y0 c8p_y1 c8p_y2; 7,`word 4611686018427387904:int64`; 9,`word 0:int64`; 12,c8p_y0; 13,c8p_y1; 14,c8p_y2];;
let C8P_MID = prove(c3b_seg `T` (c3b_pred 152 [] c8p_trkMIDpre []) (c3b_pred 275 [Lp 273] c8p_trkMIDpost []),
  C8P_VSEG_TAC "mid" [275]);;

let c8p_trkHpre = [0,`a0:int32`; 1,`a1:int32`; 2,`a2:int32`; 3,`y3:int64`; 4,`y4:int64`; 5,`y5:int64`; 6,`x6:int64`; 7,`x7:int64`;
   9,`v:int64`; 12,`y12:int64`; 13,`y13:int64`; 14,`y14:int64`];;
let c8p_hl = `va1_pcross y4 y3 y5 y12 y13 y14 v`;;
let c8p_W9 mv = subst [mv,`m:int64->byte`] `va1_w32s 16420 9 (\k. word_zx (EL k (va1_pcross y4 y3 y5 y12 y13 y14 v)):int32) (m:int64->byte)`;;
let c8p_trk3 ii = [8, list_mk_icomb "va1_hseed" [`a0:int32`;`a1:int32`;`a2:int32`; ii]; 15, mk_comb(`word:num->int32`, mk_binop `( * ):num->num->num` `4` ii)];;
let C8P_HDRA_STMT = c3b_seg `read (bytes32 (word 16392)) m0 = (t:int32) /\ va1_mdl mdl m0 /\ va1_w32s 65536 262144 tbl m0`
   (c3b_pred 329 [] c8p_trkHpre [])
   (mk_abs(`s:wasmstate`, mk_exists(`m1:int64->byte`, list_mk_conj [c3b_bodym `m1:int64->byte` 550 [Lp 548] (c8p_trk3 `0`) [];
      c3b_F `m1:int64->byte`; c8p_W9 `m1:int64->byte`])));;
let C8P_W9_TAC : tactic =
  REWRITE_TAC[va1_w32s] THEN CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN BETA_TAC THEN
  REPEAT CONJ_TAC THEN C3B_MEMFACT_TAC THEN
  REWRITE_TAC[va1_pcross] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[va1_fix30; COND_SWAP];;

let C8P_MEMSPLIT_TAC (w9:tactic) : tactic = fun g ->
  if (match strip_comb (snd g) with (Const("va1_w32s",_), b::_) -> b = `16420` | _ -> false) then w9 g else C3B_MEMFACT_TAC g;;
let C8P_HDRA = prove(C8P_HDRA_STMT,
  REPEAT GEN_TAC THEN TRY(DISCH_THEN STRIP_ASSUME_TAC) THEN C3B_INIT_TAC THEN
  c3b_time "hdra" (C3B_RUN C3B_EXEC [550]) THEN
  ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN C3B_EXISTS_MEM_TAC THEN
  REWRITE_TAC[va1_hseed; ITER; MULT_CLAUSES] THEN C3B_CLOSE_TAC THEN
  REPEAT CONJ_TAC THEN C8P_MEMSPLIT_TAC (c3b_time "w9" C8P_W9_TAC));;

let C8P_EXIT3 = prove(`!i. i < 6 ==> (word_add (word (4 * i)) (word 4):int32 = word 24 <=> i + 1 = 6)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM WORD_ADD; GSYM VAL_EQ] THEN
  SUBGOAL_THEN `val (word (4 * i + 4):int32) = 4 * i + 4 /\ val (word 24:int32) = 24` (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC C3B_VW32 THEN ASM_ARITH_TAC; ARITH_TAC]);;
let C8P_HSEED_SUC = prove(`!a0 a1 a2 i. va1_hseed a0 a1 a2 (i + 1) = word_add (va1_hseed a0 a1 a2 i) (word 3663131626)`,
  REWRITE_TAC[va1_hseed; GSYM ADD1; ITER]);;
let c8p_J ii mv = subst [ii,`i:num`; mv,`m:int64->byte`]
  `!j. j < i ==> read (bytes32 (word (16456 + 4 * j))) (m:int64->byte) = va1_hmix (va1_hseed a0 a1 a2 j) /\
                 read (bytes32 (word (16480 + 4 * j))) m = va1_hjig (va1_hseed a0 a1 a2 j)`;;
let C8P_IT3_STMT = c3b_seg (list_mk_conj [`i < 6`; c3b_F `m0:int64->byte`; c8p_W9 `m0:int64->byte`; c8p_J `i:num` `m0:int64->byte`])
   (c3b_pred 550 [Lp 548] (c8p_trk3 `i:num`) [])
   (mk_abs(`s:wasmstate`, mk_exists(`m1:int64->byte`, list_mk_conj
      [mk_disj(mk_conj(c3b_bodym `m1:int64->byte` 550 [Lp 548] (c8p_trk3 `i + 1`) [], `i + 1 < 6`),
               mk_conj(c3b_bodym `m1:int64->byte` 702 [] [] [], `i + 1 = 6`));
       c3b_F `m1:int64->byte`; c8p_W9 `m1:int64->byte`; c8p_J `i + 1` `m1:int64->byte`])));;
let C8P_L3MEM_TAC : tactic =
  CONJ_TAC THENL [REPEAT CONJ_TAC THEN TRY C3B_ROW_TAC THEN TRY C3B_W32S_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [C3B_W32S_TAC THEN NO_TAC; ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_CASES_TAC `j:num = i` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN C3B_ROW_TAC THEN
    REWRITE_TAC[va1_hmix; va1_hjig] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[];
    C3B_ROW_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (is_forall o concl)) THEN
    ANTS_TAC THENL [C3B_ARITH_TAC; SIMP_TAC[]]];;
let C8P_IT3 = prove(C8P_IT3_STMT,
  REPEAT GEN_TAC THEN TRY(DISCH_THEN STRIP_ASSUME_TAC) THEN C3B_INIT_TAC THEN c3b_time "it3" (C3B_RUN1 C3B_EXEC [550; 702]) THEN
  ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  (CONJ_TAC THENL [ALL_TAC; C3B_VNORM_TAC THEN MONOTONE_MAYCHANGE_TAC]) THEN
  C3B_EXISTS_MEM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `i:num` C8P_EXIT3) (ASSUME `i < 6`)]) THEN
  REWRITE_TAC[C8P_HSEED_SUC] THEN
  C3B_VNORM_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD]) THEN C3B_WNORM_TAC THEN
  (CONJ_TAC THENL [C3B_DISJ_CLOSE_TAC; ALL_TAC]) THEN
  c3b_time "l3mem" C8P_L3MEM_TAC);;

let c8p_L3vars = [`i:num`;`m0:int64->byte`;`t:int32`;`a0:int32`;`a1:int32`;`a2:int32`;`mdl:num->int32`;`tbl:num->int32`;
                  `y3:int64`;`y4:int64`;`y5:int64`;`y12:int64`;`y13:int64`;`y14:int64`;`v:int64`];;
let c8p_L3inv ii mv = list_mk_conj [c3b_F mv; c8p_W9 mv; c8p_J ii mv];;
let c8p_L3post = mk_abs(`s:wasmstate`, mk_exists(`m1:int64->byte`, mk_conj(c3b_bodym `m1:int64->byte` 702 [] [] [], c8p_L3inv `6` `m1:int64->byte`)));;
let C8P_LOOP3_STMT = mk_forall(`d:num`, list_mk_forall(c8p_L3vars,
   mk_imp(mk_conj(`i + d = 5`, c8p_L3inv `i:num` `m0:int64->byte`),
          c3b_ens (c3b_pred 550 [Lp 548] (c8p_trk3 `i:num`) []) c8p_L3post)));;
let C8P_LOOP3 = prove(C8P_LOOP3_STMT,
  INDUCT_TAC THEN (REPEAT GEN_TAC THEN STRIP_TAC THEN
  (MATCH_MP_TAC C3B_ENS_TRANS THEN
   W(fun (asl,w) -> let it = SPEC_ALL C8P_IT3 in
     EXISTS_TAC (rand(rator(snd(dest_imp(concl it))))) THEN CONJ_TAC THENL
      [MATCH_MP_TAC it THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC]) THEN
   MATCH_MP_TAC C3B_ENS_EXISTS THEN X_GEN_TAC `m1:int64->byte` THEN
   MATCH_MP_TAC C3B_ENS_CASES THEN
   EXISTS_TAC (mk_abs(`s:wasmstate`, list_mk_conj [c3b_bodym `m1:int64->byte` 550 [Lp 548] (c8p_trk3 `i + 1`) []; `i + 1 < 6`;
                    c8p_L3inv `i + 1` `m1:int64->byte`])) THEN
   EXISTS_TAC (mk_abs(`s:wasmstate`, list_mk_conj [c3b_bodym `m1:int64->byte` 702 [] [] []; `i + 1 = 6`;
                    c8p_L3inv `i + 1` `m1:int64->byte`])) THEN
   REPEAT CONJ_TAC THENL
    [GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONV_TAC TAUT;
     ALL_TAC;
     MATCH_MP_TAC C3B_ENS_NOW THEN GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
     EXISTS_TAC `m1:int64->byte` THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `i + 1 = 6`)) THEN
     ASM_REWRITE_TAC[] THEN REWRITE_TAC[injectivity "wval"; C3B_EX_EQ]]) THEN
  (ASM_CASES_TAC `i + 1 < 6` THENL
   [ALL_TAC; MATCH_MP_TAC C3B_ENS_FALSE THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[]]) THEN
  TRY(MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC) THEN
  MATCH_MP_TAC C3B_ENS_PRE THEN EXISTS_TAC (mk_abs(`s:wasmstate`, mk_conj(c3b_bodym `m1:int64->byte` 550 [Lp 548] (c8p_trk3 `i + 1`) [],
     c8p_L3inv `i + 1` `m1:int64->byte`))) THEN
  (CONJ_TAC THENL [GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONV_TAC TAUT; ALL_TAC]) THEN
  MATCH_MP_TAC C3B_ENS_PRE_CONJ THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL (`i + 1` :: `m1:int64->byte` :: tl (tl c8p_L3vars))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC));;
let C8P_FOLD = prove
 (`!m a0 a1 a2 y3 y4 y5 y12 y13 y14 v.
     va1_w32s 16420 9 (\k. word_zx (EL k (va1_pcross y4 y3 y5 y12 y13 y14 v)):int32) m /\
     (!j. j < 6 ==> read (bytes32 (word (16456 + 4 * j))) (m:int64->byte) = va1_hmix (va1_hseed a0 a1 a2 j) /\
                    read (bytes32 (word (16480 + 4 * j))) m = va1_hjig (va1_hseed a0 a1 a2 j)) /\
     va1_pcross y4 y3 y5 y12 y13 y14 v = va1_pfrm a0 a1 a2
     ==> va1_w32s 16420 21 (va1_phdr a0 a1 a2) m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_w32s] THEN STRIP_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[va1_phdr] THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> can (find_term ((=) `16420`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN SIMP_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `k - 9` o check (fun th -> can (find_term ((=) `16456`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `16456 + 4 * (k - 9) = 16420 + 4 * k` SUBST1_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
    FIRST_X_ASSUM(MP_TAC o SPEC `k - 15` o check (fun th -> can (find_term ((=) `16456`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `16480 + 4 * (k - 15) = 16420 + 4 * k` SUBST1_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]]);;

let c8p_F mv = mk_conj(c3b_F mv, subst [mv,`m:int64->byte`] `va1_w32s 16420 21 h (m:int64->byte)`);;
let C8P_IT4_STMT = c3b_seg (list_mk_conj [`k < 2048`; c8p_F `m0:int64->byte`; c3b_A `k:num` `m0:int64->byte`;
      `read (bytes32 (word 16648)) m0 = (mdl:num->int32) 2`])
   (c3b_pred 718 [Lp 716] (c3b_trkL4 `k:num`) [])
   (mk_abs(`s:wasmstate`, mk_exists(`m1:int64->byte`, list_mk_conj
      [mk_disj(mk_conj(c3b_bodym `m1:int64->byte` 718 [Lp 716] (c3b_trkL4 `k + 1`) [], `k + 1 < 2048`),
               mk_conj(c3b_bodym `m1:int64->byte` 964 [] [] [], `k + 1 = 2048`));
       c8p_F `m1:int64->byte`; c3b_A `k + 1` `m1:int64->byte`])));;

let C8P_IT4 = prove(C8P_IT4_STMT,
  REPEAT GEN_TAC THEN TRY(DISCH_THEN STRIP_ASSUME_TAC) THEN C3B_INIT_TAC THEN c3b_time "it4" (C3B_RUN1 C3B_EXEC [718; 964]) THEN
  ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  (CONJ_TAC THENL [ALL_TAC; C3B_VNORM_TAC THEN MONOTONE_MAYCHANGE_TAC]) THEN
  C3B_EXISTS_MEM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `k:num` C3B_EXIT4) (ASSUME `k < 2048`)]) THEN
  C3B_VNORM_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD]) THEN C3B_WNORM_TAC THEN
  (CONJ_TAC THENL [C3B_DISJ_CLOSE_TAC; ALL_TAC]) THEN
  c3b_time "l4mem" C3B_L4MEM_TAC);;

let c8p_L4post = mk_abs(`s:wasmstate`, mk_exists(`m1:int64->byte`, list_mk_conj
   [c3b_bodym `m1:int64->byte` 964 [] [] []; c8p_F `m1:int64->byte`; c3b_A `2048` `m1:int64->byte`]));;

let C8P_LOOP4_STMT = mk_forall(`d:num`, list_mk_forall([`k:num`;`m0:int64->byte`;`t:int32`;`a0:int32`;`a1:int32`;`a2:int32`;`mdl:num->int32`;`tbl:num->int32`;`h:num->int32`],
   mk_imp(list_mk_conj [`k + d = 2047`; c8p_F `m0:int64->byte`; c3b_A `k:num` `m0:int64->byte`],
          c3b_ens (c3b_pred 718 [Lp 716] (c3b_trkL4 `k:num`) []) c8p_L4post)));;

let C3B_MDL2 = prove(`!mdl m. va1_mdl mdl m ==> read (bytes32 (word 16648)) m = mdl 2`,
  REWRITE_TAC[va1_mdl] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `2`) THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let C8P_LOOP4 = prove(C8P_LOOP4_STMT,
  INDUCT_TAC THEN (REPEAT GEN_TAC THEN STRIP_TAC THEN
  (MATCH_MP_TAC C3B_ENS_TRANS THEN
   W(fun (asl,w) -> let it = SPEC_ALL C8P_IT4 in
     EXISTS_TAC (rand(rator(snd(dest_imp(concl it))))) THEN CONJ_TAC THENL
      [MATCH_MP_TAC it THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; MATCH_MP_TAC C3B_MDL2 THEN ASM_REWRITE_TAC[]];
       ALL_TAC]) THEN
   MATCH_MP_TAC C3B_ENS_EXISTS THEN X_GEN_TAC `m1:int64->byte` THEN
   MATCH_MP_TAC C3B_ENS_CASES THEN
   EXISTS_TAC (mk_abs(`s:wasmstate`, list_mk_conj [c3b_bodym `m1:int64->byte` 718 [Lp 716] (c3b_trkL4 `k + 1`) []; `k + 1 < 2048`;
                    c8p_F `m1:int64->byte`; c3b_A `k + 1` `m1:int64->byte`])) THEN
   EXISTS_TAC (mk_abs(`s:wasmstate`, list_mk_conj [c3b_bodym `m1:int64->byte` 964 [] [] []; `k + 1 = 2048`;
                    c8p_F `m1:int64->byte`; c3b_A `k + 1` `m1:int64->byte`])) THEN
   REPEAT CONJ_TAC THENL
    [GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONV_TAC TAUT;
     ALL_TAC;
     MATCH_MP_TAC C3B_ENS_NOW THEN GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
     EXISTS_TAC `m1:int64->byte` THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `k + 1 = 2048`)) THEN
     ASM_REWRITE_TAC[] THEN REWRITE_TAC[injectivity "wval"; C3B_EX_EQ]]) THEN
  (ASM_CASES_TAC `k + 1 < 2048` THENL
   [ALL_TAC; MATCH_MP_TAC C3B_ENS_FALSE THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[]]) THEN
  TRY(MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC) THEN
  MATCH_MP_TAC C3B_ENS_PRE THEN EXISTS_TAC (mk_abs(`s:wasmstate`, mk_conj(c3b_bodym `m1:int64->byte` 718 [Lp 716] (c3b_trkL4 `k + 1`) [],
     list_mk_conj [c8p_F `m1:int64->byte`; c3b_A `k + 1` `m1:int64->byte`]))) THEN
  (CONJ_TAC THENL [GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONV_TAC TAUT; ALL_TAC]) THEN
  MATCH_MP_TAC C3B_ENS_PRE_CONJ THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k + 1`; `m1:int64->byte`; `t:int32`;`a0:int32`;`a1:int32`;`a2:int32`;`mdl:num->int32`;`tbl:num->int32`;`h:num->int32`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC));;

let C8P_IT5_STMT = c3b_seg (list_mk_conj [`i < 24576`; c8p_F `m0:int64->byte`; c3b_A `2048` `m0:int64->byte`; c3b_D `i:num` `m0:int64->byte`])
   (c3b_pred 972 [Lp 970] (c3b_trkL5 `i:num`) [])
   (mk_abs(`s:wasmstate`, mk_exists(`m1:int64->byte`, list_mk_conj
      [mk_disj(mk_conj(c3b_bodym `m1:int64->byte` 972 [Lp 970] (c3b_trkL5 `i + 1`) [], `i + 1 < 24576`),
               mk_conj(c3b_bodym `m1:int64->byte` 1034 [] [] [], `i + 1 = 24576`));
       c8p_F `m1:int64->byte`; c3b_A `2048` `m1:int64->byte`; c3b_D `i + 1` `m1:int64->byte`])));;

let C8P_IT5 = prove(C8P_IT5_STMT,
  REPEAT GEN_TAC THEN TRY(DISCH_THEN STRIP_ASSUME_TAC) THEN C3B_INIT_TAC THEN
  C3B_VFACTS_TAC (map (fun c -> mk_binop `word_add:int32->int32->int32` `word (4294180864 + 32 * i):int32` (mk_comb(`word:num->int32`, mk_small_numeral c))) [1966104;1966096;1966088;1966080]) THEN c3b_time "it5" (C3B_RUN1 C3B_EXEC [972; 1034]) THEN
  ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  TRY(CONJ_TAC THENL [ALL_TAC; C3B_VNORM_TAC THEN MONOTONE_MAYCHANGE_TAC]) THEN
  C3B_EXISTS_MEM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `i:num` C3B_EXIT5) (ASSUME `i < 24576`)]) THEN
  C3B_VNORM_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD]) THEN C3B_WNORM_TAC THEN
  (CONJ_TAC THENL [C3B_DISJ_CLOSE_TAC; ALL_TAC]) THEN
  c3b_time "l5mem" C3B_L5MEM_TAC);;

let c8p_L5post = mk_abs(`s:wasmstate`, mk_exists(`m1:int64->byte`, list_mk_conj
   [c3b_bodym `m1:int64->byte` 1034 [] [] []; c8p_F `m1:int64->byte`; c3b_A `2048` `m1:int64->byte`; c3b_D `24576` `m1:int64->byte`]));;

let C8P_LOOP5_STMT = mk_forall(`d:num`, list_mk_forall([`i:num`;`m0:int64->byte`;`t:int32`;`a0:int32`;`a1:int32`;`a2:int32`;`mdl:num->int32`;`tbl:num->int32`;`h:num->int32`],
   mk_imp(list_mk_conj [`i + d = 24575`; c8p_F `m0:int64->byte`; c3b_A `2048` `m0:int64->byte`; c3b_D `i:num` `m0:int64->byte`],
          c3b_ens (c3b_pred 972 [Lp 970] (c3b_trkL5 `i:num`) []) c8p_L5post)));;

let C8P_LOOP5 = prove(C8P_LOOP5_STMT,
  INDUCT_TAC THEN (REPEAT GEN_TAC THEN STRIP_TAC THEN
  (MATCH_MP_TAC C3B_ENS_TRANS THEN
   W(fun (asl,w) -> let it = SPEC_ALL C8P_IT5 in
     EXISTS_TAC (rand(rator(snd(dest_imp(concl it))))) THEN CONJ_TAC THENL
      [MATCH_MP_TAC it THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
       ALL_TAC]) THEN
   MATCH_MP_TAC C3B_ENS_EXISTS THEN X_GEN_TAC `m1:int64->byte` THEN
   MATCH_MP_TAC C3B_ENS_CASES THEN
   EXISTS_TAC (mk_abs(`s:wasmstate`, list_mk_conj [c3b_bodym `m1:int64->byte` 972 [Lp 970] (c3b_trkL5 `i + 1`) []; `i + 1 < 24576`;
                    c8p_F `m1:int64->byte`; c3b_A `2048` `m1:int64->byte`; c3b_D `i + 1` `m1:int64->byte`])) THEN
   EXISTS_TAC (mk_abs(`s:wasmstate`, list_mk_conj [c3b_bodym `m1:int64->byte` 1034 [] [] []; `i + 1 = 24576`;
                    c8p_F `m1:int64->byte`; c3b_A `2048` `m1:int64->byte`; c3b_D `i + 1` `m1:int64->byte`])) THEN
   REPEAT CONJ_TAC THENL
    [GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONV_TAC TAUT;
     ALL_TAC;
     MATCH_MP_TAC C3B_ENS_NOW THEN GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
     EXISTS_TAC `m1:int64->byte` THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `i + 1 = 24576`)) THEN
     ASM_REWRITE_TAC[] THEN REWRITE_TAC[injectivity "wval"; C3B_EX_EQ]]) THEN
  (ASM_CASES_TAC `i + 1 < 24576` THENL
   [ALL_TAC; MATCH_MP_TAC C3B_ENS_FALSE THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[]]) THEN
  TRY(MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC) THEN
  MATCH_MP_TAC C3B_ENS_PRE THEN EXISTS_TAC (mk_abs(`s:wasmstate`, mk_conj(c3b_bodym `m1:int64->byte` 972 [Lp 970] (c3b_trkL5 `i + 1`) [],
     list_mk_conj [c8p_F `m1:int64->byte`; c3b_A `2048` `m1:int64->byte`; c3b_D `i + 1` `m1:int64->byte`]))) THEN
  (CONJ_TAC THENL [GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONV_TAC TAUT; ALL_TAC]) THEN
  MATCH_MP_TAC C3B_ENS_PRE_CONJ THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i + 1`; `m1:int64->byte`; `t:int32`;`a0:int32`;`a1:int32`;`a2:int32`;`mdl:num->int32`;`tbl:num->int32`;`h:num->int32`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC));;

let C8P_TAIL_STMT = c3b_seg (list_mk_conj [c8p_F `m0:int64->byte`; c3b_A `2048` `m0:int64->byte`; c3b_D `24576` `m0:int64->byte`])
   (c3b_pred 1034 [] [] [])
   `\s. read wstatus s = WDone /\ read wstack s = [I32 (word 0)] /\ va1_f25_post t mdl tbl a0 a1 a2 (read wmem s) /\ va1_w32s 16420 21 h (read wmem s)`;;

let C8P_TAIL = prove(C8P_TAIL_STMT,
  REPEAT GEN_TAC THEN TRY(DISCH_THEN STRIP_ASSUME_TAC) THEN C3B_INIT_TAC THEN C3B_RUN C3B_EXEC [] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[injectivity "wval"] THEN
  MATCH_MP_TAC(TAUT `b /\ a ==> a /\ b`) THEN CONJ_TAC THENL [C3B_W32S_TAC THEN NO_TAC; ALL_TAC] THEN
  REWRITE_TAC[va1_f25_post; va1_w32s] THEN C3B_WNORM_TAC THEN REPEAT CONJ_TAC THEN
  TRY(C3B_ROW_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN C3B_TAILMEM_TAC);;

let c8p_Fh mv = subst [`va1_phdr a0 a1 a2`, `h:num->int32`] (c8p_F mv);;
let C8P_HDRB_STMT = c3b_seg (list_mk_conj [c8p_L3inv `6` `m0:int64->byte`; `va1_pcross y4 y3 y5 y12 y13 y14 v = va1_pfrm a0 a1 a2`])
   (c3b_pred 702 [] [] [])
   (mk_abs(`s:wasmstate`, mk_exists(`m1:int64->byte`, mk_conj(c3b_bodym `m1:int64->byte` 718 [Lp 716] (c3b_trkL4 `0`) [], c8p_Fh `m1:int64->byte`))));;
let C8P_HDRB = prove(C8P_HDRB_STMT,
  REPEAT GEN_TAC THEN TRY(DISCH_THEN STRIP_ASSUME_TAC) THEN C3B_INIT_TAC THEN C3B_RUN C3B_EXEC [718] THEN
  ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN C3B_EXISTS_MEM_TAC THEN C3B_CLOSE_TAC THEN
  MATCH_MP_TAC C8P_FOLD THEN MAP_EVERY EXISTS_TAC [`y3:int64`;`y4:int64`;`y5:int64`;`y12:int64`;`y13:int64`;`y14:int64`;`v:int64`] THEN
  ASM_REWRITE_TAC[]);;
let C8P_J0 = prove(c8p_J `0` `m:int64->byte`, REWRITE_TAC[LT]);;
let C8P_DISCH_TAC : tactic =
  ASM_REWRITE_TAC[C3B_A0; C3B_D0; C8P_J0] THEN TRY C3B_ARITH_TAC THEN
  TRY(REWRITE_TAC[va1_pfrm; va1_isqrt] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN NO_TAC);;
(* link a |- ens P Q C with b |- !vs. [H ==>] ens P' R C: match P' to Q, then H's conjuncts to assumptions *)
let c8p_link asl a b =
  let b1 = SPEC_ALL b in
  let e = if is_imp (concl b1) then rand (concl b1) else concl b1 in
  let p' = rand(rator(rator e)) and q = rand(rator(concl a)) in
  let b2 = INSTANTIATE (term_match [] p' q) b1 in
  let b2 = if is_imp (concl b2) then
     itlist (fun cj th -> let fv = frees cj in
        if fv = [] then th else
        try let ins = tryfind (fun (_,ath) -> term_match [] cj (concl ath)) asl in INSTANTIATE ins th with Failure _ -> th)
       (conjuncts (lhand (concl b2))) b2 else b2 in
  let b3 = if is_imp (concl b2) then MP b2 (TAC_PROOF((asl, lhand(concl b2)), C8P_DISCH_TAC)) else b2 in
  MATCH_MP C3B_ENS_TRANS (CONJ a b3);;
let c8p_first asl b = let b1 = SPEC_ALL b in
  if is_imp (concl b1) then MP b1 (TAC_PROOF((asl, lhand(concl b1)), C8P_DISCH_TAC)) else b1;;
let c8p_chain asl ths = itlist (fun b a -> c8p_link asl a b) (rev (tl ths)) (c8p_first asl (hd ths));;

let c8p_inst_to asl b (pre:term) =
  let b1 = SPEC_ALL b in
  let e = if is_imp (concl b1) then rand (concl b1) else concl b1 in
  let b2 = INSTANTIATE (term_match [] (rand(rator(rator e))) pre) b1 in
  let b2 = if is_imp (concl b2) then
     itlist (fun cj th -> if frees cj = [] then th else
        try INSTANTIATE (tryfind (fun (_,ath) -> term_match [] cj (concl ath)) asl) th with Failure _ -> th)
       (conjuncts (lhand (concl b2))) b2 else b2 in
  if is_imp (concl b2) then MP b2 (TAC_PROOF((asl, lhand(concl b2)), C8P_DISCH_TAC)) else b2;;
let c8p_chain_goal asl w ths =
  let pre = rand(rator(rator w)) in
  rev_itlist (fun b a -> c8p_link asl a b) (tl ths) (c8p_inst_to asl (hd ths) pre);;
let C8P_STEPS_TAC ths : tactic = fun (asl,w) -> C3B_STEP_TO_TAC (c8p_chain_goal asl w ths) (asl,w);;
let C8P_LAST_TAC th : tactic = fun (asl,w) -> ACCEPT_TAC (c8p_chain_goal asl w [th]) (asl,w);;
let c8p_n32 th = MP (SPEC `32` th) (ARITH_RULE `1 <= 32 /\ 32 <= 32`);;
(* the statement of VA1_F25_HDR, verbatim from c8p_f25h.spec *)
let C8P_HDR_STMT = `!(a0:int32) (a1:int32) (a2:int32) (t:int32) (mdl:num->int32) (tbl:num->int32) (decls:wval list).
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0) /\ wasm_decl_vals va1_f25_mc = SOME decls
     ==> ensures wasm
          (\s. read wcode s = va1_f25_mc /\ read wpc s = word 13 /\ read wstatus s = WRunning /\
               read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\
               read wlocals s = wcall_locals [I32 a2; I32 a1; I32 a0] decls /\
               va1_tick t (read wmem s) /\ read (bytes32 (word 16396)) (read wmem s) = word 4294967295 /\
               va1_mdl mdl (read wmem s) /\ va1_w32s 65536 262144 tbl (read wmem s))
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 0)] /\
               va1_f25_post t mdl tbl a0 a1 a2 (read wmem s) /\
               va1_w32s 16420 21 (va1_phdr a0 a1 a2) (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocal 0; wlocal 1; wlocal 2; wlocal 3; wlocal 4; wlocal 5; wlocal 6; wlocal 7;
                      wlocal 8; wlocal 9; wlocal 10; wlocal 11; wlocal 12; wlocal 13; wlocal 14; wlocal 15] ,,
           MAYCHANGE [wmem :> bytes(word 16396,8)] ,, MAYCHANGE [wmem :> bytes(word 16408,96)] ,,
           MAYCHANGE [wmem :> bytes(word 1130496,835584)])`;;
let VA1_F25_HDR = prove(C8P_HDR_STMT,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC C3B_ENS_PRE THEN
  EXISTS_TAC (mk_abs(`s:wasmstate`, mk_exists(`m0:int64->byte`, list_mk_conj [c3b_body 13 [] c3b_trk0 [];
     `read (bytes32 (word 16396)) (m0:int64->byte) = word 4294967295 /\ ~(word_or (word_or (a1:int32) a0) a2 = word 0) /\
      read (bytes32 (word 16392)) m0 = (t:int32) /\ va1_mdl mdl m0 /\ va1_w32s 65536 262144 tbl m0`]))) THEN
  (CONJ_TAC THENL
   [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN EXISTS_TAC `read wmem (s:wasmstate)` THEN
    C3B_ENTRY_LOCALS_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[va1_tick]) THEN ASM_REWRITE_TAC[WORD_OR_EQ_0] THEN ASM_MESON_TAC[];
    ALL_TAC]) THEN
  C3B_OPEN_TAC `m0:int64->byte` THEN
  C8P_STEPS_TAC [C8P_PRO; c8p_n32 C8P_ISQ1; C8P_MID; c8p_n32 C8P_ISQ2; C8P_HDRA] THEN
  C3B_OPEN_TAC `m1:int64->byte` THEN C8P_STEPS_TAC [SPEC `5` C8P_LOOP3] THEN
  C3B_OPEN_TAC `m2:int64->byte` THEN C8P_STEPS_TAC [C8P_HDRB] THEN
  C3B_OPEN_TAC `m3:int64->byte` THEN C8P_STEPS_TAC [SPEC `2047` C8P_LOOP4] THEN
  C3B_OPEN_TAC `m4:int64->byte` THEN C8P_STEPS_TAC [C3B_L5E; SPEC `24575` C8P_LOOP5] THEN
  C3B_OPEN_TAC `m5:int64->byte` THEN C8P_LAST_TAC C8P_TAIL);;
