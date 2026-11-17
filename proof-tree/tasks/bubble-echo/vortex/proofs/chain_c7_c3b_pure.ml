needs "ve_vort.ml";;
needs "ve_tick.ml";;
needs "ve_vk.ml";;
needs "va1_code.ml";;
needs "va1_seq_final2.ml";;
needs "pop_design_defs.ml";;
needs "pop_design_stmts.ml";;
needs "chain_c3b_dec.ml";;
needs "chain_c7_c3b_defs.ml";;
needs "chain_c7_c3b_l1.ml";;
(* Vortex chain rung C3b, layer 2 (pure HOL; Claude Opus 5.5, 2026-11-13):   *)
(* VA1_F25_ENTRY, VA1_F25_FRAME_BYTES (C1-style component frame), byte/word  *)
(* lemmas, VA1_BAD_PUNCT_B, C3B_BAD_M1, VA1_PUNCT_UNPUNCT_INVERSE, and the two *)
(* satisfiability theorems from explicit memory witnesses (method of N1's    *)
(* POP_N1_B32_SAT). No mk_thm / new_axiom / CHEAT_TAC.                       *)
(* ---- frames (copied from chain_c1_np.ml / chain_c1_frame.ml, renamed C3B_) ---- *)
let C3B_SEQ_KEEPS = prove
 (`!(d:(A,C)component) (r1:A->A->bool) (r2:A->A->bool).
     (!s s'. r1 s s' ==> read d s' = read d s) /\
     (!s s'. r2 s s' ==> read d s' = read d s)
     ==> !s s'. (r1 ,, r2) s s' ==> read d s' = read d s`,
  REWRITE_TAC[seq] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN MESON_TAC[]);;
let C3B_ASSIGNS_KEEPS = prove
 (`!(c:(A,B)component) (d:(A,C)component).
     (!y s. read d (write c y s) = read d s)
     ==> !s s'. ASSIGNS c s s' ==> read d s' = read d s`,
  REWRITE_TAC[ASSIGNS_THM] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN MESON_TAC[]);;
let C3B_COMP_TAC =
  REPEAT GEN_TAC THEN REWRITE_TAC[wlocal; READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE] THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN REWRITE_TAC[];;
let C3B_KEEPS_TAC (comptac:tactic) =
  REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
  REPEAT(MATCH_MP_TAC C3B_SEQ_KEEPS THEN CONJ_TAC) THEN
  MATCH_MP_TAC C3B_ASSIGNS_KEEPS THEN comptac;;
let C3B_B8_BYTES_OTHER = prove
 (`!a b n (y:num) (m:int64->byte).
     (a + 1 <= b \/ b + n <= a) /\ a + 1 < 2 EXP 64 /\ b + n < 2 EXP 64
     ==> read (bytes8 (word a)) (write (bytes(word b,n)) y m) =
         read (bytes8 (word a)) m`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC READ_WRITE_ORTHOGONAL_COMPONENTS THEN
  REWRITE_TAC[bytes8] THEN MATCH_MP_TAC ORTHOGONAL_COMPONENTS_SUB_LEFT THEN
  REWRITE_TAC[ORTHOGONAL_COMPONENTS_BYTES; DIMINDEX_64] THEN
  MATCH_MP_TAC NONOVERLAPPING_MODULO_SIMPLE THEN
  SUBGOAL_THEN `val(word a:int64) = a /\ val(word b:int64) = b`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;
let C3B_BYTE_COMP_TAC =
  C3B_COMP_TAC THEN
  TRY(MATCH_MP_TAC C3B_B8_BYTES_OTHER THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;
let C3B_F25_BYTE = prove(mk_forall(`a:num`, mk_imp(
   `a < 4194304 /\ ~(16396 <= a /\ a < 16404) /\ ~(16408 <= a /\ a < 16504) /\ ~(1130496 <= a /\ a < 1966080)`,
   mk_forall(`s:wasmstate`, mk_forall(`s':wasmstate`, mk_imp(list_mk_comb(C3B_FRAME, [`s:wasmstate`; `s':wasmstate`]),
     `read (wmem :> bytes8 (word a)) s' = read (wmem :> bytes8 (word a)) s`))))),
  GEN_TAC THEN STRIP_TAC THEN C3B_KEEPS_TAC C3B_BYTE_COMP_TAC);;
let VA1_F25_FRAME_BYTES = prove
 (`!(s:wasmstate) (s':wasmstate).
     (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
      MAYCHANGE [wlocal 0; wlocal 1; wlocal 2; wlocal 3; wlocal 4; wlocal 5; wlocal 6; wlocal 7;
                 wlocal 8; wlocal 9; wlocal 10; wlocal 11; wlocal 12; wlocal 13; wlocal 14; wlocal 15] ,,
      MAYCHANGE [wmem :> bytes(word 16396,8)] ,, MAYCHANGE [wmem :> bytes(word 16408,96)] ,,
      MAYCHANGE [wmem :> bytes(word 1130496,835584)]) s s'
     ==> va1_f25_frame (read wmem s) (read wmem s')`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[va1_f25_frame] THEN X_GEN_TAC `a:num` THEN DISCH_TAC THEN
  MP_TAC(SPEC `a:num` C3B_F25_BYTE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:wasmstate`; `s':wasmstate`]) THEN ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE]);;
let VA1_F25_ENTRY = prove(`wasm_entry va1_f25_mc = SOME 13`, REWRITE_TAC[CONJUNCT1 VA1_F25_CALLEE]);;
(* ---- bytes ---- *)
let C3B_RB32 = prove(`!(a:int64) (m:int64->byte). read (bytes32 a) m = word (read (bytes(a,4)) m)`,
  REWRITE_TAC[bytes32; READ_COMPONENT_COMPOSE; asword; through; read]);;
let C3B_B8 = prove(`!(a:int64) (m:int64->byte). read (bytes8 a) m = m a`, REWRITE_TAC[BYTES8_ELEMENT; READ_ELEMENT]);;
let C3B_B32_B8 = prove
 (`!b (m:int64->byte) m'. b + 4 <= 2 EXP 64 /\ read (bytes32 (word b)) m = read (bytes32 (word b)) m'
     ==> !i. i < 4 ==> read (bytes8 (word (b + i))) m = read (bytes8 (word (b + i))) m'`,
  REWRITE_TAC[C3B_RB32; C3B_B8] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `read (bytes(word b:int64,4)) m = read (bytes(word b:int64,4)) (m':int64->byte)` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int32->num`) THEN REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
    MP_TAC(ISPECL [`word b:int64`; `4`; `m:int64->byte`] READ_BYTES_BOUND) THEN
    MP_TAC(ISPECL [`word b:int64`; `4`; `m':int64->byte`] READ_BYTES_BOUND) THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT];
    REWRITE_TAC[READ_BYTES_EQ; GSYM WORD_ADD]]);;
let C3B_B8_B32 = prove
 (`!b (m:int64->byte) m'. (!i. i < 4 ==> read (bytes8 (word (b + i))) m = read (bytes8 (word (b + i))) m')
     ==> read (bytes32 (word b)) m = read (bytes32 (word b)) m'`,
  REWRITE_TAC[C3B_RB32; C3B_B8] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[READ_BYTES_EQ; GSYM WORD_ADD] THEN ASM_SIMP_TAC[]);;
let C3B_W1_BYTES = prove
 (`!b a (m:int64->byte) m'. read (bytes32 (word b)) m = read (bytes32 (word b)) m' /\ b <= a /\ a < b + 4 /\ b + 4 <= 2 EXP 64
     ==> read (bytes8 (word a)) m = read (bytes8 (word a)) m'`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`b:num`; `m:int64->byte`; `m':int64->byte`] C3B_B32_B8) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `a - b`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `b + a - b = a` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC);;
let C3B_WORD_BYTES = prove
 (`!base n f (m:int64->byte) m' a. va1_w32s base n f m /\ va1_w32s base n f m' /\ base <= a /\ a < base + 4 * n /\ base + 4 * n <= 2 EXP 64
     ==> read (bytes8 (word a)) m = read (bytes8 (word a)) m'`,
  REWRITE_TAC[va1_w32s] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC C3B_W1_BYTES THEN EXISTS_TAC `base + 4 * ((a - base) DIV 4)` THEN
  SUBGOAL_THEN `(a - base) DIV 4 < n` ASSUME_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN MP_TAC(SPECL [`a - base`; `4`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

let VA1_BAD_PUNCT_B = prove
 (`!(mdl:num->int32) (tbl:num->int32).
     va1_bad_b mdl tbl ((\k. word 251658), va1_rbinit_b tbl, (\k. word 0), (\k. word 0), (\k. word 0),
                      va1_zpseed_b mdl, word 0) = word 0`,
  REWRITE_TAC[va1_bad_b; FST; SND; BITVAL_CLAUSES; ADD_CLAUSES; NSUM_0; WORD_ADD_0]);;
let c3b_fa c asl = find (fun th -> is_forall(concl th) && can (find_term ((=) c)) (concl th)) (map snd asl);;
let c3b_at asl th e = c3b_wn (CONV_RULE NUM_REDUCE_CONV (MP (SPEC e th) (c3b_arith asl (lhand(snd(dest_forall(concl th))) |> fun l -> subst [e, fst(dest_forall(concl th))] l))));;
let C3B_BAD_M1 = prove
 (`!t mdl tbl a0 a1 a2 (m1:int64->byte).
     va1_f25_post t mdl tbl a0 a1 a2 m1 /\ va1_mdl mdl m1 /\ va1_w32s 65536 262144 tbl m1
     ==> va1_bad_b (va1_rd32 16640 m1) (va1_rd32 65536 m1)
                 (va1_rd32 1130496 m1, va1_rd32 1138688 m1, va1_rd32 1146880 m1,
                  va1_rd32 1155072 m1, va1_rd32 1163264 m1, va1_rd32 1171456 m1,
                  read (bytes32 (word 16400)) m1) = word 0`,
  REWRITE_TAC[va1_f25_post; va1_mdl; va1_w32s; va1_bad_b; FST; SND] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[WORD_ADD_0] `n = 0 ==> word_add (word 0) (word n):int32 = word 0`) THEN
  MATCH_MP_TAC NSUM_EQ_0 THEN X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  W(fun (asl,w) ->
    let tb = c3b_fa `65536` asl and mf = c3b_fa `16640` asl and bl = c3b_fa `1146880` asl
    and ra = c3b_fa `1130496` asl and rb = c3b_fa `1138688` asl and zp = c3b_fa `1171456` asl in
    let rbeq = TAC_PROOF((asl, `va1_rbinit_b (va1_rd32 65536 m1) k = va1_rbinit_b tbl k`),
       REWRITE_TAC[va1_rbinit_b; va1_rd32] THEN CONV_TAC(ONCE_DEPTH_CONV C3B_WARG_CONV) THEN
       REWRITE_TAC[c3b_at asl tb `128 * k`; c3b_at asl tb `128 * k + 1`]) in
    let zpeq = TAC_PROOF((asl, `va1_zpseed_b (va1_rd32 16640 m1) k = va1_zpseed_b mdl k`),
       REWRITE_TAC[va1_zpseed_b; va1_rd32] THEN CONV_TAC NUM_REDUCE_CONV THEN
       REWRITE_TAC[c3b_at asl mf `2`]) in
    REWRITE_TAC[rbeq; zpeq] THEN REWRITE_TAC[va1_rd32] THEN CONV_TAC(ONCE_DEPTH_CONV C3B_WARG_CONV) THEN
    REWRITE_TAC[c3b_at asl bl `k:num`; c3b_at asl bl `k + 2048`; c3b_at asl bl `k + 4096`;
                c3b_at asl ra `k:num`; c3b_at asl rb `k:num`; c3b_at asl zp `k:num`] THEN
    REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES]));;

(* a word of m1 outside f25's byte ranges equals that of m0 *)
let C3B_KEEP32_TAC : tactic = fun (asl,w) ->
  let l = lhs w in let x = rand(rand(rand(rator l))) in
  let fr = find (fun th -> match concl th with Comb(Comb(Const("va1_f25_frame",_),_),_) -> true | _ -> false) (map snd asl) in
  let fr' = REWRITE_RULE[va1_f25_frame] fr in
  (MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (mk_comb(rator l, `m0:int64->byte`)) THEN CONJ_TAC THENL
    [MATCH_MP_TAC C3B_B8_B32 THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
     MATCH_MP_TAC (SPEC (mk_binop `(+):num->num->num` x `i:num`) fr') THEN C3B_ARITH_TAC;
     ASM_SIMP_TAC[] THEN TRY C3B_ARITH_TAC]) (asl,w);;
let C3B_AARITH_TAC : tactic = fun (asl,w) ->
  let ok c = free_in `a:num` c && not (can (find_term (fun t -> type_of t = `:int64->byte`)) c) in
  let ants = filter (fun th -> ok (concl th)) (map snd asl) in
  let th = if ants = [] then ARITH_RULE w else MP (ARITH_RULE (mk_imp(list_mk_conj(map concl ants), w))) (end_itlist CONJ ants) in
  ACCEPT_TAC th (asl,w);;
let VA1_PUNCT_UNPUNCT_INVERSE = prove
 (`!(t:int32) (mdl:num->int32) (tbl:num->int32) (a0:int32) (a1:int32) (a2:int32)
   (m0:int64->byte) (m1:int64->byte) (m2:int64->byte).
     ~(t = word 4294967295) /\
     va1_punct_clean m0 /\ va1_mdl mdl m0 /\ va1_w32s 65536 262144 tbl m0 /\
     va1_f25_post t mdl tbl a0 a1 a2 m1 /\ va1_f25_frame m0 m1 /\
     va1_unpunct_post m1 m2 /\ va1_unpunct_frame m1 m2
     ==> !a. a < 4194304 ==> read (bytes8 (word a)) m2 = read (bytes8 (word a)) m0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `va1_mdl mdl m1 /\ va1_w32s 65536 262144 tbl m1` STRIP_ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> match concl th with
       Comb(Comb(Const("va1_mdl",_),_),m) -> m = `m0:int64->byte`
     | Comb(Comb(Comb(Comb(Const("va1_w32s",_),_),_),_),m) -> m = `m0:int64->byte` | _ -> false))) THEN
    REWRITE_TAC[va1_mdl; va1_w32s] THEN REPEAT STRIP_TAC THEN C3B_KEEP32_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `read (bytes32 (word 16404)) m1 = read (bytes32 (word 16404)) m0` ASSUME_TAC THENL
   [C3B_KEEP32_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`t:int32`; `mdl:num->int32`; `tbl:num->int32`; `a0:int32`; `a1:int32`; `a2:int32`; `m1:int64->byte`] C3B_BAD_M1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[va1_punct_clean; va1_unpunct_post; va1_unpunct_frame]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `va1_bad_b (va1_rd32 16640 m1) (va1_rd32 65536 m1)
                  (va1_rd32 1130496 m1, va1_rd32 1138688 m1, va1_rd32 1146880 m1,
                   va1_rd32 1155072 m1, va1_rd32 1163264 m1, va1_rd32 1171456 m1,
                   read (bytes32 (word 16400)) m1) = word 0`; WORD_ADD_0]) THEN
  X_GEN_TAC `a:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `16396 <= a /\ a < 16400` THENL
   [MATCH_MP_TAC C3B_W1_BYTES THEN EXISTS_TAC `16396` THEN ASM_REWRITE_TAC[] THEN C3B_AARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `16400 <= a /\ a < 16404` THENL
   [MATCH_MP_TAC C3B_W1_BYTES THEN EXISTS_TAC `16400` THEN ASM_REWRITE_TAC[] THEN C3B_AARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `16404 <= a /\ a < 16408` THENL
   [MATCH_MP_TAC C3B_W1_BYTES THEN EXISTS_TAC `16404` THEN ASM_REWRITE_TAC[] THEN C3B_AARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `16408 <= a /\ a < 16504` THENL
   [MATCH_MP_TAC C3B_WORD_BYTES THEN MAP_EVERY EXISTS_TAC [`16408`; `24`; `\k:num. word 0:int32`] THEN
    ASM_REWRITE_TAC[] THEN C3B_AARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `1130496 <= a /\ a < 1966080` THENL
   [MATCH_MP_TAC C3B_WORD_BYTES THEN MAP_EVERY EXISTS_TAC [`1130496`; `208896`; `\k:num. word 0:int32`] THEN
    ASM_REWRITE_TAC[] THEN C3B_AARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `read (bytes8 (word a)) (m1:int64->byte)` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) && can (find_term ((=) `m2:int64->byte`)) (concl th) &&
                                          can (find_term ((=) `bytes8`)) (concl th))) THEN C3B_AARITH_TAC;
    UNDISCH_TAC `va1_f25_frame m0 m1` THEN REWRITE_TAC[va1_f25_frame] THEN DISCH_THEN MATCH_MP_TAC THEN C3B_AARITH_TAC]);;

(* ---- memory witnesses (method of pop_n1_sat.ml POP_N1_B32_SAT, PROVED in N1; copied and generalized) ---- *)
let c3b_memw = `\(W:num->int32) (b:int64). write (bytes(word(4 * (val b DIV 4)):int64,4)) (val(W(val b DIV 4))) (\c:int64. word 0:byte) b`;;
let C3B_MEMW_B32 = prove
 (mk_forall(`W:num->int32`, mk_forall(`w:num`, mk_imp(`4 * w + 4 <= 2 EXP 64`,
   mk_eq(mk_comb(mk_comb(`read:((int64->byte),int32)component->(int64->byte)->int32`, `bytes32 (word (4 * w))`), mk_comb(c3b_memw, `W:num->int32`)), `(W:num->int32) w`)))),
  REPEAT GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN REWRITE_TAC[C3B_RB32] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `word(read (bytes(word(4 * w):int64,4))
              (write (bytes(word(4 * w):int64,4)) (val((W:num->int32) w))
                     (\c:int64. word 0:byte))):int32` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[READ_BYTES_EQ] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `val(word_add (word(4 * w)) (word i):int64) DIV 4 = w`
     (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    SUBGOAL_THEN `(4 * w + i) MOD 2 EXP 64 = 4 * w + i` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `i:num` THEN ASM_ARITH_TAC;
    SIMP_TAC[READ_WRITE_BYTES; DIMINDEX_64; ARITH_RULE `4 <= 2 EXP 64`] THEN
    REWRITE_TAC[ARITH_RULE `8 * 4 = 32`] THEN
    MP_TAC(ISPEC `(W:num->int32) w` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_32] THEN SIMP_TAC[MOD_LT; WORD_VAL]]);;
let C3B_MEMW_B8 = prove
 (mk_forall(`W1:num->int32`, mk_forall(`W2:num->int32`, mk_forall(`a:num`, mk_imp(`a < 2 EXP 64 /\ (W1:num->int32) (a DIV 4) = W2 (a DIV 4)`,
   mk_eq(mk_comb(`read (bytes8 (word a))`, mk_comb(c3b_memw, `W1:num->int32`)), mk_comb(`read (bytes8 (word a))`, mk_comb(c3b_memw, `W2:num->int32`))))))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C3B_B8] THEN BETA_TAC THEN
  SUBGOAL_THEN `val(word a:int64) = a` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]);;
(* ---- deciding memory conjuncts of an explicit witness (pop_n1 tactics, copied) ---- *)
let c3b_addr_th a =
  let four = mk_small_numeral 4 in
  if is_numeral a then
    let n = dest_numeral a in
    let q = mk_numeral (Num.quo_num n (Num.num_of_int 4)) in
    SYM(NUM_REDUCE_CONV (mk_binop `( * ):num->num->num` four q))
  else
    let b,fk = dest_binop `(+):num->num->num` a in
    let k = rand fk in
    let q = mk_numeral (Num.quo_num (dest_numeral b) (Num.num_of_int 4)) in
    ARITH_RULE (mk_eq(a, mk_binop `( * ):num->num->num` four
                                  (mk_binop `(+):num->num->num` q k)));;
let C3B_DECIDE_TAC =
  W(fun (asl,w) ->
      let l = lhs w in
      if is_cond l then
        let c = rand(rator(rator l)) in
        (SUBGOAL_THEN (mk_neg c) MP_TAC THENL
          [ASM_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[EQF_INTRO th])]) ORELSE
        (SUBGOAL_THEN c MP_TAC THENL
          [ASM_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[EQT_INTRO th])])
      else FIRST [REFL_TAC; AP_TERM_TAC THEN ASM_ARITH_TAC]);;
let C3B_MEMCONJ_TAC (mw:term) : tactic =
  REPEAT STRIP_TAC THEN BETA_TAC THEN
  W(fun (asl,w) ->
      let a = rand(rand(rand(rator(lhs w)))) in
      let th = c3b_addr_th a in
      SUBST1_TAC th THEN MP_TAC (BETA_RULE (SPECL [mw; rand(rand(concl th))] C3B_MEMW_B32))) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  BETA_TAC THEN REPEAT C3B_DECIDE_TAC;;
let c3b_W0 = `\w. if w = 4099 then word 4294967295
                  else if 4160 <= w /\ w < 5184 then (mdl:num->int32) (w - 4160)
                  else if 16384 <= w /\ w < 278528 then (tbl:num->int32) (w - 16384)
                  else word 0:int32`;;
let c3b_WT = `\w. if w = 4098 then (t:int32) else if w = 4099 then word 4294967295
                  else if 4160 <= w /\ w < 5184 then (mdl:num->int32) (w - 4160)
                  else if 16384 <= w /\ w < 278528 then (tbl:num->int32) (w - 16384)
                  else word 0:int32`;;
let c3b_W1 = mk_abs(`w:num`, mk_cond(`w = 4099 \/ w = 4102 \/ w = 4103 \/ w = 4104 \/ (282624 <= w /\ w < 286720) \/ (292864 <= w /\ w < 294912)`,
   `if w = 4099 then (t:int32) else if w = 4102 then (a0:int32) else if w = 4103 then (a1:int32) else if w = 4104 then (a2:int32)
    else if 282624 <= w /\ w < 284672 then word 251658 else if 284672 <= w /\ w < 286720 then va1_rbinit_b (tbl:num->int32) (w - 284672)
    else va1_zpseed_b (mdl:num->int32) (w - 292864)`, mk_comb(c3b_W0, `w:num`)));;
let VA1_F25_SAT = prove
 (`!(a0:int32) (a1:int32) (a2:int32) (t:int32) (mdl:num->int32) (tbl:num->int32).
     ?(decls:wval list) (s:wasmstate).
       wasm_decl_vals va1_f25_mc = SOME decls /\
       read wcode s = va1_f25_mc /\ read wpc s = word 13 /\ read wstatus s = WRunning /\
       read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
       read wmemsize s = 4194304 /\
       read wlocals s = wcall_locals [I32 a2; I32 a1; I32 a0] decls /\
       va1_tick t (read wmem s) /\ read (bytes32 (word 16396)) (read wmem s) = word 4294967295 /\
       va1_mdl mdl (read wmem s) /\ va1_w32s 65536 262144 tbl (read wmem s)`,
  REPEAT GEN_TAC THEN
  EXISTS_TAC `[I64 (word 0); I64 (word 0); I64 (word 0); I64 (word 0); I64 (word 0); I32 (word 0); I64 (word 0); I64 (word 0); I32 (word 0); I64 (word 0); I64 (word 0); I64 (word 0); I32 (word 0)]` THEN
  EXISTS_TAC (subst [mk_comb(c3b_memw, c3b_WT), `mm:int64->byte`]
   `write wcode va1_f25_mc (write wpc (word 13) (write wstatus WRunning (write wstack [] (write wlabels []
     (write warity 1 (write wmemsize 4194304 (write wlocals (wcall_locals [I32 a2; I32 a1; I32 a0]
       [I64 (word 0); I64 (word 0); I64 (word 0); I64 (word 0); I64 (word 0); I32 (word 0); I64 (word 0); I64 (word 0); I32 (word 0); I64 (word 0); I64 (word 0); I64 (word 0); I32 (word 0)])
       (write wmem (mm:int64->byte) (ARB:wasmstate)))))))))`) THEN
  REWRITE_TAC[C3B_DECLS] THEN CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  REWRITE_TAC[va1_tick; va1_mdl; va1_w32s] THEN REPEAT CONJ_TAC THEN C3B_MEMCONJ_TAC c3b_WT);;

let c3b_m0 = mk_comb(c3b_memw, c3b_W0) and c3b_m1 = mk_comb(c3b_memw, c3b_W1);;
let C3B_WEQ_TAC (wa:term) (wb:term) : tactic =
  W(fun (asl,w) -> MATCH_MP_TAC (BETA_RULE (SPECL [wa; wb; `a:num`] C3B_MEMW_B8))) THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`a:num`; `4`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(a DIV 4 = 4099 \/ a DIV 4 = 4102 \/ a DIV 4 = 4103 \/ a DIV 4 = 4104 \/
                  (282624 <= a DIV 4 /\ a DIV 4 < 286720) \/ (292864 <= a DIV 4 /\ a DIV 4 < 294912))`
    (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;;
let VA1_PUNCT_UNPUNCT_SAT = prove
 (`!(t:int32) (mdl:num->int32) (tbl:num->int32) (a0:int32) (a1:int32) (a2:int32).
     ~(t = word 4294967295)
     ==> ?(m0:int64->byte) (m1:int64->byte) (m2:int64->byte).
           va1_punct_clean m0 /\ va1_mdl mdl m0 /\ va1_w32s 65536 262144 tbl m0 /\
           va1_f25_post t mdl tbl a0 a1 a2 m1 /\ va1_f25_frame m0 m1 /\
           va1_unpunct_post m1 m2 /\ va1_unpunct_frame m1 m2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  EXISTS_TAC c3b_m0 THEN EXISTS_TAC c3b_m1 THEN EXISTS_TAC c3b_m0 THEN
  SUBGOAL_THEN (list_mk_conj [mk_comb(`va1_f25_post t mdl tbl a0 a1 a2`, c3b_m1); mk_comb(`va1_mdl mdl`, c3b_m1);
                              mk_comb(`va1_w32s 65536 262144 tbl`, c3b_m1)]) STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[va1_f25_post; va1_mdl; va1_w32s] THEN REPEAT CONJ_TAC THEN C3B_MEMCONJ_TAC c3b_W1; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (mk_conj(mk_eq(mk_comb(`read (bytes32 (word 16404))`, c3b_m0), `word 0:int32`),
                        mk_eq(mk_comb(`read (bytes32 (word 16404))`, c3b_m1), `word 0:int32`))) STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [C3B_MEMCONJ_TAC c3b_W0; C3B_MEMCONJ_TAC c3b_W1]; ALL_TAC] THEN
  MP_TAC(SPECL [`t:int32`; `mdl:num->int32`; `tbl:num->int32`; `a0:int32`; `a1:int32`; `a2:int32`; c3b_m1] C3B_BAD_M1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC BETA_RULE THEN
  REWRITE_TAC[va1_punct_clean; va1_unpunct_post; va1_f25_frame; va1_unpunct_frame] THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN
  REPEAT CONJ_TAC THEN
  FIRST [X_GEN_TAC `a:num` THEN STRIP_TAC THEN FIRST [C3B_WEQ_TAC c3b_W1 c3b_W0; C3B_WEQ_TAC c3b_W0 c3b_W1];
         ASM_REWRITE_TAC[WORD_ADD_0] THEN NO_TAC;
         REWRITE_TAC[va1_w32s; va1_mdl] THEN C3B_MEMCONJ_TAC c3b_W0]);;
