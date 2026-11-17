needs "ve_vort.ml";;
needs "ve_tick.ml";;
needs "ve_vk.ml";;
needs "va1_code.ml";;
needs "va1_seq_final2.ml";;
needs "pop_design_defs.ml";;
needs "pop_design_stmts.ml";;
needs "pop_l2_cdrift.ml";;
needs "pop_l3_jdrift.ml";;
needs "pop_l4_drop.ml";;
needs "pop_l1_rimd.ml";;
needs "pop_l1_rim.ml";;
needs "pop_l5_unbirth.ml";;
needs "pop_h1_hol.ml";;
needs "pop_n1_sat.ml";;
needs "pop_q0_calls.ml";;
needs "pop_q1_untick.ml";;
needs "pop_q2_forward.ml";;
needs "pop_r5_jig_defs.ml";;
needs "pop_r5jig_dec.ml";;
needs "pop_r5jig_lem.ml";;
needs "pop_r5_corr_defs.ml";;
needs "pop_r5c_lem.ml";;
needs "pop_r5b_bdec.ml";;
needs "pop_r5bp_lem.ml";;
needs "pop_r5bp_lem2.ml";;
needs "pop_r5bp_lem3.ml";;
needs "pop_r5bp_lem4.ml";;
needs "pop_r5bp_lem5b.ml";;
needs "pop_r5bp_lem6.ml";;
needs "pop_s0_end.ml";;
needs "pop_r5_r4c_final.ml";;
needs "chain_c1_host.ml";;
needs "chain_c3a_defs.ml";;
needs "chain_c3a_f26a.ml";;
needs "chain_c3a_f26b.ml";;
needs "chain_c3a_f26c.ml";;
needs "chain_c3a_seq.ml";;
needs "chain_c3a_fin.ml";;
needs "chain_c2_host_pop.ml";;
needs "chain_c2_chain.ml";;
needs "chain_c1_np.ml";;
needs "chain_c1_frame.ml";;
(* ========================================================================= *)
(* Vortex chain, rung C4, layer 1 of 2 (C4 agent, Claude Opus 5.5,          *)
(* 2026-11-13). Spec chain_c4_final.spec. The five C4 definitions exactly   *)
(* as pinned; byte/word lemmas (method of C3b's pure layer and of pop_n1's  *)
(* POP_N1_B32_SAT, copied and renamed C4_); frame lemmas; the union frame;  *)
(* va1_film_bytes from the union frame and the pins at both ends; the       *)
(* satisfiability theorems. Pure HOL; no stepping; no mk_thm / new_axiom.   *)
(* ========================================================================= *)

let va1_clean = new_definition
 `va1_clean (m:int64->byte) <=>
    va1_w32s 16408 26 (\k. word 0) m /\ va1_w32s 65536 262144 (\k. word 0) m /\
    va1_w32s 1130496 2048 (\k. word 0) m /\ va1_w32s 1138688 2048 (\k. word 0) m /\
    va1_w32s 1146880 2048 (\k. word 0) m /\ va1_w32s 1155072 2048 (\k. word 0) m /\
    va1_bs ((\k. word 0),(\k. word 0),(\k. word 0),word 0) m`;;
let va1_punct_frame = new_definition
 `va1_punct_frame (m0:int64->byte) (m:int64->byte) <=>
    !a. a < 4194304 /\ ~(16288 <= a /\ a < 16384) /\ ~(16396 <= a /\ a < 16404) /\ ~(16408 <= a /\ a < 16504) /\
        ~(65536 <= a /\ a < 1114112) /\ ~(1130496 <= a /\ a < 1966080)
        ==> read (bytes8 (word a)) m = read (bytes8 (word a)) m0`;;
let va1_punct_rel = new_definition
 `va1_punct_rel (mdl:num->int32) (gl:num->wval) (m:int64->byte) (gl':num->wval) (m':int64->byte) <=>
    gl' = gl /\
    read (bytes32 (word 16396)) m' = read (bytes32 (word 16392)) m /\
    read (bytes32 (word 16400)) m' = word 0 /\
    (?tbl. va1_w32s 65536 262144 tbl m' /\ va1_w32s 1138688 2048 (va1_rbinit tbl) m') /\
    va1_w32s 1130496 2048 (\k. word 251658) m' /\
    va1_w32s 1146880 2048 (\k. word 0) m' /\ va1_w32s 1155072 2048 (\k. word 0) m' /\
    va1_w32s 1163264 2048 (\k. word 0) m' /\ va1_w32s 1171456 2048 (va1_zpseed mdl) m' /\
    va1_w32s 1179648 196608 (\k. word 0) m' /\
    va1_punct_frame m m'`;;
let va1_autopunct_rel = new_definition
 `va1_autopunct_rel (mdl:num->int32) (N:num) (x:(num->int32)#(num->int32))
                    (gl:num->wval) (m:int64->byte) (gl':num->wval) (m':int64->byte) <=>
    ?m1:int64->byte.
      read (bytes32 (word 16392)) m1 = word_add (read (bytes32 (word 16392)) m) (word 1) /\
      va1_vab N (va1_swf mdl x) m1 /\ va1_np_frame m m1 /\ va1_punct_rel mdl gl m1 gl' m'`;;
let va1_film_bytes = new_definition
 `va1_film_bytes (N:num) (m0:int64->byte) (m:int64->byte) <=>
    !a. a < 4194304 /\ ~(16288 <= a /\ a < 16384) /\ ~(1114112 + 12 * N <= a /\ a < 1122304) /\
        ~(1122304 + 12 * N <= a /\ a < 1130496) /\ ~(1966080 <= a /\ a < 2039808)
        ==> read (bytes8 (word a)) m = read (bytes8 (word a)) m0`;;

(* ---- bytes and words ---- *)
let C4_RB32 = prove(`!(a:int64) (m:int64->byte). read (bytes32 a) m = word (read (bytes(a,4)) m)`,
  REWRITE_TAC[bytes32; READ_COMPONENT_COMPOSE; asword; through; read]);;
let C4_B8 = prove(`!(a:int64) (m:int64->byte). read (bytes8 a) m = m a`, REWRITE_TAC[BYTES8_ELEMENT; READ_ELEMENT]);;
let C4_B32_B8 = prove
 (`!b (m:int64->byte) m'. b + 4 <= 2 EXP 64 /\ read (bytes32 (word b)) m = read (bytes32 (word b)) m'
     ==> !i. i < 4 ==> read (bytes8 (word (b + i))) m = read (bytes8 (word (b + i))) m'`,
  REWRITE_TAC[C4_RB32; C4_B8] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `read (bytes(word b:int64,4)) m = read (bytes(word b:int64,4)) (m':int64->byte)` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int32->num`) THEN REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
    MP_TAC(ISPECL [`word b:int64`; `4`; `m:int64->byte`] READ_BYTES_BOUND) THEN
    MP_TAC(ISPECL [`word b:int64`; `4`; `m':int64->byte`] READ_BYTES_BOUND) THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT];
    REWRITE_TAC[READ_BYTES_EQ; GSYM WORD_ADD]]);;
let C4_B8_B32 = prove
 (`!b (m:int64->byte) m'. (!i. i < 4 ==> read (bytes8 (word (b + i))) m = read (bytes8 (word (b + i))) m')
     ==> read (bytes32 (word b)) m = read (bytes32 (word b)) m'`,
  REWRITE_TAC[C4_RB32; C4_B8] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[READ_BYTES_EQ; GSYM WORD_ADD] THEN ASM_SIMP_TAC[]);;
let C4_W1_BYTES = prove
 (`!b a (m:int64->byte) m'. read (bytes32 (word b)) m = read (bytes32 (word b)) m' /\ b <= a /\ a < b + 4 /\ b + 4 <= 2 EXP 64
     ==> read (bytes8 (word a)) m = read (bytes8 (word a)) m'`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`b:num`; `m:int64->byte`; `m':int64->byte`] C4_B32_B8) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `a - b`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `b + a - b = a` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC);;
let C4_WORD_BYTES = prove
 (`!base n f (m:int64->byte) m' a. va1_w32s base n f m /\ va1_w32s base n f m' /\ base <= a /\ a < base + 4 * n /\ base + 4 * n <= 2 EXP 64
     ==> read (bytes8 (word a)) m = read (bytes8 (word a)) m'`,
  REWRITE_TAC[va1_w32s] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC C4_W1_BYTES THEN EXISTS_TAC `base + 4 * ((a - base) DIV 4)` THEN
  SUBGOAL_THEN `(a - base) DIV 4 < n` ASSUME_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN MP_TAC(SPECL [`a - base`; `4`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

(* a frame keeps a block of words *)
let C4_KEEP_W32S = prove
 (`!(m0:int64->byte) m base n (f:num->int32).
     (!k i. k < n /\ i < 4 ==> read (bytes8 (word (base + 4 * k + i))) m = read (bytes8 (word (base + 4 * k + i))) m0) /\
     va1_w32s base n f m0 ==> va1_w32s base n f m`,
  REWRITE_TAC[va1_w32s] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `read (bytes32 (word (base + 4 * k))) (m0:int64->byte)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC C4_B8_B32 THEN ASM_SIMP_TAC[GSYM ADD_ASSOC]; ASM_SIMP_TAC[]]);;
let C4_KEEP_W32 = prove
 (`!(m0:int64->byte) m b.
     (!i. i < 4 ==> read (bytes8 (word (b + i))) m = read (bytes8 (word (b + i))) m0)
     ==> read (bytes32 (word b)) m = read (bytes32 (word b)) m0`,
  REWRITE_TAC[C4_B8_B32]);;
(* the tactics: goal `va1_w32s base n f m` or `read (bytes32 (word b)) m = v`, with a frame !a. C a ==> eq in the assumptions *)
let C4_W_TAC (m0:term) : tactic = fun (asl,w) ->
  let l = lhs w in
  let rd = rator l in
  (MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (mk_comb(rd, m0)) THEN CONJ_TAC THENL
    [MATCH_MP_TAC C4_KEEP_W32 THEN REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
     ASM_REWRITE_TAC[]]) (asl,w);;
let C4_WS_TAC (m0:term) : tactic =
  MATCH_MP_TAC C4_KEEP_W32S THEN EXISTS_TAC m0 THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];;

let C4_MDL_W32S = prove
 (`!(mdl:num->int32) (m:int64->byte). va1_mdl mdl m <=> va1_w32s 16640 1024 mdl m`,
  REWRITE_TAC[va1_mdl; va1_w32s]);;
let C4_VAB_W32S = prove
 (`!N (x:(num->int32)#(num->int32)) (m:int64->byte).
     va1_vab N x m <=> va1_w32s 1114112 (3 * N) (FST x) m /\ va1_w32s 1122304 (3 * N) (SND x) m`,
  REWRITE_TAC[va1_vab; va1_w32s]);;
let C4_NPST_W = prove
 (`!t ap mdl N (x:(num->int32)#(num->int32)) (m:int64->byte).
     va1_np_st t ap mdl N x m <=>
     read (bytes32 (word 16392)) m = t /\ read (bytes32 (word 16396)) m = word 4294967295 /\
     read (bytes32 (word 16512)) m = ap /\ va1_w32s 16640 1024 mdl m /\
     va1_w32s 1114112 (3 * N) (FST x) m /\ va1_w32s 1122304 (3 * N) (SND x) m`,
  REWRITE_TAC[va1_np_st; va1_tick; va1_pop; C4_MDL_W32S; C4_VAB_W32S; CONJ_ASSOC]);;
let C4_CLEAN_W = prove
 (`!(m:int64->byte). va1_clean m <=>
     va1_w32s 16408 26 (\k. word 0) m /\ va1_w32s 65536 262144 (\k. word 0) m /\
     va1_w32s 1130496 2048 (\k. word 0) m /\ va1_w32s 1138688 2048 (\k. word 0) m /\
     va1_w32s 1146880 2048 (\k. word 0) m /\ va1_w32s 1155072 2048 (\k. word 0) m /\
     va1_w32s 1179648 196608 (\k. word 0) m /\ va1_w32s 1163264 2048 (\k. word 0) m /\
     va1_w32s 1171456 2048 (\k. word 0) m /\ read (bytes32 (word 16400)) m = word 0`,
  REWRITE_TAC[va1_clean; va1_bs; FST; SND]);;

(* ---- the union frame U: outside [16288,16384), [16392,16512), [65536,2039808) ---- *)
let c4_uf = `\(m0:int64->byte) (m:int64->byte). !a. a < 4194304 /\ ~(16288 <= a /\ a < 16384) /\
     ~(16392 <= a /\ a < 16512) /\ ~(65536 <= a /\ a < 2039808)
     ==> read (bytes8 (word a)) m = read (bytes8 (word a)) m0`;;
let c4_ufc m0 m = rhs(concl(BETA_CONV(mk_comb(rhs(concl(BETA_CONV(mk_comb(c4_uf, m0)))), m))));;
let C4_UF_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_np_frame; va1_punct_frame; va1_pop_frame; va1_unp_frame] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;;
let C4_UF_NP = prove(mk_forall(`m0:int64->byte`, mk_forall(`m:int64->byte`,
  mk_imp(`va1_np_frame m0 m`, c4_ufc `m0:int64->byte` `m:int64->byte`))), C4_UF_TAC);;
let C4_UF_PUNCT = prove(mk_forall(`m0:int64->byte`, mk_forall(`m:int64->byte`,
  mk_imp(`va1_punct_frame m0 m`, c4_ufc `m0:int64->byte` `m:int64->byte`))), C4_UF_TAC);;
let C4_UF_POP = prove(mk_forall(`m0:int64->byte`, mk_forall(`m:int64->byte`,
  mk_imp(`va1_pop_frame m0 m`, c4_ufc `m0:int64->byte` `m:int64->byte`))), C4_UF_TAC);;
let C4_UF_UNP = prove(mk_forall(`m0:int64->byte`, mk_forall(`m:int64->byte`,
  mk_imp(`va1_unp_frame m0 m`, c4_ufc `m0:int64->byte` `m:int64->byte`))), C4_UF_TAC);;
let C4_UF_TRANS = prove(list_mk_forall([`m0:int64->byte`; `m1:int64->byte`; `m2:int64->byte`],
  mk_imp(mk_conj(c4_ufc `m0:int64->byte` `m1:int64->byte`, c4_ufc `m1:int64->byte` `m2:int64->byte`),
         c4_ufc `m0:int64->byte` `m2:int64->byte`)), MESON_TAC[]);;

(* va1_clean is kept by the no-pop and pop frames *)
let C4_CLEAN_NP = prove
 (`!(m0:int64->byte) m. va1_np_frame m0 m /\ va1_clean m0 ==> va1_clean m`,
  REWRITE_TAC[C4_CLEAN_W; va1_np_frame] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN TRY(C4_WS_TAC `m0:int64->byte`) THEN C4_W_TAC `m0:int64->byte`);;

(* ---- va1_film_bytes from U and the pins at both ends ---- *)
let C4_FILM_BYTES_OF = prove
 (mk_forall(`N:num`, mk_forall(`ap:int32`, mk_forall(`mdl:num->int32`, mk_forall(`x0:(num->int32)#(num->int32)`,
  mk_forall(`m0:int64->byte`, mk_forall(`m:int64->byte`,
   mk_imp(list_mk_conj [`N <= 640`; c4_ufc `m0:int64->byte` `m:int64->byte`;
     `va1_np_st (word 0) ap mdl N x0 m0`; `va1_np_st (word 0) ap mdl N x0 m`; `va1_clean m0`; `va1_clean m`;
     `read (bytes32 (word 16404)) m = read (bytes32 (word 16404)) m0`],
    `va1_film_bytes N m0 m`))))))),
  REPEAT GEN_TAC THEN REWRITE_TAC[C4_NPST_W; C4_CLEAN_W; va1_film_bytes] THEN STRIP_TAC THEN
  X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  (* only linear case facts `a < t` / `~(a < t)` are added, so each arithmetic call sees at most 4 disjunctions *)
  let w1 b = MATCH_MP_TAC C4_W1_BYTES THEN EXISTS_TAC b THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC in
  let wb b n f = MATCH_MP_TAC C4_WORD_BYTES THEN MAP_EVERY EXISTS_TAC [b; n; f] THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC in
  let uf = FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC in
  let no = MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC in
  let z = `\k:num. word 0:int32` in
  let rec chain l = match l with
      [] -> uf
    | (t,tac)::rest -> ASM_CASES_TAC (mk_binop `(<):num->num->bool` `a:num` t) THENL [tac; chain rest] in
  chain [`16392`, uf; `16396`, w1 `16392`; `16400`, w1 `16396`; `16404`, w1 `16400`; `16408`, w1 `16404`;
         `16512`, wb `16408` `26` z; `65536`, uf; `1114112`, wb `65536` `262144` z;
         `1114112 + 12 * N`, wb `1114112` `3 * N` `FST(x0:(num->int32)#(num->int32))`; `1122304`, no;
         `1122304 + 12 * N`, wb `1122304` `3 * N` `SND(x0:(num->int32)#(num->int32))`; `1130496`, no;
         `1138688`, wb `1130496` `2048` z; `1146880`, wb `1138688` `2048` z; `1155072`, wb `1146880` `2048` z;
         `1163264`, wb `1155072` `2048` z; `1171456`, wb `1163264` `2048` z; `1179648`, wb `1171456` `2048` z;
         `1966080`, wb `1179648` `196608` z; `2039808`, no]);;

(* ---- memory witnesses (method of pop_n1_sat.ml POP_N1_B32_SAT, PROVED in N1; as in C3b, renamed) ---- *)
let c4_memw = `\(W:num->int32) (b:int64). write (bytes(word(4 * (val b DIV 4)):int64,4)) (val(W(val b DIV 4))) (\c:int64. word 0:byte) b`;;
let C4_MEMW_B32 = prove
 (mk_forall(`W:num->int32`, mk_forall(`w:num`, mk_imp(`4 * w + 4 <= 2 EXP 64`,
   mk_eq(mk_comb(mk_comb(`read:((int64->byte),int32)component->(int64->byte)->int32`, `bytes32 (word (4 * w))`), mk_comb(c4_memw, `W:num->int32`)), `(W:num->int32) w`)))),
  REPEAT GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN REWRITE_TAC[C4_RB32] THEN
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
(* a witness keeps a byte of m when its word there is m's word *)
let C4_MEMW_KEEP = prove
 (mk_forall(`W:num->int32`, mk_forall(`m:int64->byte`, mk_forall(`a:num`,
   mk_imp(`a < 4194304 /\ (W:num->int32) (a DIV 4) = read (bytes32 (word (4 * (a DIV 4)))) (m:int64->byte)`,
     mk_eq(mk_comb(`read (bytes8 (word a))`, mk_comb(c4_memw, `W:num->int32`)), `read (bytes8 (word a)) (m:int64->byte)`))))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`4 * (a DIV 4)`; mk_comb(c4_memw, `W:num->int32`); `m:int64->byte`] C4_B32_B8) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [MP_TAC(SPECL [`a:num`; `4`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(W:num->int32) (a DIV 4)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC C4_MEMW_B32 THEN MP_TAC(SPECL [`a:num`; `4`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o SPEC `a MOD 4`) THEN REWRITE_TAC[] THEN
    ANTS_TAC THENL [MP_TAC(SPECL [`a:num`; `4`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `4 * a DIV 4 + a MOD 4 = a` (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(SPECL [`a:num`; `4`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]);;
(* deciding the memory conjuncts of an explicit witness (pop_n1 / C3b tactics, copied) *)
let c4_addr_th a =
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
let C4_DECIDE_TAC =
  W(fun (asl,w) ->
      let l = lhs w in
      if is_cond l then
        let c = rand(rator(rator l)) in
        (SUBGOAL_THEN (mk_neg c) MP_TAC THENL
          [ASM_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[EQF_INTRO th])]) ORELSE
        (SUBGOAL_THEN c MP_TAC THENL
          [ASM_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[EQT_INTRO th])])
      else FIRST [REFL_TAC; AP_TERM_TAC THEN ASM_ARITH_TAC]);;
let C4_MEMCONJ_TAC (mw:term) : tactic =
  REPEAT STRIP_TAC THEN BETA_TAC THEN
  W(fun (asl,w) ->
      let a = rand(rand(rand(rator(lhs w)))) in
      let th = c4_addr_th a in
      SUBST1_TAC th THEN MP_TAC (BETA_RULE (SPECL [mw; rand(rand(concl th))] C4_MEMW_B32))) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  BETA_TAC THEN REPEAT C4_DECIDE_TAC;;
(* a byte outside every word range of the witness: the witness keeps it *)
let C4_MEMKEEP_TAC (mw:term) : tactic =
  X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC (BETA_RULE (SPEC mw C4_MEMW_KEEP)) THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`a:num`; `4`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`a DIV 4`,`q:num`) THEN GEN_TAC THEN STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THENL [MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC; POP_ASSUM(K ALL_TAC)]) THEN REFL_TAC;;

let c4_Wp = `\w. if w = 4099 then read (bytes32 (word 16392)) (m:int64->byte)
                 else if w = 4100 then word 0
                 else if 16384 <= w /\ w < 278528 then word 0
                 else if 282624 <= w /\ w < 284672 then word 251658
                 else if 284672 <= w /\ w < 286720 then va1_rbinit (\k. word 0) (w - 284672)
                 else if 292864 <= w /\ w < 294912 then va1_zpseed (mdl:num->int32) (w - 292864)
                 else if 286720 <= w /\ w < 491520 then word 0
                 else read (bytes32 (word (4 * w))) m`;;
let VA1_PUNCT_REL_SAT = prove
 (`!(mdl:num->int32) (gl:num->wval) (m:int64->byte). ?gl' m'. va1_punct_rel mdl gl m gl' m'`,
  REPEAT GEN_TAC THEN MAP_EVERY EXISTS_TAC [`gl:num->wval`; mk_comb(c4_memw, c4_Wp)] THEN
  REWRITE_TAC[va1_punct_rel; va1_punct_frame] THEN
  REPEAT CONJ_TAC THENL
   [C4_MEMCONJ_TAC c4_Wp; C4_MEMCONJ_TAC c4_Wp;
    EXISTS_TAC `\k:num. word 0:int32` THEN REWRITE_TAC[va1_w32s] THEN CONJ_TAC THEN C4_MEMCONJ_TAC c4_Wp;
    REWRITE_TAC[va1_w32s] THEN C4_MEMCONJ_TAC c4_Wp;
    REWRITE_TAC[va1_w32s] THEN C4_MEMCONJ_TAC c4_Wp;
    REWRITE_TAC[va1_w32s] THEN C4_MEMCONJ_TAC c4_Wp;
    REWRITE_TAC[va1_w32s] THEN C4_MEMCONJ_TAC c4_Wp;
    REWRITE_TAC[va1_w32s] THEN C4_MEMCONJ_TAC c4_Wp;
    REWRITE_TAC[va1_w32s] THEN C4_MEMCONJ_TAC c4_Wp;
    C4_MEMKEEP_TAC c4_Wp]);;

let c4_Ws = `\w. if w = 4098 then (t1:int32)
                 else if 278528 <= w /\ w < 278528 + 3 * N then FST (va1_swf (mdl:num->int32) (x:(num->int32)#(num->int32))) (w - 278528)
                 else if 280576 <= w /\ w < 280576 + 3 * N then SND (va1_swf mdl x) (w - 280576)
                 else read (bytes32 (word (4 * w))) (m:int64->byte)`;;
let VA1_AUTOPUNCT_REL_SAT = prove
 (`!(mdl:num->int32) (N:num) (x:(num->int32)#(num->int32)) (gl:num->wval) (m:int64->byte).
     N <= 640 ==> ?gl' m'. va1_autopunct_rel mdl N x gl m gl' m'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[va1_autopunct_rel] THEN
  ABBREV_TAC `t1 = word_add (read (bytes32 (word 16392)) (m:int64->byte)) (word 1)` THEN
  MP_TAC(SPECL [`mdl:num->int32`; `gl:num->wval`; mk_comb(c4_memw, c4_Ws)] VA1_PUNCT_REL_SAT) THEN
  DISCH_THEN(X_CHOOSE_THEN `g2:num->wval` (X_CHOOSE_TAC `m2:int64->byte`)) THEN
  MAP_EVERY EXISTS_TAC [`g2:num->wval`; `m2:int64->byte`; mk_comb(c4_memw, c4_Ws)] THEN
  REPEAT CONJ_TAC THENL
   [C4_MEMCONJ_TAC c4_Ws;
    REWRITE_TAC[va1_vab] THEN CONJ_TAC THEN C4_MEMCONJ_TAC c4_Ws;
    REWRITE_TAC[va1_np_frame] THEN C4_MEMKEEP_TAC c4_Ws;
    FIRST_ASSUM ACCEPT_TAC]);;

(* ---- the start is realisable; the function table ---- *)
let C4_START_SAT = prove
 (`!(ap:int32) (mdl:num->int32) (N:num) (x0:(num->int32)#(num->int32)).
     N <= 640 ==> ?m0:int64->byte. va1_np_st (word 0) ap mdl N x0 m0 /\ va1_clean m0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word 0:int32`; `word 4294967295:int32`; `ap:int32`; `mdl:num->int32`; `N:num`;
    `x0:(num->int32)#(num->int32)`; `\i:num. word 0:int32`; `\i:num. word 0:int32`;
    `((\i:num. word 0:int32),(\i:num. word 0:int32),(\i:num. word 0:int32),(\i:num. word 0:int32),
      (\i:num. word 0:int32),(\i:num. word 0:int32),(\i:num. word 0:int32),(word 0:int32))`] VA1_ST_SAT) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  REWRITE_TAC[va1_st; va1_np_st; va1_clean; FST; SND] THEN MESON_TAC[]);;
let c4_fs = `\i. if i = 9 then (va1_f9_mc,0,0) else if i = 10 then (va1_f10_mc,0,0)
         else if i = 11 then (va1_f11_mc,0,0) else if i = 12 then (va1_f12_mc,0,0)
         else if i = 13 then (va1_f13_mc,0,1) else if i = 14 then (va1_f14_mc,0,1)
         else if i = 15 then (va1_f15_mc,0,0) else if i = 16 then (va1_f16_mc,0,0)
         else if i = 17 then (va1_f17_mc,1,0) else if i = 18 then (va1_f18_mc,1,0)
         else if i = 19 then (va1_f19_mc,0,0) else if i = 20 then (va1_f20_mc,0,0)
         else if i = 21 then (va1_f21_mc,0,0) else if i = 22 then (va1_f22_mc,0,0)
         else if i = 23 then (va1_f23_mc,0,0) else if i = 24 then (va1_f24_mc,0,0)
         else if i = 26 then (va1_f26_mc,0,1)
         else if i = 27 then (va1_f27_mc,0,0) else (va1_f28_mc,0,0)`;;
let C4_FS_SAT = prove
 (mk_conj(mk_comb(`va1_fs_np`, c4_fs), mk_conj(mk_comb(`va1_fs_pop`, c4_fs), mk_eq(mk_comb(c4_fs, `26`), `(va1_f26_mc,0,1)`))),
  REWRITE_TAC[va1_fs_np; va1_fs_pop] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;
let VA1_FILM_SAT = prove
 (`(?fs:num->byte list#num#num. va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1)) /\
  (!(ap:int32) (mdl:num->int32) (N:num) (x0:(num->int32)#(num->int32)).
     N <= 640 ==> ?m0:int64->byte. va1_np_st (word 0) ap mdl N x0 m0 /\ va1_clean m0) /\
  (?(fs:num->byte list#num#num) (mdl:num->int32) (N:num) (x0:(num->int32)#(num->int32)) (m0:int64->byte).
     va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\ mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
     va1_np_st (word 0) (word 0) mdl N x0 m0 /\ va1_clean m0) /\
  (!K. ?(fs:num->byte list#num#num) (mdl:num->int32) (N:num) (x0:(num->int32)#(num->int32)) (m0:int64->byte).
     va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\ mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
     va1_np_st (word 0) (word K) mdl N x0 m0 /\ va1_clean m0)`,
  let inst ap =
    MP_TAC(ISPECL [ap; `\k:num. word 1:int32`; `1`; `((\i:num. word 0:int32),(\i:num. word 0:int32))`] C4_START_SAT) THEN
    REWRITE_TAC[ARITH_RULE `1 <= 640`] THEN DISCH_THEN(X_CHOOSE_TAC `m0:int64->byte`) THEN
    MAP_EVERY EXISTS_TAC [c4_fs; `\k:num. word 1:int32`; `1`; `((\i:num. word 0:int32),(\i:num. word 0:int32))`;
                          `m0:int64->byte`] THEN
    REWRITE_TAC[C4_FS_SAT] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] in
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC c4_fs THEN REWRITE_TAC[C4_FS_SAT] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    REWRITE_TAC[C4_START_SAT];
    inst `word 0:int32`;
    GEN_TAC THEN inst `word K:int32`]);;
