needs "ve_vort.ml";;
needs "ve_tick.ml";;
needs "ve_vk.ml";;
needs "va1_code.ml";;
needs "va1_seq_final2.ml";;
needs "pop_design_defs.ml";;
needs "pop_design_stmts.ml";;
(* ========================================================================= *)
(* Vortex pop effort, segment N1 (SEGMENT PROVER N1, Claude Opus 5.5,        *)
(* 2026-11-11): memory satisfiability of the pop state predicate.            *)
(*                                                                           *)
(*   VA1_ST_SAT        : va1_st is satisfiable for ANY values (N <= 640)     *)
(*   VA1_POP_STATE_SAT : a pop-window state (t = 130, p = 120) with an       *)
(*                       empty, well-formed births log exists                *)
(*                                                                           *)
(* TAIL layer (design section 5): loaded after PREFIX (= basis               *)
(* 31c533df051f: ve_vort, ve_tick, ve_vk, va1_code, va1_seq_final2,          *)
(* pop_design_defs, pop_design_stmts) and pop_h1_hol.ml. It uses only the    *)
(* definitions of pop_design_defs.ml / va1_seq_final2.ml and the statement   *)
(* strings of pop_design_stmts.ml (sha256 97f899dc...): each goal is proved  *)
(* as prove(parse_term pop_spec_NAME, TAC), so the statement is character-   *)
(* identical to the frozen one. No new definitions, no parser changes, no   *)
(* mk_thm / new_axiom / CHEAT_TAC. Helper names carry the prefix POP_N1.     *)
(*                                                                           *)
(* Idea: one core lemma, POP_N1_B32_SAT: for ANY W : num -> int32 there is a *)
(* memory m with read (bytes32 (word (4 * w))) m = W w for every word index  *)
(* w (4 w + 4 <= 2^64). Witness: byte b of m is byte b of                    *)
(* write (bytes (word (4 * (val b DIV 4)), 4)) (val (W (val b DIV 4))) m0.   *)
(* Then W is chosen piecewise by word index; every region of va1_st is       *)
(* 4-aligned and the regions are pairwise disjoint (word indices):           *)
(*   T 4098, P 4099, ND 4100, hp 4102..4127, AUTO 4128, mdl 4160..5183,      *)
(*   TBL 16384..278527, VA 278528.., VB 280576.. (3N <= 1920 words each),    *)
(*   RA 282624, RB 284672, JQ 286720, JP 288768, ZQ 290816, ZP 292864        *)
(*   (2048 words each), DI 294912..491519.                                   *)
(* ========================================================================= *)

let POP_N1_READ_BYTES32 = prove
 (`!(a:int64) (m:int64->byte). read (bytes32 a) m = word (read (bytes(a,4)) m)`,
  REWRITE_TAC[bytes32; READ_COMPONENT_COMPOSE; asword; through; read]);;

let POP_N1_B32_SAT = prove
 (`!W:num->int32. ?m:int64->byte.
      !w. 4 * w + 4 <= 2 EXP 64 ==> read (bytes32 (word (4 * w))) m = W w`,
  GEN_TAC THEN
  EXISTS_TAC
   `\b:int64. write (bytes(word(4 * (val b DIV 4)):int64,4))
                    (val((W:num->int32)(val b DIV 4))) (\c:int64. word 0:byte) b` THEN
  X_GEN_TAC `w:num` THEN DISCH_TAC THEN
  REWRITE_TAC[POP_N1_READ_BYTES32] THEN
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

(* ---- one conjunct of the unfolded va1_st: `read (bytes32 (word A)) m = v` *)
(*      or `!k. k < n ==> read (bytes32 (word (b + 4 * k))) m = f k`, with    *)
(*      the core property of m as assumption "m". "m" is REMOVED before any  *)
(*      arithmetic: its piecewise W would make ASM_ARITH_TAC split every     *)
(*      conditional (observed: > 600 s without finishing).                   *)

let pop_n1_addr_th a =
  (* a = numeral 4q  |->  |- a = 4 * q ;  a = b + 4 * k  |->  |- a = 4 * (b/4 + k) *)
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

let POP_N1_DECIDE_TAC =
  (* the goal is `(if c then a else b) = v` or `a = v`: decide c from the    *)
  (* bound hypotheses only (k < n, j < 3 * N, N <= 640), rewrite it away;    *)
  (* never case-split (negated conditions would make ASM_ARITH_TAC blow up). *)
  W(fun (asl,w) ->
      let l = lhs w in
      if is_cond l then
        let c = rand(rator(rator l)) in
        (SUBGOAL_THEN (mk_neg c) MP_TAC THENL
          [ASM_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[EQF_INTRO th])]) ORELSE
        (SUBGOAL_THEN c MP_TAC THENL
          [ASM_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[EQT_INTRO th])])
      else FIRST [REFL_TAC; AP_TERM_TAC THEN ASM_ARITH_TAC]);;

let POP_N1_IF_TAC = REPEAT POP_N1_DECIDE_TAC;;

let POP_N1_CONJ_TAC =
  REPEAT STRIP_TAC THEN
  W(fun (asl,w) ->
      let a = rand(rand(rand(rator(lhs w)))) in
      let th = pop_n1_addr_th a in
      SUBST1_TAC th THEN
      REMOVE_THEN "m" (fun mth -> MP_TAC(SPEC (rand(rand(concl th))) mth))) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
                  DISCH_THEN SUBST1_TAC] THEN
  BETA_TAC THEN POP_N1_IF_TAC;;

let VA1_ST_SAT = prove(parse_term pop_spec_VA1_ST_SAT,
  MAP_EVERY X_GEN_TAC
   [`t:int32`; `p:int32`; `ap:int32`; `mdl:num->int32`; `N:num`;
    `x:(num->int32)#(num->int32)`; `hp:num->int32`; `tbl:num->int32`] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`ra:num->int32`; `rb:num->int32`; `jq:num->int32`; `jp:num->int32`;
    `di:num->int32`; `zq:num->int32`; `zp:num->int32`; `nd:int32`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC
   `\w. if w = 4098 then t:int32
        else if w = 4099 then p
        else if w = 4100 then nd
        else if w = 4128 then ap
        else if 4102 <= w /\ w < 4128 then hp (w - 4102)
        else if 4160 <= w /\ w < 5184 then mdl (w - 4160)
        else if 16384 <= w /\ w < 278528 then tbl (w - 16384)
        else if 278528 <= w /\ w < 280576 then FST x (w - 278528)
        else if 280576 <= w /\ w < 282624 then SND x (w - 280576)
        else if 282624 <= w /\ w < 284672 then ra (w - 282624)
        else if 284672 <= w /\ w < 286720 then rb (w - 284672)
        else if 286720 <= w /\ w < 288768 then jq (w - 286720)
        else if 288768 <= w /\ w < 290816 then jp (w - 288768)
        else if 290816 <= w /\ w < 292864 then zq (w - 290816)
        else if 292864 <= w /\ w < 294912 then zp (w - 292864)
        else di (w - 294912)` POP_N1_B32_SAT) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:int64->byte` (LABEL_TAC "m")) THEN
  EXISTS_TAC `m:int64->byte` THEN
  REWRITE_TAC[va1_st; va1_tick; va1_pop; va1_mdl; va1_vab; va1_w32s; va1_bs] THEN
  REPEAT CONJ_TAC THEN POP_N1_CONJ_TAC);;

let VA1_POP_STATE_SAT = prove(parse_term pop_spec_VA1_POP_STATE_SAT,
  REWRITE_TAC[va1_pop_window; va1_log_ok] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;
