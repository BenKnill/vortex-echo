needs "ve_vort.ml";;
needs "ve_tick.ml";;
needs "ve_vk.ml";;
needs "va1_code.ml";;
needs "va1_seq_final2.ml";;
needs "pop_design_defs.ml";;
needs "pop_design_stmts.ml";;
(* ========================================================================= *)
(* Vortex pop, segment L2 (SEG-L2 prover, Claude Opus 5.5, 2026-11-11):      *)
(* the ripple (corrugation) drift pair f19 / f20 of vortex_a1.wasm on the    *)
(* exact bytes. Lemma file (a LEAFCHAIN layer); the spec-locked final leaf   *)
(* only re-binds VA1_CDRIFT_OK.                                              *)
(*                                                                           *)
(* f19 (143 B, entry pc 3, locals l0 l1): l0 := 0; loop (pc 7, body 9):      *)
(*   block (pc 9): exit if ival RB[l0/4] > 52371633 (br_if pc 28); else      *)
(*     ZQ[l0/4] := ZQ[l0/4] + wrap((sx ZP[l0/4] + 2) >>u 2) (store pc 64);   *)
(*   block (pc 68): the same for bead l0/4 + 1 (br_if pc 87, store pc 123);  *)
(*   l0 := l0 + 8; br_if (l0 <> 8192) at pc 139; end 141; end 142.           *)
(* f20: identical except i32.sub at pc 63 and pc 122.                         *)
(* Loop invariant at count i (l0 = 8i): ZQ[k] = OP zq[k] (va1_cdrift rb zp k) *)
(* for k < 2i, zq k above; RB, ZP unchanged. Each body splits on the two     *)
(* bead branches (4 straight-line paths: 22, 40, 40, 58 steps).              *)
(* ========================================================================= *)

let cdrift_inv mc op =
  let t = subst [mc,`MC:byte list`; op,`OP:int32->int32->int32`]
   `\i s. read wcode s = MC /\ read wstatus s = WRunning /\
          read wmemsize s = 4194304 /\ read warity s = 0 /\
          read wlabels s = [0,7,0] /\
          read (wlocal 0) s = I32 (word (8 * i)) /\
          read wstack s = (if read wpc s = word 9 then []
                           else [I32 (word (bitval (~(word (8 * i):int32 = word 8192))))]) /\
          (!k. k < 2048 ==> read (wmem :> bytes32 (word (1138688 + 4 * k))) s = (rb:num->int32) k) /\
          (!k. k < 2048 ==> read (wmem :> bytes32 (word (1163264 + 4 * k))) s =
                            (if k < 2 * i then OP ((zq:num->int32) k) (va1_cdrift rb zp k) else zq k)) /\
          (!k. k < 2048 ==> read (wmem :> bytes32 (word (1171456 + 4 * k))) s = (zp:num->int32) k)` in
  rhs(concl(TOP_DEPTH_CONV BETA_CONV t));;

let CDRIFT_SETUP_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[va1_w32s];;

let CDRIFT_ENTRY_TAC exec =
  ENSURES_INIT_TAC "s0" THEN MEMNAME_TAC THEN
  CAP_MSTEPS_TAC exec (1--3) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LT; injectivity "wval"];;

(* the six loads of beads 2i and 2i+1, in the address form the steps produce *)
let CDRIFT_LOADS_TAC =
  MAP_EVERY (fun (a,b,j,f) ->
    SUBGOAL_THEN (subst [a,`aa:num`; f,`ff:num->int32`; j,`jj:num`]
                    `read (bytes32 (word aa)) mm = (ff:num->int32) jj`) ASSUME_TAC THENL
     [SUBGOAL_THEN (subst [a,`aa:num`; b,`bb:num`; j,`jj:num`] `aa = bb + 4 * jj`) SUBST1_TAC THENL
       [ARITH_TAC; ASM_SIMP_TAC[LT_REFL; ARITH_RULE `~(2 * i + 1 < 2 * i)`]];
      ALL_TAC])
   [`8 * i + 1138688`,`1138688`,`2 * i`,`rb:num->int32`;
    `8 * i + 1138692`,`1138688`,`2 * i + 1`,`rb:num->int32`;
    `8 * i + 1163264`,`1163264`,`2 * i`,`zq:num->int32`;
    `8 * i + 1163268`,`1163264`,`2 * i + 1`,`zq:num->int32`;
    `8 * i + 1171456`,`1171456`,`2 * i`,`zp:num->int32`;
    `8 * i + 1171460`,`1171456`,`2 * i + 1`,`zp:num->int32`];;

(* one memory conjunct of the invariant at i + 1: split k = 2i, 2i + 1, other *)
let CDRIFT_ARITH = ARITH_RULE
  `~(2 * i + 1 < 2 * i) /\ 2 * i < 2 * (i + 1) /\ 2 * i + 1 < 2 * (i + 1)`;;

let CDRIFT_MEMGOAL_TAC =
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MAP_EVERY (fun c -> ASM_CASES_TAC (subst [c,`cc:num`] `k:num = cc`) THENL
    [FIRST_X_ASSUM SUBST_ALL_TAC THEN REPEAT B32_PEEL_TAC THEN
     ASM_SIMP_TAC[LT_REFL; CDRIFT_ARITH; va1_cdrift; WORD_ADD_0; WORD_SUB_0];
     ALL_TAC]) [`2 * i`; `2 * i + 1`] THEN
  REPEAT B32_PEEL_TAC THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `(k < 2 * (i + 1) <=> k < 2 * i)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[]];;

(* the invariant at i + 1 from the final memory (a write chain over mm) *)
let CDRIFT_POST_TAC =
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN CDRIFT_MEMGOAL_TAC;;

let CDRIFT_BODY_TAC exec =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `2 * i < 2048 /\ 2 * i + 1 < 2048` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_add (word (8 * i)) (word 8):int32 = word (8 * (i + 1))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun c -> VAL_TAC (subst [c,`cc:num`]
      `val(word_add (word (8 * i)) (word cc):int32) = 8 * i + cc`))
    [`1138688`; `1163264`; `1171456`; `1138692`; `1163268`; `1171460`] THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  CDRIFT_LOADS_TAC THEN
  MAP_EVERY (fun a -> B32O_TAC a `8 * i + 1163264`)
    [`8 * i + 1138692`; `8 * i + 1163268`; `8 * i + 1171460`] THEN
  ASM_CASES_TAC `ival ((rb:num->int32) (2 * i)) > &52371633` THENL
   [ASM_CASES_TAC `ival ((rb:num->int32) (2 * i + 1)) > &52371633` THENL
     [CAP_MSTEPS_TAC exec (1--22); CAP_MSTEPS_TAC exec (1--40)];
    ASM_CASES_TAC `ival ((rb:num->int32) (2 * i + 1)) > &52371633` THENL
     [CAP_MSTEPS_TAC exec (1--40); CAP_MSTEPS_TAC exec (1--58)]] THEN
  CDRIFT_POST_TAC;;

let CDRIFT_BACK_TAC exec =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(word (8 * i):int32 = word 8192) <=> F` ASSUME_TAC THENL
   [REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN
    SUBGOAL_THEN `val(word (8 * i):int32) = 8 * i` SUBST1_TAC THENL
     [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC;
      REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  CAP_MSTEPS_TAC exec (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[];;

let CDRIFT_EXIT_TAC exec =
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  CAP_MSTEPS_TAC exec (1--3) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[];;

let CDRIFT_TAC mc exec op =
  CDRIFT_SETUP_TAC THEN
  ENSURES_WHILE_UP_TAC `1024` `9` `139` (cdrift_inv mc op) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; CDRIFT_ENTRY_TAC exec; CDRIFT_BODY_TAC exec; CDRIFT_BACK_TAC exec;
    CDRIFT_EXIT_TAC exec];;

let VA1_F19_EXEC = FAST_MK_EXEC_RULE va1_f19_mc 3;;
let VA1_F20_EXEC = FAST_MK_EXEC_RULE va1_f20_mc 3;;

let VA1_CDRIFT_FWD = prove
 (lhand(rhs(concl va1_cdrift_ok)),
  CDRIFT_TAC `va1_f19_mc` VA1_F19_EXEC `word_add:int32->int32->int32`);;

let VA1_CDRIFT_BWD = prove
 (rand(rhs(concl va1_cdrift_ok)),
  CDRIFT_TAC `va1_f20_mc` VA1_F20_EXEC `word_sub:int32->int32->int32`);;

let VA1_CDRIFT_OK = prove
 (parse_term pop_spec_VA1_CDRIFT_OK,
  PURE_REWRITE_TAC[va1_cdrift_ok] THEN CONJ_TAC THENL
   [ACCEPT_TAC VA1_CDRIFT_FWD; ACCEPT_TAC VA1_CDRIFT_BWD]);;
