needs "ve_vort.ml";;
needs "ve_tick.ml";;
needs "ve_vk.ml";;
needs "va1_code.ml";;
needs "va1_seq_final2.ml";;
needs "pop_design_defs.ml";;
needs "pop_design_stmts.ml";;
needs "pop_l1_rimd.ml";;
(* ========================================================================= *)
(* Vortex pop, segment L1 (SEG-L1 prover, Claude Opus 5.5, 2026-11-11):      *)
(* lemma file 2 of 2 (LEAFCHAIN layer): loop 2 of f15/f16 (the 2-way        *)
(* Fredkin step with an i64 copy) and the composition into the frozen        *)
(* contract va1_rim_ok; VA1_RIM_OK and VA1_RIM_INVERSE bound with the frozen *)
(* statements (pop_design_stmts.ml); the spec-locked final leaf re-binds.    *)
(* ========================================================================= *)

(* ========================================================================= *)
(* Vortex pop L1: loop 2 of the rim pair (pc 155 .. end), the 2-way         *)
(* Fredkin step with an i64 copy. A at PA, B at PB (2048 words each):        *)
(* per iteration i < 1024 (beads 2i, 2i+1): A pair := B pair (one i64 load   *)
(* and store), B[k] := OP (old A[k]) RD[k]. f15: PA = RA 1130496,            *)
(* PB = RB 1138688, OP = word_add; f16: PA = RB, PB = RA, OP = word_sub.     *)
(* ========================================================================= *)

let rim_seg2_stmt mc pa pb opv =
  subst [mc,`MC:byte list`; pa,`PA:num`; pb,`PB:num`; opv,`OP:int32->int32->int32`;
         RIMF,`RF:wasmstate->wasmstate->bool`]
 `!(ai:num->int32) (bi:num->int32) (rd:num->int32).
   ensures wasm
    (\s. read wcode s = MC /\ read wpc s = word 155 /\ read wstatus s = WRunning /\
         read wstack s = [] /\ read wlabels s = [] /\ read warity s = 0 /\
         read wmemsize s = 4194304 /\
         (!m. m < 2048 ==> read (wmem :> bytes32 (word (PA + 4 * m))) s = ai m) /\
         (!m. m < 2048 ==> read (wmem :> bytes32 (word (PB + 4 * m))) s = bi m) /\
         (!m. m < 2048 ==> read (wmem :> bytes32 (word (1998848 + 4 * m))) s = rd m))
    (\s. read wstatus s = WDone /\ read wstack s = [] /\
         (!m. m < 2048 ==> read (wmem :> bytes32 (word (PA + 4 * m))) s = bi m) /\
         (!m. m < 2048 ==> read (wmem :> bytes32 (word (PB + 4 * m))) s = OP (ai m) (rd m)))
    RF`;;

let rim_l2_inv mc pa pb opv =
  let t = subst [mc,`MC:byte list`; pa,`PA:num`; pb,`PB:num`; opv,`OP:int32->int32->int32`]
   `\i s. read wcode s = MC /\ read wstatus s = WRunning /\
          read wmemsize s = 4194304 /\ read warity s = 0 /\
          read wlabels s = [0,159,0] /\
          read (wlocal 1) s = I32 (word (8 * i)) /\
          read wstack s = (if read wpc s = word 161 then []
                           else [I32 (word (bitval (~(word (8 * i) = word 8192:int32))))]) /\
          (!m. m < 2048 ==> read (wmem :> bytes32 (word (PA + 4 * m))) s =
                            (if m < 2 * i then (bi:num->int32) m else (ai:num->int32) m)) /\
          (!m. m < 2048 ==> read (wmem :> bytes32 (word (PB + 4 * m))) s =
                            (if m < 2 * i then OP (ai m) ((rd:num->int32) m) else bi m)) /\
          (!m. m < 2048 ==> read (wmem :> bytes32 (word (1998848 + 4 * m))) s = rd m)` in
  rhs(concl(TOP_DEPTH_CONV BETA_CONV t));;

let RIM_L2_BODY_TAC exec pa pb =
  let pan = dest_numeral pa and pbn = dest_numeral pb in
  let n k = mk_numeral k in
  let pa4 = n (pan +/ Num.num_of_int 4) and pb4 = n (pbn +/ Num.num_of_int 4) in
  let sub l t = subst l t in
  let consts = [pa4; pa; pb; `1998848`; pb4; `1998852`] in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MAP_EVERY (fun c ->
     RIM_WADD_TAC (sub [c,`C:num`] `word_add (word (8 * i)) (word C):int32 = word (C + 8 * i)`) THEN
     VK_VAL_TAC (sub [c,`C:num`] `C + 8 * i`)) consts THEN
  RIM_WADD_TAC `word_add (word (8 * i)) (word 8):int32 = word (8 * (i + 1))` THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  (* loads in mm form *)
  MAP_EVERY (fun (c,b,f,j) ->
     SUBGOAL_THEN (sub [c,`C:num`; f,`FF:num->int32`; j,`J:num`] `read (bytes32 (word (C + 8 * i))) mm = (FF:num->int32) J`)
       ASSUME_TAC THENL
      [SUBST1_TAC(ARITH_RULE (sub [c,`C:num`; b,`BB:num`; j,`J:num`] `C + 8 * i = BB + 4 * J`)) THEN
       SUBGOAL_THEN (sub [j,`J:num`] `J < 2048 /\ ~(J < 2 * i)`) STRIP_ASSUME_TAC THENL
        [VK_ARITH_TAC; ASM_SIMP_TAC[]];
       ALL_TAC])
   [pa4,pa,`ai:num->int32`,`2 * i + 1`; pa,pa,`ai:num->int32`,`2 * i`;
    pb4,pb,`bi:num->int32`,`2 * i + 1`; pb,pb,`bi:num->int32`,`2 * i`] THEN
  SUBGOAL_THEN `read (bytes32 (word (1998848 + 8 * i))) mm = rd (2 * i) /\
                read (bytes32 (word (1998852 + 8 * i))) mm = rd (2 * i + 1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBST1_TAC(ARITH_RULE `1998848 + 8 * i = 1998848 + 4 * (2 * i)`);
      SUBST1_TAC(ARITH_RULE `1998852 + 8 * i = 1998848 + 4 * (2 * i + 1)`)] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN VK_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (sub [pb,`PB:num`; pb4,`PB4:num`]
     `read (bytes64 (word (PB + 8 * i))) mm = word_join ((bi:num->int32) (2 * i + 1)) (bi (2 * i))`)
    ASSUME_TAC THENL
   [REWRITE_TAC[RIM_B64_JOIN; GSYM WORD_ADD] THEN
    SUBST1_TAC(ARITH_RULE (sub [pb,`PB:num`; pb4,`PB4:num`] `(PB + 8 * i) + 4 = PB4 + 8 * i`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  VK_RW64_TAC 32 `1998848 + 8 * i` (sub [pa,`PA:num`] `PA + 8 * i`) THEN
  VK_RW64_TAC 32 `1998852 + 8 * i` (sub [pa,`PA:num`] `PA + 8 * i`) THEN
  B32O_TAC `1998852 + 8 * i` (sub [pb,`PB:num`] `PB + 8 * i`) THEN
  VK_MSTEPS_TAC exec (1--42) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      MAP_EVERY (fun c -> ASM_CASES_TAC (sub [c,`cc:num`] `m:num = cc`) THENL
        [FIRST_X_ASSUM SUBST_ALL_TAC THEN REPEAT RIM_PEEL_TAC THEN ASM_SIMP_TAC[] THEN
         REWRITE_TAC[ARITH_RULE `2 * i < 2 * (i + 1) /\ 2 * i + 1 < 2 * (i + 1)`; LT_REFL;
                     ARITH_RULE `~(2 * i + 1 < 2 * i)`];
         ALL_TAC]) [`2 * i`; `2 * i + 1`] THEN
      REPEAT RIM_PEEL_TAC THEN ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN `(m < 2 * (i + 1) <=> m < 2 * i)` SUBST1_TAC THENL
       [VK_ARITH_TAC; REWRITE_TAC[]]);;

let RIM_SEG2_TAC mc exec pa pb opv =
  REPEAT GEN_TAC THEN
  ENSURES_WHILE_UP_TAC `1024` `161` `263` (rim_l2_inv mc pa pb opv) THEN REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    ENSURES_INIT_TAC "s0" THEN MEMNAME_TAC THEN CAP_MSTEPS_TAC exec (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LT] THEN
    REPEAT CONJ_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[];
    RIM_L2_BODY_TAC exec pa pb;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`8 * i`; `8192`] VK_WORD_NE) THEN ANTS_TAC THENL [VK_ARITH_TAC; DISCH_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
    CAP_MSTEPS_TAC exec (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV)) THEN
    CAP_MSTEPS_TAC exec (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[]];;

(* ========================================================================= *)
(* Vortex pop L1: compose loop 1 and loop 2 into the frozen contract         *)
(* va1_rim_ok (both exports f15/f16).                                        *)
(* ========================================================================= *)

let RIM_EXPORT_TAC seg1 seg2 post_tac =
  REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[va1_w32s] THEN
  W(fun (asl,w) ->
    let th1 = SPECL [`tbl:num->int32`; `ra:num->int32`; `rb:num->int32`] seg1 in
    let q1 = rand(rator(concl th1)) in
    let s,body = dest_abs q1 in
    let _,rest = dest_conj body in
    let _,rest = dest_conj rest in
    ENSURES_SEQUENCE_TAC `155` (mk_abs(s,rest)) THEN CONJ_TAC THENL
     [MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
      EXISTS_TAC (rand(rator(rator(concl th1)))) THEN CONJ_TAC THENL
       [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
        REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC q1 THEN CONJ_TAC THENL
         [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[];
          ACCEPT_TAC th1]];
      MP_TAC seg2 THEN post_tac]);;

(* seg2 instance: A/B/RD from the mid state, then weaken *)
let RIM_USE_SEG2_TAC ai bi =
  DISCH_THEN(MP_TAC o SPECL [ai; bi; mk_comb(`va1_rimd tbl`, bi)]) THEN
  DISCH_THEN(fun th ->
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    EXISTS_TAC (rand(rator(rator(concl th)))) THEN CONJ_TAC THENL
     [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC (rand(rator(concl th))) THEN
      CONJ_TAC THENL
       [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
        REWRITE_TAC[READ_COMPONENT_COMPOSE; ve_fredkin_fwd; ve_fredkin_bwd; FST; SND] THEN
        CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
        ACCEPT_TAC th]]);;

let POP_L1_SEG2_F15 = rim_time "seg2 f15" (fun () -> prove
 (rim_seg2_stmt `va1_f15_mc` `1130496` `1138688` `word_add:int32->int32->int32`,
  RIM_SEG2_TAC `va1_f15_mc` POP_L1_F15_EXEC `1130496` `1138688` `word_add:int32->int32->int32`)) ();;

let POP_L1_SEG2_F16 = rim_time "seg2 f16" (fun () -> prove
 (rim_seg2_stmt `va1_f16_mc` `1138688` `1130496` `word_sub:int32->int32->int32`,
  RIM_SEG2_TAC `va1_f16_mc` POP_L1_F16_EXEC `1138688` `1130496` `word_sub:int32->int32->int32`)) ();;

let POP_L1_RIM_OK = prove
 (`va1_rim_ok`,
  REWRITE_TAC[va1_rim_ok] THEN CONJ_TAC THENL
   [RIM_EXPORT_TAC POP_L1_SEG1_F15 POP_L1_SEG2_F15 (RIM_USE_SEG2_TAC `ra:num->int32` `rb:num->int32`);
    RIM_EXPORT_TAC POP_L1_SEG1_F16 POP_L1_SEG2_F16 (RIM_USE_SEG2_TAC `rb:num->int32` `ra:num->int32`)]);;

let VA1_RIM_OK = prove(parse_term pop_spec_VA1_RIM_OK, ACCEPT_TAC POP_L1_RIM_OK);;
let VA1_RIM_INVERSE = prove(parse_term pop_spec_VA1_RIM_INVERSE, REWRITE_TAC[FREDKIN_STEP_INVERSE]);;
