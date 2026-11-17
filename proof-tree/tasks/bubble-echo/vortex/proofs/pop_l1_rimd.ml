needs "ve_vort.ml";;
needs "ve_tick.ml";;
needs "ve_vk.ml";;
needs "va1_code.ml";;
needs "va1_seq_final2.ml";;
needs "pop_design_defs.ml";;
needs "pop_design_stmts.ml";;
(* ========================================================================= *)
(* Vortex pop, segment L1 (SEG-L1 prover, Claude Opus 5.5, 2026-11-11): the *)
(* rim pair f15 (ve_rim_apply) / f16 (ve_rim_unapply) of vortex_a1.wasm on   *)
(* the exact bytes. Lemma file 1 of 2 (LEAFCHAIN layer): helper lemmas and   *)
(* loop 1 of both exports (pc 7 .. 155: RD[k] = va1_rimd tbl SRC k for every *)
(* bead k < 2048, SRC = RB for f15, RA for f16). Loop 2 (the Fredkin step)   *)
(* and VA1_RIM_OK / VA1_RIM_INVERSE are in pop_l1_rim.ml.                    *)
(* ========================================================================= *)

(* ========================================================================= *)
(* Vortex pop, segment L1 (rim pair f15/f16): helper lemmas and tactics.     *)
(* SEG-L1 prover (Claude Opus 5.5), 2026-11-11. Dev part, loaded by           *)
(* pop_l1_rimd.ml (the layered lemma file).                                   *)
(* ========================================================================= *)

(* the table column inside the in-range branch: (max r 0) >> 19 <= 99         *)
let RIM_J = prove
 (`!r:int32. val r <= 52371633 ==>
     word_and (word_ushr r 17) (word 16380) =
       word (4 * (val (word_and (word_ushr r 17) (word 16380):int32) DIV 4)) /\
     val (word_and (word_ushr r 17) (word 16380):int32) DIV 4 <= 99`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val (r:int32) DIV 524288 <= 99` ASSUME_TAC THENL
   [MP_TAC(SPECL [`val (r:int32)`; `52371633`; `524288`] DIV_MONO) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `word_and (word_ushr r 17) (word 16380):int32 = word (4 * (val (r:int32) DIV 524288))`
    SUBST1_TAC THENL
   [SUBGOAL_THEN `word_and (word_ushr r 17) (word 16380):int32 =
                  word_shl (word_and (word_ushr r 19) (word 4095)) 2` SUBST1_TAC THENL
     [BITBLAST_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `word_and (word_ushr r 19) (word 4095):int32 = word (val (r:int32) DIV 524288)`
      SUBST1_TAC THENL
     [REWRITE_TAC[GSYM VAL_EQ] THEN
      MP_TAC(ISPECL [`word_ushr r 19:int32`; `12`] VAL_WORD_AND_MASK_WORD) THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[VAL_WORD_USHR; VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
      SUBGOAL_THEN `val (r:int32) DIV 524288 < 4096 /\ val (r:int32) DIV 524288 < 4294967296`
        STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[MOD_LT]];
      REWRITE_TAC[CAP_SHL2]];
    ALL_TAC] THEN
  SUBGOAL_THEN `val (word (4 * (val (r:int32) DIV 524288)):int32) = 4 * (val (r:int32) DIV 524288)`
    SUBST1_TAC THENL [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ; ARITH_RULE `4 * x = x * 4`] THEN ASM_REWRITE_TAC[]);;

(* the clamped radius max(r,0) of an in-range bead is a small value          *)
let RIM_RR = prove
 (`!x:int32. ~(ival x > &52371633) ==> val (if ival x > &0 then x else word 0) <= 52371633`,
  GEN_TAC THEN DISCH_TAC THEN COND_CASES_TAC THENL [ALL_TAC; REWRITE_TAC[VAL_WORD_0; LE_0]] THEN
  MP_TAC(ISPEC `x:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[IVAL_VAL; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_CASES_TAC `bit 31 (x:int32)` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_LE] THEN
  CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN INT_ARITH_TAC);;

(* bytes64 as the join of its two bytes32 halves (little endian)             *)
let RIM_B64_JOIN = prove
 (`!a (m:int64->byte). read (bytes64 a) m =
      word_join (read (bytes32 (word_add a (word 4))) m) (read (bytes32 a) m)`,
  REWRITE_TAC[GSYM VAL_EQ] THEN
  SIMP_TAC[VAL_WORD_JOIN_SIMPLE; DIMINDEX_64; DIMINDEX_32; ARITH] THEN
  REWRITE_TAC[bytes64; bytes32; asword; through; read; READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64; DIMINDEX_32] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 32 = 2 EXP (8 * 4) /\ 2 EXP 64 = 2 EXP (8 * 8)`] THEN
  SIMP_TAC[READ_BYTES_BOUND; MOD_LT] THEN
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ARITH_RULE `8 = 4 + 4`] THEN
  REWRITE_TAC[READ_BYTES_COMBINE] THEN ARITH_TAC);;

let RIM_JOIN_LO = prove
 (`!h l:int32. word_zx (word_join h l:int64):int32 = l`, BITBLAST_TAC);;
let RIM_JOIN_HI = prove
 (`!h l:int32. word_zx (word_ushr (word_join h l:int64) 32):int32 = h`, BITBLAST_TAC);;

let RIM_R32_W64_SAME = prove
 (`!a (h:int32) (l:int32) (m:int64->byte).
     read (bytes32 a) (write (bytes64 a) (word_join h l) m) = l /\
     read (bytes32 (word_add a (word 4))) (write (bytes64 a) (word_join h l) m) = h`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `word_join (h:int32) (l:int32):int64`; `m:int64->byte`] VK_B64_SAME) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [RIM_B64_JOIN] THEN
  DISCH_THEN(fun th -> MP_TAC(AP_TERM `word_zx:int64->int32` th) THEN
                       MP_TAC(AP_TERM `\x:int64. word_zx (word_ushr x 32):int32` th)) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[RIM_JOIN_LO; RIM_JOIN_HI] THEN
  SIMP_TAC[]);;

let RIM_R32_W64_LO_EQ = prove
 (`!x a (h:int32) (l:int32) (m:int64->byte).
     x = a ==> read (bytes32 (word x)) (write (bytes64 (word a)) (word_join h l) m) = l`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[RIM_R32_W64_SAME]);;

let RIM_R32_W64_HI_EQ = prove
 (`!x a (h:int32) (l:int32) (m:int64->byte).
     x = a + 4 ==> read (bytes32 (word x)) (write (bytes64 (word a)) (word_join h l) m) = h`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[WORD_ADD; RIM_R32_W64_SAME]);;

(* peel one write off a bytes32 read in the goal: the same cell (bytes32, or *)
(* either half of a bytes64 write of a word_join) or a disjoint one          *)
let RIM_PEEL_TAC : tactic =
  let p32 = `read (bytes32 (word (x:num))) (write (bytes32 (word (a:num))) (v:int32) (m:int64->byte))`
  and p64 = `read (bytes32 (word (x:num))) (write (bytes64 (word (a:num))) (v:int64) (m:int64->byte))`
  and pj = `read (bytes32 (word (x:num))) (write (bytes64 (word (a:num))) (word_join (h:int32) (l:int32):int64) (m:int64->byte))` in
  fun (asl,w) ->
    let try32 () =
      let t = find_term (can (term_match [] p32)) w in
      let i = term_match [] p32 t in
      let x = instantiate i `x:num` and a = instantiate i `a:num`
      and v = instantiate i `v:int32` and m = instantiate i `m:int64->byte` in
      (SUBGOAL_THEN (mk_eq(x,a)) ASSUME_TAC THENL
        [VK_ARITH_TAC; FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP CAP_B32_SAME_EQ th])]) ORELSE
      (MP_TAC(SPECL [x; a; v; m] VK_R32_W32) THEN ANTS_TAC THENL
        [VK_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])]) in
    let try64 () =
      let t = find_term (can (term_match [] p64)) w in
      let i = term_match [] p64 t in
      let x = instantiate i `x:num` and a = instantiate i `a:num`
      and v = instantiate i `v:int64` and m = instantiate i `m:int64->byte` in
      let samel = try let j = term_match [] pj t in
                      let h = instantiate j `h:int32` and l = instantiate j `l:int32` in
                      (MP_TAC(SPECL [x; a; h; l; m] RIM_R32_W64_LO_EQ) THEN ANTS_TAC THENL
                        [VK_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])]) ORELSE
                      (MP_TAC(SPECL [x; a; h; l; m] RIM_R32_W64_HI_EQ) THEN ANTS_TAC THENL
                        [VK_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])])
                  with Failure _ -> NO_TAC in
      samel ORELSE
      (MP_TAC(SPECL [x; a; v; m] VK_R32_W64) THEN ANTS_TAC THENL
        [VK_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])]) in
    ((fun g -> try try32 () g with Failure _ -> NO_TAC g) ORELSE
     (fun g -> try try64 () g with Failure _ -> NO_TAC g)) (asl,w);;

(* the frame of both rim contracts *)
let RIMF = `MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
            MAYCHANGE [wstatus] ,, MAYCHANGE [wlocal 0; wlocal 1; wlocal 2; wlocal 3; wlocal 4; wlocal 5] ,,
            MAYCHANGE [wmem :> bytes(word 1130496,16384)] ,,
            MAYCHANGE [wmem :> bytes(word 1966080,73728)]`;;

(* assume word_add (word a) (word b) = word c, proved by arithmetic *)
let RIM_WADD_TAC t =
  SUBGOAL_THEN t ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN VK_ARITH_TAC; ALL_TAC];;

let rim_num n = mk_numeral (Num.num_of_int n);;

(* timing *)
let rim_time name f x =
  let t0 = Sys.time () in
  let r = f x in
  Printf.printf "@@TIME %s %.1fs\n%!" name (Sys.time () -. t0); r;;

(* ========================================================================= *)
(* Vortex pop L1: loop 1 of the rim pair (pc 7 .. 155), the displacement    *)
(* RD[k] = va1_rimd tbl SRC k (scratch 1998848 + 4k), k < 2048. f15 and f16 *)
(* differ here only in the source base SB at pc 27 (RB = 1138688 for f15,   *)
(* RA = 1130496 for f16).                                                    *)
(* ========================================================================= *)

let rim_seg1_stmt mc sb srcv =
  list_mk_forall([`tbl:num->int32`; `ra:num->int32`; `rb:num->int32`],
  subst [mc,`MC:byte list`; sb,`SB:num`; srcv,`SRC:num->int32`; RIMF,`RF:wasmstate->wasmstate->bool`]
 `ensures wasm
    (\s. read wcode s = MC /\ read wpc s = word 7 /\ read wstatus s = WRunning /\
         read wstack s = [] /\ read wlabels s = [] /\ read warity s = 0 /\
         read wmemsize s = 4194304 /\
         (!k. k < 262144 ==> read (wmem :> bytes32 (word (65536 + 4 * k))) s = (tbl:num->int32) k) /\
         (!k. k < 2048 ==> read (wmem :> bytes32 (word (1130496 + 4 * k))) s = ra k) /\
         (!k. k < 2048 ==> read (wmem :> bytes32 (word (1138688 + 4 * k))) s = rb k))
    (\s. read wcode s = MC /\ read wpc s = word 155 /\ read wstatus s = WRunning /\
         read wstack s = [] /\ read wlabels s = [] /\ read warity s = 0 /\
         read wmemsize s = 4194304 /\
         (!k. k < 262144 ==> read (wmem :> bytes32 (word (65536 + 4 * k))) s = tbl k) /\
         (!k. k < 2048 ==> read (wmem :> bytes32 (word (1130496 + 4 * k))) s = ra k) /\
         (!k. k < 2048 ==> read (wmem :> bytes32 (word (1138688 + 4 * k))) s = rb k) /\
         (!k. k < 2048 ==> read (wmem :> bytes32 (word (1998848 + 4 * k))) s = va1_rimd tbl SRC k))
    RF`);;

let rim_l1_inv mc srcv =
  let t = subst [mc,`MC:byte list`; srcv,`SRC:num->int32`]
   `\i s. read wcode s = MC /\ read wstatus s = WRunning /\
          read wmemsize s = 4194304 /\ read warity s = 0 /\
          read wlabels s = [0,17,0] /\
          read (wlocal 0) s = I32 (word (65536 + 512 * i)) /\
          read (wlocal 1) s = I32 (word (4 * i)) /\
          read wstack s = (if read wpc s = word 19 then []
                           else [I32 (word (bitval (~(word (4 * i) = word 8192:int32))))]) /\
          (!k. k < 262144 ==> read (wmem :> bytes32 (word (65536 + 4 * k))) s = (tbl:num->int32) k) /\
          (!k. k < 2048 ==> read (wmem :> bytes32 (word (1130496 + 4 * k))) s = (ra:num->int32) k) /\
          (!k. k < 2048 ==> read (wmem :> bytes32 (word (1138688 + 4 * k))) s = (rb:num->int32) k) /\
          (!k. k < i ==> read (wmem :> bytes32 (word (1998848 + 4 * k))) s = va1_rimd tbl SRC k)` in
  rhs(concl(TOP_DEPTH_CONV BETA_CONV t));;

(* final-state memory goals: every quantified fact over the one RD store     *)
let RIM_L1_MEMGOALS_TAC (close:tactic) =
  REPEAT CONJ_TAC THEN
  TRY(X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      ((REPEAT RIM_PEEL_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN VK_ARITH_TAC) ORELSE
       (ASM_CASES_TAC `k:num = i` THENL
         [FIRST_X_ASSUM SUBST_ALL_TAC THEN REPEAT RIM_PEEL_TAC THEN close;
          REPEAT RIM_PEEL_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN VK_ARITH_TAC])));;

let RIM_L1_BODY_TAC exec sb srcv =
  let ins t = subst [sb,`SB:num`; srcv,`SRC:num->int32`] t in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MAP_EVERY RIM_WADD_TAC
   [ins `word_add (word (4 * i)) (word SB):int32 = word (SB + 4 * i)`;
    `word_add (word (4 * i)) (word 1998848):int32 = word (1998848 + 4 * i)`;
    `word_add (word (65536 + 512 * i)) (word 512):int32 = word (65536 + 512 * (i + 1))`;
    `word_add (word (4 * i)) (word 4):int32 = word (4 * (i + 1))`] THEN
  MAP_EVERY VK_VAL_TAC [ins `SB + 4 * i`; `1998848 + 4 * i`] THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  VK_LOADFACT_TAC (ins `read (bytes32 (word (SB + 4 * i))) mm = SRC i`) THEN
  ASM_CASES_TAC (ins `ival ((SRC:num->int32) i) > &52371633`) THENL
   [(* skip: RD[i] = 0 *)
    CAP_MSTEPS_TAC exec (1--26) THEN
    ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
    RIM_L1_MEMGOALS_TAC (REWRITE_TAC[va1_rimd] THEN ASM_REWRITE_TAC[]);
    (* in range: interpolate in row i of TBL *)
    ABBREV_TAC (ins `rr = if ival ((SRC:num->int32) i) > &0 then SRC i else word 0:int32`) THEN
    SUBGOAL_THEN `val (rr:int32) <= 52371633` ASSUME_TAC THENL
     [EXPAND_TAC "rr" THEN MATCH_MP_TAC RIM_RR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN (ins `(if ~(ival ((SRC:num->int32) i) > &0) then word 0 else SRC i) = rr:int32`)
      ASSUME_TAC THENL [EXPAND_TAC "rr" THEN REWRITE_TAC[COND_SWAP]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP RIM_J) THEN
    ABBREV_TAC `JJ = val (word_and (word_ushr rr 17) (word 16380):int32) DIV 4` THEN STRIP_TAC THEN
    RIM_WADD_TAC `word_add (word (65536 + 512 * i)) (word (4 * JJ)):int32 = word (65536 + 4 * (128 * i + JJ))` THEN
    RIM_WADD_TAC `word_add (word (65536 + 4 * (128 * i + JJ))) (word 4):int32 = word (65536 + 4 * (128 * i + JJ + 1))` THEN
    MAP_EVERY VK_VAL_TAC [`65536 + 4 * (128 * i + JJ)`; `65536 + 4 * (128 * i + JJ + 1)`] THEN
    VK_LOADFACT_TAC `read (bytes32 (word (65536 + 4 * (128 * i + JJ)))) mm = tbl (128 * i + JJ)` THEN
    VK_LOADFACT_TAC `read (bytes32 (word (65536 + 4 * (128 * i + JJ + 1)))) mm = tbl (128 * i + JJ + 1)` THEN
    MP_TAC VK_COND_I64 THEN MP_TAC VK_COND_I32 THEN REPEAT DISCH_TAC THEN
    CAP_MSTEPS_TAC exec (1--67) THEN
    ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
    RIM_L1_MEMGOALS_TAC
     (REWRITE_TAC[va1_rimd; ASSUME (ins `~(ival ((SRC:num->int32) i) > &52371633)`)] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[ASSUME (ins `(if ival ((SRC:num->int32) i) > &0 then SRC i else word 0:int32) = rr`)] THEN
      REWRITE_TAC[ASSUME `val (word_and (word_ushr rr 17) (word 16380):int32) DIV 4 = JJ`] THEN
      CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[COND_SWAP])];;

let RIM_SEG1_TAC mc exec sb srcv =
  REPEAT GEN_TAC THEN
  ENSURES_WHILE_UP_TAC `2048` `19` `152` (rim_l1_inv mc srcv) THEN REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    ENSURES_INIT_TAC "s0" THEN MEMNAME_TAC THEN CAP_MSTEPS_TAC exec (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LT];
    RIM_L1_BODY_TAC exec sb srcv;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`4 * i`; `8192`] VK_WORD_NE) THEN ANTS_TAC THENL [VK_ARITH_TAC; DISCH_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
    CAP_MSTEPS_TAC exec (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
    CAP_MSTEPS_TAC exec (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[]];;

let POP_L1_F15_EXEC = FAST_MK_EXEC_RULE va1_f15_mc 7;;
let POP_L1_F16_EXEC = FAST_MK_EXEC_RULE va1_f16_mc 7;;

let POP_L1_SEG1_F15 = rim_time "seg1 f15" (fun () -> prove
 (rim_seg1_stmt `va1_f15_mc` `1138688` `rb:num->int32`,
  RIM_SEG1_TAC `va1_f15_mc` POP_L1_F15_EXEC `1138688` `rb:num->int32`)) ();;

let POP_L1_SEG1_F16 = rim_time "seg1 f16" (fun () -> prove
 (rim_seg1_stmt `va1_f16_mc` `1130496` `ra:num->int32`,
  RIM_SEG1_TAC `va1_f16_mc` POP_L1_F16_EXEC `1130496` `ra:num->int32`)) ();;
