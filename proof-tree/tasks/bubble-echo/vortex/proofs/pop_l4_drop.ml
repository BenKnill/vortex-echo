needs "ve_vort.ml";;
needs "ve_tick.ml";;
needs "ve_vk.ml";;
needs "va1_code.ml";;
needs "va1_seq_final2.ml";;
needs "pop_design_defs.ml";;
needs "pop_design_stmts.ml";;
(* ========================================================================= *)
(* Vortex pop, segment L4 (SEG-L4 prover, Claude Opus 5.5, 2026-11-11): the  *)
(* droplet pair f11 / f12 of vortex_a1.wasm (ve_drop_apply/ve_drop_unapply)  *)
(* on the exact bytes, and VA1_DROP_INVERSE. Lemma file (a LEAFCHAIN layer); *)
(* the spec-locked final leaf only re-binds VA1_DROP_OK / VA1_DROP_INVERSE.  *)
(*                                                                           *)
(* f11/f12 (142 B, entry pc 3, locals l0..l3): 3 block; 5..12 l0 := ND (word *)
(*   16400); 14..15 exit if ND = 0 (br_if to pc 141); 17..31 l1 :=           *)
(*   select(ND, 16384, ND <u 16384) = word (MIN (val ND) 16384); 33..38 l0 :=*)
(*   DI (1179648); 40 loop; 42..135 one 48-byte record (6 loads, 4 stores,   *)
(*   48 steps); 137 br_if (l1 - 1 <> 0); 139 140 141 end.                    *)
(* Loop invariant at count i: l0 = DI + 48 i, l1 = N - i, words below 12 i   *)
(* are FD nd di, the rest are di (FD = va1_drop_fwd / va1_drop_bwd). One     *)
(* record step is the pure lemma L4_F11_MEM / L4_F12_MEM (proved once).      *)
(* ========================================================================= *)

let L4_F11_EXEC = FAST_MK_EXEC_RULE va1_f11_mc 3;;
let L4_F12_EXEC = FAST_MK_EXEC_RULE va1_f12_mc 3;;

let L4_REC3 = prove
 (`!w n. w MOD 12 < 3 /\ w < 12 * n ==> (w + 3) MOD 12 = w MOD 12 + 3 /\ w + 3 < 12 * n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`w:num`; `12`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
  ABBREV_TAC `q = w DIV 12` THEN ABBREV_TAC `r = w MOD 12` THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `q:num` THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `q < n` MP_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC]]);;

let VA1_DROP_INVERSE = prove
 (parse_term pop_spec_VA1_DROP_INVERSE,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:num` THEN
  REWRITE_TAC[va1_drop_bwd; va1_drop_fwd] THEN
  ABBREV_TAC `n = MIN (val (nd:int32)) 16384` THEN
  ASM_CASES_TAC `w < 12 * n` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `w MOD 12 < 3` THENL
   [MP_TAC(SPECL [`w:num`; `n:num`] L4_REC3) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `w MOD 12 = 0 \/ w MOD 12 = 1 \/ w MOD 12 = 2`
      (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THENL
     [ASM_ARITH_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_RULE;
    SUBGOAL_THEN `~(w MOD 12 = 0) /\ ~(w MOD 12 = 1) /\ ~(w MOD 12 = 2)` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE]);;

(* the loop count *)
let L4_MIN_WORD = prove
 (`!nd:int32. word (MIN (val nd) 16384) = (if val nd < 16384 then nd else word 16384)`,
  GEN_TAC THEN REWRITE_TAC[MIN] THEN
  ASM_CASES_TAC `val (nd:int32) < 16384` THEN ASM_REWRITE_TAC[WORD_VAL] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[WORD_VAL] THEN ASM_ARITH_TAC;
    COND_CASES_TAC THEN REWRITE_TAC[WORD_VAL] THEN
    SUBGOAL_THEN `val(nd:int32) = 16384` (fun th -> REWRITE_TAC[GSYM th; WORD_VAL]) THEN
    ASM_ARITH_TAC]);;

let L4_FWD_FULL = prove
 (`!nd di. (\k. if k < 12 * MIN (val nd) 16384 then va1_drop_fwd nd di k else di k) = va1_drop_fwd nd di`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN BETA_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN REWRITE_TAC[va1_drop_fwd] THEN ASM_REWRITE_TAC[]);;

let L4_BWD_FULL = prove
 (`!nd di. (\k. if k < 12 * MIN (val nd) 16384 then va1_drop_bwd nd di k else di k) = va1_drop_bwd nd di`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN BETA_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN REWRITE_TAC[va1_drop_bwd] THEN ASM_REWRITE_TAC[]);;

let L4_ADDM1 = prove
 (`!x:int32. word_add x (word 4294967295) = word_sub x (word 1)`,
  GEN_TAC THEN BITBLAST_TAC);;

let L4_MOD_REC = prove
 (`!i k. 12 * i <= k /\ k < 12 * i + 12 ==> k MOD 12 = k - 12 * i`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `i:num` THEN ASM_ARITH_TAC);;

(* the six loads of record i from an invariant memory *)
let L4_LOADS = prove
 (`!F m i. va1_w32s 1179648 196608 F m /\ i < 16384 ==>
     read (bytes32 (word (1179648 + 48 * i))) m = F (12 * i) /\
     read (bytes32 (word (1179648 + 48 * i + 4))) m = F (12 * i + 1) /\
     read (bytes32 (word (1179648 + 48 * i + 8))) m = F (12 * i + 2) /\
     read (bytes32 (word (1179648 + 48 * i + 12))) m = F (12 * i + 3) /\
     read (bytes32 (word (1179648 + 48 * i + 16))) m = F (12 * i + 4) /\
     read (bytes32 (word (1179648 + 48 * i + 20))) m = F (12 * i + 5)`,
  REWRITE_TAC[va1_w32s] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN
  (FIRST_X_ASSUM(fun th -> W(fun (_,w) -> MP_TAC(SPEC (rand(rand w)) th))) THEN
   ANTS_TAC THENL
    [ASM_ARITH_TAC;
     DISCH_THEN(SUBST1_TAC o SYM) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC]));;

let L4_LOADS_INV = prove
 (`!(FD:int32->(num->int32)->num->int32) nd di m i.
     va1_w32s 1179648 196608 (\k. if k < 12 * i then FD nd di k else di k) m /\ i < 16384 ==>
     read (bytes32 (word (1179648 + 48 * i))) m = di (12 * i) /\
     read (bytes32 (word (1179648 + 48 * i + 4))) m = di (12 * i + 1) /\
     read (bytes32 (word (1179648 + 48 * i + 8))) m = di (12 * i + 2) /\
     read (bytes32 (word (1179648 + 48 * i + 12))) m = di (12 * i + 3) /\
     read (bytes32 (word (1179648 + 48 * i + 16))) m = di (12 * i + 4) /\
     read (bytes32 (word (1179648 + 48 * i + 20))) m = di (12 * i + 5)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP L4_LOADS) THEN
  REWRITE_TAC[ARITH_RULE `~(12 * i < 12 * i) /\ ~(12 * i + 1 < 12 * i) /\ ~(12 * i + 2 < 12 * i) /\
                          ~(12 * i + 3 < 12 * i) /\ ~(12 * i + 4 < 12 * i) /\ ~(12 * i + 5 < 12 * i)`]);;

(* every (read cell, written cell) pair of one record, distinct cells *)
let L4_B32O = prove
 (`!i. i < 16384 ==>
     (!(v:int32) (m:int64->byte). read (bytes32 (word (1179648 + 48 * i + 4))) (write (bytes32 (word (1179648 + 48 * i))) v m) = read (bytes32 (word (1179648 + 48 * i + 4))) m) /\
     (!(v:int32) (m:int64->byte). read (bytes32 (word (1179648 + 48 * i + 8))) (write (bytes32 (word (1179648 + 48 * i))) v m) = read (bytes32 (word (1179648 + 48 * i + 8))) m) /\
     (!(v:int32) (m:int64->byte). read (bytes32 (word (1179648 + 48 * i + 12))) (write (bytes32 (word (1179648 + 48 * i))) v m) = read (bytes32 (word (1179648 + 48 * i + 12))) m) /\
     (!(v:int32) (m:int64->byte). read (bytes32 (word (1179648 + 48 * i + 16))) (write (bytes32 (word (1179648 + 48 * i))) v m) = read (bytes32 (word (1179648 + 48 * i + 16))) m) /\
     (!(v:int32) (m:int64->byte). read (bytes32 (word (1179648 + 48 * i + 20))) (write (bytes32 (word (1179648 + 48 * i))) v m) = read (bytes32 (word (1179648 + 48 * i + 20))) m) /\
     (!(v:int32) (m:int64->byte). read (bytes32 (word (1179648 + 48 * i))) (write (bytes32 (word (1179648 + 48 * i + 4))) v m) = read (bytes32 (word (1179648 + 48 * i))) m) /\
     (!(v:int32) (m:int64->byte). read (bytes32 (word (1179648 + 48 * i + 8))) (write (bytes32 (word (1179648 + 48 * i + 4))) v m) = read (bytes32 (word (1179648 + 48 * i + 8))) m) /\
     (!(v:int32) (m:int64->byte). read (bytes32 (word (1179648 + 48 * i + 12))) (write (bytes32 (word (1179648 + 48 * i + 4))) v m) = read (bytes32 (word (1179648 + 48 * i + 12))) m) /\
     (!(v:int32) (m:int64->byte). read (bytes32 (word (1179648 + 48 * i + 16))) (write (bytes32 (word (1179648 + 48 * i + 4))) v m) = read (bytes32 (word (1179648 + 48 * i + 16))) m) /\
     (!(v:int32) (m:int64->byte). read (bytes32 (word (1179648 + 48 * i + 20))) (write (bytes32 (word (1179648 + 48 * i + 4))) v m) = read (bytes32 (word (1179648 + 48 * i + 20))) m) /\
     (!(v:int32) (m:int64->byte). read (bytes32 (word (1179648 + 48 * i))) (write (bytes32 (word (1179648 + 48 * i + 8))) v m) = read (bytes32 (word (1179648 + 48 * i))) m) /\
     (!(v:int32) (m:int64->byte). read (bytes32 (word (1179648 + 48 * i + 4))) (write (bytes32 (word (1179648 + 48 * i + 8))) v m) = read (bytes32 (word (1179648 + 48 * i + 4))) m) /\
     (!(v:int32) (m:int64->byte). read (bytes32 (word (1179648 + 48 * i + 12))) (write (bytes32 (word (1179648 + 48 * i + 8))) v m) = read (bytes32 (word (1179648 + 48 * i + 12))) m) /\
     (!(v:int32) (m:int64->byte). read (bytes32 (word (1179648 + 48 * i + 16))) (write (bytes32 (word (1179648 + 48 * i + 8))) v m) = read (bytes32 (word (1179648 + 48 * i + 16))) m) /\
     (!(v:int32) (m:int64->byte). read (bytes32 (word (1179648 + 48 * i + 20))) (write (bytes32 (word (1179648 + 48 * i + 8))) v m) = read (bytes32 (word (1179648 + 48 * i + 20))) m) /\
     (!(v:int32) (m:int64->byte). read (bytes32 (word (1179648 + 48 * i))) (write (bytes32 (word (1179648 + 48 * i + 16))) v m) = read (bytes32 (word (1179648 + 48 * i))) m) /\
     (!(v:int32) (m:int64->byte). read (bytes32 (word (1179648 + 48 * i + 4))) (write (bytes32 (word (1179648 + 48 * i + 16))) v m) = read (bytes32 (word (1179648 + 48 * i + 4))) m) /\
     (!(v:int32) (m:int64->byte). read (bytes32 (word (1179648 + 48 * i + 8))) (write (bytes32 (word (1179648 + 48 * i + 16))) v m) = read (bytes32 (word (1179648 + 48 * i + 8))) m) /\
     (!(v:int32) (m:int64->byte). read (bytes32 (word (1179648 + 48 * i + 12))) (write (bytes32 (word (1179648 + 48 * i + 16))) v m) = read (bytes32 (word (1179648 + 48 * i + 12))) m) /\
     (!(v:int32) (m:int64->byte). read (bytes32 (word (1179648 + 48 * i + 20))) (write (bytes32 (word (1179648 + 48 * i + 16))) v m) = read (bytes32 (word (1179648 + 48 * i + 20))) m)`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THEN
  MATCH_MP_TAC CAP_B32_OTHER THEN ASM_ARITH_TAC);;

(* arithmetic facts about the cells of record i *)
let L4_REC_ARITH = ARITH_RULE
 `!i. (12 * i + 1 = 12 * i <=> F) /\ (12 * i + 2 = 12 * i <=> F) /\ (12 * i + 4 = 12 * i <=> F) /\
      (12 * i + 2 = 12 * i + 1 <=> F) /\ (12 * i + 4 = 12 * i + 1 <=> F) /\
      (12 * i + 4 = 12 * i + 2 <=> F) /\
      (12 * i < 12 * (i + 1) <=> T) /\ (12 * i + 1 < 12 * (i + 1) <=> T) /\
      (12 * i + 2 < 12 * (i + 1) <=> T) /\ (12 * i + 4 < 12 * (i + 1) <=> T)`;;

(* one record step of the invariant: cells 0 1 2 4 of record i take FD's values; *)
(* the new memory m' is given by a read characterisation.                         *)
let L4_MEM_GEN = prove
 (`!(FD:int32->(num->int32)->num->int32) nd di m m' i x0 x1 x2 x4.
     (!k. 12 * i <= k /\ k < 12 * i + 12 /\ ~(k = 12 * i) /\ ~(k = 12 * i + 1) /\
          ~(k = 12 * i + 2) /\ ~(k = 12 * i + 4) ==> FD nd di k = di k) /\
     FD nd di (12 * i) = x0 /\ FD nd di (12 * i + 1) = x1 /\
     FD nd di (12 * i + 2) = x2 /\ FD nd di (12 * i + 4) = x4 /\
     va1_w32s 1179648 196608 (\k. if k < 12 * i then FD nd di k else di k) m /\
     (!k. k < 196608 ==> read (bytes32 (word (1179648 + 4 * k))) m' =
            if k = 12 * i then x0 else if k = 12 * i + 1 then x1 else
            if k = 12 * i + 2 then x2 else if k = 12 * i + 4 then x4 else
            read (bytes32 (word (1179648 + 4 * k))) m)
     ==> va1_w32s 1179648 196608 (\k. if k < 12 * (i + 1) then FD nd di k else di k) m'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_w32s] THEN STRIP_TAC THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  MAP_EVERY (fun t -> ASM_CASES_TAC t THENL [ASM_REWRITE_TAC[L4_REC_ARITH]; ALL_TAC])
    [`k = 12 * i`; `k = 12 * i + 1`; `k = 12 * i + 2`; `k = 12 * i + 4`] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `k < 12 * i` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `k < 12 * (i + 1)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    COND_CASES_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* peel one write off a read (same cell or provably disjoint cell); unlike     *)
(* B32_PEEL_TAC it also works when the same-cell rewrite closes the goal.      *)
let L4_PEEL_TAC : tactic = fun (asl,w) ->
  let pat = `read (bytes32 (word (x:num))) (write (bytes32 (word (a:num))) (v:int32) (m:int64->byte))` in
  let t = find_term (can (term_match [] pat)) w in
  let x = rand(rand(rand(rator t))) in
  let a = rand(rand(rand(rator(rator(rand t))))) in
  ((SUBGOAL_THEN (mk_eq(x,a)) MP_TAC THENL
     [ASM_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP CAP_B32_SAME_EQ th])]) ORELSE
   (MP_TAC(SPECL [x;a] CAP_B32_OTHER) THEN ANTS_TAC THENL
     [ASM_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])])) (asl,w);;

(* the write chains of f11 and f12, as read characterisations *)
let L4_CHAIN_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MAP_EVERY (fun t -> ASM_CASES_TAC t THENL
     [ASM_REWRITE_TAC[L4_REC_ARITH] THEN REPEAT L4_PEEL_TAC THEN NO_TAC; ALL_TAC])
    [`k = 12 * i`; `k = 12 * i + 1`; `k = 12 * i + 2`; `k = 12 * i + 4`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT L4_PEEL_TAC THEN NO_TAC;;

let L4_CHAIN11 = prove
 (`!m i x0 x1 x2 x4. i < 16384 ==>
     !k. k < 196608 ==>
       read (bytes32 (word (1179648 + 4 * k)))
         (write (bytes32 (word (1179648 + 48 * i + 4))) x1
           (write (bytes32 (word (1179648 + 48 * i + 8))) x2
             (write (bytes32 (word (1179648 + 48 * i))) x0
               (write (bytes32 (word (1179648 + 48 * i + 16))) x4 m)))) =
       (if k = 12 * i then x0 else if k = 12 * i + 1 then x1 else
        if k = 12 * i + 2 then x2 else if k = 12 * i + 4 then x4 else
        read (bytes32 (word (1179648 + 4 * k))) m)`,
  L4_CHAIN_TAC);;

let L4_CHAIN12 = prove
 (`!m i x0 x1 x2 x4. i < 16384 ==>
     !k. k < 196608 ==>
       read (bytes32 (word (1179648 + 4 * k)))
         (write (bytes32 (word (1179648 + 48 * i + 8))) x2
           (write (bytes32 (word (1179648 + 48 * i + 4))) x1
             (write (bytes32 (word (1179648 + 48 * i + 16))) x4
               (write (bytes32 (word (1179648 + 48 * i))) x0 m)))) =
       (if k = 12 * i then x0 else if k = 12 * i + 1 then x1 else
        if k = 12 * i + 2 then x2 else if k = 12 * i + 4 then x4 else
        read (bytes32 (word (1179648 + 4 * k))) m)`,
  L4_CHAIN_TAC);;

(* the cells of record i under va1_drop_fwd / va1_drop_bwd *)
let L4_CELLS_TAC defn =
  REPEAT GEN_TAC THEN REWRITE_TAC[defn] THEN
  ABBREV_TAC `n = MIN (val (nd:int32)) 16384` THEN DISCH_TAC THEN
  SUBGOAL_THEN `12 * i < 12 * n /\ 12 * i + 1 < 12 * n /\ 12 * i + 2 < 12 * n /\ 12 * i + 4 < 12 * n`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `(12 * i) MOD 12 = 0 /\ (12 * i + 1) MOD 12 = 1 /\ (12 * i + 2) MOD 12 = 2 /\
                (12 * i + 4) MOD 12 = 4` (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `i:num` THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[GSYM ADD_ASSOC; L4_ADDM1] THEN CONV_TAC NUM_REDUCE_CONV THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(SPECL [`i:num`; `k:num`] L4_MOD_REC) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `~(k - 12 * i = 0) /\ ~(k - 12 * i = 1) /\ ~(k - 12 * i = 2) /\ ~(k - 12 * i = 4) /\
                ~(k - 12 * i < 3)` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];;

let L4_FWD_CELLS = prove
 (`!nd di i. i < MIN (val nd) 16384 ==>
    va1_drop_fwd nd di (12 * i) = word_add (di (12 * i)) (di (12 * i + 3)) /\
    va1_drop_fwd nd di (12 * i + 1) = word_add (di (12 * i + 1)) (word_add (di (12 * i + 4)) (word 4294967295)) /\
    va1_drop_fwd nd di (12 * i + 2) = word_add (di (12 * i + 2)) (di (12 * i + 5)) /\
    va1_drop_fwd nd di (12 * i + 4) = word_add (di (12 * i + 4)) (word 4294967295) /\
    (!k. 12 * i <= k /\ k < 12 * i + 12 /\ ~(k = 12 * i) /\ ~(k = 12 * i + 1) /\
         ~(k = 12 * i + 2) /\ ~(k = 12 * i + 4) ==> va1_drop_fwd nd di k = di k)`,
  L4_CELLS_TAC va1_drop_fwd);;

let L4_BWD_CELLS = prove
 (`!nd di i. i < MIN (val nd) 16384 ==>
    va1_drop_bwd nd di (12 * i) = word_sub (di (12 * i)) (di (12 * i + 3)) /\
    va1_drop_bwd nd di (12 * i + 1) = word_sub (di (12 * i + 1)) (di (12 * i + 4)) /\
    va1_drop_bwd nd di (12 * i + 2) = word_sub (di (12 * i + 2)) (di (12 * i + 5)) /\
    va1_drop_bwd nd di (12 * i + 4) = word_add (di (12 * i + 4)) (word 1) /\
    (!k. 12 * i <= k /\ k < 12 * i + 12 /\ ~(k = 12 * i) /\ ~(k = 12 * i + 1) /\
         ~(k = 12 * i + 2) /\ ~(k = 12 * i + 4) ==> va1_drop_bwd nd di k = di k)`,
  L4_CELLS_TAC va1_drop_bwd);;

let L4_FWD_ZERO = prove
 (`!di. va1_drop_fwd (word 0) di = di`,
  REWRITE_TAC[FUN_EQ_THM; va1_drop_fwd; VAL_WORD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[LT]);;

let l4_inv mc fd = subst [mc,`MC:byte list`; fd,`FD:int32->(num->int32)->num->int32`]
 `\i s. read wcode s = MC /\ read wstatus s = WRunning /\
        read wmemsize s = 4194304 /\ read warity s = 0 /\
        read wlabels s = [0,40,0; 0,141,0] /\
        read (wlocal 0) s = I32 (word (1179648 + 48 * i)) /\
        read (wlocal 1) s = I32 (word (N - i)) /\
        read wstack s = (if read wpc s = word 42 then [] else [I32 (word (N - i))]) /\
        va1_w32s 1179648 196608 (\k. if k < 12 * i then FD (nd:int32) (di:num->int32) k else di k)
                 (read wmem s)`;;

let l4_f11_tm, l4_f12_tm =
  match conjuncts (rhs (concl va1_drop_ok)) with [a;b] -> a,b | _ -> failwith "conj";;

let L4_STEPS_TAC execth snums =
  MAP_EVERY (fun s (asl,w) ->
     let mths = filter (fun th -> is_memfact (concl th)) (map snd asl) in
     WASM_SINGLE_STEP_TAC execth (READ_COMPONENT_COMPOSE :: mths) s (asl,w))
   (statenames "s" snums);;

let L4_ENTRY_TAC exec =
  ENSURES_INIT_TAC "s0" THEN ABBREV_TAC `mm = read wmem s0` THEN
  L4_STEPS_TAC exec (1--16) THEN ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0; LT; ETA_AX] THEN
  EXPAND_TAC "N" THEN REWRITE_TAC[L4_MIN_WORD] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[];;

let L4_F11_MEM = prove
 (`!nd di m i. i < MIN (val nd) 16384 /\
     va1_w32s 1179648 196608 (\k. if k < 12 * i then va1_drop_fwd nd di k else di k) m
     ==> va1_w32s 1179648 196608 (\k. if k < 12 * (i + 1) then va1_drop_fwd nd di k else di k)
          (write (bytes32 (word (1179648 + 48 * i + 4)))
             (word_add (di (12 * i + 1)) (word_add (di (12 * i + 4)) (word 4294967295)))
           (write (bytes32 (word (1179648 + 48 * i + 8))) (word_add (di (12 * i + 2)) (di (12 * i + 5)))
            (write (bytes32 (word (1179648 + 48 * i))) (word_add (di (12 * i)) (di (12 * i + 3)))
             (write (bytes32 (word (1179648 + 48 * i + 16))) (word_add (di (12 * i + 4)) (word 4294967295))
               m))))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `di:num->int32` o MATCH_MP L4_FWD_CELLS) THEN
  SUBGOAL_THEN `i < 16384` ASSUME_TAC THENL
   [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `MIN (val (nd:int32)) 16384` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC L4_MEM_GEN THEN
  MAP_EVERY EXISTS_TAC [`m:int64->byte`;
    `word_add (di (12 * i)) (di (12 * i + 3)):int32`;
    `word_add (di (12 * i + 1)) (word_add (di (12 * i + 4)) (word 4294967295)):int32`;
    `word_add (di (12 * i + 2)) (di (12 * i + 5)):int32`;
    `word_add (di (12 * i + 4)) (word 4294967295):int32`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MATCH_MP_TAC L4_CHAIN11 THEN FIRST_ASSUM ACCEPT_TAC);;

let L4_F12_MEM = prove
 (`!nd di m i. i < MIN (val nd) 16384 /\
     va1_w32s 1179648 196608 (\k. if k < 12 * i then va1_drop_bwd nd di k else di k) m
     ==> va1_w32s 1179648 196608 (\k. if k < 12 * (i + 1) then va1_drop_bwd nd di k else di k)
          (write (bytes32 (word (1179648 + 48 * i + 8))) (word_sub (di (12 * i + 2)) (di (12 * i + 5)))
           (write (bytes32 (word (1179648 + 48 * i + 4))) (word_sub (di (12 * i + 1)) (di (12 * i + 4)))
            (write (bytes32 (word (1179648 + 48 * i + 16))) (word_add (di (12 * i + 4)) (word 1))
             (write (bytes32 (word (1179648 + 48 * i))) (word_sub (di (12 * i)) (di (12 * i + 3)))
               m))))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `di:num->int32` o MATCH_MP L4_BWD_CELLS) THEN
  SUBGOAL_THEN `i < 16384` ASSUME_TAC THENL
   [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `MIN (val (nd:int32)) 16384` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC L4_MEM_GEN THEN
  MAP_EVERY EXISTS_TAC [`m:int64->byte`;
    `word_sub (di (12 * i)) (di (12 * i + 3)):int32`;
    `word_sub (di (12 * i + 1)) (di (12 * i + 4)):int32`;
    `word_sub (di (12 * i + 2)) (di (12 * i + 5)):int32`;
    `word_add (di (12 * i + 4)) (word 1):int32`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MATCH_MP_TAC L4_CHAIN12 THEN FIRST_ASSUM ACCEPT_TAC);;

let L4_BWD_ZERO = prove
 (`!di. va1_drop_bwd (word 0) di = di`,
  REWRITE_TAC[FUN_EQ_THM; va1_drop_bwd; VAL_WORD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[LT]);;

let L4_BODY_TAC exec fd memth =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `i < 16384` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  VAL_TAC `val(word (1179648 + 48 * i):int32) = 1179648 + 48 * i` THEN
  VAL_TAC `val(word_add (word (1179648 + 48 * i)) (word 4):int32) = 1179648 + 48 * i + 4` THEN
  VAL_TAC `val(word_add (word (1179648 + 48 * i)) (word 8):int32) = 1179648 + 48 * i + 8` THEN
  VAL_TAC `val(word_add (word (1179648 + 48 * i)) (word 12):int32) = 1179648 + 48 * i + 12` THEN
  VAL_TAC `val(word_add (word (1179648 + 48 * i)) (word 16):int32) = 1179648 + 48 * i + 16` THEN
  VAL_TAC `val(word_add (word (1179648 + 48 * i)) (word 20):int32) = 1179648 + 48 * i + 20` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP L4_B32O) THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN ABBREV_TAC `mm = read wmem s0` THEN
  FIRST_ASSUM(fun wth -> if can (term_match [] `va1_w32s b n f m`) (concl wth) then
    MP_TAC(SPECL [fd; `nd:int32`; `di:num->int32`; `mm:int64->byte`; `i:num`] L4_LOADS_INV) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [ACCEPT_TAC wth; FIRST_ASSUM ACCEPT_TAC]; STRIP_TAC]
    else NO_TAC) THEN
  L4_STEPS_TAC exec (1--48) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[CAP_DEC; injectivity "wval"; CONS_11] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
    MATCH_MP_TAC memth THEN ASM_REWRITE_TAC[]];;

let L4_BACK_TAC exec =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(word (N - i):int32 = word 0) <=> F` ASSUME_TAC THENL
   [REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN
    SUBGOAL_THEN `val(word (N - i):int32) = N - i` SUBST1_TAC THENL
     [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC;
      REWRITE_TAC[VAL_WORD_0] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN ABBREV_TAC `mm = read wmem s0` THEN
  L4_STEPS_TAC exec (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let L4_EXIT_TAC exec fd fullth =
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN ABBREV_TAC `mm = read wmem s0` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUB_REFL]) THEN
  SUBGOAL_THEN (subst [fd,`FD:int32->(num->int32)->num->int32`]
    `(\k. if k < 12 * N then FD (nd:int32) (di:num->int32) k else di k) = FD nd di`)
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [EXPAND_TAC "N" THEN REWRITE_TAC[fullth]; ALL_TAC] THEN
  L4_STEPS_TAC exec (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let L4_DROP_TAC mc exec fd zeroth fullth memth =
  REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_CASES_TAC `nd:int32 = word 0` THENL
   [ASM_REWRITE_TAC[zeroth] THEN ENSURES_INIT_TAC "s0" THEN ABBREV_TAC `mm = read wmem s0` THEN
    L4_STEPS_TAC exec (1--7) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `N = MIN (val (nd:int32)) 16384` THEN
  SUBGOAL_THEN `1 <= N /\ N <= 16384` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN SUBGOAL_THEN `~(val(nd:int32) = 0)` MP_TAC THENL
     [ASM_REWRITE_TAC[VAL_EQ_0]; ARITH_TAC]; ALL_TAC] THEN
  ENSURES_WHILE_UP_TAC `N:num` `42` `137` (l4_inv mc fd) THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC; L4_ENTRY_TAC exec; L4_BODY_TAC exec fd memth; L4_BACK_TAC exec;
    L4_EXIT_TAC exec fd fullth];;

let L4_F11 = prove(l4_f11_tm,
  L4_DROP_TAC `va1_f11_mc` L4_F11_EXEC `va1_drop_fwd` L4_FWD_ZERO L4_FWD_FULL L4_F11_MEM);;
let L4_F12 = prove(l4_f12_tm,
  L4_DROP_TAC `va1_f12_mc` L4_F12_EXEC `va1_drop_bwd` L4_BWD_ZERO L4_BWD_FULL L4_F12_MEM);;
(* the frozen statements, proved from their pop_spec_* strings *)
let VA1_DROP_OK = prove(parse_term pop_spec_VA1_DROP_OK,
  REWRITE_TAC[va1_drop_ok; L4_F11; L4_F12]);;
