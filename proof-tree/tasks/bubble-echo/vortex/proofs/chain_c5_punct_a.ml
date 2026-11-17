(* ========================================================================= *)
(* Vortex chain rung C5 part 2 "puncture" (lane vortex-chain-20261111-142342 *)
(* c5, Claude Opus 5.5, 2026-11-13), layer A: f33 states and frame, the step *)
(* tactic, memory lemmas, the host entry, the three early exits, the         *)
(* epilogue and the non-vacuity witnesses. Spec chain_c5_punct.spec;         *)
(* statements filled by c5/spec/asm_punct.py. Stable layer: never edit.      *)
(* ========================================================================= *)

needs "chain_c5_leaves.ml";;

let va1_f33_pre = new_definition
 `va1_f33_pre (a0:int32) (a1:int32) (a2:int32) (m:int64->byte) (s:wasmstate) <=>
    read wcode s = va1_puncture_mc /\ read wpc s = word 17 /\ read wstatus s = WRunning /\
    read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\ read wmemsize s = 4194304 /\
    read (wglobal 0) s = I32 (word 16384) /\ read (wlocal 0) s = I32 a0 /\
    read (wlocal 1) s = I32 a1 /\ read (wlocal 2) s = I32 a2 /\ read wmem s = m`;;

let va1_f33_frame = new_definition
 `va1_f33_frame (m0:int64->byte) (m:int64->byte) <=>
    !a. a < 4194304 /\ ~(16288 <= a /\ a < 16384) /\ ~(65536 <= a /\ a < 1114112)
        ==> read (bytes8 (word a)) m = read (bytes8 (word a)) m0`;;

let va1_f33_epi_pre = new_definition
 `va1_f33_epi_pre (r:int32) (s:wasmstate) <=>
    read wcode s = va1_puncture_mc /\ read wpc s = word 1238 /\ read wstatus s = WRunning /\
    read wstack s = [I32 r] /\ read wlabels s = [0,1241,0] /\ read warity s = 1 /\
    read (wlocal 3) s = I32 (word 16288)`;;

(* ---- stepping f33 under wasmc: memory reads and decided conditions are  *)
(* given to the step conversion, so loaded values stay state-free         *)
let c5_is_rd comp s t = is_eq t &&
  (match lhs t with Comb(Comb(Const("read",_),c),s') -> c = comp && s' = s | _ -> false);;
let c5_statefree t = not (can (find_term (fun u -> type_of u = `:wasmstate`)) t);;
let C5S_STEP exec sname : tactic = fun (asl,w) ->
  let s = rand w in
  let mths = map snd (filter (fun (_,th) -> c5_is_rd `wmem` s (concl th)) asl) in
  let sf = map snd (filter (fun (_,th) -> let c = concl th in
      c5_statefree c && not (is_forall c) && not (is_imp c)) asl) in
  (WASMC_STEP_TAC exec (READ_COMPONENT_COMPOSE :: (mths @ sf)) sname THEN
   DISCARD_OLD_WASMSTATE_TAC sname) (asl,w);;
let C5S_STEPS exec snums = MAP_EVERY (fun n -> C5S_STEP exec ("s"^string_of_int n)) snums;;
let c5_ctr = ref 0;;
let C5S_RUN exec : tactic =
  REPEAT (fun g -> incr c5_ctr; C5S_STEP exec ("r"^string_of_int !c5_ctr) g);;
let C5_PRE_TAC (pre:thm) =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pre] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = fst(dest_const(fst(strip_comb(lhs(snd(strip_forall(concl pre)))))))
                     with Failure _ -> false));;

(* ---- memory lemmas ---- *)
let VA1_C5_B8_W32_OTHER = prove
 (`!a b (y:int32) (m:int64->byte).
     (a + 1 <= b \/ b + 4 <= a) /\ a + 1 < 2 EXP 64 /\ b + 4 < 2 EXP 64
     ==> read (bytes8 (word a)) (write (bytes32 (word b)) y m) = read (bytes8 (word a)) m`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC READ_WRITE_ORTHOGONAL_COMPONENTS THEN
  REWRITE_TAC[bytes8; bytes32] THEN MATCH_MP_TAC ORTHOGONAL_COMPONENTS_SUB_LEFT THEN
  MATCH_MP_TAC ORTHOGONAL_COMPONENTS_SUB_RIGHT THEN
  REWRITE_TAC[ORTHOGONAL_COMPONENTS_BYTES; DIMINDEX_64] THEN
  MATCH_MP_TAC NONOVERLAPPING_MODULO_SIMPLE THEN
  SUBGOAL_THEN `val(word a:int64) = a /\ val(word b:int64) = b`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let VA1_C5_B32_W32_OTHER = prove
 (`!a b (y:int32) (m:int64->byte).
     (a + 4 <= b \/ b + 4 <= a) /\ a + 4 < 2 EXP 64 /\ b + 4 < 2 EXP 64
     ==> read (bytes32 (word a)) (write (bytes32 (word b)) y m) = read (bytes32 (word a)) m`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC READ_WRITE_ORTHOGONAL_COMPONENTS THEN
  REWRITE_TAC[bytes32] THEN MATCH_MP_TAC ORTHOGONAL_COMPONENTS_SUB_LEFT THEN
  MATCH_MP_TAC ORTHOGONAL_COMPONENTS_SUB_RIGHT THEN
  REWRITE_TAC[ORTHOGONAL_COMPONENTS_BYTES; DIMINDEX_64] THEN
  MATCH_MP_TAC NONOVERLAPPING_MODULO_SIMPLE THEN
  SUBGOAL_THEN `val(word a:int64) = a /\ val(word b:int64) = b`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let VA1_C5_B32_SAME = prove
 (`!b (y:int32) (m:int64->byte). read (bytes32 (word b)) (write (bytes32 (word b)) y m) = y`,
  MESON_TAC[READ_WRITE_VALID_COMPONENT; VALID_COMPONENT_BYTES32]);;

(* ---- host entry ---- *)
let VA1_F33_ENTRY = prove
 (`!a0 a1 a2 s.
     read wmemsize s = 4194304 /\ read (wglobal 0) s = I32 (word 16384)
     ==> va1_f33_pre a0 a1 a2 (read wmem s)
          (wcall_entry va1_puncture_mc 3 1 [I32 a2; I32 a1; I32 a0] 17
            [I32 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); I64 (word 0)] s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[wglobal; READ_COMPONENT_COMPOSE; READ_ELEMENT]) THEN
  REWRITE_TAC[va1_f33_pre; wglobal] THEN C5_ENTRY_TAC THEN ASM_REWRITE_TAC[]);;

(* ---- the three early exits and the epilogue: straight stepping ---- *)
let C5_F33_STRAIGHT_TAC pre =
  REPEAT GEN_TAC THEN TRY(DISCH_THEN STRIP_ASSUME_TAC) THEN ENSURES_INIT_TAC "s0" THEN C5_PRE_TAC pre THEN
  C5S_RUN C5_F33_EXEC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let VA1_F33_GUARD_P = prove(`!fs a0 a1 a2 m.
     ~(read (bytes32 (word 16396)) m = word 4294967295)
     ==> ensures (wasmc fs) (va1_f33_pre a0 a1 a2 m)
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 1)] /\
               read (wglobal 0) s = I32 (word 16384) /\ read wmem s = m)
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocal 3; wlocal 4] ,, MAYCHANGE [wglobal 0])`, C5_F33_STRAIGHT_TAC va1_f33_pre);;
let VA1_F33_GUARD_T = prove(`!fs a0 a1 a2 m.
     read (bytes32 (word 16396)) m = word 4294967295 /\ read (bytes32 (word 16392)) m = word 0
     ==> ensures (wasmc fs) (va1_f33_pre a0 a1 a2 m)
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 3)] /\
               read (wglobal 0) s = I32 (word 16384) /\ read wmem s = m)
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocal 3; wlocal 4] ,, MAYCHANGE [wglobal 0])`, C5_F33_STRAIGHT_TAC va1_f33_pre);;
let VA1_F33_GUARD_ARGS = prove(`!fs a0 a1 a2 m.
     read (bytes32 (word 16396)) m = word 4294967295 /\ ~(read (bytes32 (word 16392)) m = word 0) /\
     a0 = word 0 /\ a1 = word 0 /\ a2 = word 0
     ==> ensures (wasmc fs) (va1_f33_pre a0 a1 a2 m)
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 2)] /\
               read (wglobal 0) s = I32 (word 16384) /\ read wmem s = m)
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocal 3; wlocal 4] ,, MAYCHANGE [wglobal 0])`, C5_F33_STRAIGHT_TAC va1_f33_pre);;
let VA1_F33_EPILOGUE = prove(`!fs r. ensures (wasmc fs) (va1_f33_epi_pre r)
          (\s. read wstatus s = WDone /\ read wstack s = [I32 r] /\ read (wglobal 0) s = I32 (word 16384))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocal 4] ,, MAYCHANGE [wglobal 0])`, C5_F33_STRAIGHT_TAC va1_f33_epi_pre);;

(* ---- non-vacuity ---- *)
let VA1_C5_PRE_AT = prove
 (`!a0 a1 a2 m. va1_f33_pre a0 a1 a2 m
     (wcall_entry va1_puncture_mc 3 1 [I32 a2; I32 a1; I32 a0] 17
      [I32 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0);
       F64 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0);
       F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); F64 (word 0); F64 (word 0);
       F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); I64 (word 0)]
      (write wmem (m) (write wmemsize 4194304 (write (wglobal 0) (I32 (word 16384)) (ARB:wasmstate)))))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`a0:int32`; `a1:int32`; `a2:int32`;
    `write wmem m (write wmemsize 4194304 (write (wglobal 0) (I32 (word 16384)) (ARB:wasmstate)))`] VA1_F33_ENTRY) THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN REWRITE_TAC[]);;

let VA1_F33_SAT = prove
 (`!a0 a1 a2. ?fs m1 m2 m3 s1 s2 s3.
     fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\
     ~(read (bytes32 (word 16396)) m1 = word 4294967295) /\
     read (bytes32 (word 16396)) m2 = word 4294967295 /\ read (bytes32 (word 16392)) m2 = word 0 /\
     read (bytes32 (word 16396)) m3 = word 4294967295 /\ ~(read (bytes32 (word 16392)) m3 = word 0) /\
     va1_f33_pre a0 a1 a2 m1 s1 /\ va1_f33_pre a0 a1 a2 m2 s2 /\ va1_f33_pre a0 a1 a2 m3 s3`,
  REPEAT GEN_TAC THEN
  EXISTS_TAC `\f. if f = 32 then (va1_f32_mc,2,1) else (va1_f34_mc,3,0)` THEN
  MAP_EVERY EXISTS_TAC
   [`write (bytes32 (word 16396)) (word 0:int32) (ARB:int64->byte)`; `write (bytes32 (word 16396)) (word 4294967295:int32) (write (bytes32 (word 16392)) (word 0:int32) (ARB:int64->byte))`; `write (bytes32 (word 16396)) (word 4294967295:int32) (write (bytes32 (word 16392)) (word 1:int32) (ARB:int64->byte))`] THEN
  MAP_EVERY EXISTS_TAC
   [`wcall_entry va1_puncture_mc 3 1 [I32 a2; I32 a1; I32 a0] 17
      [I32 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0);
       F64 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0);
       F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); F64 (word 0); F64 (word 0);
       F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); I64 (word 0)]
      (write wmem (write (bytes32 (word 16396)) (word 0:int32) (ARB:int64->byte)) (write wmemsize 4194304 (write (wglobal 0) (I32 (word 16384)) (ARB:wasmstate))))`; `wcall_entry va1_puncture_mc 3 1 [I32 a2; I32 a1; I32 a0] 17
      [I32 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0);
       F64 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0);
       F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); F64 (word 0); F64 (word 0);
       F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); I64 (word 0)]
      (write wmem (write (bytes32 (word 16396)) (word 4294967295:int32) (write (bytes32 (word 16392)) (word 0:int32) (ARB:int64->byte))) (write wmemsize 4194304 (write (wglobal 0) (I32 (word 16384)) (ARB:wasmstate))))`; `wcall_entry va1_puncture_mc 3 1 [I32 a2; I32 a1; I32 a0] 17
      [I32 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0);
       F64 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0);
       F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); F64 (word 0); F64 (word 0);
       F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); I64 (word 0)]
      (write wmem (write (bytes32 (word 16396)) (word 4294967295:int32) (write (bytes32 (word 16392)) (word 1:int32) (ARB:int64->byte))) (write wmemsize 4194304 (write (wglobal 0) (I32 (word 16384)) (ARB:wasmstate))))`] THEN
  REWRITE_TAC[VA1_C5_PRE_AT] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[VA1_C5_B32_SAME] THEN
  SIMP_TAC[VA1_C5_B32_W32_OTHER; ARITH; VA1_C5_B32_SAME] THEN CONV_TAC WORD_REDUCE_CONV);;

let VA1_F33_EPI_SAT = prove
 (`!r. ?s. va1_f33_epi_pre r s`,
  GEN_TAC THEN
  EXISTS_TAC `write wcode va1_puncture_mc (write wpc (word 1238) (write wstatus WRunning
     (write wstack [I32 r] (write wlabels [0,1241,0] (write warity 1
     (write (wlocal 3) (I32 (word 16288)) (ARB:wasmstate)))))))` THEN
  REWRITE_TAC[va1_f33_epi_pre] THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN REWRITE_TAC[]);;
