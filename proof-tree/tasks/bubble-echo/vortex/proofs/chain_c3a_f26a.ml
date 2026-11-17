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
(* ========================================================================= *)
(* Vortex chain, rung C3a, layer 2: f26 (ve_unpuncture) check loop (C3A,     *)
(* Claude Opus 5.5, 2026-11-13). f26 pc 69..309: the 2048-bead check loop    *)
(* (no stores) by ENSURES_WHILE_UP_TAC. Invariant at count i: memory = the   *)
(* entry memory mm, local0 = nd + sum of va1_mis over beads < i (i32 word),  *)
(* local1 = the ZSEED mix, local2 = TBL row address, local3 = 4 i,           *)
(* local4 = i. One body (92 steps) proved once.                              *)
(* ========================================================================= *)

let C3A_F26_EXEC = FAST_MK_EXEC_RULE va1_f26_mc 5;;

let C3_VAL32 = prove(`!x. x < 4294967296 ==> val(word x:int32) = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_32] THEN ASM_ARITH_TAC);;
let C3_VALZ = prove(`!x z. x = z /\ z < 4294967296 ==> val(word x:int32) = z`, MESON_TAC[C3_VAL32]);;
let C3_VADDZ = prove(`!x y z. x + y = z /\ z < 4294967296 ==> val(word_add (word x) (word y):int32) = z`,
  REWRITE_TAC[GSYM WORD_ADD] THEN MESON_TAC[C3_VAL32]);;
let C3_W32S_AT = prove(`!base n (f:num->int32) m k a. va1_w32s base n f m /\ k < n /\ a = base + 4 * k
   ==> read (bytes32 (word a)) m = f k`, REWRITE_TAC[va1_w32s] THEN MESON_TAC[]);;
let C3_COND_I64 = prove(`!c a b. (if c then I64 a else I64 b) = I64 (if c then a else b)`, MESON_TAC[]);;
let C3_COND_I32 = prove(`!c a b. (if c then I32 a else I32 b) = I32 (if c then a else b)`, MESON_TAC[]);;

let C3_NSUM_LT_SUC = prove
 (`!f i. nsum {k | k < i + 1} f = nsum {k | k < i} f + f i`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{k | k < i + 1} = i INSERT {k | k < i}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[NSUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN ARITH_TAC);;

let C3_NSUM_LT_0 = prove
 (`!f. nsum {k | k < 0} f = 0`,
  REWRITE_TAC[LT; EMPTY_GSPEC; NSUM_CLAUSES]);;

let C3_NSUM_LT_2048 = prove
 (`!f. nsum {k | k < 2048} f = nsum (0..2047) f`,
  GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC);;

(* one bead: the word the bytes accumulate = nd + the count over beads < i+1 *)
let C3_ACC_STEP = prove
 (`!mdl tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32) i.
  word_add (word_add (word_add (word_add (word_add (word_add (word_add nd (word (nsum {k | k < i} (va1_mis mdl tbl (ra,rb,jq,jp,zq,zp))))) (word (bitval (~(ra i = word 251658))))) (word (bitval (~(jq i = word 0))))) (word (bitval (~(jp i = word 0))))) (word (bitval (~(zq i = word 0))))) (word (bitval (~(rb i = word_add (word_zx (word_ushr (word_add (if ~(ival (word_add (word_ishr (word_add (word_mul (word_sub ((word_sx (tbl (128 * i + 1)):int64)) ((word_sx (tbl (128 * i)):int64))) (word 251658)) (word 262144)) 19) ((word_sx (tbl (128 * i)):int64))) > &1) then word 1 else word_add (word_ishr (word_add (word_mul (word_sub ((word_sx (tbl (128 * i + 1)):int64)) ((word_sx (tbl (128 * i)):int64))) (word 251658)) (word 262144)) 19) ((word_sx (tbl (128 * i)):int64))) (word 1)) 1)) (word 251658)))))) (word (bitval (~(zp i = word_zx (word_ishr (word_add (word_mul (word_zx (word_xor (word_ushr (word_mul (word_xor (word_ushr (word_xor (word_add (word_mul (mdl 2) (word 3266489909)) (word 2769733223)) (word_mul (word_xor (word i) (word 2654435769)) (word 2246822507))) 15) (word_xor (word_add (word_mul (mdl 2) (word 3266489909)) (word 2769733223)) (word_mul (word_xor (word i) (word 2654435769)) (word 2246822507)))) (word 739982445)) 12) (word_mul (word_xor (word_ushr (word_xor (word_add (word_mul (mdl 2) (word 3266489909)) (word 2769733223)) (word_mul (word_xor (word i) (word 2654435769)) (word 2246822507))) 15) (word_xor (word_add (word_mul (mdl 2) (word 3266489909)) (word 2769733223)) (word_mul (word_xor (word i) (word 2654435769)) (word 2246822507)))) (word 739982445)))) (word 329853:int64)) (word 18446176457274163200)) 48)))))
  = word_add nd (word (nsum {k | k < i + 1} (va1_mis mdl tbl (ra,rb,jq,jp,zq,zp))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C3_NSUM_LT_SUC] THEN
  REWRITE_TAC[va1_mis; va1_rbinit; va1_rbv; va1_zpseed; va1_zpx1; va1_zpx0; COND_SWAP] THEN
  REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]);;

(* ---- stepping ------------------------------------------------------------ *)
let C3_STEPS_TAC execth snums =
  MAP_EVERY (fun s (asl,w) ->
     let mths = filter (fun th -> is_memfact (concl th)) (map snd asl) in
     WASM_SINGLE_STEP_TAC execth (READ_COMPONENT_COMPOSE :: C3_COND_I64 :: C3_COND_I32 :: mths) s (asl,w))
   (statenames "s" snums);;

let rec C3_STEPS_TO execth pc : tactic = fun (asl,w) ->
  let s = rand w in
  let cur = dest_small_numeral(rand(rhs(concl(find_read_th "wpc" s (map snd asl))))) in
  if cur = pc then ALL_TAC (asl,w) else
  let n = fst(dest_var s) in
  let k = int_of_string(String.sub n 1 (String.length n - 1)) + 1 in
  (C3_STEPS_TAC execth [k] THEN C3_STEPS_TO execth pc) (asl,w);;

(* a load fact from a va1_w32s assumption at a computed address *)
let C3_LOAD_TAC (base:int) (n:int) (f:term) (mm:term) (k:term) (a:term) : tactic = fun (asl,w) ->
  let wth = find (fun th -> let c = concl th in try let h,args = strip_comb c in
     fst(dest_const h) = "va1_w32s" && dest_small_numeral(hd args) = base && rand c = mm
     with _ -> false) (map snd asl) in
  let th = SPECL [mk_small_numeral base; mk_small_numeral n; f; mm; k; a] C3_W32S_AT in
  (MP_TAC th THEN ANTS_TAC THENL [REWRITE_TAC[wth] THEN ASM_ARITH_TAC; DISCH_TAC]) (asl,w);;

let C3_F26_FRAME = `MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
    MAYCHANGE [wlocal 0; wlocal 1; wlocal 2; wlocal 3; wlocal 4; wlocal 5] ,,
    MAYCHANGE [wmem :> bytes(word 16396,116)] ,, MAYCHANGE [wmem :> bytes(word 1130496,835584)]`;;

let c3_mis = `va1_mis mdl tbl ((ra:num->int32),(rb:num->int32),(jq:num->int32),(jp:num->int32),(zq:num->int32),(zp:num->int32))`;;
let c3_atoms = `\m. va1_pop p ap m /\ read (bytes32 (word 16404)) m = (h:int32) /\ va1_w32s 16408 26 hp m /\
   va1_w32s 65536 262144 (tbl:num->int32) m /\ va1_w32s 1130496 2048 (ra:num->int32) m /\
   va1_w32s 1138688 2048 (rb:num->int32) m /\ va1_w32s 1146880 2048 (jq:num->int32) m /\
   va1_w32s 1155072 2048 (jp:num->int32) m /\ va1_w32s 1163264 2048 (zq:num->int32) m /\
   va1_w32s 1171456 2048 (zp:num->int32) m /\ va1_w32s 1179648 196608 (di:num->int32) m /\
   read (bytes32 (word 16400)) m = (nd:int32)`;;
let c3_atoms_on m = rhs(concl(BETA_CONV (mk_comb(c3_atoms,m))));;
let c3_inv1 = subst [c3_mis,`MIS:num->num`]
 `\i s. read wcode s = va1_f26_mc /\ read wstatus s = WRunning /\ read wmemsize s = 4194304 /\
        read warity s = 1 /\ read wlabels s = [0,69,0; 0,726,0] /\ C3ATOMS (read wmem s) /\
        read (wlocal 0) s = I32 (word_add (nd:int32) (word (nsum {k | k < i} MIS))) /\
        read (wlocal 1) s = I32 (word_add (word_mul ((mdl:num->int32) 2) (word 3266489909)) (word 2769733223)) /\
        read (wlocal 2) s = I32 (word (65536 + 512 * i)) /\ read (wlocal 3) s = I32 (word (4 * i)) /\
        read (wlocal 4) s = I32 (word i) /\
        read wstack s = (if read wpc s = word 71 then [] else [I32 (word (bitval (~(word (4 * i) = word 8192:int32))))])`;;

let c3_fill tm = rhs(concl(TOP_DEPTH_CONV BETA_CONV (vsubst [c3_atoms, `C3ATOMS:(int64->byte)->bool`] tm)));;
let c3_inv1 = c3_fill c3_inv1;;

let C3_CHECK_HYPS = `va1_w32s 65536 262144 (tbl:num->int32) mm /\ va1_w32s 1130496 2048 (ra:num->int32) mm /\
   va1_w32s 1138688 2048 (rb:num->int32) mm /\ va1_w32s 1146880 2048 (jq:num->int32) mm /\
   va1_w32s 1155072 2048 (jp:num->int32) mm /\ va1_w32s 1163264 2048 (zq:num->int32) mm /\
   va1_w32s 1171456 2048 (zp:num->int32) mm`;;

let c3_check_tm = c3_fill(subst [c3_mis,`MIS:num->num`; C3_F26_FRAME,`CF:wasmstate->wasmstate->bool`] (I(
 `ensures wasm
   (\s. read wcode s = va1_f26_mc /\ read wpc s = word 69 /\ read wstatus s = WRunning /\
        read wmemsize s = 4194304 /\ read warity s = 1 /\ read wlabels s = [0,726,0] /\
        read wstack s = [] /\ C3ATOMS (read wmem s) /\
        read (wlocal 0) s = I32 nd /\
        read (wlocal 1) s = I32 (word_add (word_mul (mdl 2) (word 3266489909)) (word 2769733223)) /\
        read (wlocal 2) s = I32 (word 65536) /\ read (wlocal 3) s = I32 (word 0) /\
        read (wlocal 4) s = I32 (word 0))
   (\s. read wcode s = va1_f26_mc /\ read wpc s = word 309 /\ read wstatus s = WRunning /\
        read wmemsize s = 4194304 /\ read warity s = 1 /\ read wlabels s = [0,726,0] /\
        read wstack s = [] /\ C3ATOMS (read wmem s) /\
        read (wlocal 0) s = I32 (word_add nd (word (nsum (0..2047) MIS))))
   CF`)));;

let C3_BODY_TAC : tactic =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN ABBREV_TAC `mm = read wmem s0` THEN
  C3_LOAD_TAC 1130496 2048 `ra:num->int32` `mm:int64->byte` `i:num` `4 * i + 1130496` THEN
  C3_LOAD_TAC 1146880 2048 `jq:num->int32` `mm:int64->byte` `i:num` `4 * i + 1146880` THEN
  C3_LOAD_TAC 1155072 2048 `jp:num->int32` `mm:int64->byte` `i:num` `4 * i + 1155072` THEN
  C3_LOAD_TAC 1163264 2048 `zq:num->int32` `mm:int64->byte` `i:num` `4 * i + 1163264` THEN
  C3_LOAD_TAC 1138688 2048 `rb:num->int32` `mm:int64->byte` `i:num` `4 * i + 1138688` THEN
  C3_LOAD_TAC 1171456 2048 `zp:num->int32` `mm:int64->byte` `i:num` `4 * i + 1171456` THEN
  C3_LOAD_TAC 65536 262144 `tbl:num->int32` `mm:int64->byte` `128 * i + 1` `512 * i + 65540` THEN
  C3_LOAD_TAC 65536 262144 `tbl:num->int32` `mm:int64->byte` `128 * i` `512 * i + 65536` THEN
  MAP_EVERY (fun b -> SUBGOAL_THEN
     (subst [mk_small_numeral b,`B:num`] `val(word_add (word (4 * i)) (word B):int32) = 4 * i + B`)
     ASSUME_TAC THENL [MATCH_MP_TAC C3_VADDZ THEN ASM_ARITH_TAC; ALL_TAC])
    [1130496;1146880;1155072;1163264;1138688;1171456] THEN
  SUBGOAL_THEN `val(word_add (word (65536 + 512 * i)) (word 4):int32) = 512 * i + 65540` ASSUME_TAC THENL
   [MATCH_MP_TAC C3_VADDZ THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word (65536 + 512 * i):int32) = 512 * i + 65536` ASSUME_TAC THENL
   [MATCH_MP_TAC C3_VALZ THEN ASM_ARITH_TAC; ALL_TAC] THEN
  C3_STEPS_TO C3A_F26_EXEC 306 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[C3_ACC_STEP] THEN
  REWRITE_TAC[GSYM WORD_ADD; injectivity "wval"; CONS_11] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `(65536 + 512 * i) + 512 = 65536 + 512 * (i + 1) /\ 4 * i + 4 = 4 * (i + 1)`];;

let C3_F26_CHECK = prove(c3_check_tm,
  ENSURES_WHILE_UP_TAC `2048` `71` `306` c3_inv1 THEN REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    ENSURES_INIT_TAC "s0" THEN ABBREV_TAC `mm = read wmem s0` THEN C3_STEPS_TAC C3A_F26_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[C3_NSUM_LT_0; WORD_ADD_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    C3_BODY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(word (4 * i) = word 8192:int32)` ASSUME_TAC THENL
     [DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN
      SUBGOAL_THEN `val(word (4 * i):int32) = 4 * i /\ val(word 8192:int32) = 8192`
        (fun th -> REWRITE_TAC[th]) THENL
       [CONJ_TAC THEN MATCH_MP_TAC C3_VAL32 THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN ABBREV_TAC `mm = read wmem s0` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(word (4 * i) = word 8192:int32)`; BITVAL_CLAUSES]) THEN
    C3_STEPS_TAC C3A_F26_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN ABBREV_TAC `mm = read wmem s0` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `4 * 2048 = 8192`; BITVAL_CLAUSES]) THEN
    C3_STEPS_TAC C3A_F26_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[C3_NSUM_LT_2048]]);;
