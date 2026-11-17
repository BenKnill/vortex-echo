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
(* ========================================================================= *)
(* Vortex chain, rung C3a, layer 3: f26 zeroing loops (C3A, Claude Opus 5.5, *)
(* 2026-11-13). Loop 2 (pc 556..646): 1024 x 6 eight-byte zero stores into   *)
(* RA RB JQ JP ZQ ZP; loop 3 (pc 652..716): 24576 x 4 into DI. Each loop is  *)
(* stated with a tight frame (its locals and its memory region only); the    *)
(* other memory atoms are carried around it later by the frame.              *)
(* ========================================================================= *)

let C3_VADD_MOD = prove
 (`!x y z. x + y = z + 4294967296 /\ z < 4294967296 ==> val(word_add (word x) (word y):int32) = z`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ONCE_REWRITE_TAC[ARITH_RULE `z + 4294967296 = 1 * 4294967296 + z`] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT]);;

let C3_WNZ = prove
 (`!x. 0 < x /\ x < 4294967296 ==> ~(word x:int32 = word 0)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int32->num`) THEN
  ASM_SIMP_TAC[C3_VAL32; VAL_WORD_0] THEN ASM_ARITH_TAC);;

let C3_W32S_EXT = prove
 (`!base n (g:num->int32) g' m. va1_w32s base n g m /\ (!k. k < n ==> g k = g' k) ==> va1_w32s base n g' m`,
  REWRITE_TAC[va1_w32s] THEN MESON_TAC[]);;

let C3_Z64_SETA = prove
 (`!base n (f:num->int32) c a m.
     va1_w32s base n f m /\ c + 1 < n /\ base + 4 * n <= 4294967296 /\ a = base + 4 * c
     ==> va1_w32s base n (\j. if j = c \/ j = c + 1 then word 0 else f j) (write (bytes64 (word a)) (word 0) m)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL5_W32S_Z64 THEN ASM_REWRITE_TAC[]);;

let C3_COND_ARITH_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC th) THEN REPEAT(POP_ASSUM MP_TAC) THEN ARITH_TAC;;

let C3_Z64X2 = prove
 (`!base n (f:num->int32) i a m.
     va1_w32s base n (\k. if k < 2 * i then word 0 else f k) m /\ 2 * i + 1 < n /\
     base + 4 * n <= 4294967296 /\ a = base + 8 * i
     ==> va1_w32s base n (\k. if k < 2 * (i + 1) then word 0 else f k) (write (bytes64 (word a)) (word 0) m)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC C3_W32S_EXT THEN
  EXISTS_TAC `\j. if j = 2 * i \/ j = 2 * i + 1 then word 0 else (\k. if k < 2 * i then word 0 else (f:num->int32) k) j` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC C3_Z64_SETA THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `k < 2 * i` THEN ASM_REWRITE_TAC[] THENL
     [COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `k = 2 * i \/ k = 2 * i + 1` THEN ASM_REWRITE_TAC[] THENL
     [COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
      COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC]]);;

let C3_Z64X4 = prove
 (`!base n (f:num->int32) i m.
     va1_w32s base n (\k. if k < 8 * i then word 0 else f k) m /\ 8 * i + 8 <= n /\
     base + 4 * n <= 4294967296
     ==> va1_w32s base n (\k. if k < 8 * (i + 1) then word 0 else f k)
          (write (bytes64 (word (base + 32 * i))) (word 0)
           (write (bytes64 (word (base + 32 * i + 8))) (word 0)
            (write (bytes64 (word (base + 32 * i + 16))) (word 0)
             (write (bytes64 (word (base + 32 * i + 24))) (word 0) m))))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `g0 = \k. if k < 8 * i then word 0 else (f:num->int32) k` THEN
  ABBREV_TAC `g1 = \j. if j = 8 * i + 6 \/ j = (8 * i + 6) + 1 then word 0 else (g0:num->int32) j` THEN
  ABBREV_TAC `g2 = \j. if j = 8 * i + 4 \/ j = (8 * i + 4) + 1 then word 0 else (g1:num->int32) j` THEN
  ABBREV_TAC `g3 = \j. if j = 8 * i + 2 \/ j = (8 * i + 2) + 1 then word 0 else (g2:num->int32) j` THEN
  ABBREV_TAC `g4 = \j. if j = 8 * i \/ j = 8 * i + 1 then word 0 else (g3:num->int32) j` THEN
  MATCH_MP_TAC C3_W32S_EXT THEN EXISTS_TAC `g4:num->int32` THEN CONJ_TAC THENL
   [EXPAND_TAC "g4" THEN MATCH_MP_TAC C3_Z64_SETA THEN
    REPEAT CONJ_TAC THEN TRY ARITH_TAC THEN TRY(ASM_ARITH_TAC) THEN
    EXPAND_TAC "g3" THEN MATCH_MP_TAC C3_Z64_SETA THEN
    REPEAT CONJ_TAC THEN TRY ARITH_TAC THEN TRY(ASM_ARITH_TAC) THEN
    EXPAND_TAC "g2" THEN MATCH_MP_TAC C3_Z64_SETA THEN
    REPEAT CONJ_TAC THEN TRY ARITH_TAC THEN TRY(ASM_ARITH_TAC) THEN
    EXPAND_TAC "g1" THEN MATCH_MP_TAC C3_Z64_SETA THEN
    REPEAT CONJ_TAC THEN TRY ARITH_TAC THEN TRY(ASM_ARITH_TAC) THEN
    EXPAND_TAC "g0" THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXPAND_TAC ["g4";"g3";"g2";"g1";"g0"] THEN REWRITE_TAC[] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MAP_EVERY ASM_CASES_TAC [`k = 8 * i`; `k = 8 * i + 1`; `k = 8 * i + 2`; `k = 8 * i + 3`;
                             `k = 8 * i + 4`; `k = 8 * i + 5`; `k = 8 * i + 6`; `k = 8 * i + 7`] THEN
    ASM_REWRITE_TAC[] THEN TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC) THEN
    REPEAT(COND_CASES_TAC THEN REWRITE_TAC[]) THEN ASM_ARITH_TAC]);;

(* ---- the two zeroing loops ------------------------------------------------ *)
let c3_z2 v = subst [v,`v:num->int32`] `\k. if k < 2 * i then word 0 else (v:num->int32) k`;;
let c3_inv2 = `\i s. read wcode s = va1_f26_mc /\ read wstatus s = WRunning /\ read wmemsize s = 4194304 /\
   read warity s = 1 /\ read wlabels s = [0,556,0; 0,726,0] /\
   read (wlocal 3) s = I32 (word (4294959104 + 8 * i)) /\ read (wlocal 0) s = I32 (r:int32) /\
   read wstack s = (if read wpc s = word 558 then [] else [I32 (word (4294959104 + 8 * i))]) /\
   va1_w32s 1130496 2048 (\k. if k < 2 * i then word 0 else (ra:num->int32) k) (read wmem s) /\
   va1_w32s 1138688 2048 (\k. if k < 2 * i then word 0 else (rb:num->int32) k) (read wmem s) /\
   va1_w32s 1146880 2048 (\k. if k < 2 * i then word 0 else (jq:num->int32) k) (read wmem s) /\
   va1_w32s 1155072 2048 (\k. if k < 2 * i then word 0 else (jp:num->int32) k) (read wmem s) /\
   va1_w32s 1163264 2048 (\k. if k < 2 * i then word 0 else (zq:num->int32) k) (read wmem s) /\
   va1_w32s 1171456 2048 (\k. if k < 2 * i then word 0 else (zp:num->int32) k) (read wmem s)`;;

let C3_LOOP2_FRAME = `MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wlocal 3] ,,
   MAYCHANGE [wmem :> bytes(word 1130496,49152)]`;;

let c3_loop2_tm = subst [C3_LOOP2_FRAME,`CF:wasmstate->wasmstate->bool`]
 `ensures wasm
   (\s. read wcode s = va1_f26_mc /\ read wpc s = word 556 /\ read wstatus s = WRunning /\
        read wmemsize s = 4194304 /\ read warity s = 1 /\ read wlabels s = [0,726,0] /\
        read wstack s = [] /\ read (wlocal 3) s = I32 (word 4294959104) /\ read (wlocal 0) s = I32 (r:int32) /\
        va1_w32s 1130496 2048 (ra:num->int32) (read wmem s) /\ va1_w32s 1138688 2048 (rb:num->int32) (read wmem s) /\
        va1_w32s 1146880 2048 (jq:num->int32) (read wmem s) /\ va1_w32s 1155072 2048 (jp:num->int32) (read wmem s) /\
        va1_w32s 1163264 2048 (zq:num->int32) (read wmem s) /\ va1_w32s 1171456 2048 (zp:num->int32) (read wmem s))
   (\s. read wcode s = va1_f26_mc /\ read wpc s = word 646 /\ read wstatus s = WRunning /\
        read wmemsize s = 4194304 /\ read warity s = 1 /\ read wlabels s = [0,726,0] /\
        read wstack s = [] /\ read (wlocal 0) s = I32 r /\
        va1_w32s 1130496 2048 (\k. word 0) (read wmem s) /\ va1_w32s 1138688 2048 (\k. word 0) (read wmem s) /\
        va1_w32s 1146880 2048 (\k. word 0) (read wmem s) /\ va1_w32s 1155072 2048 (\k. word 0) (read wmem s) /\
        va1_w32s 1163264 2048 (\k. word 0) (read wmem s) /\ va1_w32s 1171456 2048 (\k. word 0) (read wmem s))
   CF`;;

let C3_ALLZERO = prove
 (`!(f:num->int32) c n. n <= c ==> (!k. k < n ==> (if k < c then word 0 else f k) = word 0)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let C3_W32S_ALLZERO = prove
 (`!base n (f:num->int32) c m. va1_w32s base n (\k. if k < c then word 0 else f k) m /\ n <= c
     ==> va1_w32s base n (\k. word 0) m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC C3_W32S_EXT THEN
  EXISTS_TAC `\k. if k < c then word 0 else (f:num->int32) k` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let C3_LOOP_ENTRY_TAC =
  ENSURES_INIT_TAC "s0" THEN C3_STEPS_TAC C3A_F26_EXEC (1--1) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LT; ETA_AX] THEN
  REWRITE_TAC[ETA_AX];;

let C3_LOOP_BACK_TAC (c0:term) (st:term) (bound:term) =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN (subst [c0,`C0:num`; st,`ST:num`] `~(word (C0 + ST * i) = word 0:int32)`) ASSUME_TAC THENL
   [MATCH_MP_TAC C3_WNZ THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN
  C3_STEPS_TAC C3A_F26_EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let C3_W32S_ALLZERO2 = prove
 (`!base n (f:num->int32) c m. va1_w32s base n (\k. if k < c then word 0 else f k) m ==> n <= c
     ==> va1_w32s base n (\k. word 0) m`,
  MESON_TAC[C3_W32S_ALLZERO]);;

let C3_ALLZERO_TAC : tactic = fun (asl,w) ->
  let _,args = strip_comb w in
  let b = hd args and m = last args in
  let th = find (fun th -> let c = concl th in
     try let h,a = strip_comb c in fst(dest_const h) = "va1_w32s" && hd a = b && last a = m && c <> w
     with _ -> false) (map snd asl) in
  (MATCH_MP_TAC (MATCH_MP C3_W32S_ALLZERO2 th) THEN ARITH_TAC) (asl,w);;

let rec C3_CHAIN_TAC (zths:thm list) : tactic = fun g ->
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         MATCH_MP_TAC PL5_W32S_W64 THEN CONJ_TAC THENL [ALL_TAC; REPEAT CONJ_TAC THEN ASM_ARITH_TAC] THEN
         C3_CHAIN_TAC zths;
         FIRST (map (fun zth -> MATCH_MP_TAC zth THEN CONJ_TAC THENL [ALL_TAC; REPEAT CONJ_TAC THEN ASM_ARITH_TAC] THEN
                    C3_CHAIN_TAC zths) zths)] g;;

let C3_LOOP_EXIT_TAC (zw:thm) =
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[zw]) THEN
  C3_STEPS_TAC C3A_F26_EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN C3_ALLZERO_TAC;;

let C3_W2_EXIT = WORD_REDUCE_CONV `word (4294959104 + 8 * 1024):int32`;;
let C3_W3_EXIT = WORD_REDUCE_CONV `word (4294180864 + 32 * 24576):int32`;;

let C3_LOOP2 = prove(c3_loop2_tm,
  ENSURES_WHILE_UP_TAC `1024` `558` `643` c3_inv2 THEN REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    C3_LOOP_ENTRY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MAP_EVERY (fun (b,r) -> SUBGOAL_THEN
       (subst [mk_small_numeral b,`B:num`; mk_small_numeral r,`R:num`]
          `val(word_add (word (4294959104 + 8 * i)) (word B):int32) = R + 8 * i`)
       ASSUME_TAC THENL [MATCH_MP_TAC C3_VADD_MOD THEN ASM_ARITH_TAC; ALL_TAC])
      [1138688,1130496; 1179648,1171456; 1171456,1163264; 1163264,1155072; 1155072,1146880; 1146880,1138688] THEN
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN ABBREV_TAC `mm = read wmem s0` THEN
    C3_STEPS_TO C3A_F26_EXEC 643 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM WORD_ADD; ARITH_RULE `(4294959104 + 8 * i) + 8 = 4294959104 + 8 * (i + 1)`] THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN C3_CHAIN_TAC [C3_Z64X2];
    C3_LOOP_BACK_TAC `4294959104` `8` `1024`;
    C3_LOOP_EXIT_TAC C3_W2_EXIT]);;

let c3_inv3 = `\i s. read wcode s = va1_f26_mc /\ read wstatus s = WRunning /\ read wmemsize s = 4194304 /\
   read warity s = 1 /\ read wlabels s = [0,652,0; 0,726,0] /\
   read (wlocal 3) s = I32 (word (4294180864 + 32 * i)) /\ read (wlocal 0) s = I32 (r:int32) /\
   read wstack s = (if read wpc s = word 654 then [] else [I32 (word (4294180864 + 32 * i))]) /\
   va1_w32s 1179648 196608 (\k. if k < 8 * i then word 0 else (di:num->int32) k) (read wmem s)`;;

let C3_LOOP3_FRAME = `MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wlocal 3] ,,
   MAYCHANGE [wmem :> bytes(word 1179648,786432)]`;;

let c3_loop3_tm = subst [C3_LOOP3_FRAME,`CF:wasmstate->wasmstate->bool`]
 `ensures wasm
   (\s. read wcode s = va1_f26_mc /\ read wpc s = word 652 /\ read wstatus s = WRunning /\
        read wmemsize s = 4194304 /\ read warity s = 1 /\ read wlabels s = [0,726,0] /\
        read wstack s = [] /\ read (wlocal 3) s = I32 (word 4294180864) /\ read (wlocal 0) s = I32 (r:int32) /\
        va1_w32s 1179648 196608 (di:num->int32) (read wmem s))
   (\s. read wcode s = va1_f26_mc /\ read wpc s = word 716 /\ read wstatus s = WRunning /\
        read wmemsize s = 4194304 /\ read warity s = 1 /\ read wlabels s = [0,726,0] /\
        read wstack s = [] /\ read (wlocal 0) s = I32 r /\ va1_w32s 1179648 196608 (\k. word 0) (read wmem s))
   CF`;;

let C3_LOOP3 = prove(c3_loop3_tm,
  ENSURES_WHILE_UP_TAC `24576` `654` `713` c3_inv3 THEN REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    C3_LOOP_ENTRY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MAP_EVERY (fun (b,r) -> SUBGOAL_THEN
       (subst [mk_small_numeral b,`B:num`; r,`R:num`]
          `val(word_add (word (4294180864 + 32 * i)) (word B):int32) = R`)
       ASSUME_TAC THENL [MATCH_MP_TAC C3_VADD_MOD THEN ASM_ARITH_TAC; ALL_TAC])
      [1966104,`1179648 + 32 * i + 24`; 1966096,`1179648 + 32 * i + 16`;
       1966088,`1179648 + 32 * i + 8`; 1966080,`1179648 + 32 * i`] THEN
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN ABBREV_TAC `mm = read wmem s0` THEN
    C3_STEPS_TO C3A_F26_EXEC 713 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM WORD_ADD; ARITH_RULE `(4294180864 + 32 * i) + 32 = 4294180864 + 32 * (i + 1)`] THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC C3_Z64X4 THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    C3_LOOP_BACK_TAC `4294180864` `32` `24576`;
    C3_LOOP_EXIT_TAC C3_W3_EXIT]);;
