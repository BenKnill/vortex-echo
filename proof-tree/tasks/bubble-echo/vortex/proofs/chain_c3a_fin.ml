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
(* ========================================================================= *)
(* Vortex chain, rung C3a, layer 6 (C3A, Claude Opus 5.5, 2026-11-13): the   *)
(* host-call form with its byte frame, the va1_bad lemmas (pure HOL) and the *)
(* satisfiability of both preconditions.                                     *)
(* ========================================================================= *)

(* ---- host call ------------------------------------------------------------ *)
let C3_B8_BYTES_OTHER = prove
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

let c3_tframe = rand(snd(dest_imp(snd(strip_forall(concl VA1_TICK_UNPUNCT)))));;
let c3_tf tm = vsubst [c3_tframe, `cf:wasmstate->wasmstate->bool`] tm;;
let C3_T_MEMSIZE = prove(c3_tf `!s s'. (cf:wasmstate->wasmstate->bool) s s' ==> read wmemsize s' = read wmemsize s`,
  C3_KEEPS_TAC C3_COMP_TAC);;
let C3_T_GLOBALS = prove(c3_tf `!s s'. (cf:wasmstate->wasmstate->bool) s s' ==> read wglobals s' = read wglobals s`,
  C3_KEEPS_TAC C3_COMP_TAC);;
let C3_T_KEEPS = prove(c3_tf `!s s'. (cf:wasmstate->wasmstate->bool) s s'
   ==> read wmemsize s' = read wmemsize s /\ read wglobals s' = read wglobals s`,
  MESON_TAC[C3_T_MEMSIZE; C3_T_GLOBALS]);;
let C3_T_BYTE = prove(c3_tf `!a. a < 4194304 /\ ~(16392 <= a /\ a < 16512) /\ ~(65536 <= a /\ a < 2039808)
     ==> !s s'. (cf:wasmstate->wasmstate->bool) s s'
                ==> read (wmem :> bytes8 (word a)) s' = read (wmem :> bytes8 (word a)) s`,
  GEN_TAC THEN STRIP_TAC THEN
  C3_KEEPS_TAC (C3_COMP_TAC THEN
    TRY(MATCH_MP_TAC C3_B8_BYTES_OTHER THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC)));;
let C3_T_FRAME_BYTES = prove(c3_tf `!s s'. (cf:wasmstate->wasmstate->bool) s s'
     ==> va1_unp_frame (read wmem s) (read wmem s')`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[va1_unp_frame] THEN
  X_GEN_TAC `a:num` THEN DISCH_TAC THEN
  MP_TAC(SPEC `a:num` C3_T_BYTE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:wasmstate`; `s':wasmstate`]) THEN
  ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE]);;

let VA1_HCALL_UNPUNCT = prove
 (`!fs gl p ap mdl N y hp tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32) h m.
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
     fs 10 = (va1_f10_mc,0,0) /\ fs 26 = (va1_f26_mc,0,1) /\ fs 28 = (va1_f28_mc,0,0) /\
     ~(p = word 4294967295) /\ ~(p = word 0) /\
     va1_st p p ap mdl N y hp tbl (ra,rb,jq,jp,di,zq,zp,nd) m /\ read (bytes32 (word 16404)) m = h
     ==> va1_hcall (wasmc fs) va1_tick_backward_mc [] (word 1)
           (\gl' m'. gl' = gl /\
                     va1_st (word_sub p (word 1)) (word 4294967295) ap mdl N (ve_fredkin_bwdn (\i. ve_vk mdl) 16 y)
                            (\k. if k < 24 then word 0 else hp k) (\k. word 0)
                            ((\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),word 0) m' /\
                     read (bytes32 (word 16404)) m' = word_add h (va1_bad mdl tbl (ra,rb,jq,jp,zq,zp,nd)) /\
                     va1_unp_frame m m') gl m`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `p:int32`; `ap:int32`; `mdl:num->int32`;
                `N:num`; `y:(num->int32)#(num->int32)`; `hp:num->int32`; `tbl:num->int32`;
                `ra:num->int32`; `rb:num->int32`; `jq:num->int32`; `jp:num->int32`; `di:num->int32`;
                `zq:num->int32`; `zp:num->int32`; `nd:int32`; `h:int32`] VA1_TICK_UNPUNCT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun lth ->
    let _,[step;pp;qq;cc] = strip_comb(concl lth) in
    let eth,dth = CONJ_PAIR VA1_TICKB_CALLEE in
    let code = rand(lhand(concl eth)) and e = rand(rand(concl eth))
    and decls = rand(rand(concl dth)) in
    MATCH_MP_TAC (ISPECL [step; code; e; decls; `[]:wval list`; `word 1:int32`; pp; qq; cc]
                    VA1_HCALL_ENSURES) THEN
    REWRITE_TAC[eth; dth; lth] THEN CONJ_TAC THENL
     [GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      ASM_REWRITE_TAC[WCALL_ENTRY_READS; LENGTH];
      REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
      MAP_EVERY (fun kth -> FIRST_ASSUM(MP_TAC o MATCH_MP kth) THEN
                            ASM_REWRITE_TAC[WCALL_ENTRY_READS; LENGTH] THEN DISCH_TAC)
        [C3_T_KEEPS; C3_T_FRAME_BYTES] THEN
      ASM_REWRITE_TAC[]]));;

(* ---- va1_bad (pure HOL) ---------------------------------------------------- *)
let VA1_BAD_PUNCT = prove
 (`!mdl tbl. va1_bad mdl tbl ((\k. word 251658), va1_rbinit tbl, (\k. word 0), (\k. word 0), (\k. word 0),
                            va1_zpseed mdl, word 0) = word 0`,
  REWRITE_TAC[va1_bad; va1_mis; BITVAL_CLAUSES; ADD_CLAUSES; NSUM_0; WORD_ADD_0]);;

let C3_BITVAL_LE1 = prove(`!b. bitval b <= 1`, GEN_TAC THEN REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN ARITH_TAC);;
let C3_MIS_LE6 = prove
 (`!mdl tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (zq:num->int32) (zp:num->int32) k.
     va1_mis mdl tbl (ra,rb,jq,jp,zq,zp) k <= 6`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_mis; bitval] THEN
  REPEAT COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV);;
let C3_SUM_LE = prove
 (`!mdl tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (zq:num->int32) (zp:num->int32).
     nsum (0..2047) (\k. va1_mis mdl tbl (ra,rb,jq,jp,zq,zp) k) <= 12288`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`0..2047`; `\k. va1_mis mdl tbl ((ra:num->int32),(rb:num->int32),(jq:num->int32),(jp:num->int32),(zq:num->int32),(zp:num->int32)) k`; `6`] NSUM_BOUND) THEN
  REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG; C3_MIS_LE6] THEN ARITH_TAC);;

let VA1_BAD_COUNT = prove
 (`!mdl tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32).
     val nd <= 16384
     ==> val (va1_bad mdl tbl (ra,rb,jq,jp,zq,zp,nd)) = val nd + nsum (0..2047) (\k. va1_mis mdl tbl (ra,rb,jq,jp,zq,zp) k)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[va1_bad] THEN
  MP_TAC(SPECL [`mdl:num->int32`; `tbl:num->int32`; `ra:num->int32`; `rb:num->int32`; `jq:num->int32`;
                `jp:num->int32`; `zq:num->int32`; `zp:num->int32`] C3_SUM_LE) THEN
  ABBREV_TAC `S = nsum (0..2047) (\k. va1_mis mdl tbl ((ra:num->int32),(rb:num->int32),(jq:num->int32),(jp:num->int32),(zq:num->int32),(zp:num->int32)) k)` THEN
  DISCH_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `S MOD 4294967296 = S` SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let VA1_BAD_ZERO_IFF = prove
 (`!mdl tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32).
     val nd <= 16384
     ==> (va1_bad mdl tbl (ra,rb,jq,jp,zq,zp,nd) = word 0 <=>
          nd = word 0 /\
          !k. k < 2048 ==> ra k = word 251658 /\ rb k = va1_rbinit tbl k /\ jq k = word 0 /\
                           jp k = word 0 /\ zq k = word 0 /\ zp k = va1_zpseed mdl k)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ_0] THEN ASM_SIMP_TAC[VA1_BAD_COUNT] THEN
  REWRITE_TAC[ADD_EQ_0; VAL_EQ_0] THEN AP_TERM_TAC THEN
  SIMP_TAC[NSUM_EQ_0_IFF; FINITE_NUMSEG; IN_NUMSEG; LE_0] THEN
  REWRITE_TAC[va1_mis; ADD_EQ_0; BITVAL_EQ_0] THEN
  REWRITE_TAC[ARITH_RULE `k <= 2047 <=> k < 2048`] THEN MESON_TAC[]);;

(* ---- satisfiability -------------------------------------------------------- *)
let C3_ST_H_SAT = prove
 (`!t p ap mdl N x hp tbl ps (h:int32). N <= 640 ==> ?m. va1_st t p ap mdl N x hp tbl ps m /\ read (bytes32 (word 16404)) m = h`,
  MAP_EVERY X_GEN_TAC
   [`t:int32`; `p:int32`; `ap:int32`; `mdl:num->int32`; `N:num`;
    `x:(num->int32)#(num->int32)`; `hp:num->int32`; `tbl:num->int32`] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`ra:num->int32`; `rb:num->int32`; `jq:num->int32`; `jp:num->int32`;
    `di:num->int32`; `zq:num->int32`; `zp:num->int32`; `nd:int32`; `h:int32`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC
   `\w. if w = 4098 then t:int32
        else if w = 4099 then p
        else if w = 4100 then nd
        else if w = 4101 then h
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

let VA1_UNPUNCT_SAT = prove
 (`(?fs:num->byte list#num#num. fs 10 = (va1_f10_mc,0,0) /\ fs 26 = (va1_f26_mc,0,1) /\ fs 28 = (va1_f28_mc,0,0)) /\
  (!gl p ap mdl N y hp tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32) h.
     N <= 640
     ==> ?s. read wcode s = va1_tick_backward_mc /\ read wpc s = word 3 /\ read wstatus s = WRunning /\
             read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
             read wmemsize s = 4194304 /\ read wglobals s = gl /\
             va1_st p p ap mdl N y hp tbl (ra,rb,jq,jp,di,zq,zp,nd) (read wmem s) /\
             read (bytes32 (word 16404)) (read wmem s) = h)`,
  CONJ_TAC THENL
   [EXISTS_TAC `\i. if i = 10 then (va1_f10_mc,0,0) else if i = 26 then (va1_f26_mc,0,1) else (va1_f28_mc,0,0)` THEN
    REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`p:int32`; `p:int32`; `ap:int32`; `mdl:num->int32`; `N:num`; `y:(num->int32)#(num->int32)`;
       `hp:num->int32`; `tbl:num->int32`; `(ra:num->int32),(rb:num->int32),(jq:num->int32),(jp:num->int32),(di:num->int32),(zq:num->int32),(zp:num->int32),(nd:int32)`;
       `h:int32`] C3_ST_H_SAT) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:int64->byte` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `write wmem (m:int64->byte) (write wglobals (gl:num->wval) (write wmemsize 4194304
                (write warity 1 (write wlabels [] (write wstack [] (write wstatus WRunning
                (write wpc (word 3) (write wcode va1_tick_backward_mc (ARB:wasmstate)))))))))` THEN
    CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN ASM_REWRITE_TAC[]]);;

let VA1_F26_SAT = prove
 (`!p ap mdl hp tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32) h.
     ?s. read wcode s = va1_f26_mc /\ read wpc s = word 5 /\ read wstatus s = WRunning /\
         read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
         read wmemsize s = 4194304 /\
         read wlocals s = wcall_locals [] [I32 (word 0); I32 (word 0); I32 (word 0); I32 (word 0); I32 (word 0); I64 (word 0)] /\
         va1_pop p ap (read wmem s) /\ va1_mdl mdl (read wmem s) /\
         read (bytes32 (word 16404)) (read wmem s) = h /\
         va1_w32s 16408 26 hp (read wmem s) /\ va1_w32s 65536 262144 tbl (read wmem s) /\
         va1_w32s 1130496 2048 ra (read wmem s) /\ va1_w32s 1138688 2048 rb (read wmem s) /\
         va1_w32s 1146880 2048 jq (read wmem s) /\ va1_w32s 1155072 2048 jp (read wmem s) /\
         va1_bs (di,zq,zp,nd) (read wmem s)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`word 0:int32`; `p:int32`; `ap:int32`; `mdl:num->int32`; `0`; `(\k:num. word 0:int32),(\k:num. word 0:int32)`;
       `hp:num->int32`; `tbl:num->int32`; `(ra:num->int32),(rb:num->int32),(jq:num->int32),(jp:num->int32),(di:num->int32),(zq:num->int32),(zp:num->int32),(nd:int32)`;
       `h:int32`] C3_ST_H_SAT) THEN
  REWRITE_TAC[LE_0; va1_st] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:int64->byte` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `write wmem (m:int64->byte) (write wlocals (wcall_locals [] [I32 (word 0); I32 (word 0); I32 (word 0); I32 (word 0); I32 (word 0); I64 (word 0)])
                (write wmemsize 4194304
                (write warity 1 (write wlabels [] (write wstack [] (write wstatus WRunning
                (write wpc (word 5) (write wcode va1_f26_mc (ARB:wasmstate)))))))))` THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN ASM_REWRITE_TAC[]);;
