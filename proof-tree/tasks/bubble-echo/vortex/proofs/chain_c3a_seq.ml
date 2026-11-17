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
(* ========================================================================= *)
(* Vortex chain, rung C3a, layer 5: call sites (C3A, Claude Opus 5.5,        *)
(* 2026-11-13). f26 at a tick_backward call site (Q0_CALL_TAC of            *)
(* pop_q0_calls.ml, with VA1_F26_OK as the leaf), and the f28 / f10 call     *)
(* sites of pop_q0_calls.ml restated with the healErr word (16404, outside   *)
(* va1_st) carried as an extra conjunct.                                     *)
(* ========================================================================= *)

let c3_zero8 = `((\k. word 0):num->int32),((\k. word 0):num->int32),((\k. word 0):num->int32),((\k. word 0):num->int32),((\k. word 0):num->int32),((\k. word 0):num->int32),((\k. word 0):num->int32),(word 0:int32)`;;

let VA1P_CALL_F26 = prove
 (subst [c3_zero8,`Z8:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32`]
 `!fs mc cp gl t p ap mdl N x hp tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32) h.
     fs 26 = (va1_f26_mc,0,1) /\ cp < 2 EXP 64 /\ N <= 640 /\ ~(p = word 4294967295) /\
     wasm_decode mc cp = SOME (Wcall 26,6)
     ==> ensures (wasmc fs)
          (\s. read wcode s = mc /\ read wpc s = word cp /\ read wstatus s = WRunning /\ read wstack s = [] /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_st t p ap mdl N x hp tbl (ra,rb,jq,jp,di,zq,zp,nd) (read wmem s) /\
               read (bytes32 (word 16404)) (read wmem s) = h)
          (\s. read wcode s = mc /\ read wpc s = word (cp + 6) /\ read wstatus s = WRunning /\
               read wstack s = [I32 (va1_bad mdl tbl (ra,rb,jq,jp,zq,zp,nd))] /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_st t (word 4294967295) ap mdl N x (\k. if k < 24 then word 0 else hp k) tbl Z8 (read wmem s) /\
               read (bytes32 (word 16404)) (read wmem s) = word_add h (va1_bad mdl tbl (ra,rb,jq,jp,zq,zp,nd)))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wmem :> bytes(word 16396,116)] ,,
           MAYCHANGE [wmem :> bytes(word 1130496,835584)])`,
  let dth = CONJUNCT2 VA1_F26_CALLEE in
  let decls = rand(rand(concl dth)) in
  let lth = REWRITE_RULE[va1_bs]
    (MP (SPECL [`p:int32`; `ap:int32`; `mdl:num->int32`; `hp:num->int32`; `tbl:num->int32`;
                `ra:num->int32`; `rb:num->int32`; `jq:num->int32`; `jp:num->int32`; `di:num->int32`;
                `zq:num->int32`; `zp:num->int32`; `nd:int32`; `h:int32`; decls] VA1_F26_OK)
        (CONJ (ASSUME `~(p:int32 = word 4294967295)`) dth)) in
  Q0_CALL_TAC lth VA1_F26_CALLEE `26` `0` `1`);;

let VA1P_CALL_F28H = prove
 (`!fs mc cp gl t p ap mdl N x hp tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32) h.
     fs 28 = (va1_f28_mc,0,0) /\ cp < 2 EXP 64 /\ N <= 640 /\ wasm_decode mc cp = SOME (Wcall 28,6)
     ==> ensures (wasmc fs)
          (\s. read wcode s = mc /\ read wpc s = word cp /\ read wstatus s = WRunning /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_st t p ap mdl N x hp tbl (ra,rb,jq,jp,di,zq,zp,nd) (read wmem s) /\
               read (bytes32 (word 16404)) (read wmem s) = h)
          (\s. read wcode s = mc /\ read wpc s = word (cp + 6) /\ read wstatus s = WRunning /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_st (word_sub t (word 1)) p ap mdl N x hp tbl (ra,rb,jq,jp,di,zq,zp,nd) (read wmem s) /\
               read (bytes32 (word 16404)) (read wmem s) = h)
          (MAYCHANGE [wpc] ,, MAYCHANGE [wmem :> bytes(word 16392,4)])`,
  REWRITE_TAC[VA1_F28_IS_TICK_DEC] THEN
  Q0_CALL_TAC (SPEC `t:int32` VE_TICK_DEC_CORRECT) VE_TICK_DEC_CALLEE `28` `0` `0`);;

let VA1P_CALL_F10H = prove
 (`!fs mc cp gl t p ap mdl N x hp tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32) h.
     fs 10 = (va1_f10_mc,0,0) /\ cp < 2 EXP 64 /\ N <= 640 /\ mdl 1 = word N /\ 1 <= N /\ wasm_decode mc cp = SOME (Wcall 10,6)
     ==> ensures (wasmc fs)
          (\s. read wcode s = mc /\ read wpc s = word cp /\ read wstatus s = WRunning /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_st t p ap mdl N x hp tbl (ra,rb,jq,jp,di,zq,zp,nd) (read wmem s) /\
               read (bytes32 (word 16404)) (read wmem s) = h)
          (\s. read wcode s = mc /\ read wpc s = word (cp + 6) /\ read wstatus s = WRunning /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_st t p ap mdl N (ve_fredkin_bwd (ve_vk mdl) x) hp tbl (ra,rb,jq,jp,di,zq,zp,nd) (read wmem s) /\
               read (bytes32 (word 16404)) (read wmem s) = h)
          (MAYCHANGE [wpc] ,, MAYCHANGE [wmem :> bytes(word 1114112,16384)] ,,
           MAYCHANGE [wmem :> bytes(word 1966080,73728)])`,
  REWRITE_TAC[VA1_F10_IS_VORT_UNAPPLY] THEN
  Q0_CALL_TAC (Q0_VORT_LEAF VE_VORT_UNAPPLY_FREDKIN) VE_VORT_UNAPPLY_CALLEE `10` `0` `0`);;

(* ========================================================================= *)
(* tick_backward on the T = P path (layer 5 continued): pc 3..57 through the *)
(* f26 call (VA1Q1_RUN_TAC of pop_q1_untick.ml with the call sites above),   *)
(* the speed-table clear 57..121 (32768 x 4 eight-byte zero stores, under    *)
(* wasmc, the other memory atoms carried around it), then 121..WDone: f28,   *)
(* f10, the T >u P test (false: P = -1 now), 15 more f10, return 1.         *)
(* ========================================================================= *)

let C3C_STEP_TAC execth sname (asl,w) =
  let isval th = try let c = concl th in is_eq c && fst(dest_const(rator(lhs c))) = "val" with _ -> false in
  let mths = filter (fun th -> is_memfact (concl th) || isval th) (map snd asl) in
  (CAPC_STEP_TAC execth (READ_COMPONENT_COMPOSE :: VA1_GTU_MAX :: C3_COND_I64 :: mths) sname THEN
   CAP_DISCARD_OLD_TAC sname) (asl,w);;
let C3C_STEPS_TAC execth snums = MAP_EVERY (C3C_STEP_TAC execth) (statenames "s" snums);;
let rec C3C_STEPS_TO execth pc : tactic = fun (asl,w) ->
  let s = rand w in
  let cur = dest_small_numeral(rand(rhs(concl(find_read_th "wpc" s (map snd asl))))) in
  if cur = pc then ALL_TAC (asl,w) else
  let n = fst(dest_var s) in
  let k = int_of_string(String.sub n 1 (String.length n - 1)) + 1 in
  (C3C_STEP_TAC execth ("s"^string_of_int k) THEN C3C_STEPS_TO execth pc) (asl,w);;

let c3_invT = `\i s. read wcode s = va1_tick_backward_mc /\ read wstatus s = WRunning /\ read wmemsize s = 4194304 /\
   read warity s = 1 /\ read wglobals s = (gl:num->wval) /\ read wlabels s = [0,57,0; 0,131,0; 0,338,0] /\
   read (wlocal 0) s = I32 (word (4293918720 + 32 * i)) /\ read (wlocal 1) s = I32 (p:int32) /\
   read wstack s = (if read wpc s = word 59 then [] else [I32 (word (4293918720 + 32 * i))]) /\
   va1_w32s 65536 262144 (\k. if k < 8 * i then word 0 else (tbl:num->int32) k) (read wmem s)`;;

let C3_TLOOP_FRAME = `MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wlocal 0] ,,
   MAYCHANGE [wmem :> bytes(word 65536,1048576)]`;;

let c3_tloop_tm = subst [C3_TLOOP_FRAME,`CF:wasmstate->wasmstate->bool`]
 `ensures (wasmc fs)
   (\s. read wcode s = va1_tick_backward_mc /\ read wpc s = word 57 /\ read wstatus s = WRunning /\
        read wmemsize s = 4194304 /\ read warity s = 1 /\ read wglobals s = (gl:num->wval) /\
        read wlabels s = [0,131,0; 0,338,0] /\ read wstack s = [] /\
        read (wlocal 0) s = I32 (word 4293918720) /\ read (wlocal 1) s = I32 (p:int32) /\
        va1_w32s 65536 262144 (tbl:num->int32) (read wmem s))
   (\s. read wcode s = va1_tick_backward_mc /\ read wpc s = word 121 /\ read wstatus s = WRunning /\
        read wmemsize s = 4194304 /\ read warity s = 1 /\ read wglobals s = gl /\
        read wlabels s = [0,131,0; 0,338,0] /\ read wstack s = [] /\ read (wlocal 1) s = I32 p /\
        va1_w32s 65536 262144 (\k. word 0) (read wmem s))
   CF`;;

let C3_WT_EXIT = WORD_REDUCE_CONV `word (4293918720 + 32 * 32768):int32`;;

let C3_TLOOP = prove(c3_tloop_tm,
  ENSURES_WHILE_UP_TAC `32768` `59` `118` c3_invT THEN REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    ENSURES_INIT_TAC "s0" THEN C3C_STEPS_TAC VA1_TICK_BACKWARD_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LT; ETA_AX] THEN REWRITE_TAC[ETA_AX];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MAP_EVERY (fun (b,r) -> SUBGOAL_THEN
       (subst [mk_small_numeral b,`B:num`; r,`R:num`]
          `val(word_add (word (4293918720 + 32 * i)) (word B):int32) = R`)
       ASSUME_TAC THENL [MATCH_MP_TAC C3_VADD_MOD THEN ASM_ARITH_TAC; ALL_TAC])
      [1114136,`65536 + 32 * i + 24`; 1114128,`65536 + 32 * i + 16`;
       1114120,`65536 + 32 * i + 8`; 1114112,`65536 + 32 * i`] THEN
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN ABBREV_TAC `mm = read wmem s0` THEN
    C3C_STEPS_TO VA1_TICK_BACKWARD_EXEC 118 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM WORD_ADD; ARITH_RULE `(4293918720 + 32 * i) + 32 = 4293918720 + 32 * (i + 1)`] THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC C3_Z64X4 THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(word (4293918720 + 32 * i) = word 0:int32)` ASSUME_TAC THENL
     [MATCH_MP_TAC C3_WNZ THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN
    C3C_STEPS_TAC VA1_TICK_BACKWARD_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[C3_WT_EXIT]) THEN
    C3C_STEPS_TAC VA1_TICK_BACKWARD_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN C3_ALLZERO_TAC]);;

let C3_T_KEEP32 = prove(c3_keep32 65536 1114112 C3_TLOOP_FRAME, C3_KEEP32_TAC);;

let C3_CARRY2_TAC (kth:thm) : tactic =
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[va1_tick; va1_pop; va1_mdl; va1_vab; va1_bs; va1_w32s]) THEN
  REWRITE_TAC[va1_tick; va1_pop; va1_mdl; va1_vab; va1_bs; va1_w32s] THEN
  REPEAT CONJ_TAC THEN TRY(GEN_TAC THEN DISCH_TAC) THEN
  W(fun (asl,w) ->
    let a = rand(rand(rand(rator(lhs w)))) in
    MP_TAC(SPEC a kth) THEN ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> FIRST_ASSUM(fun cth -> REWRITE_TAC[MATCH_MP th cth])) THEN
    ASM_MESON_TAC[]);;

let c3_rT = subst [c3_zero8,`Z8:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32`]
 `\m. va1_tick (p:int32) m /\ va1_pop (word 4294967295) ap m /\ va1_mdl mdl m /\ va1_vab N y m /\
      va1_w32s 16408 26 (\k. if k < 24 then word 0 else (hp:num->int32) k) m /\
      va1_w32s 1130496 2048 (\k. word 0) m /\ va1_w32s 1138688 2048 (\k. word 0) m /\
      va1_w32s 1146880 2048 (\k. word 0) m /\ va1_w32s 1155072 2048 (\k. word 0) m /\
      va1_bs (((\k. word 0):num->int32),((\k. word 0):num->int32),((\k. word 0):num->int32),(word 0:int32)) m /\
      read (bytes32 (word 16404)) m = word_add h (va1_bad mdl tbl ((ra:num->int32),(rb:num->int32),(jq:num->int32),(jp:num->int32),(zq:num->int32),(zp:num->int32),(nd:int32)))`;;

let C3_S_TLOOP = prove
 (mk_imp(`N <= 640`,
   (let lth = C3_TLOOP in let _,[step;pp;qq;cc] = strip_comb(concl lth) in
    let s = `s:wasmstate` in
    let r = mk_abs(s, rhs(concl(BETA_CONV(mk_comb(c3_rT, mk_comb(`read wmem`, s)))))) in
    rand(concl(ISPECL [step;pp;qq;cc;r] C3_ENSURES_CARRY)))),
  DISCH_TAC THEN MATCH_MP_TAC C3_ENSURES_CARRY THEN CONJ_TAC THENL
   [ACCEPT_TAC C3_TLOOP; C3_CARRY2_TAC C3_T_KEEP32]);;

let C3_IMP2_TAC =
  GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[va1_st]) THEN REWRITE_TAC[va1_st] THEN ASM_REWRITE_TAC[];;
let C3_USE2_TAC (th:thm) : tactic =
  let p,q,c = c3_parts th in
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC c THEN CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC p THEN CONJ_TAC THENL [C3_IMP2_TAC; ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC q THEN CONJ_TAC THENL
   [C3_IMP2_TAC;
    FIRST [ACCEPT_TAC th;
           CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ACCEPT_TAC (CONV_RULE(TOP_DEPTH_CONV BETA_CONV) th)]];;

let C3_TCALLS = [26,VA1P_CALL_F26; 28,VA1P_CALL_F28H; 10,VA1P_CALL_F10H];;

let c3_m57 = subst [c3_zero8,`Z8:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32`]
 `\s. read wstatus s = WRunning /\ read wstack s = [] /\ read wmemsize s = 4194304 /\ read wglobals s = gl /\
      read warity s = 1 /\ read wlabels s = [0,131,0; 0,338,0] /\
      read (wlocal 0) s = I32 (word 4293918720) /\ read (wlocal 1) s = I32 p /\
      va1_st p (word 4294967295) ap mdl N y (\k. if k < 24 then word 0 else hp k) tbl Z8 (read wmem s) /\
      read (bytes32 (word 16404)) (read wmem s) = word_add h (va1_bad mdl tbl (ra,rb,jq,jp,zq,zp,nd))`;;
let c3_m121 = subst [c3_zero8,`Z8:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32`]
 `\s. read wstatus s = WRunning /\ read wstack s = [] /\ read wmemsize s = 4194304 /\ read wglobals s = gl /\
      read warity s = 1 /\ read wlabels s = [0,131,0; 0,338,0] /\ read (wlocal 1) s = I32 p /\
      va1_st p (word 4294967295) ap mdl N y (\k. if k < 24 then word 0 else hp k) (\k. word 0) Z8 (read wmem s) /\
      read (bytes32 (word 16404)) (read wmem s) = word_add h (va1_bad mdl tbl (ra,rb,jq,jp,zq,zp,nd))`;;

let VA1_TICK_UNPUNCT = prove
 (`!fs gl p ap mdl N y hp tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32) h.
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
     fs 10 = (va1_f10_mc,0,0) /\ fs 26 = (va1_f26_mc,0,1) /\ fs 28 = (va1_f28_mc,0,0) /\
     ~(p = word 4294967295) /\ ~(p = word 0)
     ==> ensures (wasmc fs)
          (\s. read wcode s = va1_tick_backward_mc /\ read wpc s = word 3 /\ read wstatus s = WRunning /\
               read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_st p p ap mdl N y hp tbl (ra,rb,jq,jp,di,zq,zp,nd) (read wmem s) /\
               read (bytes32 (word 16404)) (read wmem s) = h)
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 1)] /\
               va1_st (word_sub p (word 1)) (word 4294967295) ap mdl N (ve_fredkin_bwdn (\i. ve_vk mdl) 16 y)
                      (\k. if k < 24 then word 0 else hp k) (\k. word 0)
                      ((\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),word 0) (read wmem s) /\
               read (bytes32 (word 16404)) (read wmem s) = word_add h (va1_bad mdl tbl (ra,rb,jq,jp,zq,zp,nd)))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocal 0; wlocal 1] ,,
           MAYCHANGE [wmem :> bytes(word 16392,120)] ,, MAYCHANGE [wmem :> bytes(word 65536,1048576)] ,,
           MAYCHANGE [wmem :> bytes(word 1114112,851968)] ,, MAYCHANGE [wmem :> bytes(word 1966080,73728)])`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_SEQUENCE_TAC `57` c3_m57 THEN CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN VA1Q1_MEMNAME_TAC true "mm0" THEN
    VA1Q1_RUN_TAC VA1_TICK_BACKWARD_EXEC C3_TCALLS [57] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `121` c3_m121 THEN CONJ_TAC THENL
   [C3_USE2_TAC (MP C3_S_TLOOP (ASSUME `N <= 640`)); ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN VA1Q1_MEMNAME_TAC true "mm0" THEN
  VA1Q1_RUN_TAC VA1_TICK_BACKWARD_EXEC C3_TCALLS [] THEN
  ENSURES_FINAL_STATE_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV VA1_ITER_CONV) THEN ASM_REWRITE_TAC[]);;
