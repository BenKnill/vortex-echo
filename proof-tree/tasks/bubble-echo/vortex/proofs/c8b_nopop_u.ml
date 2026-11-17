(* ========================================================================= *)
(* C8b row B2 (lane vortex-chain-20261111-142342, role c8b, Claude Opus 5.5, *)
(* 2026-11-14): the no-pop ticks keep the unused vortex words.              *)
(* VA1_TICK_FORWARD/BACKWARD_NOPOP_VK_U = va1_seq_final2.ml's               *)
(* VA1_TICK_FORWARD/BACKWARD_NOPOP_VK with va1_vabu N uw in pre and post,   *)
(* by the same run (VA1_RUN_TAC) over call-site lemmas that carry it:       *)
(*   f9/f10 (vort): VA1_CALL_VA_U / VA1_CALL_VU_U, VA1_CALL_TAC on the B1   *)
(*   leaves VE_VORT_(UN)APPLY_FREDKIN_U;                                    *)
(*   f27/f28 (tick): C8B_GHOST_RULE on VA1_CALL_TI / VA1_CALL_TD (frame     *)
(*   bytes 16392..16395, disjoint from the unused words).                   *)
(* ========================================================================= *)

(* !vars. A ==> ensures step P Q C  |->  !vars uw. A ==> ensures step     *)
(* (\s. P s /\ va1_vabu N uw (read wmem s)) (likewise Q) C, beta-reduced    *)
let C8B_GHOST_RULE (th:thm) =
  let vars, body = strip_forall (concl th) in
  let ant = lhand body in
  let n = find (fun v -> fst(dest_var v) = "N") vars in
  let th1 = UNDISCH (SPECL vars th) in
  let th2 = CONV_RULE (TOP_DEPTH_CONV BETA_CONV) (C8B_GHOST n th1) in
  GENL (vars @ [`uw:(num->int32)#(num->int32)`]) (DISCH ant th2);;

let VA1_CALL_TI_U = C8B_GHOST_RULE VA1_CALL_TI;;
let VA1_CALL_TD_U = C8B_GHOST_RULE VA1_CALL_TD;;

let VA1_VORT_LEAF_U th =
  let vk = `VK:(num->int32)->(num->int32)->num->int32` in
  let th1 = MP (SPEC vk th) (ASSUME (mk_comb(`ve_vk_ok`,vk))) in
  let th2 = SPECL [`N:num`; `mdl:num->int32`; `FST (x:(num->int32)#(num->int32))`;
                   `SND (x:(num->int32)#(num->int32))`; `uw:(num->int32)#(num->int32)`] th1 in
  MP th2 (end_itlist CONJ (map ASSUME
    [`(mdl:num->int32) 1 = word N`; `1 <= N`; `N <= 640`]));;

let VA1_CALL_VA_U = prove
 (`!VK fs mc p gl t pt ap mdl N x (uw:(num->int32)#(num->int32)).
     ve_vk_ok VK /\ mdl 1 = word N /\ 1 <= N /\
     fs 9 = (ve_vort_apply_mc,0,0) /\ p < 2 EXP 64 /\ N <= 640 /\
     wasm_decode mc p = SOME (Wcall 9,6)
     ==> ensures (wasmc fs)
          (\s. read wcode s = mc /\ read wpc s = word p /\ read wstatus s = WRunning /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_tick t (read wmem s) /\ va1_pop pt ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\ va1_vab N x (read wmem s) /\
               va1_vabu N uw (read wmem s))
          (\s. read wcode s = mc /\ read wpc s = word (p + 6) /\ read wstatus s = WRunning /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_tick t (read wmem s) /\ va1_pop pt ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\
               va1_vab N (ve_fredkin_fwd (VK mdl) x) (read wmem s) /\
               va1_vabu N uw (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wmem :> bytes(word 1114112,16384)] ,,
           MAYCHANGE [wmem :> bytes(word 1966080,73728)])`,
  VA1_CALL_TAC (VA1_VORT_LEAF_U VE_VORT_APPLY_FREDKIN_U) VE_VORT_APPLY_CALLEE `9`);;

let VA1_CALL_VU_U = prove
 (`!VK fs mc p gl t pt ap mdl N x (uw:(num->int32)#(num->int32)).
     ve_vk_ok VK /\ mdl 1 = word N /\ 1 <= N /\
     fs 10 = (ve_vort_unapply_mc,0,0) /\ p < 2 EXP 64 /\ N <= 640 /\
     wasm_decode mc p = SOME (Wcall 10,6)
     ==> ensures (wasmc fs)
          (\s. read wcode s = mc /\ read wpc s = word p /\ read wstatus s = WRunning /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_tick t (read wmem s) /\ va1_pop pt ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\ va1_vab N x (read wmem s) /\
               va1_vabu N uw (read wmem s))
          (\s. read wcode s = mc /\ read wpc s = word (p + 6) /\ read wstatus s = WRunning /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_tick t (read wmem s) /\ va1_pop pt ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\
               va1_vab N (ve_fredkin_bwd (VK mdl) x) (read wmem s) /\
               va1_vabu N uw (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wmem :> bytes(word 1114112,16384)] ,,
           MAYCHANGE [wmem :> bytes(word 1966080,73728)])`,
  VA1_CALL_TAC (VA1_VORT_LEAF_U VE_VORT_UNAPPLY_FREDKIN_U) VE_VORT_UNAPPLY_CALLEE `10`);;

(* the generic-VK no-pop ticks (va1_seq_final2.ml's proofs, _U callees) *)
let C8B_TICK_FORWARD_NOPOP_U = prove
 (`!VK fs gl t ap mdl N x (uw:(num->int32)#(num->int32)).
     ve_vk_ok VK /\ mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
     fs 9 = (ve_vort_apply_mc,0,0) /\ fs 27 = (ve_tick_inc_mc,0,0) /\
     (ap = word 0 \/ ~(ap = word_add t (word 1)))
     ==> ensures (wasmc fs)
          (\s. read wcode s = va1_tick_forward_mc /\ read wpc s = word 3 /\
               read wstatus s = WRunning /\ read wstack s = [] /\
               read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_tick t (read wmem s) /\
               va1_pop (word 4294967295) ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\ va1_vab N x (read wmem s) /\
               va1_vabu N uw (read wmem s))
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 1)] /\
               va1_tick (word_add t (word 1)) (read wmem s) /\
               va1_pop (word 4294967295) ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\
               va1_vab N (ve_fredkin_fwdn (\i. VK mdl) 16 x) (read wmem s) /\
               va1_vabu N uw (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
           MAYCHANGE [wstatus] ,, MAYCHANGE [wlocal 0; wlocal 1; wlocal 2] ,,
           MAYCHANGE [wmem :> bytes(word 16392,4)] ,,
           MAYCHANGE [wmem :> bytes(word 1114112,16384)] ,,
           MAYCHANGE [wmem :> bytes(word 1966080,73728)])`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN VA1_MEMNAME_TAC "mm0" THEN
  VA1_RUN_TAC VA1_TICK_FORWARD_EXEC [9,VA1_CALL_VA_U; 27,VA1_CALL_TI_U] [273] THEN
  ASM_CASES_TAC `ap:int32 = word 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC;
    SUBGOAL_THEN `~(word_add t (word 1) = ap:int32)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC]] THEN
  VA1_RUN_TAC VA1_TICK_FORWARD_EXEC [9,VA1_CALL_VA_U; 27,VA1_CALL_TI_U] [] THEN
  ENSURES_FINAL_STATE_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV VA1_ITER_CONV) THEN ASM_REWRITE_TAC[]);;

let C8B_TICK_BACKWARD_NOPOP_U = prove
 (`!VK fs gl u ap mdl N y (uw:(num->int32)#(num->int32)).
     ve_vk_ok VK /\ mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
     fs 10 = (ve_vort_unapply_mc,0,0) /\ fs 28 = (ve_tick_dec_mc,0,0) /\
     ~(u = word 0)
     ==> ensures (wasmc fs)
          (\s. read wcode s = va1_tick_backward_mc /\ read wpc s = word 3 /\
               read wstatus s = WRunning /\ read wstack s = [] /\
               read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_tick u (read wmem s) /\
               va1_pop (word 4294967295) ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\ va1_vab N y (read wmem s) /\
               va1_vabu N uw (read wmem s))
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 1)] /\
               va1_tick (word_sub u (word 1)) (read wmem s) /\
               va1_pop (word 4294967295) ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\
               va1_vab N (ve_fredkin_bwdn (\i. VK mdl) 16 y) (read wmem s) /\
               va1_vabu N uw (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
           MAYCHANGE [wstatus] ,, MAYCHANGE [wlocal 0; wlocal 1] ,,
           MAYCHANGE [wmem :> bytes(word 16392,4)] ,,
           MAYCHANGE [wmem :> bytes(word 1114112,16384)] ,,
           MAYCHANGE [wmem :> bytes(word 1966080,73728)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN VA1_MEMNAME_TAC "mm0" THEN
  VA1_RUN_TAC VA1_TICK_BACKWARD_EXEC [10,VA1_CALL_VU_U; 28,VA1_CALL_TD_U] [] THEN
  ENSURES_FINAL_STATE_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV VA1_ITER_CONV) THEN ASM_REWRITE_TAC[]);;

let VA1_TICK_FORWARD_NOPOP_VK_U = prove
 (parse_term c8b_spec_VA1_TICK_FORWARD_NOPOP_VK_U,
  REWRITE_TAC[VA1_F9_IS_VORT_APPLY; VA1_F27_IS_TICK_INC] THEN
  VA1_VK_TAC C8B_TICK_FORWARD_NOPOP_U);;

let VA1_TICK_BACKWARD_NOPOP_VK_U = prove
 (parse_term c8b_spec_VA1_TICK_BACKWARD_NOPOP_VK_U,
  REWRITE_TAC[VA1_F10_IS_VORT_UNAPPLY; VA1_F28_IS_TICK_DEC] THEN
  VA1_VK_TAC C8B_TICK_BACKWARD_NOPOP_U);;
