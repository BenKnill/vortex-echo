(* ========================================================================= *)
(* C8b rows B3-B6 (lane vortex-chain-20261111-142342, role c8b, Claude Opus  *)
(* 5.5, 2026-11-14): the pop ticks keep the unused vortex words.            *)
(* B3 VA1P_CALL_F9_U / F10_U: pop_q0_calls.ml's Q0_CALL_TAC on the B1       *)
(*    leaves; every other call-site lemma the R2/R3 runs use gets the       *)
(*    conjunct by C8B_GHOST_RULE (their frames avoid [1114112,1130496)).    *)
(* B4 VA1_TICK_POP_INVERSE_COND_U, B5 VA1_TICK_FORWARD_POP_COND_U: the runs *)
(*    of pop_q1_untick.ml / pop_q2_forward.ml with the _U call lemmas.      *)
(* B6 R4, R4b, R4c: the MATCH_MP_TAC chains of pop_r5_r4c_final.ml.          *)
(* ========================================================================= *)

(* the ghosted form of a statement !vs. A ==> ensures step P Q C *)
let c8b_ghost_tm (tm:term) =
  let vs, b = strip_forall tm in
  let n = find (fun v -> fst(dest_var v) = "N") vs in
  let uw = `uw:(num->int32)#(num->int32)` in
  let a, e = dest_imp b in
  let ens, args = strip_comb e in
  let [step;p;q;c] = args in
  let addc lam = let s,bd = dest_abs lam in
    mk_abs(s, mk_conj(bd, list_mk_comb(`va1_vabu`, [n; uw; mk_comb(`read wmem`, s)]))) in
  list_mk_forall(vs @ [uw], mk_imp(a, list_mk_comb(ens, [step; addc p; addc q; c])));;

(* ---- B3 ---- *)
let Q0_VORT_LEAF_U (th:thm) =
  let th1 = MP (SPEC `ve_vk` th) VE_VK_OK in
  let th2 = SPECL [`N:num`; `mdl:num->int32`; `FST (x:(num->int32)#(num->int32))`;
                   `SND (x:(num->int32)#(num->int32))`; `uw:(num->int32)#(num->int32)`] th1 in
  MP th2 (end_itlist CONJ (map ASSUME
    [`(mdl:num->int32) 1 = word N`; `1 <= N`; `N <= 640`]));;

let VA1P_CALL_F9_U = prove(parse_term c8b_spec_VA1P_CALL_F9_U,
  REWRITE_TAC[VA1_F9_IS_VORT_APPLY] THEN
  Q0_CALL_TAC (Q0_VORT_LEAF_U VE_VORT_APPLY_FREDKIN_U) VE_VORT_APPLY_CALLEE `9` `0` `0`);;

let VA1P_CALL_F10_U = prove(parse_term c8b_spec_VA1P_CALL_F10_U,
  REWRITE_TAC[VA1_F10_IS_VORT_UNAPPLY] THEN
  Q0_CALL_TAC (Q0_VORT_LEAF_U VE_VORT_UNAPPLY_FREDKIN_U) VE_VORT_UNAPPLY_CALLEE `10` `0` `0`);;

let VA1P_CALL_F11_U = C8B_GHOST_RULE VA1P_CALL_F11;;
let VA1P_CALL_F12_U = C8B_GHOST_RULE VA1P_CALL_F12;;
let VA1P_CALL_F13_U = C8B_GHOST_RULE VA1P_CALL_F13;;
let VA1P_CALL_F14_U = C8B_GHOST_RULE VA1P_CALL_F14;;
let VA1P_CALL_F15_U = C8B_GHOST_RULE VA1P_CALL_F15;;
let VA1P_CALL_F16_U = C8B_GHOST_RULE VA1P_CALL_F16;;
let VA1P_CALL_F17_U = C8B_GHOST_RULE VA1P_CALL_F17;;
let VA1P_CALL_F18_U = C8B_GHOST_RULE VA1P_CALL_F18;;
let VA1P_CALL_F19_U = C8B_GHOST_RULE VA1P_CALL_F19;;
let VA1P_CALL_F20_U = C8B_GHOST_RULE VA1P_CALL_F20;;
let VA1P_CALL_F21_U = C8B_GHOST_RULE VA1P_CALL_F21;;
let VA1P_CALL_F22_U = C8B_GHOST_RULE VA1P_CALL_F22;;
let VA1P_CALL_F23_U = C8B_GHOST_RULE VA1P_CALL_F23;;
let VA1P_CALL_F24_U = C8B_GHOST_RULE VA1P_CALL_F24;;
let VA1P_CALL_F27_U = C8B_GHOST_RULE VA1P_CALL_F27;;
let VA1P_CALL_F28_U = C8B_GHOST_RULE VA1P_CALL_F28;;

(* ---- B4: backward pop ---- *)
let VA1Q1_CALLS_U =
  [10,VA1P_CALL_F10_U; 12,VA1P_CALL_F12_U; 14,VA1P_CALL_F14_U; 16,VA1P_CALL_F16_U;
   18,VA1P_CALL_F18_U; 20,VA1P_CALL_F20_U; 22,VA1P_CALL_F22_U; 24,VA1P_CALL_F24_U;
   28,VA1P_CALL_F28_U];;

let VA1Q1_TICK_BACKWARD_POP_U = prove
 (c8b_ghost_tm va1q1_gen_tm,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP VA1_WINDOW_FACTS) THEN
  ENSURES_INIT_TAC "s0" THEN VA1Q1_MEMNAME_TAC true "mm0" THEN
  VA1Q1_RUN_TAC VA1_TICK_BACKWARD_EXEC VA1Q1_CALLS_U [] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  VA1Q1_CLOSE_TAC);;

let VA1_TICK_POP_INVERSE_COND_U = prove(parse_term c8b_spec_VA1_TICK_POP_INVERSE_COND_U,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP VA1_WINDOW_FACTS) THEN
  SUBGOAL_THEN `val (word_add nd (word (LENGTH (L:(num->int32)list))):int32) = val nd + LENGTH L`
    ASSUME_TAC THENL [MATCH_MP_TAC VA1Q1_VAL_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!zq' zp'. va1_unb (word_add t (word 1)) (val nd + LENGTH L)
                (va1_push L (va1_drop_fwd nd di,zq',zp',nd)) =
              (va1_drop_fwd nd di,zq',zp',nd)`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC VA1_PUSH_UNB_INVERSE THEN
    ASM_SIMP_TAC[VA1_LOG_OK_DROP]; ALL_TAC] THEN
  W(fun (asl,w) ->
     let _,[_;pre;_;_] = strip_comb w in
     let st = find (fun c -> va1q1_head c = "va1_st") (conjuncts(snd(dest_abs pre))) in
     let _,stargs = strip_comb st in
     let y = el 5 stargs and pf = el 8 stargs in
     let rec tl t = if is_pair t then let a,b = dest_pair t in a::tl b else [t] in
     let projs = tl(rand(concl(ISPEC pf VA1Q1_TUPLE8))) in
     let fv = frees w @ freesl(map (concl o snd) asl) in
     let gv n = find (fun v -> fst(dest_var v) = n) fv in
     let inst = map gv ["CK";"JK";"fs";"gl";"t";"p";"ap";"mdl";"N"] @ [y] @
                map gv ["hp";"tbl"] @ projs @ [gv "uw"] in
     MP_TAC(SPECL inst VA1Q1_TICK_BACKWARD_POP_U)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[va1_pop_fwd; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND; VA1_PUSH_ND] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    let _,[_;p0;q0;_] = strip_comb(concl th) in
    MATCH_MP_TAC ENSURES_PREPOSTCONDITION_THM THEN
    MAP_EVERY EXISTS_TAC [p0;q0] THEN
    CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL [ALL_TAC; ACCEPT_TAC th]]) THENL
   [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[PAIR];
    GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> va1q1_head(concl th) = "va1_st")) THEN
    REWRITE_TAC[FREDKIN_STEP_INVERSE] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[va1_pop_fwd; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[FST; SND; PAIR] THEN
    ASM_REWRITE_TAC[VA1_PUSH_ND; FST; SND; PAIR; VA1_DROP_INVERSE;
                    FREDKIN_STEP_INVERSE; KICK_DRIFT_INVERSE; KICK_DRIFT_STEPS_INVERSE]]);;

(* ---- B5: forward pop ---- *)
let Q2_CALLS_U =
  [15,VA1P_CALL_F15_U; 21,VA1P_CALL_F21_U; 23,VA1P_CALL_F23_U; 17,VA1P_CALL_F17_U;
   19,VA1P_CALL_F19_U; 11,VA1P_CALL_F11_U; 13,VA1P_CALL_F13_U; 9,VA1P_CALL_F9_U;
   27,VA1P_CALL_F27_U];;

let VA1_TICK_FORWARD_POP_COND_U = prove
 (parse_term c8b_spec_VA1_TICK_FORWARD_POP_COND_U,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP VA1_WINDOW_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP VA1_LOG_OK_DROP) THEN
  ENSURES_INIT_TAC "s0" THEN Q2_MEMNAME_TAC "mm0" THEN
  Q2_RUN_TAC VA1_TICK_FORWARD_EXEC Q2_CALLS_U [] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `L:(num->int32)list` THEN ASM_REWRITE_TAC[] THEN
  W(fun (asl,w) ->
    let th = find (fun th -> let c = concl th in
               q2_is_head "va1_st" c && rand c = rand w) (map snd asl) in
    let ps = el 8 (snd(strip_comb(concl th))) in
    let lhs = el 8 (snd(strip_comb w)) in
    SUBGOAL_THEN (mk_eq(lhs,ps)) SUBST1_TAC THENL
     [Q2_FINAL_TAC; ACCEPT_TAC th]));;

(* ---- B6: R4, R4b, R4c ---- *)
let VA1_TICK_POP_INVERSE_U = prove(parse_term c8b_spec_VA1_TICK_POP_INVERSE_U,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC VA1_TICK_POP_INVERSE_COND_U THEN
  ASM_REWRITE_TAC POP_Q3_R1_OKS);;

let VA1_TICK_FORWARD_POP_U = prove(parse_term c8b_spec_VA1_TICK_FORWARD_POP_U,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC VA1_TICK_FORWARD_POP_COND_U THEN
  ASM_REWRITE_TAC POP_Q3_R1_OKS);;

let VA1_TICK_POP_INVERSE_R5_U = prove(parse_term c8b_spec_VA1_TICK_POP_INVERSE_R5_U,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC VA1_TICK_POP_INVERSE_U THEN
  ASM_REWRITE_TAC[VA1_CORRK_OK; VA1_JIGK_OK]);;

let VA1_TICK_FORWARD_POP_R5_U = prove(parse_term c8b_spec_VA1_TICK_FORWARD_POP_R5_U,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC VA1_TICK_FORWARD_POP_U THEN
  ASM_REWRITE_TAC[VA1_CORRK_OK; VA1_JIGK_OK]);;

let VA1_TICK_FORWARD_POP_R5C_U = prove(parse_term c8b_spec_VA1_TICK_FORWARD_POP_R5C_U,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC VA1_TICK_FORWARD_POP_R5_U THEN
  ASM_REWRITE_TAC[VA1_BIRTH_OK]);;
