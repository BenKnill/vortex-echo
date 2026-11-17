(* ========================================================================= *)
(* vortex-chain C8a row A8 (Claude Opus 5.5, 2026-11-15): the forward pop    *)
(* tick with named births, R3 form, on C8b's s2 layer (the _U call lemmas).  *)
(* C8A_BIRTH_EQ_L: va1_birth_eq gives the va1_birth_ok shape with the extra  *)
(*   conjunct L = va1_born ... inside ?L (VA1_BIRTH_EQ_OK's proof).          *)
(* VA1P_CALL_F13_N: the f13 call site from it (Q0_CALL_TAC, as VA1P_CALL_F13)*)
(*   and VA1P_CALL_F13_NU = C8B_GHOST_RULE of it (frame unchanged).          *)
(* VA1_TICK_FORWARD_POP_COND_NU: B5's run (pop_q2_forward.ml Q2_RUN_TAC with *)
(*   the _U call lemmas) with f13's call lemma replaced; at the end the      *)
(*   births term of the statement is shown equal to the call's L by          *)
(*   expanding the q2v abbreviations (Q2_FINAL_TAC's normal form), then B5's *)
(*   close.                                                                  *)
(* ========================================================================= *)

let C8A_BIRTH_EQ_L = prove(mk_imp(`va1_birth_eq`, parse_term c8a_birth_okn_body),
  REWRITE_TAC[va1_birth_eq] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`mdl:num->int32`; `hp:num->int32`; `tbl:num->int32`; `t:int32`; `p:int32`; `ap:int32`;
     `ra:num->int32`; `rb:num->int32`; `di:num->int32`; `zq:num->int32`; `zp:num->int32`; `nd:int32`; `decls:wval list`]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_POSTCONDITION_THM) THEN
  REWRITE_TAC[] THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `va1_born mdl hp tbl t ra rb zq zp nd` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC VA1_BORN_SHAPE THEN ASM_MESON_TAC[va1_log_ok]);;

let C8A_Q0_CONTRACT_IMP (impth:thm) (vars:term list) (ants:term list) (cth:thm) =
  let body = MP impth (ASSUME (lhand(concl impth))) in
  let dth = CONJUNCT2 cth in
  let decls = rand(rand(concl dth)) in
  let th1 = SPECL (vars @ [decls]) body in
  MP th1 (end_itlist CONJ (map ASSUME ants @ [dth]));;

let VA1P_CALL_F13_N = prove(parse_term c8a_f13n_stmt,
  Q0_CALL_TAC (C8A_Q0_CONTRACT_IMP C8A_BIRTH_EQ_L
                   [q0_mdl; q0_hp; q0_tbl; q0_t; q0_p; q0_ap; q0_ra; q0_rb; q0_di; q0_zq; q0_zp; q0_nd]
                   [`va1_pop_window t p`; `va1_log_ok t di nd`] VA1_F13_CALLEE)
    VA1_F13_CALLEE `13` `0` `1`);;

let VA1P_CALL_F13_NU = C8B_GHOST_RULE VA1P_CALL_F13_N;;

let Q2_CALLS_NU =
  [15,VA1P_CALL_F15_U; 21,VA1P_CALL_F21_U; 23,VA1P_CALL_F23_U; 17,VA1P_CALL_F17_U;
   19,VA1P_CALL_F19_U; 11,VA1P_CALL_F11_U; 13,VA1P_CALL_F13_NU; 9,VA1P_CALL_F9_U;
   27,VA1P_CALL_F27_U];;

(* the statement's births term = the f13 call's L (whose equation L = va1_born .. q2v.. is consumed) *)
let C8A_BIRTHS_TAC : tactic = fun (asl,w) ->
  let isb t = try let h,a = strip_comb t in fst(dest_const h) = "va1_born" && length a = 9 with Failure _ -> false in
  let bt = find_term isb w in
  let lv = `L:(num->int32)list` in
  FIRST_X_ASSUM(fun lth -> let c = concl lth in
    if is_eq c && lhs c = lv && isb (rhs c) then
      SUBGOAL_THEN (mk_eq(bt, lv)) SUBST1_TAC THENL
       [REWRITE_TAC[lth] THEN Q2_FINAL_TAC; ALL_TAC]
    else NO_TAC) (asl,w);;

let VA1_TICK_FORWARD_POP_COND_NU = prove
 (parse_term c8a_spec_VA1_TICK_FORWARD_POP_COND_NU,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP VA1_WINDOW_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP VA1_LOG_OK_DROP) THEN
  ENSURES_INIT_TAC "s0" THEN Q2_MEMNAME_TAC "mm0" THEN
  Q2_RUN_TAC VA1_TICK_FORWARD_EXEC Q2_CALLS_NU [] THEN
  ENSURES_FINAL_STATE_TAC THEN
  C8A_BIRTHS_TAC THEN
  ASM_REWRITE_TAC[] THEN
  W(fun (asl,w) ->
    let th = find (fun th -> let c = concl th in
               q2_is_head "va1_st" c && rand c = rand w) (map snd asl) in
    let ps = el 8 (snd(strip_comb(concl th))) in
    let lhs = el 8 (snd(strip_comb w)) in
    SUBGOAL_THEN (mk_eq(lhs,ps)) SUBST1_TAC THENL
     [Q2_FINAL_TAC; ACCEPT_TAC th]));;
