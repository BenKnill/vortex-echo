(* demo1 VORTEX lane staging split (2026-11-10), restructured in pass 3 (2026-11-11). VK_SEG2_GEN keeps its statement *)
(* (vk_gen_prove (vk_seg2_stmt vk_mcv), checked below). VK_SEG2_TAC2 is VK_SEG2_TAC (ve_vk_tacs.ml) step for step,    *)
(* except that the entry, body and back-edge subgoals of the B1 loop, which VK_SEG2_TAC proved in both the r = 0 and  *)
(* r <> 0 branches, are closed by ACCEPT_TAC with VK_B1_ENTRY_GEN / VK_B1_BODY_GEN / VK_B1_BACK_GEN (ve_vk_g2a.ml,     *)
(* ve_vk_g2b.ml): theorems whose hypotheses are assumptions present at that point (UNDISCH_ALL) and whose conclusion   *)
(* must be the subgoal (aconv; any other subgoal fails). Load order: g1, g3, g2a, g2b, g2, g4.                       *)
needs "ve_vk_g2b.ml";;

let VK_USE_TAC name (th:thm) : tactic = fun (asl,w as g) ->
  if aconv (concl th) w && forall (fun h -> exists (fun (_,a) -> aconv h (concl a)) asl || aconv h VK_DEC_H) (hyp th)
  then ACCEPT_TAC th g
  else failwith ("VK_USE_TAC " ^ name ^ ": not the proved subgoal");;

let VK_SEG2_TAC2 mc exec b2th entryth bodyth backth =
  VK_SEG2_SETUP_TAC THEN
  ASM_CASES_TAC `N < 3` THENL
   [SUBGOAL_THEN `q = 0 /\ r = 3 * N` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
     [MAP_EVERY EXPAND_TAC ["q";"r"] THEN CONJ_TAC THENL [MATCH_MP_TAC DIV_LT; MATCH_MP_TAC MOD_LT] THEN VK_ARITH_TAC;
      ALL_TAC] THEN
    ENSURES_SEQUENCE_TAC `440` (vk_mid440 mc `0` `3 * N`) THEN CONJ_TAC THENL
     [VK_B1_ENTRY_TAC exec 15 THEN REWRITE_TAC[LT];
      MP_TAC(SPECL [`N:num`; `XN:num->num->int32`; `0`; `3 * N`] b2th) THEN
      ANTS_TAC THENL [VK_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th -> VK_ENS_WEAKEN_TAC th (ASM_REWRITE_TAC[]) (ASM_REWRITE_TAC[]))];
    ALL_TAC] THEN
  VK_SEG2_Q1_TAC THEN
  ASM_CASES_TAC `r = 0` THENL
   [ENSURES_WHILE_UP_TAC `q:num` `316` `431` (vk_b1_inv mc) THEN REPEAT CONJ_TAC THENL
     [VK_ARITH_TAC; VK_USE_TAC "entry" entryth; VK_USE_TAC "body" bodyth; VK_USE_TAC "back" backth;
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
      VK_MSTEPS_TAC exec (1--5) THEN VK_FINAL_TAC THEN VK_CLOSE_TAC [] ALL_TAC];
    VK_SEG2_RNZ_TAC THEN
    ENSURES_SEQUENCE_TAC `440` (vk_mid440 mc `8 * q` `r:num`) THEN CONJ_TAC THENL
     [ENSURES_WHILE_UP_TAC `q:num` `316` `431` (vk_b1_inv mc) THEN REPEAT CONJ_TAC THENL
       [VK_ARITH_TAC; VK_USE_TAC "entry" entryth; VK_USE_TAC "body" bodyth; VK_USE_TAC "back" backth;
        ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
        VK_MSTEPS_TAC exec (1--6) THEN VK_FINAL_TAC THEN VK_CLOSE_TAC [] ALL_TAC];
      MP_TAC(SPECL [`N:num`; `XN:num->num->int32`; `8 * q`; `r:num`] b2th) THEN
      ANTS_TAC THENL [VK_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th -> VK_ENS_WEAKEN_TAC th (ASM_REWRITE_TAC[]) (ASM_REWRITE_TAC[]))]];;

let VK_SEG2_GEN =
  vk_time "VK_SEG2_GEN" (fun () -> vk_gen_prove (vk_seg2_stmt vk_mcv)
    (VK_SEG2_TAC2 vk_mcv VK_GEN_EXEC (UNDISCH VK_B2_GEN)
       (UNDISCH_ALL VK_B1_ENTRY_GEN) (UNDISCH_ALL VK_B1_BODY_GEN) (UNDISCH_ALL VK_B1_BACK_GEN))) ();;

(* the statement is the one VK_SEG2_TAC proved: no hypotheses, conclusion VK_DEC_H ==> vk_seg2_stmt vk_mcv *)
let () =
  if hyp VK_SEG2_GEN <> [] || not (aconv (concl VK_SEG2_GEN) (mk_imp(VK_DEC_H, vk_seg2_stmt vk_mcv)))
  then failwith "VK_SEG2_GEN: statement or hypotheses changed"
  else Printf.printf "VK_SEG2_GEN statement check OK (no hypotheses; VK_DEC_H ==> vk_seg2_stmt vk_mcv)\n%!";;
