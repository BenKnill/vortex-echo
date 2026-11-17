(* demo1 VORTEX lane pass 3 (2026-11-11): VK_SEG2_GEN restructured so that the B1 loop (8-way unrolled acc := 0,  *)
(* pc 316 .. 431) is proved once instead of twice. VK_SEG2_TAC (ve_vk_tacs.ml) applies ENSURES_WHILE_UP_TAC to   *)
(* the same loop in its r = 0 and r <> 0 branches; the entry, body and back-edge subgoals are the same terms in   *)
(* both (they depend on the precondition, invariant, bounds and frame only, never on the branch postcondition).   *)
(* This file computes those subgoals by running the cheap setup steps of VK_SEG2_TAC (no symbolic execution),     *)
(* checks that both branches produce them (aconv conclusion, assumptions included), and proves the body here.    *)
(* ve_vk_g2b.ml proves entry and back edge; ve_vk_g2.ml proves VK_SEG2_GEN (statement unchanged:                 *)
(* vk_gen_prove (vk_seg2_stmt vk_mcv)) and closes those three subgoals with these theorems by ACCEPT_TAC.        *)
(* Load order: g1, g3, g2a, g2b, g2, g4.                                                                          *)
needs "ve_vk_g3.ml";;

(* VK_SEG2_TAC up to the N < 3 split, verbatim *)
let VK_SEG2_SETUP_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `q = (3 * N) DIV 8` THEN ABBREV_TAC `r = (3 * N) MOD 8` THEN
  SUBGOAL_THEN `8 * q + r = 3 * N /\ r < 8` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q";"r"] THEN MP_TAC(SPECL [`3 * N`; `8`] DIVISION) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `word_and (word (N * 3)) (word 7):int32 = word r /\
                word_and (word (N * 3)) (word 4294967288):int32 = word (8 * q) /\
                word_and (word (8 * (N * 3))) (word 4294967232):int32 = word (64 * q) /\
                val (word N:int32) = N`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VK_AND7; VK_ANDM8; VK_ANDM64] THEN
    REWRITE_TAC[ARITH_RULE `N * 3 = 3 * N`] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [AP_TERM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "q" THEN
      SUBST1_TAC(ARITH_RULE `64 = 8 * 8`) THEN SIMP_TAC[DIV_MULT2; ARITH_EQ];
      MATCH_MP_TAC CAP_VAL_WORD32 THEN VK_ARITH_TAC];
    ALL_TAC];;

(* the 1 <= q step after the N < 3 case, verbatim *)
let VK_SEG2_Q1_TAC : tactic =
  SUBGOAL_THEN `1 <= q` ASSUME_TAC THENL [VK_ARITH_TAC; ALL_TAC];;

(* the r <> 0 branch fact, verbatim *)
let VK_SEG2_RNZ_TAC : tactic =
  SUBGOAL_THEN `(word r:int32 = word 0) <=> F` ASSUME_TAC THENL
   [MATCH_MP_TAC VK_WORD_NE0 THEN VK_ARITH_TAC; ALL_TAC];;

(* the B1 loop rule as VK_SEG2_TAC applies it; subgoals: ~(q = 0), entry, body, back edge, exit *)
let VK_B1_WHILE_TAC : tactic =
  ENSURES_WHILE_UP_TAC `q:num` `316` `431` (vk_b1_inv vk_mcv) THEN REPEAT CONJ_TAC;;

let vk_goals (tac:tactic) (g:goal) = let (_,gs,_) = tac g in gs;;
let vk_goal1 name (tac:tactic) (g:goal) =
  match vk_goals tac g with [g'] -> g' | gs -> failwith (name ^ ": " ^ string_of_int (length gs) ^ " goals");;
let vk_nth name n (gs:goal list) =
  if length gs > n then el n gs else failwith (name ^ ": too few goals");;

let vk_time name f x =
  let t0 = Sys.time() in
  let y = f x in
  Printf.printf "VK_TIME %s %.1f s cpu\n%!" name (Sys.time() -. t0); y;;

(* the goal of VK_SEG2_TAC after setup, in the N >= 3 case, after 1 <= q (the vk_gen_prove goal is the bare     *)
(* statement: DISCH_THEN(K tac) drops the decode antecedent from the goal)                                       *)
let vk_seg2_main_goal =
  let g1 = vk_goal1 "setup" VK_SEG2_SETUP_TAC ([], vk_seg2_stmt vk_mcv) in
  let g2 = vk_nth "N<3" 1 (vk_goals (ASM_CASES_TAC `N < 3`) g1) in
  vk_goal1 "q1" VK_SEG2_Q1_TAC g2;;

(* the loop subgoals before the r split (assumptions: the common ones only) *)
let vk_b1_goals = vk_goals VK_B1_WHILE_TAC vk_seg2_main_goal;;

(* the loop subgoals inside each branch, exactly as VK_SEG2_TAC reaches them *)
let vk_b1_goals_r0 =
  vk_goals VK_B1_WHILE_TAC (vk_nth "r=0" 0 (vk_goals (ASM_CASES_TAC `r = 0`) vk_seg2_main_goal));;
let vk_b1_goals_rn =
  let g = vk_goal1 "rnz" VK_SEG2_RNZ_TAC (vk_nth "r<>0" 1 (vk_goals (ASM_CASES_TAC `r = 0`) vk_seg2_main_goal)) in
  let g' = vk_nth "seq440" 0
    (vk_goals (ENSURES_SEQUENCE_TAC `440` (vk_mid440 vk_mcv `8 * q` `r:num`) THEN CONJ_TAC) g) in
  vk_goals VK_B1_WHILE_TAC g';;

(* precheck (fails in seconds, before any symbolic execution): 5 subgoals each; for entry (1), body (2) and back *)
(* edge (3) the branch subgoal has the same conclusion (aconv) and contains every common assumption.             *)
let () =
  let n = length vk_b1_goals in
  if n <> 5 || length vk_b1_goals_r0 <> 5 || length vk_b1_goals_rn <> 5 then failwith "B1 precheck: goal count";
  List.iter (fun i ->
    let (asl,w) = el i vk_b1_goals in
    List.iter (fun (bname,bgs) ->
      let (basl,bw) = el i bgs in
      if not (aconv w bw) then failwith ("B1 precheck: conclusion differs, subgoal " ^ string_of_int i ^ " " ^ bname);
      List.iter (fun (_,th) ->
        if not (exists (fun (_,bth) -> aconv (concl th) (concl bth)) basl)
        then failwith ("B1 precheck: assumption missing, subgoal " ^ string_of_int i ^ " " ^ bname)) asl)
     ["r=0", vk_b1_goals_r0; "r<>0", vk_b1_goals_rn]) [1;2;3];
  Printf.printf "VK_B1 precheck OK: entry, body, back edge identical in both branches (%d common assumptions)\n%!"
    (length (fst (el 2 vk_b1_goals)));;

(* |- (common assumptions used) ==> body subgoal; hypotheses discharged here, re-introduced by UNDISCH_ALL in g2 *)
let VK_B1_BODY_GEN =
  vk_time "VK_B1_BODY_GEN" (fun () ->
    DISCH_ALL (TAC_PROOF(el 2 vk_b1_goals, VK_B1_BODY_TAC VK_GEN_EXEC))) ();;
