(* demo1 VORTEX lane pass 3 (2026-11-11): entry (pc 266 .. 316, 28 steps) and back edge of the B1 loop of segment 2, *)
(* proved once for both branches of VK_SEG2_TAC (subgoals computed and checked in ve_vk_g2a.ml). Tactics verbatim.   *)
(* Load order: g1, g3, g2a, g2b, g2, g4.                                                                              *)
needs "ve_vk_g2a.ml";;

let VK_B1_ENTRY_GEN =
  vk_time "VK_B1_ENTRY_GEN" (fun () ->
    DISCH_ALL (TAC_PROOF(el 1 vk_b1_goals, VK_B1_ENTRY_TAC VK_GEN_EXEC 28))) ();;

let VK_B1_BACK_GEN =
  vk_time "VK_B1_BACK_GEN" (fun () ->
    DISCH_ALL (TAC_PROOF(el 3 vk_b1_goals, VK_B1_BACK_TAC VK_GEN_EXEC))) ();;
