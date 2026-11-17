(* demo1 VORTEX lane staging split (2026-11-10): proof text moved verbatim out of ve_vk.ml so a layered basis can be *)
(* prepared in steps under the 1800 s preparation cap. ve_vk.ml needs ve_vk_g1, ve_vk_g2, ve_vk_g3 in order. *)
needs "ve_vort.ml";;
needs "ve_vk_tacs.ml";;
needs "ve_vk_stmts.ml";;

let VK_E2_GEN = vk_gen_prove (vk_e2_stmt vk_mcv) (VK_E2_TAC vk_mcv VK_GEN_EXEC);;
let VK_SEG4_GEN = vk_gen_prove (vk_seg4_stmt vk_mcv)
  (VK_SEG4_TAC vk_mcv VK_GEN_EXEC (UNDISCH VK_E2_GEN));;
let VK_B2_GEN = vk_gen_prove (vk_b2_stmt vk_mcv) (VK_B2_TAC vk_mcv VK_GEN_EXEC);;
