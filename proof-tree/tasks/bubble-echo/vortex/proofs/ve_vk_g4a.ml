(* demo1 VORTEX lane staging split (2026-11-10): proof text moved verbatim out of ve_vk.ml so a layered basis can be *)
(* prepared in steps under the 1800 s preparation cap. Load order (pass 3): g1, g3, g2a, g2b, g2, g4a, g4. *)
(* pass 3: the per-export instances and VK_SEG1_APPLY (verbatim); VK_SEG1_UNAPPLY is in ve_vk_g4.ml. *)
needs "ve_vk_g2.ml";;

let VK_SEG4_APPLY = vk_inst_code `ve_vort_apply_mc` VE_VK_APPLY_EXEC VK_SEG4_GEN;;
let VK_SEG4_UNAPPLY = vk_inst_code `ve_vort_unapply_mc` VE_VK_UNAPPLY_EXEC VK_SEG4_GEN;;
let VK_SEG2_APPLY = vk_inst_code `ve_vort_apply_mc` VE_VK_APPLY_EXEC VK_SEG2_GEN;;
let VK_SEG2_UNAPPLY = vk_inst_code `ve_vort_unapply_mc` VE_VK_UNAPPLY_EXEC VK_SEG2_GEN;;
let VK_SEG3_APPLY = vk_inst_code `ve_vort_apply_mc` VE_VK_APPLY_EXEC VK_SEG3_GEN;;
let VK_SEG3_UNAPPLY = vk_inst_code `ve_vort_unapply_mc` VE_VK_UNAPPLY_EXEC VK_SEG3_GEN;;

let VK_SEG1_APPLY = prove(vk_seg1_stmt `ve_vort_apply_mc` `1122304`,
  VK_SEG1_TAC `ve_vort_apply_mc` `1122304` VE_VK_APPLY_EXEC);;
