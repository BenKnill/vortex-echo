(* demo1 VORTEX lane staging split (2026-11-10): proof text moved verbatim out of ve_vk.ml so a layered basis can be *)
(* prepared in steps under the 1800 s preparation cap. Load order (pass 3): g1, g3, g2a, g2b, g2, g4a, g4. *)
(* pass 3: VK_SEG1_UNAPPLY (verbatim); the instances and VK_SEG1_APPLY moved to ve_vk_g4a.ml. *)
needs "ve_vk_g4a.ml";;

let VK_SEG1_UNAPPLY = prove(vk_seg1_stmt `ve_vort_unapply_mc` `1114112`,
  VK_SEG1_TAC `ve_vort_unapply_mc` `1114112` VE_VK_UNAPPLY_EXEC);;
