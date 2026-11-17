(* demo1 VORTEX lane staging split (2026-11-10): proof text moved verbatim out of ve_vk.ml so a layered basis can be *)
(* prepared in steps under the 1800 s preparation cap. Load order (2026-11-11, pass 3): g1, g3, g2a, g2b, g2, g4. *)
(* VK_SEG3_GEN does not use any SEG2 result, so it now follows g1 directly. *)
needs "ve_vk_g1.ml";;

let VK_SEG3_GEN = vk_gen_prove (vk_seg3_stmt vk_mcv) (VK_SEG3_TAC vk_mcv VK_GEN_EXEC);;
