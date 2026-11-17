(* C8p P6/P7 copy (2026-11-15) for the C7/C8b context: byte-identical to c8p_f33_c1.ml except the needs lines (C7 host file, c8p7 copies). *)
(* Vortex chain C8p rows P3/P4 (lane vortex-chain-20261111-142342, Claude Opus 5.5, 2026-11-15),
   layer C1: cell segment C1, pc 629 -> 1018 (the float formula through the select; join at 1018 with local 5 = va1_pd5b, closed per select branch). Stable layer: never edit; new files get new names. *)
needs "c8p7_f33_a.ml";;
let c8p_v1018 = c8p_vals_i @ [5,"F64","va1_pd5b " ^ CP6];;
let c8p_L1018 = "[0,1088,0; 0,1152,0; 0,431,0; 0,333,0; 0,1241,0]";;
let c8p_a1018 = c8p_mid ("read wstack s = [F64 (va1_pd5b " ^ CP6 ^ ")]") c8p_L1018 c8p_v1018;;
let C8P_SEG_C1 = prove(c8p_seg_goal 629 c8p_a629 1018 c8p_a1018, C8P_SEG_TAC 1018 [va1_pd5b]);;
