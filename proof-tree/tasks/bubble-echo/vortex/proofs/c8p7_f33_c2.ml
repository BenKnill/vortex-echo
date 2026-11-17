(* C8p P6/P7 copy (2026-11-15) for the C7/C8b context: byte-identical to c8p_f33_c2.ml except the needs lines (C7 host file, c8p7 copies). *)
(* Vortex chain C8p rows P3/P4 (lane vortex-chain-20261111-142342, Claude Opus 5.5, 2026-11-15),
   layer C2: cell segment C2, pc 1018 -> 1152 (sign and range guards, the truncations; local 32 = va1_pcell). Stable layer: never edit; new files get new names. *)
needs "c8p7_f33_c1.ml";;
let c8p_a1152 = c8p_mid "read wstack s = []" c5_L3 c8p_v1152;;
let C8P_CLOSEW_TAC defs =
  ENSURES_FINAL_STATE_TAC THEN REPEAT CONJ_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(REWRITE_TAC(injectivity "wval" :: defs) THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(REWRITE_TAC defs THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN NO_TAC);;
let C8P_SEG_C2 = prove(c8p_seg_goal 1018 c8p_a1018 1152 c8p_a1152,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C8P_SEG_INIT_TAC THEN
  MP_TAC(SPECL [`k:num`; `i:num`] VA1_C5_ADDR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C8P_DRIVE [1152] THEN C8P_CLOSEW_TAC [va1_pcell; va1_pcp; va1_pcn]);;
