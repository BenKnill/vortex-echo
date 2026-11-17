(* Vortex chain C8p rows P3/P4 (lane vortex-chain-20261111-142342, Claude Opus 5.5, 2026-11-15),
   layer P: VA1_P8_PROLOGUE (entry -> pc 333 with the named prologue values, w = the model word at 16648) and C8P_F33_TO_F25_V (prologue then outer loop). Stable layer: never edit; new files get new names. *)
needs "c8p_f33_d.ml";;
let c8p_wm = `read (bytes32 (word 16648)) (m:int64->byte)`;;
let c8p_outer_pre_m = subst [c8p_wm, `w:int32`] c8p_outer_pre;;
let c8p_main_post_m = subst [c8p_wm, `w:int32`] c8p_main_post;;
let c8p_dP = [va1_pu0; va1_pu1; va1_pu2; va1_pnrm; va1_pe1x; va1_pe1y; va1_pe1z; va1_pe2x; va1_pe2y; va1_pe2z;
  va1_pg12; va1_pg13; va1_pg14; va1_pg15; va1_pw];;
let C8P_PRO_CLOSE_TAC =
  ENSURES_FINAL_STATE_TAC THEN REPEAT CONJ_TAC THEN TRY C5_EX_TAC THEN ASM_REWRITE_TAC[LT] THEN
  REPEAT(MATCH_MP_TAC VA1_C5_FRAME_W64 THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]) THEN
  REWRITE_TAC[VA1_C5_FRAME_REFL] THEN
  TRY(REWRITE_TAC(injectivity "wval" :: c8p_dP) THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN ASM_REWRITE_TAC[] THEN NO_TAC);;
let c8p_pro_hyp = `fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\
     read (bytes32 (word 16396)) m = word 4294967295 /\ ~(read (bytes32 (word 16392)) m = word 0) /\
     ~(a0:int32 = word 0 /\ a1:int32 = word 0 /\ a2:int32 = word 0)`;;
let VA1_P8_PROLOGUE = prove
 (list_mk_forall(c5_fsa,
   mk_imp(c8p_pro_hyp, list_mk_comb(`ensures (wasmc fs)`, [`va1_f33_pre a0 a1 a2 m`; c8p_outer_pre_m; c8p_cell_frame]))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN C5_PRE_TAC va1_f33_pre THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP VA1_C5_OR3 o check (fun th -> is_neg(concl th) && is_conj(rand(concl th)))) THEN
  C8P_DRIVE [333] THEN C8P_PRO_CLOSE_TAC);;
let C8P_F33_TO_F25_V = prove
 (list_mk_forall(c5_fsa,
   mk_imp(c8p_pro_hyp, list_mk_comb(`ensures (wasmc fs)`, [`va1_f33_pre a0 a1 a2 m`; c8p_main_post_m; c8p_cell_frame]))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C5_SEQQ_TAC c8p_outer_pre_m THENL
   [MP_TAC(SPECL c5_fsa VA1_P8_PROLOGUE) THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`fs:num->byte list#num#num`; `a0:int32`; `a1:int32`; `a2:int32`; c8p_wm; `m:int64->byte`] VA1_P8_OUTER) THEN
    ASM_REWRITE_TAC[]]);;
