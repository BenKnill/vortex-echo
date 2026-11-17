(* Vortex chain C8p rows P3/P4 (lane vortex-chain-20261111-142342, Claude Opus 5.5, 2026-11-15),
   layer D: cell segment D (store, pc 1152 -> 1187), VA1_P8_CELL (433 -> 1187), VA1_P8_INNER (128 cells), va1_p8_ov and VA1_P8_OUTER (2048 rows, to pc 1232; the table prefix at k = 2048 as va1_w32s). Stable layer: never edit; new files get new names. *)
needs "c8p_f33_c2.ml";;
let c8p_B pc stk lbl body vals tb =
  parse_term (Printf.sprintf
  "\\s. read wcode s = va1_puncture_mc /\\ read wpc s = word %d /\\ read wstatus s = WRunning /\\
   %s /\\ read wlabels s = %s /\\ read warity s = 1 /\\ read wmemsize s = 4194304 /\\
   read (wglobal 0) s = I32 (word 16288) /\\ read (wlocal 0) s = I32 a0 /\\ read (wlocal 1) s = I32 a1 /\\
   read (wlocal 2) s = I32 a2 /\\ read (wlocal 3) s = I32 (word 16288) /\\ %s /\\ va1_f33_frame m (read wmem s)%s%s"
   pc stk lbl body (c8p_vtext vals) (c8p_ttext tb));;
let c8p_vals_r = c8p_vals_o @ [24,"F64","va1_pr24 a0 a1 a2 k"; 25,"F64","va1_pr25 a0 a1 a2 k"; 26,"F64","va1_pr26 a0 a1 a2 k"; 27,"F64","word 0"];;
let c8p_inner_pre = c8p_B 431 "read wstack s = []" c5_L2 ("read (wlocal 4) s = I32 (word 0) /\\ " ^ c5_kbody) c8p_vals_r "128 * k";;
let c8p_inner_post = c8p_B 1190 "read wstack s = []" c5_L2 c5_kbody c8p_vals_o "128 * k + 128";;
let va1_p8_ov = new_definition (parse_term (
  "va1_p8_ov (a0:int32) (a1:int32) (a2:int32) (w:int32) (m:int64->byte) (k:num) (s:wasmstate) <=>
    read wcode s = va1_puncture_mc /\\ read wstatus s = WRunning /\\
    read wstack s = (if read wpc s = word 335 then [] else [I32 (word (bitval (~(word k = (word 2048:int32)))))]) /\\
    read wlabels s = [0,333,0; 0,1241,0] /\\ read warity s = 1 /\\ read wmemsize s = 4194304 /\\
    read (wglobal 0) s = I32 (word 16288) /\\ read (wlocal 0) s = I32 a0 /\\ read (wlocal 1) s = I32 a1 /\\
    read (wlocal 2) s = I32 a2 /\\ read (wlocal 3) s = I32 (word 16288) /\\
    read (wlocal 11) s = I32 (word (65536 + 512 * k)) /\\ read (wlocal 23) s = I32 (word k) /\\
    va1_f33_frame m (read wmem s)" ^ c8p_vtext c8p_vals_o ^ c8p_ttext "128 * k"));;
let c8p_vals_o0 = map (fun (l,c,t) -> if l = 22 then (l,c,"word 0") else (l,c,t)) c8p_vals_o;;
let c8p_outer_pre = c8p_B 333 "read wstack s = []" "[0,1241,0]"
  "read (wlocal 11) s = I32 (word 65536) /\\ read (wlocal 23) s = I32 (word 0)" c8p_vals_o0 "0";;
let c8p_main_post =
 parse_term ("\\s. read wcode s = va1_puncture_mc /\\ read wpc s = word 1232 /\\ read wstatus s = WRunning /\\
      read wstack s = [I32 a2; I32 a1; I32 a0] /\\ read wlabels s = [0,1241,0] /\\
      read warity s = 1 /\\ read wmemsize s = 4194304 /\\
      read (wglobal 0) s = I32 (word 16288) /\\ read (wlocal 3) s = I32 (word 16288) /\\
      va1_f33_frame m (read wmem s) /\\ va1_w32s 65536 262144 (va1_ptbl a0 a1 a2 w) (read wmem s)");;
let C8P_DCLOSE_TAC =
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[va1_p8_iv] THEN REPEAT CONJ_TAC THEN TRY C5_EX_TAC THEN
  ASM_REWRITE_TAC[VA1_C5_W4_ADD; C8P_CNTS] THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
  TRY(ASM_REWRITE_TAC[] THEN TRY COND_CASES_TAC THEN REWRITE_TAC[CONS_11; injectivity "wval"] THEN MESON_TAC[]) THEN
  TRY(MATCH_MP_TAC VA1_C5_FRAME_W32 THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC) THEN
  TRY(MATCH_MP_TAC C8P_TBL_STEP THEN ASM_REWRITE_TAC[]);;
let c8p_a1187 = `\s:wasmstate. va1_p8_iv a0 a1 a2 w m k (i + 1) s`;;
let C8P_SEG_D = prove(c8p_seg_goal 1152 c8p_a1152 1187 c8p_a1187,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C8P_SEG_INIT_TAC THEN
  MP_TAC(SPECL [`k:num`; `i:num`] VA1_C5_ADDR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C8P_DRIVE [1187] THEN C8P_DCLOSE_TAC);;
let VA1_P8_CELL = prove(c8p_cell_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C8P_SEQ_TAC 559 c8p_a559 THENL [MATCH_MP_TAC C8P_SEG_A THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  C8P_SEQ_TAC 629 c8p_a629 THENL [MATCH_MP_TAC C8P_SEG_B THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  C8P_SEQ_TAC 1018 c8p_a1018 THENL [MATCH_MP_TAC C8P_SEG_C1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  C8P_SEQ_TAC 1152 c8p_a1152 THENL
   [MATCH_MP_TAC C8P_SEG_C2 THEN ASM_REWRITE_TAC[]; MATCH_MP_TAC C8P_SEG_D THEN ASM_REWRITE_TAC[]]);;
let C8P_TB_ADD = ARITH_RULE `128 * (k + 1) = 128 * k + 128`;;
let C8P_CLOSE2_TAC extra =
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[va1_p8_iv; va1_p8_ov; va1_w32s] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CONJ_TAC THEN TRY C5_EX_TAC THEN
  ASM_REWRITE_TAC(VA1_C5_W4_ADD :: C8P_CNT0 :: ADD_0 :: extra) THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
  TRY C5_REFL_EX_TAC THEN
  TRY(ASM_REWRITE_TAC[] THEN TRY COND_CASES_TAC THEN REWRITE_TAC[CONS_11; injectivity "wval"] THEN MESON_TAC[]);;
let C8P_SEG_INIT2_TAC =
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[va1_p8_iv; va1_p8_ov]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_TAC o check (is_exists o concl))) THEN
  (fun (asl,w) -> let pth = find_read_th "wpc" `s0:wasmstate` (map snd asl) in
     RULE_ASSUM_TAC(fun th -> if can (find_term is_cond) (concl th) && not (is_forall (concl th)) then
        CONV_RULE(DEPTH_CONV WORD_RED_CONV) (REWRITE_RULE[pth] th) else th) (asl,w)) THEN
  ABBREV_TAC `mm = read wmem (s0:wasmstate)`;;
let C8P_CELL_USE_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `a0:int32`; `a1:int32`; `a2:int32`; `w:int32`; `m:int64->byte`; `k:num`; `i:num`] VA1_P8_CELL) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN REWRITE_TAC[SUBSUMED_REFL] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[va1_p8_iv]) THEN ASM_REWRITE_TAC[];;
let c8p_cell_frame = `MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocals] ,, MAYCHANGE [wglobal 0] ,, MAYCHANGE [wmem]`;;
let VA1_P8_INNER = prove
 (list_mk_forall([`fs:num->byte list#num#num`; `a0:int32`; `a1:int32`; `a2:int32`; `w:int32`; `m:int64->byte`; `k:num`],
   mk_imp(`fs 32 = (va1_f32_mc,2,1) /\ k < 2048`,
     list_mk_comb(`ensures (wasmc fs)`, [c8p_inner_pre; c8p_inner_post; c8p_cell_frame]))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_WHILE_UP_TAC `128` `433` `1187` `\i s. va1_p8_iv a0 a1 a2 w m k i s` THEN REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;
    C8P_SEG_INIT2_TAC THEN C8P_DRIVE [433] THEN C8P_CLOSE2_TAC [];
    C8P_CELL_USE_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(SPEC `i:num` VA1_C5_W4_NE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    C8P_SEG_INIT2_TAC THEN C8P_DRIVE [433] THEN C8P_CLOSE2_TAC [];
    C8P_SEG_INIT2_TAC THEN C5_NORM_ASM_TAC THEN C8P_DRIVE [1190] THEN C8P_CLOSE2_TAC []]);;
let c8p_fsa = [`fs:num->byte list#num#num`; `a0:int32`; `a1:int32`; `a2:int32`; `w:int32`; `m:int64->byte`];;
let VA1_P8_OUTER = prove
 (list_mk_forall(c8p_fsa,
   mk_imp(`fs 32 = (va1_f32_mc,2,1)`, list_mk_comb(`ensures (wasmc fs)`, [c8p_outer_pre; c8p_main_post; c8p_cell_frame]))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_WHILE_UP_TAC `2048` `335` `1223` `\k s. va1_p8_ov a0 a1 a2 w m k s` THEN REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;
    C8P_SEG_INIT2_TAC THEN C8P_DRIVE [335] THEN C8P_CLOSE2_TAC [];
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN C5_SEQQ_TAC c8p_inner_pre THENL
     [C8P_SEG_INIT2_TAC THEN C8P_DRIVE [431] THEN C8P_CLOSE2_TAC [va1_pr24; va1_pr25; va1_pr26; va1_prt; va1_prs; va1_prc];
      C5_SEQQ_TAC c8p_inner_post THENL
       [MP_TAC(SPECL (c8p_fsa @ [`k:num`]) VA1_P8_INNER) THEN ASM_REWRITE_TAC[];
        C8P_SEG_INIT2_TAC THEN C8P_DRIVE [1223] THEN C8P_CLOSE2_TAC [VA1_C5_W512_ADD; VA1_C5_K1_ADD; C8P_CNTS; C8P_TB_ADD]]];
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    MP_TAC(SPEC `k:num` VA1_C5_K_NE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    C8P_SEG_INIT2_TAC THEN C8P_DRIVE [335] THEN C8P_CLOSE2_TAC [];
    C8P_SEG_INIT2_TAC THEN C5_NORM_ASM_TAC THEN C8P_DRIVE [1232] THEN C8P_CLOSE2_TAC []]);;
