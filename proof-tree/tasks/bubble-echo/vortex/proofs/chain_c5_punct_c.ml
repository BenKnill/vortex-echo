(* ========================================================================= *)
(* Vortex chain rung C5 part 2c (lane vortex-chain-20261111-142342 c5, Claude *)
(* Opus 5.5, 2026-11-13), layer C: the f33 table loops and VA1_F33_TO_F25.   *)
(* VA1_C5_INNER: the 128-cell inner loop, pc 431 -> 1190, by                 *)
(* ENSURES_WHILE_UP_TAC with invariant va1_c5_iv and body VA1_C5_CELL.       *)
(* va1_c5_ov and VA1_C5_OUTER: the 2048-row outer loop, pc 333 -> 1232,      *)
(* including the tail (end, three local.get) up to the call 25 instruction.  *)
(* VA1_C5_PROLOGUE: entry pc 17 -> 333 (f34 call, four f32 calls inline);    *)
(* its memory frame uses VA1_C5_FRAME_W64. Stable layer: never edit.         *)
(* ========================================================================= *)
needs "chain_c5_punct_b.ml";;
let VA1_C5_W512_ADD = prove
 (`!k. word_add (word (65536 + 512 * k)) (word 512):int32 = word (65536 + 512 * (k + 1))`,
  GEN_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC);;
let VA1_C5_K1_ADD = prove
 (`!k. word_add (word k) (word 1):int32 = word (k + 1)`,
  REWRITE_TAC[GSYM WORD_ADD]);;
let c5_B pc stk lbl body fl =
  parse_term (Printf.sprintf
  "\\s. read wcode s = va1_puncture_mc /\\ read wpc s = word %d /\\ read wstatus s = WRunning /\\
   %s /\\ read wlabels s = %s /\\ read warity s = 1 /\\ read wmemsize s = 4194304 /\\
   read (wglobal 0) s = I32 (word 16288) /\\ read (wlocal 0) s = I32 a0 /\\ read (wlocal 1) s = I32 a1 /\\
   read (wlocal 2) s = I32 a2 /\\ read (wlocal 3) s = I32 (word 16288) /\\ %s /\\ va1_f33_frame m (read wmem s)%s"
   pc stk lbl body
   (String.concat "" (map (fun l -> Printf.sprintf " /\\ (?v. read (wlocal %d) s = F64 v)" l) fl)));;
let c5_L2 = "[0,333,0; 0,1241,0]";;
let c5_outer_f64 = [8;9;10;12;13;14;15;16;17;18;19;20;21;22];;
let c5_kbody = "read (wlocal 11) s = I32 (word (65536 + 512 * k)) /\\ read (wlocal 23) s = I32 (word k)";;
let c5_inner_pre = c5_B 431 "read wstack s = []" c5_L2 ("read (wlocal 4) s = I32 (word 0) /\\ " ^ c5_kbody) c5_inner_f64;;
let c5_inner_post = c5_B 1190 "read wstack s = []" c5_L2 c5_kbody c5_outer_f64;;
let C5_CLOSE2_TAC extra =
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[va1_c5_iv] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CONJ_TAC THEN TRY C5_EX_TAC THEN
  ASM_REWRITE_TAC(VA1_C5_W4_ADD :: extra) THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
  TRY C5_REFL_EX_TAC THEN
  TRY(ASM_REWRITE_TAC[] THEN TRY COND_CASES_TAC THEN REWRITE_TAC[CONS_11; injectivity "wval"] THEN MESON_TAC[]);;
let C5_NORM_ASM_TAC = RULE_ASSUM_TAC(CONV_RULE(NUM_REDUCE_CONV THENC DEPTH_CONV WORD_RED_CONV) o REWRITE_RULE[BITVAL_CLAUSES]);;
let C5_CELL_USE_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `a0:int32`; `a1:int32`; `a2:int32`; `m:int64->byte`; `k:num`; `i:num`] VA1_C5_CELL) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN REWRITE_TAC[SUBSUMED_REFL] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[va1_c5_iv]) THEN ASM_REWRITE_TAC[];;
let VA1_C5_INNER = prove
 (list_mk_forall([`fs:num->byte list#num#num`; `a0:int32`; `a1:int32`; `a2:int32`; `m:int64->byte`; `k:num`],
   mk_imp(`fs 32 = (va1_f32_mc,2,1) /\ k < 2048`,
     list_mk_comb(`ensures (wasmc fs)`, [c5_inner_pre; c5_inner_post; c5_cell_frame]))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_WHILE_UP_TAC `128` `433` `1187` `\i s. va1_c5_iv a0 a1 a2 m k i s` THEN REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;
    C5_SEG_INIT_TAC THEN C5_DRIVE4 [433] THEN C5_CLOSE2_TAC [];
    C5_CELL_USE_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(SPEC `i:num` VA1_C5_W4_NE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    C5_SEG_INIT_TAC THEN C5_DRIVE4 [433] THEN C5_CLOSE2_TAC [];
    C5_SEG_INIT_TAC THEN C5_NORM_ASM_TAC THEN C5_DRIVE4 [1190] THEN C5_CLOSE2_TAC []]);;

let va1_c5_ov = new_definition
 `va1_c5_ov (a0:int32) (a1:int32) (a2:int32) (m:int64->byte) (k:num) (s:wasmstate) <=>
    read wcode s = va1_puncture_mc /\ read wstatus s = WRunning /\
    read wstack s = (if read wpc s = word 335 then [] else [I32 (word (bitval (~(word k = (word 2048:int32)))))]) /\
    read wlabels s = [0,333,0; 0,1241,0] /\ read warity s = 1 /\ read wmemsize s = 4194304 /\
    read (wglobal 0) s = I32 (word 16288) /\ read (wlocal 0) s = I32 a0 /\ read (wlocal 1) s = I32 a1 /\
    read (wlocal 2) s = I32 a2 /\ read (wlocal 3) s = I32 (word 16288) /\
    read (wlocal 11) s = I32 (word (65536 + 512 * k)) /\ read (wlocal 23) s = I32 (word k) /\
    va1_f33_frame m (read wmem s) /\
    (?v. read (wlocal 8) s = F64 v) /\ (?v. read (wlocal 9) s = F64 v) /\ (?v. read (wlocal 10) s = F64 v) /\
    (?v. read (wlocal 12) s = F64 v) /\ (?v. read (wlocal 13) s = F64 v) /\ (?v. read (wlocal 14) s = F64 v) /\
    (?v. read (wlocal 15) s = F64 v) /\ (?v. read (wlocal 16) s = F64 v) /\ (?v. read (wlocal 17) s = F64 v) /\
    (?v. read (wlocal 18) s = F64 v) /\ (?v. read (wlocal 19) s = F64 v) /\ (?v. read (wlocal 20) s = F64 v) /\
    (?v. read (wlocal 21) s = F64 v) /\ (?v. read (wlocal 22) s = F64 v)`;;
let c5_outer_pre = c5_B 333 "read wstack s = []" "[0,1241,0]"
  "read (wlocal 11) s = I32 (word 65536) /\\ read (wlocal 23) s = I32 (word 0)" c5_outer_f64;;
let c5_main_post =
 `\s. read wcode s = va1_puncture_mc /\ read wpc s = word 1232 /\ read wstatus s = WRunning /\
      read wstack s = [I32 a2; I32 a1; I32 a0] /\ read wlabels s = [0,1241,0] /\
      read warity s = 1 /\ read wmemsize s = 4194304 /\
      read (wglobal 0) s = I32 (word 16288) /\ read (wlocal 3) s = I32 (word 16288) /\
      va1_f33_frame m (read wmem s)`;;
let C5_SEQQ_TAC q =
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN EXISTS_TAC q THEN CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; CONJ_TAC];;
let C5_SEG_INIT2_TAC =
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[va1_c5_iv; va1_c5_ov]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_TAC o check (is_exists o concl))) THEN
  (fun (asl,w) -> let pth = find_read_th "wpc" `s0:wasmstate` (map snd asl) in
     RULE_ASSUM_TAC(fun th -> if can (find_term is_cond) (concl th) then
        CONV_RULE(DEPTH_CONV WORD_RED_CONV) (REWRITE_RULE[pth] th) else th) (asl,w)) THEN
  ABBREV_TAC `mm = read wmem (s0:wasmstate)`;;
let C5_CLOSE3_TAC extra =
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[va1_c5_iv; va1_c5_ov] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CONJ_TAC THEN TRY C5_EX_TAC THEN
  ASM_REWRITE_TAC(VA1_C5_W4_ADD :: extra) THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
  TRY C5_REFL_EX_TAC THEN
  TRY(ASM_REWRITE_TAC[] THEN TRY COND_CASES_TAC THEN REWRITE_TAC[CONS_11; injectivity "wval"] THEN MESON_TAC[]);;
let c5_fsa = [`fs:num->byte list#num#num`; `a0:int32`; `a1:int32`; `a2:int32`; `m:int64->byte`];;
let VA1_C5_OUTER = prove
 (list_mk_forall(c5_fsa,
   mk_imp(`fs 32 = (va1_f32_mc,2,1)`, list_mk_comb(`ensures (wasmc fs)`, [c5_outer_pre; c5_main_post; c5_cell_frame]))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_WHILE_UP_TAC `2048` `335` `1223` `\k s. va1_c5_ov a0 a1 a2 m k s` THEN REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;
    C5_SEG_INIT2_TAC THEN C5_DRIVE4 [335] THEN C5_CLOSE3_TAC [];
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN C5_SEQQ_TAC c5_inner_pre THENL
     [C5_SEG_INIT2_TAC THEN C5_DRIVE4 [431] THEN C5_CLOSE3_TAC [];
      C5_SEQQ_TAC c5_inner_post THENL
       [MP_TAC(SPECL (c5_fsa @ [`k:num`]) VA1_C5_INNER) THEN ASM_REWRITE_TAC[];
        C5_SEG_INIT2_TAC THEN C5_DRIVE4 [1223] THEN C5_CLOSE3_TAC [VA1_C5_W512_ADD; VA1_C5_K1_ADD]]];
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    MP_TAC(SPEC `k:num` VA1_C5_K_NE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    C5_SEG_INIT2_TAC THEN C5_DRIVE4 [335] THEN C5_CLOSE3_TAC [];
    C5_SEG_INIT2_TAC THEN C5_NORM_ASM_TAC THEN C5_DRIVE4 [1232] THEN C5_CLOSE3_TAC []]);;
let VA1_C5_B8_W64_OTHER = prove
 (`!a b (y:int64) (m:int64->byte).
     (a + 1 <= b \/ b + 8 <= a) /\ a + 1 < 2 EXP 64 /\ b + 8 < 2 EXP 64
     ==> read (bytes8 (word a)) (write (bytes64 (word b)) y m) = read (bytes8 (word a)) m`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC READ_WRITE_ORTHOGONAL_COMPONENTS THEN
  REWRITE_TAC[bytes8; bytes64] THEN MATCH_MP_TAC ORTHOGONAL_COMPONENTS_SUB_LEFT THEN
  MATCH_MP_TAC ORTHOGONAL_COMPONENTS_SUB_RIGHT THEN
  REWRITE_TAC[ORTHOGONAL_COMPONENTS_BYTES; DIMINDEX_64] THEN
  MATCH_MP_TAC NONOVERLAPPING_MODULO_SIMPLE THEN
  SUBGOAL_THEN `val(word a:int64) = a /\ val(word b:int64) = b`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;
let VA1_C5_FRAME_W64 = prove
 (`!m0 m b (y:int64). 16288 <= b /\ b + 8 <= 16384 /\ va1_f33_frame m0 m
     ==> va1_f33_frame m0 (write (bytes64 (word b)) y m)`,
  REWRITE_TAC[va1_f33_frame] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:num`; `b:num`; `y:int64`; `m:int64->byte`] VA1_C5_B8_W64_OTHER) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;
let VA1_C5_FRAME_REFL = prove
 (`!m. va1_f33_frame m m`, REWRITE_TAC[va1_f33_frame]);;
let C5_PRO_CLOSE_TAC =
  ENSURES_FINAL_STATE_TAC THEN REPEAT CONJ_TAC THEN TRY C5_EX_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC VA1_C5_FRAME_W64 THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]) THEN
  REWRITE_TAC[VA1_C5_FRAME_REFL];;
let VA1_C5_PROLOGUE = prove
 (list_mk_forall(c5_fsa,
   mk_imp(`fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\
     read (bytes32 (word 16396)) m = word 4294967295 /\ ~(read (bytes32 (word 16392)) m = word 0) /\
     ~(a0:int32 = word 0 /\ a1:int32 = word 0 /\ a2:int32 = word 0)`,
   list_mk_comb(`ensures (wasmc fs)`, [`va1_f33_pre a0 a1 a2 m`; c5_outer_pre; c5_cell_frame]))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN C5_PRE_TAC va1_f33_pre THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP VA1_C5_OR3 o check (fun th -> is_neg(concl th) && is_conj(rand(concl th)))) THEN
  C5_DRIVE4 [333] THEN C5_PRO_CLOSE_TAC);;
let VA1_F33_TO_F25 = prove
 (`!fs a0 a1 a2 m.
     fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\
     read (bytes32 (word 16396)) m = word 4294967295 /\ ~(read (bytes32 (word 16392)) m = word 0) /\
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0)
     ==> ensures (wasmc fs) (va1_f33_pre a0 a1 a2 m)
          (\s. read wcode s = va1_puncture_mc /\ read wpc s = word 1232 /\ read wstatus s = WRunning /\
               read wstack s = [I32 a2; I32 a1; I32 a0] /\ read wlabels s = [0,1241,0] /\
               read warity s = 1 /\ read wmemsize s = 4194304 /\
               read (wglobal 0) s = I32 (word 16288) /\ read (wlocal 3) s = I32 (word 16288) /\
               va1_f33_frame m (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocals] ,, MAYCHANGE [wglobal 0] ,, MAYCHANGE [wmem])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C5_SEQQ_TAC c5_outer_pre THENL
   [MP_TAC(SPECL c5_fsa VA1_C5_PROLOGUE) THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL c5_fsa VA1_C5_OUTER) THEN ASM_REWRITE_TAC[]]);;
