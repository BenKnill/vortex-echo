(* ========================================================================= *)
(* Vortex pop R5 droplet birth (vortex-r5birth PROVE-birth r1, Claude Opus   *)
(* 5.5, 2026-11-11): lemma layer 2 on pop_r5bp_lem.ml. Loop-2 and loop-3     *)
(* back edges (BACK2 4363->2706|4391, BACK3 6027->4493|6085), loop entries   *)
(* (ENTRY2 2612->2706|6085, ENTRY3 4391->4493|6085), epilogue EPI            *)
(* 6085->WDone (ND := n), loop-2 segments SEGF 2706->2905|4363, SEGG         *)
(* 2905->3009, ISQ4 (isqrt loop 3007), and R5B_MI0 (the invariant at entry). *)
(* ========================================================================= *)
let () = r5b_extra := [VK_COND_I64; VK_COND_I32; R5B_SEL1_NZ; R5B_SPD_NZ; R5B_SHL2; R5B_ADDZQ; R5B_MUL48; R5B_INC1];;
(* ---- copied from pop_l5_unbirth.ml (PROVED, SEG-L5), renamed *)
let PL5_BS_R5B = prove
 (`!bs:(num->int32)#(num->int32)#(num->int32)#int32. !m.
     va1_bs bs m <=>
     va1_w32s 1179648 196608 (FST bs) m /\ va1_w32s 1163264 2048 (FST (SND bs)) m /\
     va1_w32s 1171456 2048 (FST (SND (SND bs))) m /\ read (bytes32 (word 16400)) m = SND (SND (SND bs))`,
  REWRITE_TAC[FORALL_PAIR_THM; va1_bs]);;
let R5B_W32S_W32 = prove
 (`!base n f e (v:int32) m.
     va1_w32s base n f m /\ (e + 4 <= base \/ base + 4 * n <= e) /\
     base + 4 * n <= 4294967296 /\ e < 4294967296
     ==> va1_w32s base n f (write (bytes32 (word e)) v m)`,
  REWRITE_TAC[va1_w32s] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`base + 4 * k`; `e:num`; `v:int32`; `m:int64->byte`] VK_R32_W32) THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[]]));;
let R5B_MI0 = prove(mk_forall(`m:int64->byte`, mk_imp(`va1_bs (di,zq,zp,nd) (m:int64->byte)`, r5b_mi `val (nd:int32)` `m:int64->byte`)),
  GEN_TAC THEN REWRITE_TAC[va1_bs] THEN STRIP_TAC THEN EXISTS_TAC `[]:(num->int32)list` THEN
  ASM_REWRITE_TAC[ALL; LENGTH; ADD_CLAUSES; va1_push]);;

(* ---- R5 PROVE-birth: loop 2 (spray) segment lemmas: k = l15, n = l1, record base l0 = 48 n *)
let r5b_L2 = [Lp 2704; Blk 6084];;
let r5b_L2B = [Blk 4362; Lp 2704; Blk 6084];;
let r5b_trk2 = [15,`word k:int32`; 1,`word n:int32`; 3,`word_add t (word 1):int32`];;
let r5b_seg2 p q = list_mk_forall([`m0:int64->byte`;`k:num`;`n:num`;`t:int32`], mk_imp(`k < 2048 /\ n < 16384`, r5b_ens p q));;
(* back edge of loop 2: 4363 -> 2706 (k+1, n < 16384) | 4391 (k = 2047 or n = 16384) *)
let R5B_BACK2 = prove(list_mk_forall([`m0:int64->byte`;`k:num`;`n:num`;`t:int32`],
   mk_imp(`k < 2048 /\ n <= 16384`,
    r5b_ens (r5b_pred 4363 r5b_L2 r5b_trk2 [])
     (mk_abs(`s:wasmstate`, mk_disj(
        r5b_body 2706 r5b_L2 [15,`word (k + 1):int32`; 1,`word n:int32`; 3,`word_add t (word 1):int32`] [`k + 1 < 2048`; `n < 16384`],
        r5b_body 4391 [Blk 6084] [1,`word n:int32`; 3,`word_add t (word 1):int32`] [`n <= 16384`]))))),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val (word k:int32) = k /\ val (word n:int32) = n` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  R5B_SEG_TAC "back2" [2706; 4391]);;
(* ---- R5 PROVE-birth: loop 3 (antipode): k = l0, n = l14, pointers l11 = k << 21, l12 = TBL row, l13 = RA[k], l15 = RB[k] *)
let r5b_L3 = [Lp 4491; Blk 6084];;
let r5b_L3B = [Blk 6026; Lp 4491; Blk 6084];;
let r5b_trk3 kk nn = [0, mk_comb(`word:num->int32`, kk); 14, mk_comb(`word:num->int32`, nn); 3,`word_add t (word 1):int32`;
  11, subst [kk,`k:num`] `word (2097152 * k):int32`; 12, subst [kk,`k:num`] `word (65536 + 512 * k):int32`;
  13, subst [kk,`k:num`] `word (1130496 + 4 * k):int32`; 15, subst [kk,`k:num`] `word (1138688 + 4 * k):int32`];;
let r5b_seg3 p q = list_mk_forall([`m0:int64->byte`;`k:num`;`n:num`;`t:int32`], mk_imp(`k < 2048 /\ n < 16384`, r5b_ens p q));;
let r5b_val3_tac = SUBGOAL_THEN `val (word (1130496 + 4 * k):int32) = 1130496 + 4 * k /\ val (word (1138688 + 4 * k):int32) = 1138688 + 4 * k /\
     val (word (65536 + 512 * k):int32) = 65536 + 512 * k /\ val (word k:int32) = k /\ val (word n:int32) = n /\ val (word (48 * n):int32) = 48 * n`
     STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; ALL_TAC];;
(* back edge of loop 3: 6027 -> 4493 (k+1, pointers advanced, n < 16384) | 6085 *)
let R5B_BACK3 = prove(list_mk_forall([`m0:int64->byte`;`k:num`;`n:num`;`t:int32`],
   mk_imp(`k < 2048 /\ n <= 16384`,
    r5b_ens (r5b_pred 6027 r5b_L3 (r5b_trk3 `k:num` `n:num`) [])
     (mk_abs(`s:wasmstate`, mk_disj(
        r5b_body 4493 r5b_L3 (r5b_trk3 `k + 1` `n:num`) [`k + 1 < 2048`; `n < 16384`],
        r5b_body 6085 [] [14,`word n:int32`; 3,`word_add t (word 1):int32`] [`n <= 16384`]))))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val (word k:int32) = k /\ val (word n:int32) = n` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_add (word (2097152 * k)) (word 2097152):int32 = word (2097152 * (k + 1)) /\
                word_add (word (65536 + 512 * k)) (word 512):int32 = word (65536 + 512 * (k + 1)) /\
                word_add (word (1130496 + 4 * k)) (word 4):int32 = word (1130496 + 4 * (k + 1)) /\
                word_add (word (1138688 + 4 * k)) (word 4):int32 = word (1138688 + 4 * (k + 1))` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  R5B_INIT_TAC THEN r5b_time "back3" (R5B_RUN R5B_EXEC [4493; 6085]) THEN R5B_FIN_TAC);;
(* ---- R5 PROVE-birth: entries of loops 2 and 3, epilogue *)
let r5b_ent_hyp = `n <= 16384`;;
let r5b_seg0 p q = list_mk_forall([`m0:int64->byte`;`n:num`;`t:int32`], mk_imp(r5b_ent_hyp, r5b_ens p q));;
(* 2612 -> 2706 (loop-2 head, k = 0) | 6085 (n = 16384, l14 = n) *)
let R5B_ENTRY2 = prove(r5b_seg0 (r5b_pred 2612 [] [1,`word n:int32`; 3,`word_add t (word 1):int32`] [])
   (mk_abs(`s:wasmstate`, mk_disj(
      r5b_body 2706 r5b_L2 [15,`word 0:int32`; 1,`word n:int32`; 3,`word_add t (word 1):int32`] [`n < 16384`],
      r5b_body 6085 [] [14,`word n:int32`; 3,`word_add t (word 1):int32`] [`n <= 16384`]))),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val (word n:int32) = n` ASSUME_TAC THENL [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  R5B_SEG_TAC "entry2" [2706; 6085]);;
(* 4391 -> 4493 (loop-3 head, k = 0) | 6085 (n = 16384, l14 = 16384) *)
let R5B_ENTRY3 = prove(r5b_seg0 (r5b_pred 4391 [Blk 6084] [1,`word n:int32`; 3,`word_add t (word 1):int32`] [])
   (mk_abs(`s:wasmstate`, mk_disj(
      r5b_body 4493 r5b_L3 (r5b_trk3 `0` `n:num`) [`n < 16384`],
      r5b_body 6085 [] [14,`word 16384:int32`; 3,`word_add t (word 1):int32`] [`n = 16384`]))),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val (word n:int32) = n` ASSUME_TAC THENL [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  R5B_SEG_TAC "entry3" [4493; 6085]);;
(* 6085 -> WDone: ND := n, return n *)
let R5B_EPI = prove(r5b_seg0 (r5b_pred 6085 [] [14,`word n:int32`; 3,`word_add t (word 1):int32`] [])
   `\s. read wstatus s = WDone /\ (?r. read wstack s = [I32 r]) /\
        read wmem s = write (bytes32 (word 16400)) (word n) (m0:int64->byte)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN R5B_INIT_TAC THEN r5b_time "epi" (R5B_RUN R5B_EXEC []) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[CONS_11; injectivity "wval"] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN ASM_REWRITE_TAC[R5B_EX_EQ] THEN MESON_TAC[]);;
(* 2706 -> 2905 (live) | 4363 (continues 2732 band, 2847 hash): spd, D13 (SPD_NZ), D14 *)
let R5B_SEGF = prove(r5b_seg2 (r5b_pred 2706 r5b_L2 r5b_trk2 [])
     (mk_abs(`s:wasmstate`, mk_disj(r5b_body 2905 r5b_L2B r5b_trk2 [], r5b_body 4363 r5b_L2 r5b_trk2 []))),
  R5B_SEG_TAC "segF" [2905; 4363]);;
(* 2905 -> 3009 (inside isqrt loop 4, counter l0 = 32) *)
let R5B_SEGG = r5b_with_thresh 60 (fun () -> prove(r5b_seg2 (r5b_pred 2905 r5b_L2B r5b_trk2 []) (r5b_pred 3009 (Lp 3007 :: r5b_L2B) ((0,`word 32:int32`) :: r5b_trk2) []),
  R5B_SEG_TAC "segG" [3009])) ();;

(* 4493 -> 4700 (live) | 6027 (continues 4506, 4521 band, 4574 hash) *)
let R5B_ISQ4 = prove(r5b_isq_stmt 3007 3063 0 r5b_L2B r5b_trk2, R5B_ISQ_TAC "isq4" 3007 3063 0 r5b_L2B r5b_trk2);;
