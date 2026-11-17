needs "ve_vort.ml";;
needs "ve_tick.ml";;
needs "ve_vk.ml";;
needs "va1_code.ml";;
needs "va1_seq_final2.ml";;
needs "pop_design_defs.ml";;
needs "pop_design_stmts.ml";;
needs "pop_r5_corr_defs.ml";;
(* ========================================================================= *)
(* Vortex pop R5, ripple kick f17/f18 (PROVE-corr, Claude Opus 5.5,          *)
(* 2026-11-11). Lemma layer: VA1_CK_SINMAG_BOUND (the sine helper is at most *)
(* 1686629713, so the sigma divisor is not 0), the three loops of both       *)
(* exports on the exact bytes (loop 1, pc 15 -> 376: LAP[k] = va1_ck_lap;    *)
(* loop 2, pc 467 -> 1349: KZ[k] = va1_ck_kk; loop 3, pc 1349 -> end:        *)
(* ZP[k] := ZP[k] +/- KZ[k]), the mid section, and the two halves of         *)
(* va1_corrk_ok va1_ck (R5C_F17_OK, R5C_F18_OK). The final leaf only binds   *)
(* VA1_CORRK_OK / VA1_CORRK_SAT.                                             *)
(* Long straight lines: R5C_FLUSH_TAC re-assumes the assumptions without the *)
(* per-step update hypotheses (discharged by PROVE_HYP in the justification) *)
(* and R5C_AUTOAB_TAC abbreviates large stack/local values; the final value  *)
(* is compared with the definition after expanding the abbreviations.        *)
(* ========================================================================= *)
let R5C_VW = prove
 (`!n. val(word n:int64) <= n`,
  REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LE]);;

let R5C_MULSHR = prove
 (`!(x:int64) (y:int64) a b n.
     val x <= a /\ val y <= b /\ a * b < 2 EXP 64
     ==> val (word_ushr (word_mul x y) n) <= (a * b) DIV 2 EXP n /\
         val (word_ushr (word_mul x y) n) = (val x * val y) DIV 2 EXP n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val (x:int64) * val (y:int64) <= a * b` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_mul x y:int64) = val x * val y` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_MUL; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `a * b` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_WORD_USHR] THEN MATCH_MP_TAC DIV_MONO THEN ASM_REWRITE_TAC[]);;

(* assume val (word_ushr (word_mul x y) 30) <= K, K = (a * b) DIV 2^30 reduced *)
let R5C_MSB_TAC x y a b : tactic =
  MP_TAC(SPECL [x; y; a; b; `30`] R5C_MULSHR) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [CONV_TAC NUM_REDUCE_CONV THEN NO_TAC; FIRST_ASSUM ACCEPT_TAC;
           REWRITE_TAC[R5C_VW] THEN NO_TAC; ASM_ARITH_TAC];
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN DISCH_TAC];;

let R5C_SUB30 = prove
 (`!y:int64. val y <= 1073741824 ==> val (word_sub (word 1073741824) y) <= 1073741824`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let R5C_TSTEP_BOUND = prove
 (`!x2 c t. val (x2:int64) <= 4294967295 /\ c <= 268435455 /\ val (t:int64) <= 1073741824
            ==> val (va1_ck_tstep x2 c t) <= 1073741824`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[va1_ck_tstep] THEN
  ASSUME_TAC(SPEC `c:num` R5C_VW) THEN
  MATCH_MP_TAC R5C_SUB30 THEN
  R5C_MSB_TAC `x2:int64` `word c:int64` `4294967295` `268435455` THEN
  ABBREV_TAC `b = word_ushr (word_mul x2 (word c)) 30:int64` THEN
  R5C_MSB_TAC `t:int64` `b:int64` `1073741824` `1073741823` THEN
  ASM_ARITH_TAC);;

let R5C_ZX64 = prove
 (`!x:int32. val (word_zx x:int64) = val x`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `x:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN ARITH_TAC);;

let VA1_CK_SINMAG_BOUND = prove
 (`!ph:int32. val (va1_ck_sinmag ph) <= 1686629713`,
  GEN_TAC THEN REWRITE_TAC[va1_ck_sinmag] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `val (word_and ph (word 1073741823):int32) <= 1073741823` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ph:int32`; `30`] VAL_WORD_AND_MASK_WORD) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [`val (ph:int32)`; `1073741824`] MOD_LT_EQ) THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `f = word_and ph (word 1073741823):int32` THEN
  SUBGOAL_THEN `val (if word_and (ph:int32) (word 1073741824) = word 0 then f
                     else word_sub (word 1073741824) f:int32) <= 1073741824` ASSUME_TAC THENL
   [COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_32] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    SUBGOAL_THEN `val (f:int32) <= 1073741824` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `ff = (if word_and (ph:int32) (word 1073741824) = word 0 then f
                    else word_sub (word 1073741824) f:int32)` THEN
  SUBGOAL_THEN `val (word_zx (ff:int32):int64) <= 1073741824` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[R5C_ZX64]; ALL_TAC] THEN
  R5C_MSB_TAC `word_zx (ff:int32):int64` `word 1686629713:int64` `1073741824` `1686629713` THEN
  ABBREV_TAC `x = word_ushr (word_mul (word_zx (ff:int32)) (word 1686629713)) 30:int64` THEN
  R5C_MSB_TAC `x:int64` `x:int64` `1686629713` `1686629713` THEN
  ABBREV_TAC `x2 = word_ushr (word_mul x x) 30:int64` THEN
  R5C_MSB_TAC `x2:int64` `word 6882960:int64` `2649351757` `6882960` THEN
  SUBGOAL_THEN `val (word_sub (word 1073741824)
                  (word_ushr (word_mul x2 (word 6882960)) 30):int64) <= 1073741824` ASSUME_TAC THENL
   [MATCH_MP_TAC R5C_SUB30 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `t1 = word_sub (word 1073741824) (word_ushr (word_mul x2 (word 6882960)) 30):int64` THEN
  SUBGOAL_THEN `val (va1_ck_tstep x2 178956971 (va1_ck_tstep x2 53687091 (va1_ck_tstep x2 25565282
                 (va1_ck_tstep x2 14913081 (va1_ck_tstep x2 9761289 t1))))) <= 1073741824` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC R5C_TSTEP_BOUND THEN
           REPEAT CONJ_TAC THEN TRY(CONV_TAC NUM_REDUCE_CONV THEN NO_TAC) THEN
           TRY(ASM_ARITH_TAC THEN NO_TAC));
    ALL_TAC] THEN
  ABBREV_TAC `t6 = va1_ck_tstep x2 178956971 (va1_ck_tstep x2 53687091 (va1_ck_tstep x2 25565282
                 (va1_ck_tstep x2 14913081 (va1_ck_tstep x2 9761289 t1))))` THEN
  R5C_MSB_TAC `t6:int64` `x:int64` `1073741824` `1686629713` THEN
  ASM_REWRITE_TAC[]);;

(* the sigma divisor (s2 * s2) >>u 30 of a floored sine is not 0 *)
let R5C_SIGDIV_NZ = prove
 (`!s2:int64. 375809638 <= val s2 /\ val s2 <= 1686629713
              ==> ~(word_ushr (word_mul s2 s2) 30 = word 0)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`s2:int64`; `s2:int64`; `1686629713`; `1686629713`; `30`] R5C_MULSHR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `(375809638 * 375809638) DIV 2 EXP 30 <= (val (s2:int64) * val s2) DIV 2 EXP 30` MP_TAC THENL
   [MATCH_MP_TAC DIV_MONO THEN MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONV_TAC(LAND_CONV(LAND_CONV NUM_REDUCE_CONV)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int64->num`) THEN REWRITE_TAC[VAL_WORD_0] THEN ASM_ARITH_TAC);;
let R5CF = `MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
            MAYCHANGE [wstatus] ,, MAYCHANGE [wlocal 0; wlocal 1; wlocal 2; wlocal 3; wlocal 4; wlocal 5; wlocal 6; wlocal 7; wlocal 8; wlocal 9; wlocal 10; wlocal 11; wlocal 12; wlocal 13; wlocal 14; wlocal 15; wlocal 16; wlocal 17; wlocal 18] ,,
            MAYCHANGE [wmem :> bytes(word 1171456,8192)] ,,
            MAYCHANGE [wmem :> bytes(word 1966080,73728)]`;;

let R5CF0 = `MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
            MAYCHANGE [wstatus] ,, MAYCHANGE [wlocal 0; wlocal 1; wlocal 2; wlocal 3; wlocal 4; wlocal 5; wlocal 6; wlocal 7; wlocal 8; wlocal 9; wlocal 10; wlocal 11; wlocal 12; wlocal 13; wlocal 14; wlocal 15; wlocal 16; wlocal 17; wlocal 18] ,,
            MAYCHANGE [wmem :> bytes(word 1966080,73728)]`;;

let r5c_l9 = `word_xor ((mdl:num->int32) 2) (word 2654435769)`;;
let r5c_l10 = `word_add (word_mul (word_add (word_shl (word_sub (t:int32) (p:int32)) 3) (word sub)) (word 3266489909)) (word 2769733223):int32`;;

let r5c_l2_stmt mc =
  list_mk_forall([`mdl:num->int32`; `tbl:num->int32`; `t:int32`; `p:int32`; `sub:num`;
                  `rb:num->int32`; `zq:num->int32`; `lap:num->int64`],
  subst [mc,`MC:byte list`; R5CF0,`RF:wasmstate->wasmstate->bool`; r5c_l9,`L9:int32`; r5c_l10,`L10:int32`]
 `ensures wasm
    (\s. read wcode s = MC /\ read wpc s = word 467 /\ read wstatus s = WRunning /\
         read wstack s = [] /\ read wlabels s = [] /\ read warity s = 0 /\
         read wmemsize s = 4194304 /\
         read (wlocal 1) s = I32 (word 1138688) /\ read (wlocal 2) s = I32 (word 2007040) /\
         read (wlocal 3) s = I32 (word 65536) /\ read (wlocal 4) s = I32 (word 0) /\
         read (wlocal 5) s = I32 (word 1163264) /\ read (wlocal 6) s = I32 (word 2015232) /\
         read (wlocal 9) s = I32 L9 /\ read (wlocal 10) s = I32 L10 /\
         read (wmem :> bytes32 (word 16648)) s = mdl 2 /\
         (!k. k < 262144 ==> read (wmem :> bytes32 (word (65536 + 4 * k))) s = tbl k) /\
         (!k. k < 2048 ==> read (wmem :> bytes32 (word (1138688 + 4 * k))) s = rb k) /\
         (!k. k < 2048 ==> read (wmem :> bytes32 (word (1163264 + 4 * k))) s = zq k) /\
         (!k. k < 2048 ==> read (wmem :> bytes64 (word (2015232 + 8 * k))) s = lap k))
    (\s. read wcode s = MC /\ read wpc s = word 1349 /\ read wstatus s = WRunning /\
         read wstack s = [] /\ read wlabels s = [] /\ read warity s = 0 /\
         read wmemsize s = 4194304 /\
         read (wmem :> bytes32 (word 16648)) s = mdl 2 /\
         (!k. k < 262144 ==> read (wmem :> bytes32 (word (65536 + 4 * k))) s = tbl k) /\
         (!k. k < 2048 ==> read (wmem :> bytes32 (word (1138688 + 4 * k))) s = rb k) /\
         (!k. k < 2048 ==> read (wmem :> bytes32 (word (1163264 + 4 * k))) s = zq k) /\
         (!k. k < 2048 ==> read (wmem :> bytes64 (word (2015232 + 8 * k))) s = lap k) /\
         (!k. k < 2048 ==> read (wmem :> bytes32 (word (2007040 + 4 * k))) s =
                           va1_ck_kk mdl tbl t p sub rb zq lap k))
    RF`);;

let r5c_l2_inv mc =
  let t = subst [mc,`MC:byte list`; r5c_l9,`L9:int32`; r5c_l10,`L10:int32`]
   `\i s. read wcode s = MC /\ read wstatus s = WRunning /\
          read wmemsize s = 4194304 /\ read warity s = 0 /\
          read wlabels s = [0,467,0] /\
          read (wlocal 1) s = I32 (word (1138688 + 4 * i)) /\
          read (wlocal 2) s = I32 (word (2007040 + 4 * i)) /\
          read (wlocal 3) s = I32 (word (65536 + 512 * i)) /\
          read (wlocal 4) s = I32 (word i) /\
          read (wlocal 5) s = I32 (word (1163264 + 4 * i)) /\
          read (wlocal 6) s = I32 (word (2015232 + 8 * i)) /\
          read (wlocal 9) s = I32 L9 /\ read (wlocal 10) s = I32 L10 /\
          read wstack s = (if read wpc s = word 469 then []
                           else [I32 (word (bitval (~(word i = word 2048:int32))))]) /\
          read (wmem :> bytes32 (word 16648)) s = (mdl:num->int32) 2 /\
          (!k. k < 262144 ==> read (wmem :> bytes32 (word (65536 + 4 * k))) s = (tbl:num->int32) k) /\
          (!k. k < 2048 ==> read (wmem :> bytes32 (word (1138688 + 4 * k))) s = (rb:num->int32) k) /\
          (!k. k < 2048 ==> read (wmem :> bytes32 (word (1163264 + 4 * k))) s = (zq:num->int32) k) /\
          (!k. k < 2048 ==> read (wmem :> bytes64 (word (2015232 + 8 * k))) s = (lap:num->int64) k) /\
          (!k. k < i ==> read (wmem :> bytes32 (word (2007040 + 4 * k))) s =
                         va1_ck_kk mdl tbl t p sub rb zq lap k)` in
  rhs(concl(TOP_DEPTH_CONV BETA_CONV t));;
let R5C_RANGE = prove
 (`!r:int32. ~(val (word_add r (word 4293289574)) > 50693911) ==> 1677722 <= val r /\ val r <= 52371633`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  MP_TAC(ISPEC `r:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  DISCH_TAC THEN ASM_CASES_TAC `1677722 <= val (r:int32)` THENL
   [SUBGOAL_THEN `(val (r:int32) + 4293289574) MOD 4294967296 = val r - 1677722` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
    SUBGOAL_THEN `(val (r:int32) + 4293289574) MOD 4294967296 = val r + 4293289574` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]]);;

let R5C_J = prove
 (`!r:int32. val r <= 52371633 ==>
     word_and (word_ushr r 17) (word 32764) =
       word (4 * (val (word_and (word_ushr r 17) (word 32764):int32) DIV 4)) /\
     val (word_and (word_ushr r 17) (word 32764):int32) DIV 4 <= 99`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val (r:int32) DIV 524288 <= 99` ASSUME_TAC THENL
   [MP_TAC(SPECL [`val (r:int32)`; `52371633`; `524288`] DIV_MONO) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `word_and (word_ushr r 17) (word 32764):int32 = word (4 * (val (r:int32) DIV 524288))`
    SUBST1_TAC THENL
   [SUBGOAL_THEN `word_and (word_ushr r 17) (word 32764):int32 =
                  word_shl (word_and (word_ushr r 19) (word 8191)) 2` SUBST1_TAC THENL
     [BITBLAST_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `word_and (word_ushr r 19) (word 8191):int32 = word (val (r:int32) DIV 524288)`
      SUBST1_TAC THENL
     [REWRITE_TAC[GSYM VAL_EQ] THEN
      MP_TAC(ISPECL [`word_ushr r 19:int32`; `13`] VAL_WORD_AND_MASK_WORD) THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[VAL_WORD_USHR; VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
      SUBGOAL_THEN `val (r:int32) DIV 524288 < 8192 /\ val (r:int32) DIV 524288 < 4294967296`
        STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[MOD_LT]];
      REWRITE_TAC[CAP_SHL2]];
    ALL_TAC] THEN
  SUBGOAL_THEN `val (word (4 * (val (r:int32) DIV 524288)):int32) = 4 * (val (r:int32) DIV 524288)`
    SUBST1_TAC THENL [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ; ARITH_RULE `4 * x = x * 4`] THEN ASM_REWRITE_TAC[]);;

let R5C_AND2047 = prove
 (`!n. word_and (word n:int32) (word 2047) = word (n MOD 2048)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  MP_TAC(ISPECL [`word n:int32`; `11`] VAL_WORD_AND_MASK_WORD) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  SUBGOAL_THEN `n MOD 2048 < 4294967296` (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL
   [MP_TAC(SPECL [`n:num`; `2048`] MOD_LT_EQ) THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `2048`; `2097152`] MOD_MOD) THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  SIMP_TAC[]);;

let R5C_IDXP = prove
 (`!i. word_and (word (i + 1)) (word 2047):int32 = word ((i + 1) MOD 2048)`,
  REWRITE_TAC[R5C_AND2047]);;

let R5C_IDXM = prove
 (`!i. word_and (word_add (word i) (word 4294967295)) (word 2047):int32 = word ((i + 2047) MOD 2048)`,
  GEN_TAC THEN REWRITE_TAC[GSYM WORD_ADD; R5C_AND2047] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `i + 4294967295 = 2097151 * 2048 + (i + 2047)` SUBST1_TAC THENL
   [ARITH_TAC; REWRITE_TAC[MOD_MULT_ADD]]);;

let R5C_SHL2V = prove
 (`!n. n < 2048 ==> val (word_shl (word n:int32) 2) = 4 * n`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[VAL_WORD_SHL; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  SUBGOAL_THEN `n MOD 4294967296 = n` SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;
let R5C_SHL3V = prove
 (`!n. n < 2048 ==> val (word_shl (word n:int32) 3) = 8 * n`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[VAL_WORD_SHL; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  SUBGOAL_THEN `n MOD 4294967296 = n` SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let R5C_WADD_TAC t =
  SUBGOAL_THEN t ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN VK_ARITH_TAC; ALL_TAC];;

(* every quantified memory fact of the post state over the one KZ store *)
let R5C_L2_MEMGOALS_TAC (close:tactic) =
  REPEAT CONJ_TAC THEN
  TRY(X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      ((REPEAT VK_PEEL_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN VK_ARITH_TAC) ORELSE
       (ASM_CASES_TAC `k:num = i` THENL
         [FIRST_X_ASSUM SUBST_ALL_TAC THEN REPEAT VK_PEEL_TAC THEN close;
          REPEAT VK_PEEL_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN VK_ARITH_TAC]))) THEN
  TRY(REPEAT VK_PEEL_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC);;

let R5C_L2_PRE_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MAP_EVERY VK_VAL_TAC [`1138688 + 4 * i`; `1163264 + 4 * i`; `2015232 + 8 * i`; `2007040 + 4 * i`; `65536 + 512 * i`] THEN
  MAP_EVERY R5C_WADD_TAC
   [`word_add (word (2015232 + 8 * i)) (word 8):int32 = word (2015232 + 8 * (i + 1))`;
    `word_add (word (1163264 + 4 * i)) (word 4):int32 = word (1163264 + 4 * (i + 1))`;
    `word_add (word (65536 + 512 * i)) (word 512):int32 = word (65536 + 512 * (i + 1))`;
    `word_add (word (2007040 + 4 * i)) (word 4):int32 = word (2007040 + 4 * (i + 1))`;
    `word_add (word (1138688 + 4 * i)) (word 4):int32 = word (1138688 + 4 * (i + 1))`;
    `word_add (word i) (word 1):int32 = word (i + 1)`] THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  SUBGOAL_THEN `read (bytes32 (word 16648)) mm = (mdl:num->int32) 2` ASSUME_TAC THENL
   [EXPAND_TAC "mm" THEN REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  VK_LOADFACT_TAC `read (bytes32 (word (1138688 + 4 * i))) mm = rb i`;;

let R5C_L2_SKIP_TAC exec =
  VK_MSTEPS_TAC exec (11--40) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
  R5C_L2_MEMGOALS_TAC
   (REWRITE_TAC[va1_ck_kk] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[]);;

(* the value held in local n / at stack position k (0 = top) of the newest state *)
let r5c_state_of w = (* the state variable of an eventually goal *) rand w;;
let r5c_local_val n (asl,w) =
  let s = rand w in
  let th = find (fun th -> let c = concl th in is_eq c &&
      (match lhs c with
         Comb(Comb(Const("read",_),l),s') -> s' = s && is_comb l &&
            (try fst(dest_const(rator l)) = "wlocal" && dest_small_numeral(rand l) = n with _ -> false)
       | _ -> false)) (map snd asl) in
  rand(rhs(concl th));;
let r5c_stack_val k (asl,w) =
  let s = rand w in
  let th = find (fun th -> let c = concl th in is_eq c &&
      (match lhs c with
         Comb(Comb(Const("read",_),Const("wstack",_)),s') -> s' = s
       | _ -> false)) (map snd asl) in
  rand(el k (dest_list(rhs(concl th))));;
let R5C_ABBREV_VAL_TAC v name : tactic =
  if is_var v then ALL_TAC else ABBREV_TAC (mk_eq(mk_var(name, type_of v), v));;
let R5C_ABL_TAC n name : tactic = fun g -> R5C_ABBREV_VAL_TAC (r5c_local_val n g) name g;;
let R5C_ABS_TAC k name : tactic = fun g -> R5C_ABBREV_VAL_TAC (r5c_stack_val k g) name g;;
let r5c_tsize tm = let rec go t = if is_numeral t then 1 else match t with Comb(a,b) -> go a + go b | Abs(_,b) -> 1 + go b | _ -> 1 in go tm;;
let r5c_maxsize () = let (asl,w) = top_realgoal() in
  itlist (fun (_,th) m -> max m (r5c_tsize (concl th))) asl 0;;

(* auto-abbreviate every non-variable local / stack value of the newest state *)
(* larger than 12 nodes, smallest first, re-reading the goal each time        *)
let r5c_abn = ref 0;;
let r5c_state_vals (asl,w) =
  let s = rand w in
  List.concat (mapfilter (fun (_,th) -> let c = concl th in
     if not (is_eq c) then fail() else
     match lhs c with
       Comb(Comb(Const("read",_),l),s') when s' = s ->
         if (try fst(dest_const(rator l)) = "wlocal" with _ -> false) then [rand(rhs c)]
         else if (try fst(dest_const l) = "wstack" with _ -> false) then map rand (dest_list(rhs c))
         else fail()
     | _ -> fail()) asl);;
let rec R5C_AUTOAB_TAC : tactic = fun g ->
  let vs = filter (fun v -> not(is_var v) && not (is_comb v && is_const(rator v) && fst(dest_const(rator v)) = "word") && (r5c_tsize v > 12 || can (find_term is_cond) v)) (r5c_state_vals g) in
  if vs = [] then ALL_TAC g else
  let v = snd(hd(sort (fun (a,_) (b,_) -> a < b) (map (fun v -> r5c_tsize v, v) vs))) in
  (incr r5c_abn;
   (ABBREV_TAC (mk_eq(mk_var("a_" ^ string_of_int !r5c_abn, type_of v), v)) THEN R5C_AUTOAB_TAC) g);;

(* step a..b, auto-abbreviating after each step *)
let R5C_STEPS_TAC exec a b =
  MAP_EVERY (fun n -> VK_MSTEPS_TAC exec [n] THEN R5C_AUTOAB_TAC) (a--b);;

(* expand every abbreviation variable occurring in the goal *)
let rec R5C_EXPAND_TAC : tactic = fun (asl,w) ->
  let fv = frees w in
  let cands = filter (fun (_,th) -> let c = concl th in
     is_eq c && is_var (rhs c) && mem (rhs c) fv && not (vk_has_read c)) asl in
  match cands with
    [] -> ALL_TAC (asl,w)
  | (_,th)::_ -> (SUBST1_TAC (SYM th) THEN R5C_EXPAND_TAC) (asl,w);;

let r5c_abdef v (asl,w) = find (fun th -> let c = concl th in is_eq c && rhs c = v) (map snd asl);;

(* spd (local 7) is neither 0 nor -1: VK_LEN_NZ on its clamp *)
let R5C_SPD_NZ_TAC n : tactic = fun g ->
  let v = r5c_local_val n g in
  if is_var v then
    let th = r5c_abdef v g in
    (MP_TAC(SPEC (rand(lhs(concl th))) VK_LEN_NZ) THEN REWRITE_TAC[th] THEN STRIP_TAC) g
  else (MP_TAC(SPEC (rand v) VK_LEN_NZ) THEN STRIP_TAC) g;;

(* expand one abbreviation variable v in the goal *)
let R5C_EXPAND1_TAC v : tactic = fun g -> SUBST1_TAC(SYM(r5c_abdef v g)) g;;

(* s2 (local n) is a floored sine: the sigma divisor is not 0 *)
let R5C_S2_TAC n : tactic = fun g ->
  let v = r5c_local_val n g in
  (MP_TAC(SPEC v R5C_SIGDIV_NZ) THEN ANTS_TAC THENL
    [R5C_EXPAND1_TAC v THEN COND_CASES_TAC THEN
     REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN VK_ARITH_TAC;
     DISCH_TAC]) g;;

(* The stepper transports old facts with the step's update equation as a     *)
(* hypothesis, so assumption theorems gain one hypothesis per step and long   *)
(* straight lines get quadratic. Re-assume every assumption (hyp-free) and    *)
(* discharge the originals in the justification with PROVE_HYP: the proved    *)
(* theorem is the same, only the bookkeeping per step stays small.            *)
let R5C_FLUSH_TAC : tactic = fun (asl,w) ->
  if forall (fun (_,th) -> hyp th = [concl th]) asl then ALL_TAC (asl,w) else
  let asl' = map (fun (l,th) -> (l, ASSUME(concl th))) asl in
  (null_meta, [asl',w],
   fun i [th] -> itlist (fun (_,ath) t -> PROVE_HYP (INSTANTIATE_ALL i ath) t) asl th);;

let R5C_STEPS_TAC exec a b =
  MAP_EVERY (fun n -> VK_MSTEPS_TAC exec [n] THEN R5C_FLUSH_TAC THEN R5C_AUTOAB_TAC) (a--b);;

(* s (local n) = |sin| of the phase of r: val s <= 1686629713 (VA1_CK_SINMAG_BOUND) *)
let R5C_SBOUND_TAC n phv : tactic = fun g ->
  let v = r5c_local_val n g in
  (SUBGOAL_THEN (mk_binop `(<=):num->num->bool` (mk_comb(`val:int64->num`, v)) `1686629713`) ASSUME_TAC THENL
    [R5C_EXPAND_TAC THEN MP_TAC(SPEC phv VA1_CK_SINMAG_BOUND) THEN
     REWRITE_TAC[va1_ck_sinmag; va1_ck_tstep; va1_ck_ph] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     DISCH_THEN ACCEPT_TAC;
     ALL_TAC]) g;;

(* first differing subterms of two terms (debug) *)
let rec r5c_diff l r =
  if l = r then None else
  match l,r with
    Comb(a,b),Comb(c,d) -> (match r5c_diff a c with Some x -> Some x | None -> r5c_diff b d)
  | _ -> Some (l,r);;

let R5C_KK_DEFS = [va1_ck_kk; va1_ck_spd; va1_ck_hj; va1_ck_hfin; va1_ck_zpq; va1_ck_on;
                   va1_ck_sinmag; va1_ck_ph; va1_ck_sig; va1_ck_tstep];;

(* close  stored = va1_ck_kk .. i  in the in-range case *)
let R5C_KK_CLOSE_TAC =
  REWRITE_TAC[va1_ck_kk] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[] THEN R5C_EXPAND_TAC THEN REWRITE_TAC R5C_KK_DEFS THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[COND_SWAP] THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  (REFL_TAC ORELSE (fun (asl,w) ->
     (match r5c_diff (lhs w) (rhs w) with
        Some(a,b) -> (print_string "@@DIFF L: "; print_term a; print_string "\n@@DIFF R: "; print_term b; print_newline())
      | None -> ()); FAIL_TAC "R5C_KK_CLOSE_TAC" (asl,w)));;

let R5C_L2_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
  R5C_L2_MEMGOALS_TAC R5C_KK_CLOSE_TAC;;

(* ---------------- the loop 2 lemma ---------------- *)
let R5C_L2_INRANGE_TAC exec =
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP R5C_RANGE) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP R5C_J) THEN
  ABBREV_TAC `JJ = val (word_and (word_ushr ((rb:num->int32) i) 17) (word 32764):int32) DIV 4` THEN STRIP_TAC THEN
  R5C_WADD_TAC `word_add (word (65536 + 512 * i)) (word (4 * JJ)):int32 = word (65536 + 4 * (128 * i + JJ))` THEN
  R5C_WADD_TAC `word_add (word (65536 + 4 * (128 * i + JJ))) (word 4):int32 = word (65536 + 4 * (128 * i + JJ + 1))` THEN
  MAP_EVERY VK_VAL_TAC [`65536 + 4 * (128 * i + JJ)`; `65536 + 4 * (128 * i + JJ + 1)`] THEN
  VK_LOADFACT_TAC `read (bytes32 (word (65536 + 4 * (128 * i + JJ)))) mm = tbl (128 * i + JJ)` THEN
  VK_LOADFACT_TAC `read (bytes32 (word (65536 + 4 * (128 * i + JJ + 1)))) mm = tbl (128 * i + JJ + 1)` THEN
  VK_LOADFACT_TAC `read (bytes32 (word (1163264 + 4 * i))) mm = zq i` THEN
  VK_LOADFACT_TAC `read (bytes64 (word (2015232 + 8 * i))) mm = lap i` THEN
  ASSUME_TAC(SPEC `i:num` R5C_IDXP) THEN ASSUME_TAC(SPEC `i:num` R5C_IDXM) THEN
  SUBGOAL_THEN `(i + 1) MOD 2048 < 2048 /\ (i + 2047) MOD 2048 < 2048` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun n -> ASSUME_TAC(UNDISCH(SPEC n R5C_SHL2V)) THEN ASSUME_TAC(UNDISCH(SPEC n R5C_SHL3V)))
    [`(i + 1) MOD 2048`; `(i + 2047) MOD 2048`] THEN
  VK_LOADFACT2_TAC `read (bytes64 (word (8 * ((i + 1) MOD 2048) + 2015232))) mm = lap ((i + 1) MOD 2048)`
    `2015232 + 8 * ((i + 1) MOD 2048)` THEN
  VK_LOADFACT2_TAC `read (bytes64 (word (8 * ((i + 2047) MOD 2048) + 2015232))) mm = lap ((i + 2047) MOD 2048)`
    `2015232 + 8 * ((i + 2047) MOD 2048)` THEN
  VK_LOADFACT2_TAC `read (bytes32 (word (4 * ((i + 1) MOD 2048) + 1163264))) mm = zq ((i + 1) MOD 2048)`
    `1163264 + 4 * ((i + 1) MOD 2048)` THEN
  VK_LOADFACT2_TAC `read (bytes32 (word (4 * ((i + 2047) MOD 2048) + 1163264))) mm = zq ((i + 2047) MOD 2048)`
    `1163264 + 4 * ((i + 2047) MOD 2048)` THEN
  MP_TAC VK_COND_I64 THEN MP_TAC VK_COND_I32 THEN REPEAT DISCH_TAC THEN
  R5C_STEPS_TAC exec 11 42 THEN VK_MSTEPS_TAC exec [43;44] THEN R5C_FLUSH_TAC THEN
  R5C_SPD_NZ_TAC 7 THEN R5C_AUTOAB_TAC THEN
  R5C_STEPS_TAC exec 45 319 THEN
  R5C_SBOUND_TAC 8 `va1_ck_ph (word_zx ((rb:num->int32) i))` THEN
  R5C_STEPS_TAC exec 320 324 THEN VK_MSTEPS_TAC exec [325] THEN R5C_FLUSH_TAC THEN
  R5C_S2_TAC 8 THEN R5C_AUTOAB_TAC THEN
  R5C_STEPS_TAC exec 326 427 THEN
  R5C_L2_FINAL_TAC;;

let R5C_L2_BODY_TAC exec =
  R5C_L2_PRE_TAC THEN VK_MSTEPS_TAC exec (1--10) THEN R5C_FLUSH_TAC THEN
  ASM_CASES_TAC `val (word_add ((rb:num->int32) i) (word 4293289574):int32) > 50693911` THENL
   [R5C_L2_SKIP_TAC exec; R5C_L2_INRANGE_TAC exec];;

let R5C_MM16648_TAC =
  SUBGOAL_THEN `read (bytes32 (word 16648)) mm = (mdl:num->int32) 2` ASSUME_TAC THENL
   [EXPAND_TAC "mm" THEN REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC];;

let R5C_L2_TAC mc exec =
  REPEAT GEN_TAC THEN
  ENSURES_WHILE_UP_TAC `2048` `469` `1346` (r5c_l2_inv mc) THEN REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    ENSURES_INIT_TAC "s0" THEN MEMNAME_TAC THEN R5C_MM16648_TAC THEN VK_MSTEPS_TAC exec [1] THEN
    ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LT];
    R5C_L2_BODY_TAC exec;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`i:num`; `2048`] VK_WORD_NE) THEN ANTS_TAC THENL [VK_ARITH_TAC; DISCH_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN R5C_MM16648_TAC THEN
    VK_MSTEPS_TAC exec (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN R5C_MM16648_TAC THEN
    VK_MSTEPS_TAC exec (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[]];;
(* ---------------- loop 1 (pc 15 -> 376): LAP[k] = va1_ck_lap rb zq k ---------------- *)
let r5c_l1_stmt mc =
  list_mk_forall([`l0:wval`; `rb:num->int32`; `zq:num->int32`],
  subst [mc,`MC:byte list`; R5CF0,`RF:wasmstate->wasmstate->bool`]
 `ensures wasm
    (\s. read wcode s = MC /\ read wpc s = word 15 /\ read wstatus s = WRunning /\
         read wstack s = [] /\ read wlabels s = [] /\ read warity s = 0 /\
         read wmemsize s = 4194304 /\ read (wlocal 0) s = l0 /\
         (!k. k < 2048 ==> read (wmem :> bytes32 (word (1138688 + 4 * k))) s = rb k) /\
         (!k. k < 2048 ==> read (wmem :> bytes32 (word (1163264 + 4 * k))) s = zq k))
    (\s. read wcode s = MC /\ read wpc s = word 376 /\ read wstatus s = WRunning /\
         read wstack s = [] /\ read wlabels s = [] /\ read warity s = 0 /\
         read wmemsize s = 4194304 /\ read (wlocal 0) s = l0 /\
         (!k. k < 2048 ==> read (wmem :> bytes32 (word (1138688 + 4 * k))) s = rb k) /\
         (!k. k < 2048 ==> read (wmem :> bytes32 (word (1163264 + 4 * k))) s = zq k) /\
         (!k. k < 2048 ==> read (wmem :> bytes64 (word (2015232 + 8 * k))) s = va1_ck_lap rb zq k))
    RF`);;

let r5c_l1_inv mc =
  let t = subst [mc,`MC:byte list`]
   `\i s. read wcode s = MC /\ read wstatus s = WRunning /\
          read wmemsize s = 4194304 /\ read warity s = 0 /\
          read wlabels s = [0,41,0] /\ read (wlocal 0) s = (l0:wval) /\
          read (wlocal 1) s = I32 (word (1163264 + 4 * i)) /\
          read (wlocal 2) s = I32 (word (1138688 + 4 * i)) /\
          read (wlocal 3) s = I32 (word (2015232 + 8 * i)) /\
          read (wlocal 4) s = I32 (word (2047 + i)) /\
          read wstack s = (if read wpc s = word 43 then []
                           else [I32 (word (bitval (~(word (2047 + i) = word 4095:int32))))]) /\
          (!k. k < 2048 ==> read (wmem :> bytes32 (word (1138688 + 4 * k))) s = (rb:num->int32) k) /\
          (!k. k < 2048 ==> read (wmem :> bytes32 (word (1163264 + 4 * k))) s = (zq:num->int32) k) /\
          (!k. k < i ==> read (wmem :> bytes64 (word (2015232 + 8 * k))) s = va1_ck_lap rb zq k)` in
  rhs(concl(TOP_DEPTH_CONV BETA_CONV t));;

let R5C_IDX1P = prove
 (`!i. word_and (word_add (word (2047 + i)) (word 4294965250)) (word 2047):int32 = word ((i + 1) MOD 2048)`,
  GEN_TAC THEN REWRITE_TAC[GSYM WORD_ADD; R5C_AND2047] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `(2047 + i) + 4294965250 = 2097152 * 2048 + (i + 1)` SUBST1_TAC THENL
   [ARITH_TAC; REWRITE_TAC[MOD_MULT_ADD]]);;
let R5C_IDX1M = prove
 (`!i. word_and (word (2047 + i)) (word 2047):int32 = word ((i + 2047) MOD 2048)`,
  REWRITE_TAC[R5C_AND2047; ADD_SYM]);;

(* the floored signed sine of loop 1 lies in [SIN035, 1686629713] *)
let R5C_IVAL_SMALL = prove
 (`!x:int64. val x < 9223372036854775808 ==> ival x = &(val x)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[IVAL_VAL; MSB_VAL; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  SUBGOAL_THEN `(9223372036854775808 <= val (x:int64)) <=> F` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[BITVAL_CLAUSES; INT_MUL_RZERO; INT_SUB_RZERO]]);;

let R5C_IVAL_NEG = prove
 (`!s:int64. val s <= 1686629713 ==> ~(ival (word_sub (word 0) s) > &375809638)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val (word_sub (word 0) (s:int64)) + val s = 18446744073709551616 \/
                (val (word_sub (word 0) s) = 0 /\ val s = 0)` MP_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD_0; DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IVAL_VAL; MSB_VAL; DIMINDEX_64] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ABBREV_TAC `a = val (word_sub (word 0) (s:int64))` THEN
  REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN
  REWRITE_TAC[INT_MUL_RZERO; INT_SUB_RZERO; INT_MUL_RID; INT_GT; INT_OF_NUM_LT] THENL
   [STRIP_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    MP_TAC(ISPEC `word_sub (word 0) (s:int64)` VAL_BOUND) THEN ASM_REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC;
    ASM_ARITH_TAC]);;

let R5C_L1S2 = prove
 (`!s sv:int64. val s <= 1686629713 /\ (sv = s \/ sv = word_sub (word 0) s)
     ==> 375809638 <= val (if ~(ival sv > &375809638) then word 375809638 else sv) /\
         val (if ~(ival sv > &375809638) then word 375809638 else sv) <= 1686629713`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN COND_CASES_TAC THEN
  TRY(REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN NO_TAC) THEN
  POP_ASSUM MP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THENL
   [SUBGOAL_THEN `ival (s:int64) = &(val s)` SUBST1_TAC THENL
     [MATCH_MP_TAC R5C_IVAL_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[INT_GT; INT_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[R5C_IVAL_NEG]]);;

let R5C_L1S2_TAC n : tactic = fun g ->
  let v2 = r5c_local_val n g in
  let th2 = r5c_abdef v2 g in
  let e2 = lhs(concl th2) in
  let v1 = rand e2 in
  let th1 = r5c_abdef v1 g in
  let e1 = lhs(concl th1) in
  let s = rand(rator e1) in
  (MP_TAC(SPECL [s; v1] R5C_L1S2) THEN ANTS_TAC THENL
    [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SUBST1_TAC(SYM th1) THEN COND_CASES_TAC THEN REWRITE_TAC[]];
     REWRITE_TAC[th2] THEN STRIP_TAC] THEN
   MP_TAC(SPEC v2 R5C_SIGDIV_NZ) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC) g;;

let R5C_LAP_CLOSE_TAC =
  REWRITE_TAC[va1_ck_lap] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[] THEN R5C_EXPAND_TAC THEN REWRITE_TAC R5C_KK_DEFS THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[COND_SWAP] THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  (REFL_TAC ORELSE (fun (asl,w) ->
     (match r5c_diff (lhs w) (rhs w) with
        Some(a,b) -> (print_string "@@DIFF L: "; print_term a; print_string "\n@@DIFF R: "; print_term b; print_newline())
      | None -> ()); FAIL_TAC "R5C_LAP_CLOSE_TAC" (asl,w)));;

let R5C_L1_BODY_TAC exec =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MAP_EVERY VK_VAL_TAC [`1163264 + 4 * i`; `1138688 + 4 * i`; `2015232 + 8 * i`] THEN
  MAP_EVERY R5C_WADD_TAC
   [`word_add (word (2015232 + 8 * i)) (word 8):int32 = word (2015232 + 8 * (i + 1))`;
    `word_add (word (1138688 + 4 * i)) (word 4):int32 = word (1138688 + 4 * (i + 1))`;
    `word_add (word (1163264 + 4 * i)) (word 4):int32 = word (1163264 + 4 * (i + 1))`;
    `word_add (word (2047 + i)) (word 1):int32 = word (2047 + (i + 1))`] THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  ASSUME_TAC(SPEC `i:num` R5C_IDX1P) THEN ASSUME_TAC(SPEC `i:num` R5C_IDX1M) THEN
  SUBGOAL_THEN `(i + 1) MOD 2048 < 2048 /\ (i + 2047) MOD 2048 < 2048` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun n -> ASSUME_TAC(UNDISCH(SPEC n R5C_SHL2V))) [`(i + 1) MOD 2048`; `(i + 2047) MOD 2048`] THEN
  VK_LOADFACT_TAC `read (bytes32 (word (1163264 + 4 * i))) mm = zq i` THEN
  VK_LOADFACT_TAC `read (bytes32 (word (1138688 + 4 * i))) mm = rb i` THEN
  VK_LOADFACT2_TAC `read (bytes32 (word (4 * ((i + 1) MOD 2048) + 1163264))) mm = zq ((i + 1) MOD 2048)`
    `1163264 + 4 * ((i + 1) MOD 2048)` THEN
  VK_LOADFACT2_TAC `read (bytes32 (word (4 * ((i + 2047) MOD 2048) + 1163264))) mm = zq ((i + 2047) MOD 2048)`
    `1163264 + 4 * ((i + 2047) MOD 2048)` THEN
  MP_TAC VK_COND_I64 THEN MP_TAC VK_COND_I32 THEN REPEAT DISCH_TAC THEN
  R5C_STEPS_TAC exec 1 112 THEN VK_MSTEPS_TAC exec [113] THEN R5C_FLUSH_TAC THEN
  R5C_SBOUND_TAC 8 `va1_ck_ph (word_sx ((rb:num->int32) i))` THEN R5C_AUTOAB_TAC THEN
  R5C_STEPS_TAC exec 114 125 THEN VK_MSTEPS_TAC exec [126] THEN R5C_FLUSH_TAC THEN
  R5C_L1S2_TAC 8 THEN R5C_AUTOAB_TAC THEN
  R5C_STEPS_TAC exec 127 153 THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
  R5C_L2_MEMGOALS_TAC R5C_LAP_CLOSE_TAC;;

let R5C_L1_TAC mc exec =
  REPEAT GEN_TAC THEN
  ENSURES_WHILE_UP_TAC `2048` `43` `373` (r5c_l1_inv mc) THEN REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    ENSURES_INIT_TAC "s0" THEN MEMNAME_TAC THEN VK_MSTEPS_TAC exec (1--9) THEN
    ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LT];
    R5C_L1_BODY_TAC exec;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`2047 + i`; `4095`] VK_WORD_NE) THEN ANTS_TAC THENL [VK_ARITH_TAC; DISCH_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
    VK_MSTEPS_TAC exec (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV)) THEN
    VK_MSTEPS_TAC exec (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[]];;
(* ---------------- loop 3 (pc 1349 -> end): ZP[k] := OP ZP[k] KZ[k] ---------------- *)
(* retargeted from pop_l3_jdrift.ml (SEG-L3): l4 = -8192 + 16 i, 4 beads per iteration *)
let R5C_WRAP = prove
 (`!a b c. a + b = c + 4294967296 ==> word_add (word a) (word b):int32 = word c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
  REWRITE_TAC[WORD_ADD_0]);;

let r5c_l3_stmt mc op =
  list_mk_forall([`kz:num->int32`; `zp:num->int32`],
  subst [mc,`MC:byte list`; op,`OP:int32->int32->int32`; R5CF,`RF:wasmstate->wasmstate->bool`]
 `ensures wasm
    (\s. read wcode s = MC /\ read wpc s = word 1349 /\ read wstatus s = WRunning /\
         read wstack s = [] /\ read wlabels s = [] /\ read warity s = 0 /\
         read wmemsize s = 4194304 /\
         (!k. k < 2048 ==> read (wmem :> bytes32 (word (2007040 + 4 * k))) s = kz k) /\
         (!k. k < 2048 ==> read (wmem :> bytes32 (word (1171456 + 4 * k))) s = zp k))
    (\s. read wstatus s = WDone /\ read wstack s = [] /\
         (!k. k < 2048 ==> read (wmem :> bytes32 (word (1171456 + 4 * k))) s = OP (zp k) (kz k)))
    RF`);;

let r5c_l3_inv mc op =
  let t = subst [mc,`MC:byte list`; op,`OP:int32->int32->int32`]
   `\i s. read wcode s = MC /\ read wstatus s = WRunning /\
          read wmemsize s = 4194304 /\ read warity s = 0 /\
          read wlabels s = [0,1354,0] /\
          read (wlocal 4) s = I32 (word (4294959104 + 16 * i)) /\
          read wstack s = (if read wpc s = word 1356 then [] else [I32 (word (4294959104 + 16 * i))]) /\
          (!k. k < 2048 ==> read (wmem :> bytes32 (word (1171456 + 4 * k))) s =
                            (if k < 4 * i then OP ((zp:num->int32) k) ((kz:num->int32) k) else zp k)) /\
          (!k. k < 2048 ==> read (wmem :> bytes32 (word (2007040 + 4 * k))) s = kz k)` in
  rhs(concl(TOP_DEPTH_CONV BETA_CONV t));;

let r5c_l3_num n = mk_small_numeral n;;
let r5c_l3_cell b = mk_binop `(+):num->num->num` (r5c_l3_num b) `16 * i`;;
let r5c_l3_idx j = if j = 0 then `4 * i` else mk_binop `(+):num->num->num` `4 * i` (r5c_l3_num j);;

let R5C_L3_BODY_TAC exec =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MAP_EVERY (fun c ->
    SUBGOAL_THEN (subst [r5c_l3_num c,`cc:num`; r5c_l3_cell (c - 8192),`bb:num`]
       `word_add (word (4294959104 + 16 * i)) (word cc):int32 = word bb`) ASSUME_TAC THENL
     [MATCH_MP_TAC R5C_WRAP THEN ARITH_TAC; ALL_TAC])
   [1179648; 2015232; 1179652; 2015236; 1179656; 2015240; 1179660; 2015244] THEN
  MAP_EVERY (fun b -> VAL_TAC (subst [r5c_l3_cell b,`bb:num`] `val(word bb:int32) = bb`))
   [1171456; 2007040; 1171460; 2007044; 1171464; 2007048; 1171468; 2007052] THEN
  SUBGOAL_THEN `word_add (word (4294959104 + 16 * i)) (word 16):int32 =
                word (4294959104 + 16 * (i + 1))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  MAP_EVERY (fun (base,f,j) ->
    let a = r5c_l3_cell (base + 4 * j) and k = r5c_l3_idx j in
    SUBGOAL_THEN (subst [a,`aa:num`; f,`ff:num->int32`; k,`kk:num`]
                   `read (bytes32 (word aa)) mm = (ff:num->int32) kk`) ASSUME_TAC THENL
     [SUBGOAL_THEN (subst [a,`aa:num`; r5c_l3_num base,`bb:num`; k,`kk:num`] `aa = bb + 4 * kk`)
        SUBST1_TAC THENL
       [ARITH_TAC;
        SUBGOAL_THEN (subst [k,`kk:num`] `kk < 2048 /\ ~(kk < 4 * i)`) STRIP_ASSUME_TAC THENL
         [ASM_ARITH_TAC; ASM_SIMP_TAC[]]];
      ALL_TAC])
   (allpairs (fun (b,f) j -> (b,f,j)) [1171456,`zp:num->int32`; 2007040,`kz:num->int32`] [0;1;2;3]) THEN
  MAP_EVERY (fun (r,wj) -> B32O_TAC (r5c_l3_cell r) (r5c_l3_cell (1171456 + 4 * wj)))
   (List.concat (map (fun j -> List.concat (map (fun wj -> if wj < j then
       [(1171456 + 4 * j, wj); (2007040 + 4 * j, wj)] else []) [0;1;2;3])) [0;1;2;3])) THEN
  CAP_MSTEPS_TAC exec (1--52) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MAP_EVERY (fun j -> let c = r5c_l3_idx j in
      ASM_CASES_TAC (subst [c,`cc:num`] `k:num = cc`) THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN REPEAT B32_PEEL_TAC THEN
        REWRITE_TAC[ARITH_RULE (subst [c,`cc:num`] `cc < 4 * (i + 1) <=> T`)];
        ALL_TAC]) [0;1;2;3] THEN
    REPEAT B32_PEEL_TAC THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(k < 4 * (i + 1) <=> k < 4 * i)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[]];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN REPEAT B32_PEEL_TAC THEN ASM_SIMP_TAC[]];;

let R5C_L3_TAC mc exec op =
  REPEAT GEN_TAC THEN
  ENSURES_WHILE_UP_TAC `512` `1356` `1483` (r5c_l3_inv mc op) THEN REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    ENSURES_INIT_TAC "s0" THEN MEMNAME_TAC THEN CAP_MSTEPS_TAC exec (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LT];
    R5C_L3_BODY_TAC exec;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(word (4294959104 + 16 * i):int32 = word 0) <=> F` ASSUME_TAC THENL
     [REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN
      SUBGOAL_THEN `val(word (4294959104 + 16 * i):int32) = 4294959104 + 16 * i` SUBST1_TAC THENL
       [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC;
        REWRITE_TAC[VAL_WORD_0] THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
    CAP_MSTEPS_TAC exec (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV)) THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV WORD_RED_CONV)) THEN
    CAP_MSTEPS_TAC exec (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[]];;
(* ---------------- the export contracts (both halves of va1_corrk_ok va1_ck) ---------------- *)
let r5c_R = `\s. read (wmem :> bytes32 (word 16392)) s = (t:int32) /\
                 read (wmem :> bytes32 (word 16396)) s = (p:int32) /\
                 (!k. k < 1024 ==> read (wmem :> bytes32 (word (16640 + 4 * k))) s = (mdl:num->int32) k) /\
                 (!k. k < 262144 ==> read (wmem :> bytes32 (word (65536 + 4 * k))) s = (tbl:num->int32) k) /\
                 (!k. k < 2048 ==> read (wmem :> bytes32 (word (1171456 + 4 * k))) s = (zp:num->int32) k)`;;
let r5c_ZPR = `\s. (!k. k < 2048 ==> read (wmem :> bytes32 (word (1171456 + 4 * k))) s = (zp:num->int32) k)`;;

let r5c_A376 = `\s. read wstatus s = WRunning /\ read wstack s = [] /\ read wlabels s = [] /\
                 read warity s = 0 /\ read wmemsize s = 4194304 /\ read (wlocal 0) s = I32 (word sub) /\
                 (!k. k < 2048 ==> read (wmem :> bytes32 (word (1138688 + 4 * k))) s = (rb:num->int32) k) /\
                 (!k. k < 2048 ==> read (wmem :> bytes32 (word (1163264 + 4 * k))) s = (zq:num->int32) k) /\
                 (!k. k < 2048 ==> read (wmem :> bytes64 (word (2015232 + 8 * k))) s = va1_ck_lap rb zq k) /\
                 read (wmem :> bytes32 (word 16392)) s = (t:int32) /\
                 read (wmem :> bytes32 (word 16396)) s = (p:int32) /\
                 (!k. k < 1024 ==> read (wmem :> bytes32 (word (16640 + 4 * k))) s = (mdl:num->int32) k) /\
                 (!k. k < 262144 ==> read (wmem :> bytes32 (word (65536 + 4 * k))) s = (tbl:num->int32) k) /\
                 (!k. k < 2048 ==> read (wmem :> bytes32 (word (1171456 + 4 * k))) s = (zp:num->int32) k)`;;

let r5c_A467 = subst [r5c_l9,`L9:int32`; r5c_l10,`L10:int32`]
 `\s. read wstatus s = WRunning /\ read wstack s = [] /\ read wlabels s = [] /\
      read warity s = 0 /\ read wmemsize s = 4194304 /\
      read (wlocal 1) s = I32 (word 1138688) /\ read (wlocal 2) s = I32 (word 2007040) /\
      read (wlocal 3) s = I32 (word 65536) /\ read (wlocal 4) s = I32 (word 0) /\
      read (wlocal 5) s = I32 (word 1163264) /\ read (wlocal 6) s = I32 (word 2015232) /\
      read (wlocal 9) s = I32 L9 /\ read (wlocal 10) s = I32 L10 /\
      read (wmem :> bytes32 (word 16648)) s = (mdl:num->int32) 2 /\
      (!k. k < 262144 ==> read (wmem :> bytes32 (word (65536 + 4 * k))) s = (tbl:num->int32) k) /\
      (!k. k < 2048 ==> read (wmem :> bytes32 (word (1138688 + 4 * k))) s = (rb:num->int32) k) /\
      (!k. k < 2048 ==> read (wmem :> bytes32 (word (1163264 + 4 * k))) s = (zq:num->int32) k) /\
      (!k. k < 2048 ==> read (wmem :> bytes64 (word (2015232 + 8 * k))) s = va1_ck_lap rb zq k) /\
      (!k. k < 2048 ==> read (wmem :> bytes32 (word (1171456 + 4 * k))) s = (zp:num->int32) k)`;;

let r5c_A1349 =
 `\s. read wstatus s = WRunning /\ read wstack s = [] /\ read wlabels s = [] /\
      read warity s = 0 /\ read wmemsize s = 4194304 /\
      (!k. k < 2048 ==> read (wmem :> bytes32 (word (2007040 + 4 * k))) s =
                        va1_ck (mdl:num->int32) (hp:num->int32) (tbl:num->int32) (t:int32) (p:int32) sub (rb:num->int32) (zq:num->int32) k) /\
      (!k. k < 2048 ==> read (wmem :> bytes32 (word (1171456 + 4 * k))) s = (zp:num->int32) k)`;;

(* use a segment lemma instance th under a frame-stable fact r *)
let R5C_USE_SEG_TAC th r pretac posttac frametac =
  MATCH_MP_TAC VK_ENSURES_SEG THEN
  EXISTS_TAC (rand(rator(rator(concl th)))) THEN EXISTS_TAC (rand(rator(concl th))) THEN
  EXISTS_TAC r THEN REPEAT CONJ_TAC THENL
   [ACCEPT_TAC th;
    X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN pretac;
    X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN posttac;
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN frametac];;

let R5C_CLOSE_FACTS_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[]);;

(* local 0 = the parameter sub, from the call frame *)
let R5C_WLOCAL0_TAC =
  FIRST_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `wlocals`)) (concl th))) THEN
  REWRITE_TAC[wlocal; READ_COMPONENT_COMPOSE] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[wcall_locals; LENGTH; READ_ELEMENT] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[EL; HD];;

let R5C_MID_TAC exec =
  ENSURES_INIT_TAC "s0" THEN MEMNAME_TAC THEN
  SUBGOAL_THEN `read (bytes32 (word 16392)) mm = (t:int32) /\ read (bytes32 (word 16396)) mm = (p:int32)`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "mm" THEN REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  VK_LOADFACT2_TAC `read (bytes32 (word 16648)) mm = (mdl:num->int32) 2` `16640 + 4 * 2` THEN
  VK_MSTEPS_TAC exec (1--31) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[];;

let R5C_EXPORT_TAC mc exec l1th l2th l3th =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[va1_tick; va1_pop; va1_mdl; va1_w32s] THEN
  ENSURES_SEQUENCE_TAC `1349` r5c_A1349 THEN CONJ_TAC THENL
   [MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC R5CF0 THEN CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
    ENSURES_SEQUENCE_TAC `467` r5c_A467 THEN CONJ_TAC THENL
     [ENSURES_SEQUENCE_TAC `376` r5c_A376 THEN CONJ_TAC THENL
       [R5C_USE_SEG_TAC (SPECL [`I32 (word sub)`; `rb:num->int32`; `zq:num->int32`] l1th) r5c_R
         (CONJ_TAC THENL [R5C_CLOSE_FACTS_TAC THEN R5C_WLOCAL0_TAC; R5C_CLOSE_FACTS_TAC])
         R5C_CLOSE_FACTS_TAC VK_FRAME_TAC;
        R5C_MID_TAC exec];
      R5C_USE_SEG_TAC (SPECL [`mdl:num->int32`; `tbl:num->int32`; `t:int32`; `p:int32`; `sub:num`;
                              `rb:num->int32`; `zq:num->int32`; `va1_ck_lap rb zq`] l2th) r5c_ZPR
        R5C_CLOSE_FACTS_TAC (REWRITE_TAC[va1_ck] THEN R5C_CLOSE_FACTS_TAC) VK_FRAME_TAC];
    R5C_USE_SEG_TAC (SPECL [`va1_ck mdl hp tbl t p sub rb zq`; `zp:num->int32`] l3th) `\s:wasmstate. T`
      R5C_CLOSE_FACTS_TAC (CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN R5C_CLOSE_FACTS_TAC) (REWRITE_TAC[])];;
let r5c_time name f x =
  let t0 = Sys.time () in
  let r = f x in
  Printf.printf "@@TIME %s %.1fs\n%!" name (Sys.time () -. t0); r;;
let R5C_F17_EXEC = r5c_time "exec f17" (fun () -> FAST_MK_EXEC_RULE va1_f17_mc 15) ();;
let R5C_F18_EXEC = r5c_time "exec f18" (fun () -> FAST_MK_EXEC_RULE va1_f18_mc 15) ();;

let R5C_L1_F17 = r5c_time "L1 f17" (fun () -> prove(r5c_l1_stmt `va1_f17_mc`, R5C_L1_TAC `va1_f17_mc` R5C_F17_EXEC)) ();;
let R5C_L2_F17 = r5c_time "L2 f17" (fun () -> prove(r5c_l2_stmt `va1_f17_mc`, R5C_L2_TAC `va1_f17_mc` R5C_F17_EXEC)) ();;
let R5C_L3_F17 = r5c_time "L3 f17" (fun () -> prove(r5c_l3_stmt `va1_f17_mc` `word_add:int32->int32->int32`,
   R5C_L3_TAC `va1_f17_mc` R5C_F17_EXEC `word_add:int32->int32->int32`)) ();;
let R5C_F17_OK = r5c_time "export f17" (fun () -> prove(lhand(rhs(concl(SPEC `va1_ck` va1_corrk_ok))),
   R5C_EXPORT_TAC `va1_f17_mc` R5C_F17_EXEC R5C_L1_F17 R5C_L2_F17 R5C_L3_F17)) ();;

let R5C_L1_F18 = r5c_time "L1 f18" (fun () -> prove(r5c_l1_stmt `va1_f18_mc`, R5C_L1_TAC `va1_f18_mc` R5C_F18_EXEC)) ();;
let R5C_L2_F18 = r5c_time "L2 f18" (fun () -> prove(r5c_l2_stmt `va1_f18_mc`, R5C_L2_TAC `va1_f18_mc` R5C_F18_EXEC)) ();;
let R5C_L3_F18 = r5c_time "L3 f18" (fun () -> prove(r5c_l3_stmt `va1_f18_mc` `word_sub:int32->int32->int32`,
   R5C_L3_TAC `va1_f18_mc` R5C_F18_EXEC `word_sub:int32->int32->int32`)) ();;
let R5C_F18_OK = r5c_time "export f18" (fun () -> prove(rand(rhs(concl(SPEC `va1_ck` va1_corrk_ok))),
   R5C_EXPORT_TAC `va1_f18_mc` R5C_F18_EXEC R5C_L1_F18 R5C_L2_F18 R5C_L3_F18)) ();;
