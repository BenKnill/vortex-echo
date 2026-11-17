(* vortex-chain C8a (Claude Opus 5.5, 2026-11-14): pure-HOL shape lemmas: record tags, fold shapes, VA1_BORN_SHAPE, VA1_BIRTH_EQ_OK *)
let C8A_REC_TAC def = REPEAT GEN_TAC THEN REWRITE_TAC[def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[va1_rec12] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;
let C8A_REC1_TAG = prove(`!mdl hp tbl t rb zq zp k. va1_b1_rec mdl hp tbl t rb zq zp k 6 = word_add t (word 1) /\
   va1_b1_rec mdl hp tbl t rb zq zp k 10 = word 0 /\ va1_b1_rec mdl hp tbl t rb zq zp k 11 = word 0`, C8A_REC_TAC va1_b1_rec);;
let C8A_REC2_TAG = prove(`!mdl hp tbl t rb k. va1_b2_rec mdl hp tbl t rb k 6 = word_add t (word 1) /\
   va1_b2_rec mdl hp tbl t rb k 10 = word 0 /\ va1_b2_rec mdl hp tbl t rb k 11 = word 0`, C8A_REC_TAC va1_b2_rec);;
let C8A_REC3_TAG = prove(`!mdl hp tbl t rb k. va1_b3_rec mdl hp tbl t rb k 6 = word_add t (word 1) /\
   va1_b3_rec mdl hp tbl t rb k 10 = word 0 /\ va1_b3_rec mdl hp tbl t rb k 11 = word 0`, C8A_REC_TAC va1_b3_rec);;
let C8A_FOLD1_SHAPE = prove(`!mdl hp tbl t rb nd k st. ALL (\r:num->int32. r 6 = word_add t (word 1) /\ r 10 = word 0 /\ r 11 = word 0) (FST st) /\ val (nd:int32) + LENGTH (FST st) <= 16384
   ==> ALL (\r:num->int32. r 6 = word_add t (word 1) /\ r 10 = word 0 /\ r 11 = word 0) (FST (va1_fold1 mdl hp tbl t rb nd k st)) /\
       val nd + LENGTH (FST (va1_fold1 mdl hp tbl t rb nd k st)) <= 16384`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[va1_fold1] THEN GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `st:(num->int32)list#(num->int32)#(num->int32)`) THEN
  ASM_REWRITE_TAC[] THEN SPEC_TAC(`va1_fold1 mdl hp tbl t rb nd k st`,`s:(num->int32)list#(num->int32)#(num->int32)`) THEN
  GEN_TAC THEN REWRITE_TAC[va1_step1] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[ALL_APPEND; ALL; LENGTH_APPEND; LENGTH] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[C8A_REC1_TAG] THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_LE] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;
let C8A_FOLD2_SHAPE = prove(`!mdl hp tbl t rb nd k L. ALL (\r:num->int32. r 6 = word_add t (word 1) /\ r 10 = word 0 /\ r 11 = word 0) L /\ val (nd:int32) + LENGTH L <= 16384
   ==> ALL (\r:num->int32. r 6 = word_add t (word 1) /\ r 10 = word 0 /\ r 11 = word 0) (va1_fold2 mdl hp tbl t rb nd k L) /\
       val nd + LENGTH (va1_fold2 mdl hp tbl t rb nd k L) <= 16384`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[va1_fold2] THEN GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `L:(num->int32)list`) THEN
  ASM_REWRITE_TAC[] THEN SPEC_TAC(`va1_fold2 mdl hp tbl t rb nd k L`,`l:(num->int32)list`) THEN
  GEN_TAC THEN REWRITE_TAC[va1_step2] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[ALL_APPEND; ALL; LENGTH_APPEND; LENGTH] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[C8A_REC2_TAG] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_LE]) THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;
let C8A_FOLD3_SHAPE = prove(`!mdl hp tbl t ra rb nd k L. ALL (\r:num->int32. r 6 = word_add t (word 1) /\ r 10 = word 0 /\ r 11 = word 0) L /\ val (nd:int32) + LENGTH L <= 16384
   ==> ALL (\r:num->int32. r 6 = word_add t (word 1) /\ r 10 = word 0 /\ r 11 = word 0) (va1_fold3 mdl hp tbl t ra rb nd k L) /\
       val nd + LENGTH (va1_fold3 mdl hp tbl t ra rb nd k L) <= 16384`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[va1_fold3] THEN GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `L:(num->int32)list`) THEN
  ASM_REWRITE_TAC[] THEN SPEC_TAC(`va1_fold3 mdl hp tbl t ra rb nd k L`,`l:(num->int32)list`) THEN
  GEN_TAC THEN REWRITE_TAC[va1_step3] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[ALL_APPEND; ALL; LENGTH_APPEND; LENGTH] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[C8A_REC3_TAG] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_LE]) THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;
let VA1_BORN_SHAPE = prove(`!mdl hp tbl t ra rb zq zp nd. val nd <= 16384
    ==> ALL (\r. r 6 = word_add t (word 1) /\ r 10 = word 0 /\ r 11 = word 0) (va1_born mdl hp tbl t ra rb zq zp nd) /\
        val nd + LENGTH (va1_born mdl hp tbl t ra rb zq zp nd) <= 16384`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[va1_born] THEN
  MATCH_MP_TAC C8A_FOLD3_SHAPE THEN MATCH_MP_TAC C8A_FOLD2_SHAPE THEN MATCH_MP_TAC C8A_FOLD1_SHAPE THEN
  ASM_REWRITE_TAC[ALL; LENGTH; ADD_CLAUSES]);;
let VA1_BIRTH_EQ_OK = prove(`va1_birth_eq ==> va1_birth_ok`,
  REWRITE_TAC[va1_birth_eq; va1_birth_ok] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`mdl:num->int32`; `hp:num->int32`; `tbl:num->int32`; `t:int32`; `p:int32`; `ap:int32`;
     `ra:num->int32`; `rb:num->int32`; `di:num->int32`; `zq:num->int32`; `zp:num->int32`; `nd:int32`; `decls:wval list`]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_POSTCONDITION_THM) THEN
  REWRITE_TAC[] THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `va1_born mdl hp tbl t ra rb zq zp nd` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC VA1_BORN_SHAPE THEN ASM_MESON_TAC[va1_log_ok]);;
