needs "ve_vort.ml";;
needs "ve_tick.ml";;
needs "ve_vk.ml";;
needs "va1_code.ml";;
needs "va1_seq_final2.ml";;
needs "pop_design_defs.ml";;
needs "pop_design_stmts.ml";;
(* ========================================================================= *)
(* Vortex pop effort, segment H1 (pure-HOL algebra for rungs R1-R3), prover *)
(* H1 (Claude Opus 5.5), 2026-11-11. TAIL layer 1 of the design (section 5): *)
(* PREFIX, then this file, then pop_n1_sat.ml, then q0/q1/q2.               *)
(* Goals: the frozen strings of pop_design_stmts.ml (sha256 97f899dc...),   *)
(* each proved as prove(parse_term pop_spec_NAME, TAC), so every statement  *)
(* is character-identical to the frozen one: VA1_PUSH_CLAUSES,               *)
(* VA1_UNB_CLAUSES, VA1P_KD_FWDN_CLAUSES, VA1P_KD_BWDN_CLAUSES,              *)
(* VA1_WINDOW_FACTS, VA1_PUSH_ND, VA1_DROP_INVERSE, VA1_LOG_OK_DROP,         *)
(* VA1_LOG_OK_PUSH, VA1_PUSH_UNB_INVERSE, VA1_LOG_OK_POP_FWD. Helper lemmas  *)
(* carry the prefix VA1H. Pure HOL: no wasm stepping, no new definitions,   *)
(* no parser changes, no mk_thm / new_axiom / CHEAT_TAC.                     *)
(*                                                                           *)
(* Main argument (VA1_PUSH_UNB_INVERSE): va1_unb b peels exactly the        *)
(* records pushed by va1_push L when every record of L is stamped b and the *)
(* free slots are zero (VA1H_UNB_PUSH_GEN, induction on L with the count     *)
(* c + LENGTH L); one pop undoes one push (VA1H_POP1_PUSH1: the slot was     *)
(* zero, debit and credit cancel mod 2^32); un-birth then stops at the old   *)
(* top, whose tag is at most T and so differs from T+1 (no wrap).            *)
(* ========================================================================= *)

(* ---- H1 helper lemmas, prefix VA1H ---- *)
let VA1H_VAL_ADD1 = prove
 (`!x:int32. val x + 1 < 4294967296 ==> val (word_add x (word 1)) = val x + 1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_1; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT]);;

let VA1H_VAL_SUC = prove
 (`!t:int32. ~(word_add t (word 1) = word 0) ==> val (word_add t (word 1)) = val t + 1`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC VA1H_VAL_ADD1 THEN
  MP_TAC(ISPEC `t:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `x < 4294967296 /\ ~(x = 4294967295) ==> x + 1 < 4294967296`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `~(word_add t (word 1):int32 = word 0)` THEN REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  ASM_REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_1; VAL_WORD_0; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let VA1H_MOD12 = prove
 (`!i j. j < 12 ==> (12 * i + j) MOD 12 = j`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT]);;

let VA1H_SLOT6 = prove
 (`!n. (12 * n <= 12 * n + 6 /\ 12 * n + 6 < 12 * n + 12) /\ (12 * n + 6) - 12 * n = 6`,
  ARITH_TAC);;

let VA1H_LT12 = prove
 (`!q c M. c < 12 ==> (q * 12 + c < 12 * M <=> q < M)`,
  ARITH_TAC);;

let VA1H_PUSH1_ND = prove
 (`!r di zq zp nd. SND(SND(SND(va1_push1 r (di,zq,zp,nd)))) = word_add nd (word 1)`,
  REWRITE_TAC[va1_push1; LET_DEF; LET_END_DEF; FST; SND]);;

let VA1H_PUSH1_DI = prove
 (`!r di zq zp nd w. FST (va1_push1 r (di,zq,zp,nd)) w =
      if 12 * val nd <= w /\ w < 12 * val nd + 12 then r (w - 12 * val nd) else di w`,
  REWRITE_TAC[va1_push1; LET_DEF; LET_END_DEF; FST; SND]);;

let VA1H_POP1_PUSH1 = prove
 (`!r di zq zp nd.
     val (nd:int32) < 16384 /\
     (!w. 12 * val nd <= w /\ w < 12 * val nd + 12 ==> di w = word 0)
     ==> va1_pop1 (va1_push1 r (di,zq,zp,nd)) = (di,zq,zp,nd)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val (word_add nd (word 1):int32) = val (nd:int32) + 1` ASSUME_TAC THENL
  [MATCH_MP_TAC VA1H_VAL_ADD1 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[va1_push1; va1_pop1; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[ADD_SUB; WORD_VAL; PAIR_EQ] THEN
  REWRITE_TAC[ARITH_RULE `12 * n <= 12 * n + 7 /\ 12 * n + 7 < 12 * n + 12 /\ (12 * n + 7) - 12 * n = 7`;
              ARITH_RULE `12 * n <= 12 * n + 8 /\ 12 * n + 8 < 12 * n + 12 /\ (12 * n + 8) - 12 * n = 8`;
              ARITH_RULE `12 * n <= 12 * n + 9 /\ 12 * n + 9 < 12 * n + 12 /\ (12 * n + 9) - 12 * n = 9`] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN REPEAT CONJ_TAC THEN X_GEN_TAC `i:num` THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE);;

let VA1H_UNB_PUSH1 = prove
 (`!b r di zq zp nd c.
     val (nd:int32) < 16384 /\ r 6 = b /\
     (!w. 12 * val nd <= w /\ w < 12 * val nd + 12 ==> di w = word 0)
     ==> va1_unb b (SUC c) (va1_push1 r (di,zq,zp,nd)) = va1_unb b c (di,zq,zp,nd)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val (word_add nd (word 1):int32) = val (nd:int32) + 1` ASSUME_TAC THENL
  [MATCH_MP_TAC VA1H_VAL_ADD1 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[CONJUNCT2 va1_unb; VA1H_PUSH1_ND; VA1H_PUSH1_DI] THEN
  ASM_REWRITE_TAC[ADD_SUB; VA1H_SLOT6; ARITH_RULE `0 < n + 1`] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC VA1H_POP1_PUSH1 THEN ASM_REWRITE_TAC[]);;

let VA1H_UNB_PUSH_GEN = prove
 (`!b L bs c.
     (!w. 12 * val (SND(SND(SND bs))) <= w /\ w < 196608 ==> FST bs w = word 0) /\
     ALL (\r:num->int32. r 6 = b) L /\
     val (SND(SND(SND (bs:(num->int32)#(num->int32)#(num->int32)#int32)))) + LENGTH L <= 16384
     ==> va1_unb b (c + LENGTH L) (va1_push L bs) = va1_unb b c bs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[va1_push; LENGTH; ADD_CLAUSES; ALL] THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`di:num->int32`; `zq:num->int32`; `zp:num->int32`; `nd:int32`; `c:num`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `val (word_add nd (word 1):int32) = val (nd:int32) + 1` ASSUME_TAC THENL
  [MATCH_MP_TAC VA1H_VAL_ADD1 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `SUC(c + n) = SUC c + n`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`va1_push1 h (di,zq,zp,nd)`; `SUC c`]) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[VA1H_PUSH1_ND; VA1H_PUSH1_DI] THEN CONJ_TAC THENL
   [X_GEN_TAC `w:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(w < 12 * val (nd:int32) + 12)` (fun th -> REWRITE_TAC[th]) THENL
    [ASM_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ASM_ARITH_TAC];
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC VA1H_UNB_PUSH1 THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `w:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let VA1H_LOG_OK_PUSH1 = prove
 (`!u r di zq zp nd.
     va1_log_ok u di nd /\ r 6 = u /\ val (nd:int32) < 16384
     ==> va1_log_ok u (FST (va1_push1 r (di,zq,zp,nd))) (word_add nd (word 1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_log_ok] THEN STRIP_TAC THEN
  SUBGOAL_THEN `val (word_add nd (word 1):int32) = val (nd:int32) + 1` ASSUME_TAC THENL
  [MATCH_MP_TAC VA1H_VAL_ADD1 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[VA1H_PUSH1_ND; VA1H_PUSH1_DI] THEN REPEAT CONJ_TAC THENL
  [ASM_ARITH_TAC;
   X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_CASES_TAC `i = val (nd:int32)` THENL
   [ASM_REWRITE_TAC[VA1H_SLOT6; LE_REFL];
    SUBGOAL_THEN `~(12 * val (nd:int32) <= 12 * i + 6)` (fun th -> REWRITE_TAC[th]) THENL
    [ASM_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]];
   X_GEN_TAC `w:num` THEN STRIP_TAC THEN
   SUBGOAL_THEN `~(w < 12 * val (nd:int32) + 12)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

let VA1H_LOG_OK_PUSH_GEN = prove
 (`!u L bs. va1_log_ok u (FST bs) (SND(SND(SND bs))) /\ ALL (\r:num->int32. r 6 = u) L /\
            val (SND(SND(SND (bs:(num->int32)#(num->int32)#(num->int32)#int32)))) + LENGTH L <= 16384
            ==> va1_log_ok u (FST (va1_push L bs)) (SND(SND(SND (va1_push L bs))))`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL [SIMP_TAC[va1_push]; ALL_TAC] THEN
  REWRITE_TAC[va1_push; LENGTH; ALL] THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`di:num->int32`; `zq:num->int32`; `zp:num->int32`; `nd:int32`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `val (word_add nd (word 1):int32) = val (nd:int32) + 1` ASSUME_TAC THENL
  [MATCH_MP_TAC VA1H_VAL_ADD1 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[VA1H_PUSH1_ND] THEN CONJ_TAC THENL
  [MATCH_MP_TAC VA1H_LOG_OK_PUSH1 THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let VA1H_LOG_OK_MONO = prove
 (`!t u di nd. va1_log_ok t di nd /\ val (t:int32) <= val (u:int32) ==> va1_log_ok u di nd`,
  REWRITE_TAC[va1_log_ok] THEN MESON_TAC[LE_TRANS]);;

(* ---- the frozen H1 goals ---- *)
let VA1_PUSH_CLAUSES = prove(parse_term pop_spec_VA1_PUSH_CLAUSES, REWRITE_TAC[va1_push]);;
let VA1_UNB_CLAUSES = prove(parse_term pop_spec_VA1_UNB_CLAUSES, REWRITE_TAC[va1_unb]);;
let VA1P_KD_FWDN_CLAUSES = prove(parse_term pop_spec_VA1P_KD_FWDN_CLAUSES, REWRITE_TAC[ve_kd_fwdn]);;
let VA1P_KD_BWDN_CLAUSES = prove(parse_term pop_spec_VA1P_KD_BWDN_CLAUSES, REWRITE_TAC[ve_kd_bwdn]);;

let VA1_WINDOW_FACTS = prove(parse_term pop_spec_VA1_WINDOW_FACTS,
  REWRITE_TAC[va1_pop_window] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val (word_add t (word 1):int32) = val (t:int32) + 1` ASSUME_TAC THENL
  [MATCH_MP_TAC VA1H_VAL_ADD1 THEN
   MP_TAC(ISPEC `word_add p (word 520):int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN
   CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[NOT_LE] THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[VAL_WORD_0] THEN ASM_ARITH_TAC);;

let VA1_PUSH_ND = prove(parse_term pop_spec_VA1_PUSH_ND,
  LIST_INDUCT_TAC THEN REWRITE_TAC[va1_push; LENGTH; FST; SND; WORD_ADD_0] THEN
  REWRITE_TAC[ADD1; WORD_ADD] THEN
  REPEAT GEN_TAC THEN ASM_REWRITE_TAC[va1_push1; LET_DEF; LET_END_DEF] THEN CONV_TAC WORD_RULE);;

let VA1_DROP_INVERSE = prove(parse_term pop_spec_VA1_DROP_INVERSE,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:num` THEN
  REWRITE_TAC[va1_drop_bwd; va1_drop_fwd] THEN
  SPEC_TAC(`MIN (val (nd:int32)) 16384`,`M:num`) THEN GEN_TAC THEN
  MP_TAC(SPECL [`w:num`; `12`] DIVISION) THEN REWRITE_TAC[ARITH_RULE `~(12 = 0)`] THEN
  MAP_EVERY ABBREV_TAC [`q = w DIV 12`; `r = w MOD 12`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
  SPEC_TAC(`r:num`,`r:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MULT_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[VA1H_LT12; ARITH] THEN
  REPEAT CONJ_TAC THEN ASM_CASES_TAC `q < M:num` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_RULE);;

let VA1_LOG_OK_DROP = prove(parse_term pop_spec_VA1_LOG_OK_DROP,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_log_ok; va1_drop_fwd] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `MIN (val (nd:int32)) 16384 = val nd` SUBST1_TAC THENL
  [REWRITE_TAC[MIN] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
  [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   SIMP_TAC[VA1H_MOD12; ARITH] THEN REWRITE_TAC[COND_ID] THEN ASM_SIMP_TAC[];
   X_GEN_TAC `w:num` THEN STRIP_TAC THEN
   ASM_SIMP_TAC[ARITH_RULE `a <= w ==> ~(w < a)`]]);;

let VA1_LOG_OK_PUSH = prove(parse_term pop_spec_VA1_LOG_OK_PUSH,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word_add t (word 1):int32`; `L:(num->int32)list`;
                 `(di,zq,zp,nd):(num->int32)#(num->int32)#(num->int32)#int32`] VA1H_LOG_OK_PUSH_GEN) THEN
  REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC VA1H_LOG_OK_MONO THEN EXISTS_TAC `t:int32` THEN
  ASM_SIMP_TAC[VA1H_VAL_SUC; ARITH_RULE `x <= x + 1`]);;

let VA1_PUSH_UNB_INVERSE = prove(parse_term pop_spec_VA1_PUSH_UNB_INVERSE,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_log_ok] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`word_add t (word 1):int32`; `L:(num->int32)list`;
                 `(di,zq,zp,nd):(num->int32)#(num->int32)#(num->int32)#int32`; `val(nd:int32)`]
                VA1H_UNB_PUSH_GEN) THEN
  ASM_REWRITE_TAC[FST; SND] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_CASES_TAC `val (nd:int32) = 0` THENL [ASM_REWRITE_TAC[va1_unb]; ALL_TAC] THEN
  SUBGOAL_THEN `?k. val (nd:int32) = SUC k` (X_CHOOSE_TAC `k:num`) THENL
  [EXISTS_TAC `val (nd:int32) - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(di (12 * k + 6) = word_add t (word 1):int32)` ASSUME_TAC THENL
  [DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN ASM_SIMP_TAC[VA1H_VAL_SUC] THEN
   MATCH_MP_TAC(ARITH_RULE `a <= b ==> ~(a = b + 1)`) THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[CONJUNCT2 va1_unb; FST; SND; SUC_SUB1]);;

let VA1_LOG_OK_POP_FWD = prove(parse_term pop_spec_VA1_LOG_OK_POP_FWD,
  REPEAT STRIP_TAC THEN REWRITE_TAC[va1_pop_fwd; LET_DEF; LET_END_DEF; FST; SND] THEN
  MATCH_MP_TAC VA1_LOG_OK_PUSH THEN ASM_SIMP_TAC[VA1_LOG_OK_DROP]);;
