(* vortex-chain rung C8e row E4 pure part (c8e_k1b: kind-1 inverse; replaces c8e_k1.ml, whose copy kept a broken first C8E_JIDX attempt), C8e PROVER (Claude Opus 5.5), 2026-11-15. *)
let C8E_IVAL_LE = prove
 (`!x:int32. ~(ival x > &52371633) /\ ival x > &0 ==> val x <= 52371633`,
  GEN_TAC THEN REWRITE_TAC[ival; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `x:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC);;
let C8E_JIDX = prove
 (`!r:int32 c. val r <= 52371633
     ==> val (word_and (word_ushr r 17) (word c):int32) DIV 4 <= 99`,
  REPEAT STRIP_TAC THEN TRANS_TAC LE_TRANS `val (word_ushr (r:int32) 17) DIV 4` THEN
  CONJ_TAC THENL [MATCH_MP_TAC DIV_MONO THEN REWRITE_TAC[VAL_WORD_AND_LE]; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_USHR] THEN ASM_ARITH_TAC);;
let C8E_SM_TAC : tactic =
  FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `2048`)) (concl th)
                         then REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `m < 2048`))] else failwith "");;
let C8E_TBLIDX_TAC (jt:term) : tactic =
  ABBREV_TAC (mk_eq(`J:num`, jt)) THEN
  SUBGOAL_THEN `J <= 99` ASSUME_TAC THENL [EXPAND_TAC "J" THEN MATCH_MP_TAC C8E_JIDX THEN
    FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(tbl:num->int32) (128 * m + J) = tbl' (128 * m + J) /\ tbl (128 * m + J + 1) = tbl' (128 * m + J + 1)`
    (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN C8E_ARITH_TAC;;
let C8E_RIMD_LF = prove
 (`!tbl tbl'. (!k. k < 262144 ==> tbl k = tbl' k) ==> c8e_lf 2048 (va1_rimd tbl) (va1_rimd tbl')`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[c8e_lf] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[va1_rimd] THEN C8E_SM_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ABBREV_TAC `r = if ival ((S:num->int32) m) > &0 then S m else word 0` THEN
  SUBGOAL_THEN `val (r:int32) <= 52371633` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN COND_CASES_TAC THEN REWRITE_TAC[VAL_WORD_0; LE_0] THEN
    MATCH_MP_TAC C8E_IVAL_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  C8E_TBLIDX_TAC `val (word_and (word_ushr (r:int32) 17) (word 16380):int32) DIV 4`);;
(* instantiate every assumption !k. k < 2048 ==> ... at the given indices and rewrite with the results *)
let C8E_AGREE_TAC (idxs:term list) : tactic = fun (asl,w) ->
  let isfa th = let c = concl th in is_forall c &&
    (let b = snd(dest_forall c) in is_imp b && can (term_match [] `x < 2048`) (lhand b)) in
  let fas = filter isfa (map snd asl) in
  let ths = List.concat (map (fun fa -> let v = fst(dest_forall(concl fa)) in
     map (fun i -> let i' = inst [] i in
       let lt = TAC_PROOF((asl, mk_binop `(<):num->num->bool` i' `2048`),
                  FIRST [C8E_ARITH_TAC; SIMP_TAC[MOD_LT_EQ; ARITH_EQ] THEN NO_TAC]) in
       MATCH_MP (SPEC i' fa) lt) (filter (fun i -> type_of i = type_of v) idxs)) fas) in
  REWRITE_TAC ths (asl,w);;
let C8E_LAP_LOC = prove
 (`!rb rb' zq zq' k. (!k. k < 2048 ==> rb k = rb' k /\ zq k = zq' k) /\ k < 2048
     ==> va1_ck_lap rb zq k = va1_ck_lap rb' zq' k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[va1_ck_lap] THEN
  C8E_AGREE_TAC [`k:num`; `(k + 1) MOD 2048`; `(k + 2047) MOD 2048`]);;
let C8E_CDRIFT_LF = prove
 (`!rb rb'. (!k. k < 2048 ==> rb k = rb' k) ==> c8e_lf 2048 (va1_cdrift rb) (va1_cdrift rb')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[c8e_lf; va1_cdrift] THEN REPEAT STRIP_TAC THEN C8E_AGREE_TAC [`m:num`]);;
let C8E_JDRIFT_LF = prove
 (`!mdl mdl'. mdl' 3 = mdl 3 ==> c8e_lf 2048 (va1_jdrift mdl) (va1_jdrift mdl')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[c8e_lf; va1_jdrift] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  C8E_AGREE_TAC [`m:num`]);;
let C8E_BAND = prove
 (`!r:int32. ~(val (word_add r (word 4293289574)) > 50693911) ==> val r <= 52371633`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_ADD; DIMINDEX_32; VAL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `r:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN ASM_CASES_TAC `val (r:int32) < 1677722` THENL
   [ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < 1677722 ==> x + 4293289574 < 4294967296`] THEN ARITH_TAC;
    SUBGOAL_THEN `val (r:int32) + 4293289574 = (val r - 1677722) + 1 * 4294967296` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[MOD_MULT_ADD]] THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < 4294967296 ==> x - 1677722 < 4294967296`] THEN ARITH_TAC]);;
let C8E_CKSPD_LOC = prove
 (`!tbl tbl' r m. (!k. k < 262144 ==> tbl k = tbl' k) /\ val (r:int32) <= 52371633 /\ m < 2048
     ==> va1_ck_spd tbl r m = va1_ck_spd tbl' r m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[va1_ck_spd; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  C8E_TBLIDX_TAC `val (word_and (word_ushr (r:int32) 17) (word 32764):int32) DIV 4`);;
let C8E_JGSPD_LOC = prove
 (`!tbl tbl' r m. (!k. k < 262144 ==> tbl k = tbl' k) /\ ival (r:int32) < &52371634 /\ m < 2048
     ==> va1_jg_spd tbl r m = va1_jg_spd tbl' r m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[va1_jg_spd; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ABBREV_TAC `rr = if ival (r:int32) > &0 then r else word 0` THEN
  SUBGOAL_THEN `val (rr:int32) <= 52371633` ASSUME_TAC THENL
   [EXPAND_TAC "rr" THEN COND_CASES_TAC THEN REWRITE_TAC[VAL_WORD_0; LE_0] THEN
    MATCH_MP_TAC C8E_IVAL_LE THEN ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  C8E_TBLIDX_TAC `val (word_and (word_ushr (rr:int32) 17) (word 16380):int32) DIV 4`);;
let C8E_JGF_LOC = prove
 (`!hp hp' t p m. (!k. k < 24 ==> hp k = hp' k) ==> va1_jg_f hp t p m = va1_jg_f hp' t p m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[va1_jg_f; va1_jg_term; va1_jg_ph] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[ARITH]);;
let C8E_CK_LF = prove
 (`!mdl mdl' hp hp' tbl tbl' t p i rb rb'.
     mdl' 2 = mdl 2 /\ (!k. k < 262144 ==> tbl k = tbl' k) /\ (!k. k < 2048 ==> rb k = rb' k)
     ==> c8e_lf 2048 (va1_ck mdl hp tbl t p i rb) (va1_ck mdl' hp' tbl' t p i rb')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[c8e_lf; va1_ck] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!k. k < 2048 ==> va1_ck_lap rb S k = va1_ck_lap rb' S' k` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC C8E_LAP_LOC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[va1_ck_kk] THEN C8E_AGREE_TAC [`m:num`; `(m + 1) MOD 2048`; `(m + 2047) MOD 2048`] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ASM_CASES_TAC `val (word_add ((rb':num->int32) m) (word 4293289574)) > 50693911` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP C8E_BAND) THEN
  SUBGOAL_THEN `va1_ck_spd tbl ((rb':num->int32) m) m = va1_ck_spd tbl' (rb' m) m /\
                va1_ck_hj mdl' t p i m = va1_ck_hj mdl t p i m /\
                (!spd. va1_ck_zpq mdl' spd m = va1_ck_zpq mdl spd m)` (fun th -> REWRITE_TAC[th]) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC C8E_CKSPD_LOC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[va1_ck_hj]; ASM_REWRITE_TAC[va1_ck_zpq]]);;
let C8E_JIGK_LF = prove
 (`!mdl mdl' hp hp' tbl tbl' t p rb rb'.
     mdl' 3 = mdl 3 /\ (!k. k < 24 ==> hp k = hp' k) /\
     (!k. k < 262144 ==> tbl k = tbl' k) /\ (!k. k < 2048 ==> rb k = rb' k)
     ==> c8e_lf 2048 (va1_jigk mdl hp tbl t p rb) (va1_jigk mdl' hp' tbl' t p rb')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[c8e_lf; va1_jigk] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  C8E_AGREE_TAC [`m:num`; `(m + 1) MOD 2048`; `(m + 2047) MOD 2048`] THEN
  ASM_CASES_TAC `bit 0 ((mdl:num->int32) 3) /\ ival ((rb':num->int32) m) < &52371634` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `va1_jg_spd tbl ((rb':num->int32) m) m = va1_jg_spd tbl' (rb' m) m /\
                va1_jg_f hp t p m = va1_jg_f hp' t p m` (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THENL [MATCH_MP_TAC C8E_JGSPD_LOC THEN ASM_REWRITE_TAC[]; MATCH_MP_TAC C8E_JGF_LOC THEN ASM_REWRITE_TAC[]]);;
let C8E_AGREEN_TAC (bound:term) (idxs:term list) : tactic = fun (asl,w) ->
  let pat = mk_binop `(<):num->num->bool` `x:num` bound in
  let isfa th = let c = concl th in is_forall c &&
    (let b = snd(dest_forall c) in is_imp b && can (term_match [] pat) (lhand b)) in
  let fas = filter isfa (map snd asl) in
  let ths = List.concat (map (fun fa ->
     map (fun i ->
       let lt = TAC_PROOF((asl, mk_binop `(<):num->num->bool` i bound),
                  FIRST [C8E_ARITH_TAC; SIMP_TAC[MOD_LT_EQ; ARITH_EQ] THEN NO_TAC]) in
       MATCH_MP (SPEC i fa) lt) idxs) fas) in
  REWRITE_TAC ths (asl,w);;
let c8e_agbs = new_definition
 `c8e_agbs (bs:(num->int32)#(num->int32)#(num->int32)#int32) bs' <=>
    (!w. w < 196608 ==> FST bs w = FST bs' w) /\
    (!k. k < 2048 ==> FST (SND bs) k = FST (SND bs') k /\ FST (SND (SND bs)) k = FST (SND (SND bs')) k) /\
    SND (SND (SND bs)) = SND (SND (SND bs'))`;;
let C8E_POP1_LOC = prove
 (`!bs bs'. c8e_agbs bs bs' /\ 0 < val (SND (SND (SND bs))) /\ val (SND (SND (SND bs))) <= 16384
     ==> c8e_agbs (va1_pop1 bs) (va1_pop1 bs') /\ val (SND (SND (SND (va1_pop1 bs)))) = val (SND (SND (SND bs))) - 1`,
  REWRITE_TAC[FORALL_PAIR_THM; c8e_agbs; va1_pop1; LET_DEF; LET_END_DEF; FST; SND] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  C8E_AGREEN_TAC `196608` [`12 * (val (p2:int32) - 1) + 7`; `12 * (val (p2:int32) - 1) + 8`; `12 * (val (p2:int32) - 1) + 9`] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN C8E_AGREEN_TAC `196608` [`w:num`];
    REPEAT STRIP_TAC THEN C8E_AGREEN_TAC `2048` [`k:num`];
    REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN MATCH_MP_TAC MOD_LT THEN C8E_ARITH_TAC]);;
let C8E_UNB_LOC = prove
 (`!b c bs bs'. c8e_agbs bs bs' /\ val (SND (SND (SND bs))) <= 16384
     ==> c8e_agbs (va1_unb b c bs) (va1_unb b c bs') /\ val (SND (SND (SND (va1_unb b c bs)))) <= 16384`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[va1_unb] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `SND (SND (SND (bs':(num->int32)#(num->int32)#(num->int32)#int32))) = SND (SND (SND (bs:(num->int32)#(num->int32)#(num->int32)#int32)))` SUBST1_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(CONJUNCT2(CONJUNCT2(GEN_REWRITE_RULE I [c8e_agbs] th)))]); ALL_TAC] THEN
  ASM_CASES_TAC `0 < val (SND (SND (SND (bs:(num->int32)#(num->int32)#(num->int32)#int32))))` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FST (bs':(num->int32)#(num->int32)#(num->int32)#int32) (12 * (val (SND (SND (SND bs))) - 1) + 6) =
                FST (bs:(num->int32)#(num->int32)#(num->int32)#int32) (12 * (val (SND (SND (SND bs))) - 1) + 6)` SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [c8e_agbs]) THEN
    DISCH_THEN(fun th -> CONV_TAC SYM_CONV THEN MATCH_MP_TAC th) THEN C8E_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`bs:(num->int32)#(num->int32)#(num->int32)#int32`; `bs':(num->int32)#(num->int32)#(num->int32)#int32`] C8E_POP1_LOC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN C8E_ARITH_TAC);;
let C8E_DROP_LOC = prove
 (`!nd di di'. (!w. w < 196608 ==> di w = di' w) /\ val nd <= 16384
     ==> !w. w < 196608 ==> va1_drop_bwd nd di w = va1_drop_bwd nd di' w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[va1_drop_bwd] THEN
  SUBGOAL_THEN `MIN (val (nd:int32)) 16384 = val nd` SUBST1_TAC THENL [REWRITE_TAC[MIN] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `w + 3 < 196608` (fun th -> ASM_SIMP_TAC[th]) THEN
  SUBGOAL_THEN `w DIV 12 < val (nd:int32)` MP_TAC THENL [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ]; ALL_TAC] THEN
  MP_TAC(SPECL [`w:num`; `12`] DIVISION) THEN ASM_ARITH_TAC);;
let c8e_agps = new_definition
 `c8e_agps (ps:(num->int32)#(num->int32)#(num->int32)#(num->int32)#((num->int32)#(num->int32)#(num->int32)#int32)) ps' <=>
    (!k. k < 2048 ==> FST ps k = FST ps' k /\ FST (SND ps) k = FST (SND ps') k /\
                      FST (SND (SND ps)) k = FST (SND (SND ps')) k /\ FST (SND (SND (SND ps))) k = FST (SND (SND (SND ps'))) k /\
                      FST (SND (SND (SND (SND (SND ps))))) k = FST (SND (SND (SND (SND (SND ps'))))) k /\
                      FST (SND (SND (SND (SND (SND (SND ps)))))) k = FST (SND (SND (SND (SND (SND (SND ps')))))) k) /\
    (!w. w < 196608 ==> FST (SND (SND (SND (SND ps)))) w = FST (SND (SND (SND (SND ps')))) w) /\
    SND (SND (SND (SND (SND (SND (SND ps)))))) = SND (SND (SND (SND (SND (SND (SND ps'))))))`;;
let C8E_POPBWD_LOC = prove
 (`!mdl mdl' hp hp' tbl tbl' t p ps ps'.
     mdl' 2 = mdl 2 /\ mdl' 3 = mdl 3 /\ (!k. k < 24 ==> hp k = hp' k) /\ (!k. k < 262144 ==> tbl k = tbl' k) /\
     c8e_agps ps ps' /\ val (SND (SND (SND (SND (SND (SND (SND ps))))))) <= 16384
     ==> c8e_agps (va1_pop_bwd mdl hp tbl t p ps) (va1_pop_bwd mdl' hp' tbl' t p ps')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY (fun v -> SPEC_TAC(v,v)) [`ps:(num->int32)#(num->int32)#(num->int32)#(num->int32)#((num->int32)#(num->int32)#(num->int32)#int32)`;
                                      `ps':(num->int32)#(num->int32)#(num->int32)#(num->int32)#((num->int32)#(num->int32)#(num->int32)#int32)`] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`ra':num->int32`; `rb':num->int32`; `jq':num->int32`; `jp':num->int32`; `di':num->int32`; `zq':num->int32`; `zp':num->int32`; `nd':int32`;
                       `ra:num->int32`; `rb:num->int32`; `jq:num->int32`; `jp:num->int32`; `di:num->int32`; `zq:num->int32`; `zp:num->int32`; `nd:int32`] THEN
  REWRITE_TAC[c8e_agps; FST; SND] THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[va1_pop_bwd; LET_DEF; LET_END_DEF; FST; SND] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND] THEN
  MP_TAC(ISPECL [`word_add (t:int32) (word 1)`; `val (nd:int32)`; `(di:num->int32),(zq:num->int32),(zp:num->int32),(nd:int32)`;
                 `(di':num->int32),(zq':num->int32),(zp':num->int32),(nd:int32)`] C8E_UNB_LOC) THEN
  ANTS_TAC THENL [REWRITE_TAC[c8e_agbs; FST; SND] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `bs = va1_unb (word_add t (word 1)) (val nd) (di,zq,zp,nd)` THEN
  ABBREV_TAC `bs' = va1_unb (word_add t (word 1)) (val nd) (di',zq',zp',nd)` THEN
  REWRITE_TAC[c8e_agbs] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2048`; `va1_rimd tbl`; `va1_rimd tbl'`; `(ra:num->int32),(rb:num->int32)`; `(ra':num->int32),(rb':num->int32)`] C8E_FRED_LOC) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[C8E_RIMD_LF] THEN REWRITE_TAC[c8e_ag; FST; SND] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[c8e_ag] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2048`; `va1_jigk mdl hp tbl t p rb`; `va1_jigk mdl' hp' tbl' t p rb'`; `va1_jdrift mdl`; `va1_jdrift mdl'`;
                 `(jq:num->int32),(jp:num->int32)`; `(jq':num->int32),(jp':num->int32)`] C8E_KD_LOC) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[C8E_JIGK_LF; C8E_JDRIFT_LF] THEN REWRITE_TAC[c8e_ag; FST; SND] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[c8e_ag] THEN STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL [`2048`; `\i:num. va1_ck mdl hp tbl t p i rb`; `\i:num. va1_ck mdl' hp' tbl' t p i rb'`;
                 `\i:num. va1_cdrift rb`; `\i:num. va1_cdrift rb'`] C8E_KDN_LOC)) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[C8E_CK_LF; C8E_CDRIFT_LF]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`4`; `FST (SND (bs:(num->int32)#(num->int32)#(num->int32)#int32)),FST (SND (SND bs))`;
                             `FST (SND (bs':(num->int32)#(num->int32)#(num->int32)#int32)),FST (SND (SND bs'))`]) THEN
  ANTS_TAC THENL [REWRITE_TAC[c8e_ag; FST; SND] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[c8e_ag] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`SND (SND (SND (bs:(num->int32)#(num->int32)#(num->int32)#int32)))`; `FST (bs:(num->int32)#(num->int32)#(num->int32)#int32)`;
                 `FST (bs':(num->int32)#(num->int32)#(num->int32)#int32)`] C8E_DROP_LOC) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN ASM_SIMP_TAC[]);;
let C8E_BORN_TAG = prove
 (`!mdl hp tbl t ra rb zq zp nd. val (nd:int32) <= 16384
     ==> ALL (\r. r 6 = word_add t (word 1)) (va1_born mdl hp tbl t ra rb zq zp nd) /\
         val nd + LENGTH (va1_born mdl hp tbl t ra rb zq zp nd) <= 16384`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (SPEC_ALL VA1_BORN_SHAPE)) THEN
  REWRITE_TAC[GSYM AND_ALL] THEN SIMP_TAC[]);;
let VA1_POP_BWD_FWD = prove
 (`!mdl hp tbl t p ra rb jq jp di zq zp nd.
     va1_log_ok t di nd /\ ~(word_add t (word 1) = word 0)
     ==> va1_pop_bwd mdl hp tbl t p
           (va1_pop_fwd va1_ck va1_jigk (va1_pop_births mdl hp tbl t p (ra,rb,jq,jp,di,zq,zp,nd))
                        mdl hp tbl t p (ra,rb,jq,jp,di,zq,zp,nd)) = (ra,rb,jq,jp,di,zq,zp,nd)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ALL (\r. r 6 = word_add t (word 1)) (va1_pop_births mdl hp tbl t p (ra,rb,jq,jp,di,zq,zp,nd)) /\
                val (nd:int32) + LENGTH (va1_pop_births mdl hp tbl t p (ra,rb,jq,jp,di,zq,zp,nd)) <= 16384` MP_TAC THENL
   [REWRITE_TAC[va1_pop_births; LET_DEF; LET_END_DEF; FST; SND] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    MATCH_MP_TAC C8E_BORN_TAG THEN ASM_MESON_TAC[va1_log_ok]; ALL_TAC] THEN
  ABBREV_TAC `L = va1_pop_births mdl hp tbl t p (ra,rb,jq,jp,di,zq,zp,nd)` THEN STRIP_TAC THEN
  REWRITE_TAC[va1_pop_fwd] THEN REWRITE_TAC[va1_pop_bwd; LET_DEF; LET_END_DEF; FST; SND] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND; VA1_PUSH_ND] THEN
  SUBGOAL_THEN `val (word_add (nd:int32) (word (LENGTH (L:(num->int32)list)))) = val nd + LENGTH L` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN
    MP_TAC(ISPEC `nd:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
    SUBGOAL_THEN `LENGTH (L:(num->int32)list) MOD 4294967296 = LENGTH L` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[VA1_PUSH_UNB_INVERSE; VA1_LOG_OK_DROP] THEN
  REWRITE_TAC[FST; SND; PAIR; VA1_DROP_INVERSE; KICK_DRIFT_STEPS_INVERSE; KICK_DRIFT_INVERSE; FREDKIN_STEP_INVERSE]);;
let C8E_VAL_ND_ADD = prove
 (`!nd n. val (nd:int32) + n <= 16384 ==> val (word_add nd (word n)) = val nd + n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `n MOD 4294967296 = n` SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;
let C8E_PF_ND = prove
 (`!mdl hp tbl t p ra rb jq jp di zq zp nd. va1_log_ok t di nd
     ==> val (SND (SND (SND (SND (SND (SND (SND (va1_pop_fwd va1_ck va1_jigk
            (va1_pop_births mdl hp tbl t p (ra,rb,jq,jp,di,zq,zp,nd)) mdl hp tbl t p (ra,rb,jq,jp,di,zq,zp,nd))))))))) <= 16384`,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[va1_log_ok]) THEN
  SUBGOAL_THEN `val (nd:int32) + LENGTH (va1_pop_births mdl hp tbl t p (ra,rb,jq,jp,di,zq,zp,nd)) <= 16384` ASSUME_TAC THENL
   [REWRITE_TAC[va1_pop_births; LET_DEF; LET_END_DEF; FST; SND] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    ASM_SIMP_TAC[C8E_BORN_TAG]; ALL_TAC] THEN
  REWRITE_TAC[va1_pop_fwd; LET_DEF; LET_END_DEF; FST; SND] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[FST; SND; VA1_PUSH_ND] THEN ASM_SIMP_TAC[C8E_VAL_ND_ADD]);;
let C8E_SHIFT = prove
 (`!(f:num->int32) g b n. (!k. k < n ==> f (b + k) = g k) ==> (!w. b <= w /\ w < b + n ==> g (w - b) = f w)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `w - b:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `b + (w - b) = w:num` SUBST1_TAC THENL [ASM_ARITH_TAC; MESON_TAC[]]);;
let c8e_k1_E = `!w. sg' w = va1_put_ps (va1_pop_fwd va1_ck va1_jigk
         (va1_pop_births (\k. (sg:num->int32) (64 + k)) (\k. sg (6 + k)) (\k. sg (12288 + k)) (sg 2) (sg 3) (va1_sg_ps sg))
         (\k. sg (64 + k)) (\k. sg (6 + k)) (\k. sg (12288 + k)) (sg 2) (sg 3) (va1_sg_ps sg))
       (va1_put_x (3 * val (sg 65)) (ve_fredkin_fwd (ve_vk (\k. sg (64 + k))) (va1_sg_x sg))
         (va1_put 2 1 (\i. word_add (sg 2) (word 1)) sg)) w`;;
let C8E_ADDSUB1 = WORD_RULE `!x:int32. word_sub (word_add x (word 1)) (word 1) = x`;;
let C8E_SARITH_TAC : tactic = fun (asl,w) -> let simple,_ = c8e_numasms asl in (MAP_EVERY MP_TAC simple THEN ARITH_TAC) (asl,w);;
let rec C8E_THR_TAC (ts:term list) : tactic = match ts with
    [] -> FIRST [C8E_CONTRA_TAC; C8E_SARITH_TAC]
  | t::r -> ASM_CASES_TAC (mk_binop `(<):num->num->bool` `w:num` t) THENL
              [FIRST [C8E_SARITH_TAC; C8E_CONTRA_TAC]; C8E_THR_TAC r];;
let C8E_SPLITFA = prove
 (`!(P:num->bool) Q R. (!k. P k ==> Q k /\ R k) <=> (!k. P k ==> Q k) /\ (!k. P k ==> R k)`, MESON_TAC[]);;
let VA1_INV_K1 = prove
 (`!(PT:(num->int32)->num->int32) sg. va1_dom sg /\ va1_kind sg = 1 ==> va1_bwd (va1_fwdt PT sg) = sg`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[va1_dom] THEN STRIP_TAC THEN
  SUBGOAL_THEN `va1_pop_window ((sg:num->int32) 2) (sg 3)` ASSUME_TAC THENL
   [REWRITE_TAC[va1_pop_window] THEN UNDISCH_TAC `va1_kind sg = 1` THEN REWRITE_TAC[va1_kind] THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP VA1_WINDOW_FACTS) THEN
  SUBGOAL_THEN `va1_log_ok ((sg:num->int32) 2) (\w. sg (290816 + w)) (sg 4)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `sg' = va1_fwdt PT sg` THEN
  SUBGOAL_THEN c8e_k1_E (LABEL_TAC "E") THENL
   [EXPAND_TAC "sg'" THEN REWRITE_TAC[va1_fwdt; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    ASM_REWRITE_TAC[ARITH_EQ]; ALL_TAC]) THEN
  (ABBREV_TAC `PF = va1_pop_fwd va1_ck va1_jigk
         (va1_pop_births (\k. (sg:num->int32) (64 + k)) (\k. sg (6 + k)) (\k. sg (12288 + k)) (sg 2) (sg 3) (va1_sg_ps sg))
         (\k. sg (64 + k)) (\k. sg (6 + k)) (\k. sg (12288 + k)) (sg 2) (sg 3) (va1_sg_ps sg)` THEN
  ABBREV_TAC `FX = ve_fredkin_fwd (ve_vk (\k. (sg:num->int32) (64 + k))) (va1_sg_x sg)`) THEN
  (SUBGOAL_THEN `(sg':num->int32) 2 = word_add (sg 2) (word 1) /\ sg' 3 = sg 3 /\ sg' 65 = sg 65 /\
                sg' 4 = SND (SND (SND (SND (SND (SND (SND (PF:(num->int32)#(num->int32)#(num->int32)#(num->int32)#((num->int32)#(num->int32)#(num->int32)#int32)))))))) /\
                (!k. k < 1024 ==> sg' (64 + k) = sg (64 + k)) /\ (!k. k < 24 ==> sg' (6 + k) = sg (6 + k)) /\
                (!k. k < 262144 ==> sg' (12288 + k) = sg (12288 + k)) /\
                (!w. ~(274432 <= w /\ w < 274432 + 3 * val (sg 65)) /\ ~(276480 <= w /\ w < 276480 + 3 * val (sg 65)) /\
                     ~(w = 2) /\ ~(w = 4) /\ (w < 278528 \/ 487424 <= w) ==> sg' w = sg w)` STRIP_ASSUME_TAC THENL
   [USE_THEN "E" (fun th -> REWRITE_TAC[th]) THEN REPEAT STRIP_TAC THEN C8E_EVAL_TAC THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC]) THEN
  (SUBGOAL_THEN `c8e_agps PF (va1_sg_ps sg') /\ c8e_ag (3 * val ((sg:num->int32) 65)) FX (va1_sg_x sg')` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c8e_agps; c8e_ag; va1_sg_ps; va1_sg_x; FST; SND] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    REPEAT STRIP_TAC THEN USE_THEN "E" (fun th -> REWRITE_TAC[th]) THEN C8E_EVAL_TAC THEN REWRITE_TAC[ADD_SUB2] THEN
    CONV_TAC NUM_REDUCE_CONV; ALL_TAC]) THEN
  (SUBGOAL_THEN `c8e_ag (3 * val ((sg:num->int32) 65)) (va1_sg_x sg') FX` ASSUME_TAC THENL
   [REWRITE_TAC[c8e_ag; va1_sg_x] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT STRIP_TAC THEN
    USE_THEN "E" (fun th -> REWRITE_TAC[th]) THEN C8E_EVAL_TAC THEN REWRITE_TAC[ADD_SUB2]; ALL_TAC]) THEN
  (REMOVE_THEN "E" (K ALL_TAC)) THEN
  (SUBGOAL_THEN `va1_pop_bwd (\k. (sg:num->int32) (64 + k)) (\k. sg (6 + k)) (\k. sg (12288 + k)) (sg 2) (sg 3) PF = va1_sg_ps sg /\
                val (SND (SND (SND (SND (SND (SND (SND (PF:(num->int32)#(num->int32)#(num->int32)#(num->int32)#((num->int32)#(num->int32)#(num->int32)#int32)))))))))  <= 16384`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "PF" THEN REWRITE_TAC[va1_sg_ps] THEN CONJ_TAC THENL
     [MATCH_MP_TAC VA1_POP_BWD_FWD; MATCH_MP_TAC C8E_PF_ND] THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  (MP_TAC(ISPECL [`\k. (sg:num->int32) (64 + k)`; `\k. (sg':num->int32) (64 + k)`; `\k. (sg:num->int32) (6 + k)`; `\k. (sg':num->int32) (6 + k)`;
                 `\k. (sg:num->int32) (12288 + k)`; `\k. (sg':num->int32) (12288 + k)`; `(sg:num->int32) 2`; `(sg:num->int32) 3`;
                 `PF:(num->int32)#(num->int32)#(num->int32)#(num->int32)#((num->int32)#(num->int32)#(num->int32)#int32)`;
                 `va1_sg_ps sg'`] C8E_POPBWD_LOC)) THEN
  (ANTS_TAC THENL
   [CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(GEN_TAC THEN DISCH_TAC) THEN
    FIRST [FIRST_ASSUM MATCH_MP_TAC; CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC] THEN C8E_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
  (REWRITE_TAC[va1_bwd; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[C8E_ADDSUB1]) THEN
  (ABBREV_TAC `BW = va1_pop_bwd (\k. (sg':num->int32) (64 + k)) (\k. sg' (6 + k)) (\k. sg' (12288 + k)) (sg 2) (sg 3) (va1_sg_ps sg')` THEN
  SUBGOAL_THEN `c8e_lf (3 * val ((sg:num->int32) 65)) (ve_vk (\k. sg' (64 + k))) (ve_vk (\k. sg (64 + k)))` ASSUME_TAC THENL
   [MATCH_MP_TAC C8E_VK_LF THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `16 + j` o check(fun th -> is_forall(concl th) && can (find_term ((=) `1024`)) (concl th))) THEN
      REWRITE_TAC[ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN MATCH_MP_TAC THEN C8E_ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`3 * val ((sg:num->int32) 65)`; `ve_vk (\k. (sg':num->int32) (64 + k))`; `ve_vk (\k. (sg:num->int32) (64 + k))`;
                 `va1_sg_x sg'`; `FX:(num->int32)#(num->int32)`] C8E_FRED_LOC) THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "FX" THEN REWRITE_TAC[FREDKIN_STEP_INVERSE] THEN
  REWRITE_TAC[c8e_ag; va1_sg_x] THEN DISCH_THEN(LABEL_TAC "L" o CONJUNCT2) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `BW:(num->int32)#(num->int32)#(num->int32)#(num->int32)#((num->int32)#(num->int32)#(num->int32)#int32)`)) (concl th) &&
                                          not (is_eq (concl th)))) THEN
  REWRITE_TAC[c8e_agps; va1_sg_ps; FST; SND] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[C8E_SPLITFA] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `BW:(num->int32)#(num->int32)#(num->int32)#(num->int32)#((num->int32)#(num->int32)#(num->int32)#int32)`)) (concl th)
                                 then ASSUME_TAC(MATCH_MP C8E_SHIFT th) else failwith ""))) THEN
  (REWRITE_TAC[FUN_EQ_THM; va1_put_ps; va1_put_x; C8E_PUT_AP] THEN X_GEN_TAC `w:num` THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `w = 4` SUBST1_TAC THENL [C8E_ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  REPLICATE_TAC 7 (COND_CASES_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN C8E_ARITH_TAC; ALL_TAC]) THEN
  COND_CASES_TAC THENL
   [USE_THEN "L" (MP_TAC o SPEC `w - 276480`) THEN ANTS_TAC THENL [C8E_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN AP_TERM_TAC THEN C8E_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [USE_THEN "L" (MP_TAC o SPEC `w - 274432`) THEN ANTS_TAC THENL [C8E_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN AP_TERM_TAC THEN C8E_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `w = 2` SUBST1_TAC THENL [C8E_ARITH_TAC; REWRITE_TAC[]]; ALL_TAC] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN C8E_CONTRA_TAC; DISCH_TAC THEN C8E_CONTRA_TAC;
    C8E_THR_TAC [`278528`; `280576`; `282624`; `284672`; `286720`; `288768`; `290816`; `487424`]]));;
