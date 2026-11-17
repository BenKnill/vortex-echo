(* c8f_runs.ml (vortex-chain C8f, Claude Opus 5.5, 2026-11-15): host-call runs along ITER va1_fwd from C8e's host lemmas. *)
let C8F_FWD_RUN_C = prove
 (`!fs gl j sg m. va1_fs_all fs /\
     (!i. i < j ==> va1_dom (ITER i va1_fwd sg) /\ (va1_kind (ITER i va1_fwd sg) = 0 \/ va1_kind (ITER i va1_fwd sg) = 1)) /\
     va1_snap m = sg
     ==> va1_hrun (wasmc fs) (REPLICATE j T) (\gl' m'. gl' = gl /\ va1_snap m' = ITER j va1_fwd sg) gl m`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[REPLICATE; VA1_HRUN_CLAUSES; ITER] THEN MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[REPLICATE; VA1_HRUN_CLAUSES] THEN
  MATCH_MP_TAC VA1_HCALL_MONO THEN
  EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\ va1_snap m' = va1_fwdt va1_ptbl_sg sg` THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`g:num->wval`; `x:int64->byte`] THEN BETA_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    REWRITE_TAC[C8F_ITER_ALT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[va1_fwd] THEN
    REWRITE_TAC[GSYM va1_fwd; GSYM C8F_ITER_ALT] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    UNDISCH_TAC `va1_snap m = (sg:num->int32)` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[ITER; LT_0] THEN STRIP_TAC THENL
     [MATCH_MP_TAC C8E_S0F; MATCH_MP_TAC C8E_S1F] THEN ASM_REWRITE_TAC[]]);;
let C8F_FWD_RUN_N = prove
 (`!fs gl j sg m. va1_fs_all fs /\ gl 0 = I32 (word 16384) /\
     (!i. i < j ==> va1_dom (ITER i va1_fwd sg) /\ ~(va1_kind (ITER i va1_fwd sg) = 3)) /\
     va1_snap m = sg
     ==> va1_hrun (wasmn fs) (REPLICATE j T) (\gl' m'. gl' = gl /\ va1_snap m' = ITER j va1_fwd sg) gl m`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[REPLICATE; VA1_HRUN_CLAUSES; ITER] THEN MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[REPLICATE; VA1_HRUN_CLAUSES] THEN
  MATCH_MP_TAC VA1_HCALL_MONO THEN
  EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\ va1_snap m' = va1_fwd sg` THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`g:num->wval`; `x:int64->byte`] THEN BETA_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    REWRITE_TAC[C8F_ITER_ALT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM C8F_ITER_ALT] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    UNDISCH_TAC `va1_snap m = (sg:num->int32)` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[ITER; LT_0] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `m:int64->byte`] VA1_FWD_FUNCTION) THEN
    ASM_REWRITE_TAC[]]);;
let C8F_BWD_RUN_C = prove
 (`!fs j sg gl m. va1_fs_all fs /\
     (!i. i < j ==> va1_dom (ITER i va1_fwd sg) /\ ~(va1_kind (ITER i va1_fwd sg) = 3)) /\
     va1_snap m = ITER j va1_fwd sg
     ==> va1_hrun (wasmc fs) (REPLICATE j F) (\gl' m'. gl' = gl /\ va1_snap m' = sg) gl m`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[REPLICATE; VA1_HRUN_CLAUSES; ITER] THEN MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[REPLICATE; VA1_HRUN_CLAUSES] THEN
  FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (is_forall o concl)) THEN
  REWRITE_TAC[ARITH_RULE `j < SUC j`] THEN STRIP_TAC THEN
  MATCH_MP_TAC VA1_HCALL_MONO THEN
  EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\ va1_snap m' = va1_bwd (va1_snap m)` THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`g:num->wval`; `x:int64->byte`] THEN BETA_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[ITER] THEN CONJ_TAC THENL [X_GEN_TAC `i:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`va1_ptbl_sg`; `ITER j va1_fwd (sg:num->int32)`] VA1_BWD_FWD) THEN ASM_REWRITE_TAC[GSYM va1_fwd] THEN SIMP_TAC[];
    SUBGOAL_THEN `~(va1_kind (ITER j va1_fwd (sg:num->int32)) = 4)` ASSUME_TAC THENL [ASM_MESON_TAC[va1_dom]; ALL_TAC] THEN
    MP_TAC(SPEC `ITER j va1_fwd (sg:num->int32)` C8E_KIND_RANGE) THEN
    REWRITE_TAC[ASSUME `~(va1_kind (ITER j va1_fwd (sg:num->int32)) = 4)`; ASSUME `~(va1_kind (ITER j va1_fwd (sg:num->int32)) = 3)`] THEN
    STRIP_TAC THENL
     [MATCH_MP_TAC C8E_S0B; MATCH_MP_TAC C8E_S1B; MATCH_MP_TAC C8E_S2B] THEN
    MAP_EVERY EXISTS_TAC [`va1_ptbl_sg`; `ITER j va1_fwd (sg:num->int32)`] THEN ASM_REWRITE_TAC[ITER] THEN REWRITE_TAC[va1_fwd]]);;
let C8F_WALK = prove
 (`!fs K sg0. va1_fs_all fs /\ (!i. i < K ==> va1_dom (ITER i va1_fwd sg0) /\ va1_kind (ITER i va1_fwd sg0) = 1)
     ==> !cs u gl m. u <= K /\ va1_cmds_ok K u cs /\ va1_snap m = ITER u va1_fwd sg0
           ==> va1_hrun (wasmc fs) cs (\gl' m'. gl' = gl /\ va1_snap m' = ITER (va1_cmds_end u cs) va1_fwd sg0) gl m`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "W")) THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[VA1_HRUN_CLAUSES; VA1_CMDS_END_CLAUSES] THEN MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[VA1_HRUN_CLAUSES; VA1_CMDS_END_CLAUSES; VA1_CMDS_OK_CLAUSES] THEN
  ASM_CASES_TAC `h:bool` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN MATCH_MP_TAC VA1_HCALL_MONO THENL
   [EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\ va1_snap m' = va1_fwdt va1_ptbl_sg (va1_snap m)` THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`g:num->wval`; `x:int64->byte`] THEN BETA_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[GSYM ADD1; ITER; GSYM va1_fwd] THEN ASM_ARITH_TAC;
      USE_THEN "W" (MP_TAC o SPEC `u:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MATCH_MP_TAC C8E_S1F THEN ASM_REWRITE_TAC[]];
    EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\ va1_snap m' = va1_bwd (va1_snap m)` THEN
    SUBGOAL_THEN `ITER u va1_fwd (sg0:num->int32) = va1_fwd (ITER (u - 1) va1_fwd sg0)` ASSUME_TAC THENL
     [SUBGOAL_THEN `u = SUC (u - 1)` (fun th -> GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV) [th]) THENL
       [ASM_ARITH_TAC; REWRITE_TAC[ITER]]; ALL_TAC] THEN
    USE_THEN "W" (MP_TAC o SPEC `u - 1`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`g:num->wval`; `x:int64->byte`] THEN BETA_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`va1_ptbl_sg`; `ITER (u - 1) va1_fwd (sg0:num->int32)`] VA1_BWD_FWD) THEN
      ASM_REWRITE_TAC[ARITH_EQ] THEN REWRITE_TAC[va1_fwd] THEN SIMP_TAC[];
      MATCH_MP_TAC C8E_S1B THEN MAP_EVERY EXISTS_TAC [`va1_ptbl_sg`; `ITER (u - 1) va1_fwd (sg0:num->int32)`] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[va1_fwd]]]);;
let C8F_REP_APPEND = prove
 (`!m n (x:A). APPEND (REPLICATE m x) (REPLICATE n x) = REPLICATE (m + n) x`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; APPEND; ADD_CLAUSES]);;
let C8F_TO_N = prove
 (`!fs cs (Q:(num->wval)->(int64->byte)->bool) gl m. va1_hrun (wasmc fs) cs Q gl m ==> va1_hrun (wasmn fs) cs Q gl m`,
  GEN_TAC THEN MATCH_MP_TAC C7_HRUN_TRANSFER THEN REWRITE_TAC[VA1_C5P_EVENTUALLY_WASMN]);;
let C8F_HRUN_BOTH = prove
 (`!(step:wasmstate->wasmstate->bool) cs R1 R2 (Q:(num->wval)->(int64->byte)->bool) gl m.
     (!s s'. ~(read wstatus s = WRunning) ==> ~step s s') /\
     va1_hrun step cs R1 gl m /\ va1_hrun step cs R2 gl m /\ (!g x. R1 g x /\ R2 g x ==> Q g x)
     ==> va1_hrun step cs Q gl m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VA1_HRUN_MONO THEN EXISTS_TAC `\g x. (R1:(num->wval)->(int64->byte)->bool) g x /\ R2 g x` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MATCH_MP C8F_HRUN_CONJ (ASSUME `!s s'. ~(read wstatus s = WRunning) ==> ~(step:wasmstate->wasmstate->bool) s s'`)) THEN
  ASM_REWRITE_TAC[]);;
let C8F_BOTH_TAC (p1:term->bool) (p2:term->bool) : tactic = fun (asl,w) ->
  let hr t = try fst(dest_const(fst(strip_comb t))) = "va1_hrun" with _ -> false in
  let _,[_;_;_;gw;mw] = strip_comb w in
  let ok t = hr t && (let _,[_;_;_;g;m] = strip_comb t in g = gw && m = mw) in
  let a1 = snd(find (fun (_,th) -> ok (concl th) && p1 (concl th)) asl)
  and a2 = snd(find (fun (_,th) -> ok (concl th) && p2 (concl th)) asl) in
  let _,[st;cs;r1;_;_] = strip_comb (concl a1) and _,[_;_;r2;_;_] = strip_comb (concl a2) in
  (MATCH_MP_TAC (ISPECL [st;cs;r1;r2] C8F_HRUN_BOTH) THEN REWRITE_TAC[a1;a2] THEN
   CONJ_TAC THENL [REWRITE_TAC[C8F_WASMN_FINAL; C8F_WASMC_FINAL]; ALL_TAC]) (asl,w);;
let C8F_HCALL_BOTH = prove
 (`!(step:wasmstate->wasmstate->bool) code args r R1 R2 (Q:(num->wval)->(int64->byte)->bool) gl m.
     (!s s'. ~(read wstatus s = WRunning) ==> ~step s s') /\
     va1_hcall step code args r R1 gl m /\ va1_hcall step code args r R2 gl m /\ (!g x. R1 g x /\ R2 g x ==> Q g x)
     ==> va1_hcall step code args r Q gl m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VA1_HCALL_MONO THEN EXISTS_TAC `\g x. (R1:(num->wval)->(int64->byte)->bool) g x /\ R2 g x` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC C8F_HCALL_CONJ THEN ASM_REWRITE_TAC[]);;
let C8F_HBOTH_TAC (p1:term->bool) (p2:term->bool) : tactic = fun (asl,w) ->
  let hr t = try fst(dest_const(fst(strip_comb t))) = "va1_hcall" with _ -> false in
  let _,[_;_;_;_;_;gw;mw] = strip_comb w in
  let ok t = hr t && (let _,[_;_;_;_;_;g;m] = strip_comb t in g = gw && m = mw) in
  let a1 = snd(find (fun (_,th) -> ok (concl th) && p1 (concl th)) asl)
  and a2 = snd(find (fun (_,th) -> ok (concl th) && p2 (concl th)) asl) in
  let _,[st;cd;ar;r;r1;_;_] = strip_comb (concl a1) and _,[_;_;_;_;r2;_;_] = strip_comb (concl a2) in
  (MATCH_MP_TAC (ISPECL [st;cd;ar;r;r1;r2] C8F_HCALL_BOTH) THEN REWRITE_TAC[a1;a2] THEN
   CONJ_TAC THENL [REWRITE_TAC[C8F_WASMN_FINAL; C8F_WASMC_FINAL]; ALL_TAC]) (asl,w);;
let C8F_GSUB_TAC (g:term) : tactic =
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try lhs(concl th) = g with _ -> false));;
