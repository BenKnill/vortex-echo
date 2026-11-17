(* c8f_conj.ml (vortex-chain C8f, Claude Opus 5.5, 2026-11-15): two host-call runs with the same start may be conjoined, because a
   finished call (status not WRunning) has no successor under wasmc or wasmn. *)
let C8F_EV_CONJ = prove
 (`!(step:A->A->bool) P Q.
     (!s s'. P s ==> ~step s s') /\ (!s s'. Q s ==> ~step s s')
     ==> !s. eventually step P s /\ eventually step Q s ==> eventually step (\s. P s /\ Q s) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s:A. eventually step P s ==> eventually step Q s ==> eventually step (\s. P s /\ Q s) s`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC eventually_INDUCT THEN CONJ_TAC THEN X_GEN_TAC `s:A` THENL
   [DISCH_TAC THEN GEN_REWRITE_TAC LAND_CONV [eventually_CASES] THEN STRIP_TAC THENL
     [GEN_REWRITE_TAC I [eventually_CASES] THEN DISJ1_TAC THEN BETA_TAC THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [eventually_CASES] THEN STRIP_TAC THENL
     [ASM_MESON_TAC[];
      GEN_REWRITE_TAC I [eventually_CASES] THEN DISJ2_TAC THEN ASM_MESON_TAC[]]]);;

let C8F_WASMC_FINAL = prove
 (`!fs s s'. ~(read wstatus s = WRunning) ==> ~wasmc fs s s'`,
  SIMP_TAC[wasmc; WASM_FINAL]);;
let C8F_WASMN_FINAL = prove
 (`!fs s s'. ~(read wstatus s = WRunning) ==> ~wasmn fs s s'`,
  SIMP_TAC[wasmn; WASM_FINAL]);;

let C8F_HCALL_CONJ = prove
 (`!(step:wasmstate->wasmstate->bool) code args r (Q1:(num->wval)->(int64->byte)->bool) Q2 gl m.
     (!s s'. ~(read wstatus s = WRunning) ==> ~step s s') /\
     va1_hcall step code args r Q1 gl m /\ va1_hcall step code args r Q2 gl m
     ==> va1_hcall step code args r (\g x. Q1 g x /\ Q2 g x) gl m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_hcall] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `e:num` (X_CHOOSE_THEN `decls:wval list` STRIP_ASSUME_TAC))
    (X_CHOOSE_THEN `e2:num` (X_CHOOSE_THEN `decls2:wval list` STRIP_ASSUME_TAC)))) THEN
  UNDISCH_TAC `wasm_entry code = SOME (e2:num)` THEN ASM_REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  UNDISCH_TAC `wasm_decl_vals code = SOME (decls2:wval list)` THEN ASM_REWRITE_TAC[option_INJ] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  MAP_EVERY EXISTS_TAC [`e:num`; `decls:wval list`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s0:wasmstate` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`step:wasmstate->wasmstate->bool`;
    `\s. read wstatus s = WDone /\ read wstack s = [I32 r] /\ read wmemsize s = 4194304 /\
         (Q1:(num->wval)->(int64->byte)->bool) (read wglobals s) (read wmem s)`;
    `\s. read wstatus s = WDone /\ read wstack s = [I32 r] /\ read wmemsize s = 4194304 /\
         (Q2:(num->wval)->(int64->byte)->bool) (read wglobals s) (read wmem s)`] C8F_EV_CONJ) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN REPEAT GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[distinctness "wstat"]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `wcall_entry code (LENGTH (args:wval list)) 1 args e decls s0`) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC C1_EV_MONO THEN GEN_TAC THEN BETA_TAC THEN MESON_TAC[]);;

let C8F_HRUN_CONJ = prove
 (`!(step:wasmstate->wasmstate->bool).
     (!s s'. ~(read wstatus s = WRunning) ==> ~step s s')
     ==> !cs (Q1:(num->wval)->(int64->byte)->bool) Q2 gl m.
           va1_hrun step cs Q1 gl m /\ va1_hrun step cs Q2 gl m ==> va1_hrun step cs (\g x. Q1 g x /\ Q2 g x) gl m`,
  GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[VA1_HRUN_CLAUSES] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC VA1_HCALL_MONO THEN
  EXISTS_TAC `\g x. va1_hrun step t (Q1:(num->wval)->(int64->byte)->bool) g x /\ va1_hrun step t Q2 g x` THEN
  CONJ_TAC THENL [BETA_TAC THEN REPEAT GEN_TAC THEN FIRST_X_ASSUM MATCH_ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC C8F_HCALL_CONJ THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]);;
let c8f_has s t = can (find_term (fun u -> is_const u && fst(dest_const u) = s)) t;;
