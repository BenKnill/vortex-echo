(* ========================================================================= *)
(* C8b rows B7, B8 (lane vortex-chain-20261111-142342, role c8b, Claude Opus *)
(* 5.5, 2026-11-14): the un-puncture tick (C3a) and the auto puncture tick   *)
(* (C6b, wasmn) keep the unused vortex words.                               *)
(* B7: chain_c3a_seq.ml's VA1_TICK_UNPUNCT run with _U call sites (f26, f28 *)
(*     by C8B_GHOST_RULE; f10 by Q0_CALL_TAC on the B1 leaf) and the table  *)
(*     clear loop (frame [65536,1114112)) carrying the conjunct by          *)
(*     C8B_GHOST.                                                           *)
(* B8: chain_c7_c6b_host.ml's proof with the prefix re-run on the _U call   *)
(*     sites; at the call 33 the conjunct moves from the call-time memory   *)
(*     m1 to the final memory through C6a's frame (va1_c6a_mem keeps        *)
(*     [1114112,1130496)): C8B_C6A_VABU.                                    *)
(* ========================================================================= *)

let c8b_addv (lam:term) =
  let s,bd = dest_abs lam in
  mk_abs(s, mk_conj(bd, list_mk_comb(`va1_vabu`,
    [`N:num`; `uw:(num->int32)#(num->int32)`; mk_comb(`read wmem`, s)])));;

(* ---- B7 ---- *)
let VA1P_CALL_F26_U = C8B_GHOST_RULE VA1P_CALL_F26;;
let VA1P_CALL_F28H_U = C8B_GHOST_RULE VA1P_CALL_F28H;;
let VA1P_CALL_F10H_U = prove(c8b_ghost_tm (concl VA1P_CALL_F10H),
  REWRITE_TAC[VA1_F10_IS_VORT_UNAPPLY] THEN
  Q0_CALL_TAC (Q0_VORT_LEAF_U VE_VORT_UNAPPLY_FREDKIN_U) VE_VORT_UNAPPLY_CALLEE `10` `0` `0`);;

let C3_TCALLS_U = [26,VA1P_CALL_F26_U; 28,VA1P_CALL_F28H_U; 10,VA1P_CALL_F10H_U];;
let c3_m57_u = c8b_addv c3_m57 and c3_m121_u = c8b_addv c3_m121;;

let VA1_TICK_UNPUNCT_U = prove(parse_term c8b_spec_VA1_TICK_UNPUNCT_U,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_SEQUENCE_TAC `57` c3_m57_u THEN CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN VA1Q1_MEMNAME_TAC true "mm0" THEN
    VA1Q1_RUN_TAC VA1_TICK_BACKWARD_EXEC C3_TCALLS_U [57] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `121` c3_m121_u THEN CONJ_TAC THENL
   [C3_USE2_TAC (CONV_RULE (TOP_DEPTH_CONV BETA_CONV)
      (C8B_GHOST `N:num` (MP C3_S_TLOOP (ASSUME `N <= 640`)))); ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN VA1Q1_MEMNAME_TAC true "mm0" THEN
  VA1Q1_RUN_TAC VA1_TICK_BACKWARD_EXEC C3_TCALLS_U [] THEN
  ENSURES_FINAL_STATE_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV VA1_ITER_CONV) THEN ASM_REWRITE_TAC[]);;

(* ---- B8 ---- *)
(* C6a's puncture frame keeps the vortex arrays, so the unused words of the *)
(* call-time memory m1 survive into the final memory                       *)
let C8B_C6A_VABU_TAC (base:term) : tactic =
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN (subst [base,`bb:num`]
    `read (bytes32 (word (bb + 4 * j))) (m':int64->byte) = read (bytes32 (word (bb + 4 * j))) (m1:int64->byte)`)
    SUBST1_TAC THENL
   [MATCH_MP_TAC C6A_B32_KEEP THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th -> if can (find_term ((=) `16288`)) (concl th) then MATCH_MP_TAC th else NO_TAC) THEN
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[]];;

let C8B_C6A_VABU = prove
 (`!N (uw:(num->int32)#(num->int32)) mdl (m1:int64->byte) m'.
     va1_c6a_mem mdl m1 m' /\ va1_vabu N uw m1 ==> va1_vabu N uw m'`,
  REWRITE_TAC[va1_c6a_mem; va1_c6a_frame; va1_vabu] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONJ_TAC THENL [C8B_C6A_VABU_TAC `1114112`; C8B_C6A_VABU_TAC `1122304`]);;

let C6B_PREFIX_VK_U = prove
 (c8b_ghost_tm (concl C6B_PREFIX_VK),
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN VA1_MEMNAME_TAC "mm0" THEN
  VA1_RUN_TAC VA1_TICK_FORWARD_EXEC [9,VA1_CALL_VA_U; 27,VA1_CALL_TI_U] [309] THEN
  ENSURES_FINAL_STATE_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV VA1_ITER_CONV) THEN ASM_REWRITE_TAC[]);;

let C6B_PREFIX_U = prove
 (c8b_ghost_tm (concl C6B_PREFIX),
  REWRITE_TAC[VA1_F9_IS_VORT_APPLY; VA1_F27_IS_TICK_INC] THEN VA1_VK_TAC C6B_PREFIX_VK_U);;

let C6B_MID309_U = c8b_addv C6B_MID309;;
let C6B_POSTM_U = `\m:int64->byte. ?m1. va1_tf_mid N mdl t x (m0:int64->byte) m1 /\ va1_c6a_mem mdl m1 m /\
   read (bytes32 (word 16408)) m = a0 /\ read (bytes32 (word 16412)) m = a1 /\ read (bytes32 (word 16416)) m = a2 /\
   va1_vabu N (uw:(num->int32)#(num->int32)) m`;;
let C6B_MID315_U = c6b_mid 315 `[I32 (word 0)]` (rhs(concl(BETA_CONV(mk_comb(C6B_POSTM_U, `read wmem s`)))));;

let C6B_PREFIX_MID_U = prove
 (list_mk_forall([`fs:num->byte list#num#num`; `gl:num->wval`; `t:int32`; `mdl:num->int32`; `N:num`;
    `x:(num->int32)#(num->int32)`; `m0:int64->byte`; `a0:int32`; `a1:int32`; `a2:int32`;
    `uw:(num->int32)#(num->int32)`],
   mk_imp(`(fs:num->byte list#num#num) 9 = (va1_f9_mc,0,0) /\ fs 27 = (va1_f27_mc,0,0) /\
     (mdl:num->int32) 1 = word N /\ 1 <= N /\ N <= 640 /\ ~(word_add (t:int32) (word 1) = word 0) /\
     va1_tick t m0 /\ va1_pop (word 4294967295) (word_add t (word 1)) m0 /\ va1_mdl mdl m0 /\
     va1_vab N (x:(num->int32)#(num->int32)) m0 /\
     read (bytes32 (word 16516)) m0 = (a0:int32) /\ read (bytes32 (word 16520)) m0 = (a1:int32) /\
     read (bytes32 (word 16524)) m0 = (a2:int32) /\ va1_vabu N (uw:(num->int32)#(num->int32)) m0`,
     list_mk_comb(`ensures (wasmc (fs:num->byte list#num#num))`, [C6B_PRE; C6B_MID309_U; C6B_FR1]))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ensures] THEN X_GEN_TAC `s:wasmstate` THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `t:int32`; `mdl:num->int32`; `N:num`;
                `x:(num->int32)#(num->int32)`; `uw:(num->int32)#(num->int32)`] C6B_PREFIX_U) THEN
  ASM_REWRITE_TAC[ensures] THEN DISCH_THEN(MP_TAC o SPEC `s:wasmstate`) THEN
  ANTS_TAC THENL [CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC C6A_EV_MONO THEN X_GEN_TAC `s':wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  SUBGOAL_THEN `va1_tf_mid N mdl t x m0 (read wmem (s':wasmstate))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[va1_tf_mid] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPEC `a:num` C6B_FR1_BYTE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`s:wasmstate`; `s':wasmstate`]) THEN ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE];
    ALL_TAC] THEN
  MAP_EVERY (fun b ->
    MP_TAC(SPECL [`N:num`; `mdl:num->int32`; `t:int32`; `x:(num->int32)#(num->int32)`; `m0:int64->byte`;
                  `read wmem (s':wasmstate)`; b] C6B_MID_B32) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC) [`16516`; `16520`; `16524`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[va1_pop]) THEN ASM_REWRITE_TAC[]);;

let C6B_CALL_U = prove
 (list_mk_forall([`fs:num->byte list#num#num`; `gl:num->wval`; `t:int32`; `mdl:num->int32`; `N:num`;
    `x:(num->int32)#(num->int32)`; `m0:int64->byte`; `a0:int32`; `a1:int32`; `a2:int32`;
    `uw:(num->int32)#(num->int32)`],
   mk_imp(`(fs:num->byte list#num#num) 33 = (va1_puncture_mc,3,1) /\ fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\
           fs 34 = (va1_f34_mc,3,0) /\ (gl:num->wval) 0 = I32 (word 16384) /\ ~(word_add (t:int32) (word 1) = word 0) /\
           ~((a0:int32) = word 0 /\ (a1:int32) = word 0 /\ (a2:int32) = word 0)`,
     list_mk_comb(`ensures (wasmn (fs:num->byte list#num#num))`, [C6B_MID309_U; C6B_MID315_U; C6B_FR3]))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ensures] THEN X_GEN_TAC `s:wasmstate` THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  ABBREV_TAC `m1 = read wmem (s:wasmstate)` THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `word_add t (word 1):int32`; `mdl:num->int32`; `a0:int32`; `a1:int32`;
                `a2:int32`; `m1:int64->byte`] VA1_PUNCTURE_OK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[va1_tf_mid]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun po ->
    let qq = rand(rator(concl po)) in
    MP_TAC(SPECL [`fs:num->byte list#num#num`; `a0:int32`; `a1:int32`; `a2:int32`; `[]:wval list`; `m1:int64->byte`;
      `word 0:int32`; `\m':int64->byte. va1_c6a_mem mdl m1 m' /\ read (bytes32 (word 16408)) m' = a0 /\
         read (bytes32 (word 16412)) m' = a1 /\ read (bytes32 (word 16416)) m' = a2`; qq] VA1_TF_CALL33_SITE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[po] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN MESON_TAC[]; ALL_TAC]) THEN
  REWRITE_TAC[ensures] THEN DISCH_THEN(MP_TAC o SPEC `s:wasmstate`) THEN
  ANTS_TAC THENL
   [CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[wglobal; READ_COMPONENT_COMPOSE; READ_ELEMENT];
    ALL_TAC] THEN
  MATCH_MP_TAC C6A_EV_MONO THEN X_GEN_TAC `s':wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> C6A_KEEPS_ON C6B_KEEPS3 th) THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `m1:int64->byte` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C8B_C6A_VABU THEN EXISTS_TAC `mdl:num->int32` THEN EXISTS_TAC `m1:int64->byte` THEN
  ASM_REWRITE_TAC[]);;

let VA1_TICK_FORWARD_PUNCT_U = prove(parse_term c8b_spec_VA1_TICK_FORWARD_PUNCT_U,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* the conjunct on the entry memory m0 (the precondition is false otherwise) *)
  ASM_CASES_TAC `va1_vabu N (uw:(num->int32)#(num->int32)) m0` THENL
   [ALL_TAC;
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC `\s:wasmstate. F` THEN CONJ_TAC THENL
     [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_MESON_TAC[]; REWRITE_TAC[ensures]]] THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC (mk_binop `(,,):(wasmstate->wasmstate->bool)->(wasmstate->wasmstate->bool)->wasmstate->wasmstate->bool` C6B_FR1
     (mk_binop `(,,):(wasmstate->wasmstate->bool)->(wasmstate->wasmstate->bool)->wasmstate->wasmstate->bool` C6B_FR3 C6B_FR4)) THEN
  CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC C6B_PRE THEN CONJ_TAC THENL
   [GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_TRANS THEN EXISTS_TAC C6B_MID309_U THEN CONJ_TAC THENL
   [MATCH_MP_TAC VA1_C5P_ENSURES_WASMN THEN MATCH_MP_TAC C6B_PREFIX_MID_U THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_TRANS THEN EXISTS_TAC C6B_MID315_U THEN CONJ_TAC THENL
   [MATCH_MP_TAC C6B_CALL_U THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC VA1_C5P_ENSURES_WASMN THEN
  MP_TAC(BETA_RULE(ISPECL [`fs:num->byte list#num#num`; `gl:num->wval`; C6B_POSTM_U] C6B_TAIL_W)) THEN
  REWRITE_TAC[]);;
