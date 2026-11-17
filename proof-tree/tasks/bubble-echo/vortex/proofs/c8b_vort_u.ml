(* ========================================================================= *)
(* C8b row B1 (lane vortex-chain-20261111-142342, role c8b, Claude Opus 5.5, *)
(* 2026-11-14): the unused vortex words.                                     *)
(*   va1_vabu N u m   VA words j (1114112 + 4j) = FST u j and VB words j     *)
(*                    (1122304 + 4j) = SND u j for 3N <= j < 2048            *)
(* VE_VORT_(UN)APPLY_LOOP_CORRECT_U: the Fredkin loop theorems of ve_vort.ml *)
(* with va1_vabu N u added to pre and post (same frame), by a copy of        *)
(* VORT_TAC whose loop invariant carries the two extra conjuncts (the loop   *)
(* stores only words j < 3N).                                                *)
(* VE_VORT_(UN)APPLY_FREDKIN_U: the whole exports, composed from the field   *)
(* phase (ve_vk_ok, whose frame is locals + scratch, so va1_vabu survives by *)
(* VA1_ENSURES_GHOST) and the loop theorems above.                           *)
(* Never edits ve_vort*.ml; the tactics below are renamed copies (_U).       *)
(* ========================================================================= *)

let va1_vabu = new_definition
 `va1_vabu N (u:(num->int32)#(num->int32)) (m:int64->byte) <=>
    (!j. 3 * N <= j /\ j < 2048 ==> read (bytes32 (word (1114112 + 4 * j))) m = FST u j) /\
    (!j. 3 * N <= j /\ j < 2048 ==> read (bytes32 (word (1122304 + 4 * j))) m = SND u j)`;;

(* a fact R that every frame transition preserves rides along an ensures *)
let VA1_ENSURES_GHOST = prove
 (`!(step:A->A->bool) P Q C R.
     ensures step P Q C /\ (!s s'. R s /\ C s s' ==> R s')
     ==> ensures step (\s. P s /\ R s) (\s. Q s /\ R s) C`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures] THEN STRIP_TAC THEN
  X_GEN_TAC `s:A` THEN BETA_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `eventually step (\s'. Q s' /\ C s s') (s:A)` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_MONO) THEN
  BETA_TAC THEN ASM_MESON_TAC[]);;

(* ---- the loop: copies of ve_vort_tacs.ml pieces with the ghost conjuncts *)

let vort_inv_u mc pa pb na nb ai bi =
  let t = subst [mc,`MC:byte list`; pa,`PA:num`; pb,`PB:num`; na,`NA:num->int32`; nb,`NB:num->int32`;
                 ai,`AI:num->int32`; bi,`BI:num->int32`]
   `\i s. read wcode s = MC /\ read wstatus s = WRunning /\
          read wmemsize s = 4194304 /\ read warity s = 0 /\
          read wlabels s = [0,1370,0; 0,1512,0] /\
          read (wlocal 3) s = I32 (word (PA + 8 * i)) /\
          read (wlocal 14) s = I32 (word (PB + 8 * i)) /\
          read (wlocal 0) s = I32 (word (1974272 + 8 * i)) /\
          read (wlocal 4) s = I32 (word (2 * q - 2 * i)) /\
          read (wlocal 2) s = I32 (word r) /\
          read wstack s = (if read wpc s = word 1372 then [] else [I32 (word (2 * q - 2 * i))]) /\
          (!m. m < 3 * N ==> read (wmem :> bytes32 (word (PA + 4 * m))) s =
                             (if m < 2 * i then NA m else AI m)) /\
          (!m. m < 3 * N ==> read (wmem :> bytes32 (word (PB + 4 * m))) s =
                             (if m < 2 * i then NB m else BI m)) /\
          (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1974272 + 4 * m))) s = (vd:num->int32) m) /\
          (!j. 3 * N <= j /\ j < 2048 ==> read (wmem :> bytes32 (word (1114112 + 4 * j))) s =
                             FST (uw:(num->int32)#(num->int32)) j) /\
          (!j. 3 * N <= j /\ j < 2048 ==> read (wmem :> bytes32 (word (1122304 + 4 * j))) s =
                             SND (uw:(num->int32)#(num->int32)) j)` in
  rhs(concl(TOP_DEPTH_CONV BETA_CONV t));;

(* an unused-word conjunct after the stores: every store is to a word < 3N *)
let VORT_MEMU_TAC =
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN REPEAT B32_PEEL_TAC THEN ASM_SIMP_TAC[] THEN NO_TAC;;

let VORT_BODY_U_TAC exec pa pb ai bi =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `2 * i + 2 <= 3 * N` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  VORT_VALS_TAC pa pb THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  VORT_LOADFACTS_TAC pa pb ai bi THEN VORT_B32O_FACTS_TAC pa pb THEN
  CAP_MSTEPS_TAC exec (1--50) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  ASM_SIMP_TAC[injectivity "wval"; CONS_11; VE_DEC2] THEN
  REPEAT CONJ_TAC THEN TRY(WORD_NUM_EQ_TAC THEN NO_TAC) THEN
  TRY VORT_MEMU_TAC THEN
  TRY(VORT_MEM_TAC THEN NO_TAC);;

let VORT_EXIT_EVEN_U_TAC exec =
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUB_REFL]) THEN
  CAP_MSTEPS_TAC exec (1--6) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  FIRST [VORT_MEMU_TAC;
         X_GEN_TAC `m:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
         COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC];;

let VORT_EXIT_ODD_U_TAC exec pa pb ai bi =
  SUBGOAL_THEN `(word r:int32 = word 0) <=> F` ASSUME_TAC THENL
   [REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN
    SUBGOAL_THEN `val(word r:int32) = r` SUBST1_TAC THENL
     [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC;
      REWRITE_TAC[VAL_WORD_0] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 * q < 3 * N` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun b -> VAL_TAC (subst [b,`bb:num`] `val(word (bb + 8 * q):int32) = bb + 8 * q`))
   [pa; pb; `1974272`] THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUB_REFL]) THEN
  MAP_EVERY (fun (b,f) ->
    SUBGOAL_THEN (subst [b,`bb:num`; f,`ff:num->int32`] `read (bytes32 (word (bb + 8 * q))) mm = ff (2 * q)`)
      ASSUME_TAC THENL
     [SUBGOAL_THEN (subst [b,`bb:num`] `bb + 8 * q = bb + 4 * (2 * q)`) SUBST1_TAC THENL
       [ARITH_TAC; ASM_SIMP_TAC[LT_REFL]];
      ALL_TAC]) [pa,ai; pb,bi; `1974272`,`vd:num->int32`] THEN
  MAP_EVERY (fun (x,y) -> B32O_TAC (subst [x,`bb:num`] `bb + 8 * q`) (subst [y,`bb:num`] `bb + 8 * q`))
   [pb,pa; `1974272`,pa; pa,pb] THEN
  CAP_MSTEPS_TAC exec (1--20) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  FIRST [VORT_MEMU_TAC;
   (X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `m = 2 * q` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[ARITH_RULE `4 * 2 * q = 8 * q`] THEN
      ASM_REWRITE_TAC[CAP_B32_SAME];
      REPEAT B32_PEEL_TAC THEN ASM_SIMP_TAC[] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC])];;

let VORT_U_TAC mc exec pa pb na nb ai bi =
  REWRITE_TAC[va1_vabu; GSYM READ_COMPONENT_COMPOSE] THEN
  VORT_SETUP_TAC THEN
  ENSURES_WHILE_UP_TAC `q:num` `1372` `1473` (vort_inv_u mc pa pb na nb ai bi) THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC; VORT_ENTRY_TAC exec; VORT_BODY_U_TAC exec pa pb ai bi; VORT_BACK_TAC exec;
    ASM_CASES_TAC `r = 0` THENL
     [VORT_EXIT_EVEN_U_TAC exec; VORT_EXIT_ODD_U_TAC exec pa pb ai bi]];;

(* ---- the frame side condition of VA1_ENSURES_GHOST: a frame made of     *)
(* MAYCHANGE over non-memory components and memory byte regions disjoint  *)
(* from the unused words preserves va1_vabu N u                            *)

(* peel every write (bytes(word b,n)) off a read (bytes32 (word a)), by arithmetic *)
let VA1_B32_PEEL_BYTES_TAC : tactic = fun (asl,w) ->
  let pat = `read (bytes32 (word (a:num))) (write (bytes(word (b:num),(n:num))) (y:num) (m:int64->byte))` in
  let t = find_term (can (term_match [] pat)) w in
  let i = term_match [] pat t in
  (MP_TAC (SPECL (map (fun v -> instantiate i v) [`a:num`;`b:num`;`n:num`;`y:num`;`m:int64->byte`]) B32_BYTES_OTHER) THEN
   ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC]) (asl,w);;

let VA1_VABU_FRAME_TAC : tactic =
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC MP_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [MAYCHANGE; SEQ_ID] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [GSYM SEQ_ASSOC] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_SEQ] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> if is_var(rhs(concl th)) then SUBST1_TAC(SYM th) else SUBST1_TAC th) THEN
  CONV_TAC(ONCE_DEPTH_CONV(CHANGED_CONV WMEM_READ_OVER_WRITES_CONV)) THEN
  REWRITE_TAC[va1_vabu] THEN STRIP_TAC THEN CONJ_TAC THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REPEAT VA1_B32_PEEL_BYTES_TAC THEN ASM_SIMP_TAC[];;

(* ---- the whole exports ------------------------------------------------- *)

(* an ensures whose frame keeps the unused words, with va1_vabu N uw added *)
let C8B_GHOST (n:term) (th1:thm) =
  let _,[_;_;_;c] = strip_comb (concl th1) in
  let r = mk_abs(`s:wasmstate`, list_mk_comb(`va1_vabu`,
            [n; `uw:(num->int32)#(num->int32)`; `read wmem (s:wasmstate)`])) in
  let s = `s:wasmstate` and s' = `s':wasmstate` in
  let side = list_mk_forall([s;s'], mk_imp(mk_conj(mk_comb(r,s), list_mk_comb(c,[s;s'])), mk_comb(r,s'))) in
  MATCH_MP VA1_ENSURES_GHOST (CONJ th1 (prove(side, VA1_VABU_FRAME_TAC)));;

(* VE_VORT_COMPOSE_TAC of ve_vort.ml with the ghost conjunct: the field     *)
(* phase (selected conjunct of ve_vk_ok) carries va1_vabu by C8B_GHOST, the *)
(* loop theorem (_U) by its statement                                       *)
let C8B_VORT_COMPOSE_TAC sel loopth src post_tac =
  REWRITE_TAC[ve_fredkin_fwd; ve_fredkin_bwd; FST; SND] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  GEN_TAC THEN DISCH_THEN(MP_TAC o sel o REWRITE_RULE[ve_vk_ok]) THEN
  DISCH_THEN(fun pth ->
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`N:num`; `mdl:num->int32`; `va:num->int32`; `vb:num->int32`] pth) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o C8B_GHOST `N:num`) THEN
    MP_TAC(SPECL [`N:num`; `va:num->int32`; `vb:num->int32`;
                  mk_comb(`(VK:(num->int32)->(num->int32)->num->int32) mdl`, src);
                  `uw:(num->int32)#(num->int32)`] loopth) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
  (fun (asl,w) ->
     let th2 = snd(hd asl) and th1 = snd(hd(tl asl)) in
     let _,[_;p1;q1;_] = strip_comb(concl th1) in
     let _,[_;p2;r2;_] = strip_comb(concl th2) in
     let x = `s:wasmstate` in
     let pimp = TAC_PROOF((asl, mk_forall(x, mk_imp(mk_comb(q1,x), mk_comb(p2,x)))),
       X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
       ASM_REWRITE_TAC[] THEN
       FIRST_X_ASSUM(fun th -> if can (find_term ((=) `16640`)) (concl th)
                               then MP_TAC(SPEC `1` th) else NO_TAC) THEN
       CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[]) in
     let th2a = MATCH_MP ENSURES_PRECONDITION_THM (CONJ pimp th2) in
     let th12 = MATCH_MP ENSURES_TRANS (CONJ th1 th2a) in
     (MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC (rand(concl th12)) THEN
      CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
      MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC p1 THEN CONJ_TAC THENL
       [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC r2 THEN CONJ_TAC THENL
       [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
        (X_GEN_TAC `m:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN post_tac);
        ACCEPT_TAC th12]) (asl,w));;

let VE_VORT_APPLY_LOOP_CORRECT_U = prove
 (parse_term c8b_spec_VE_VORT_APPLY_LOOP_CORRECT_U,
  VORT_U_TAC `ve_vort_apply_mc` VE_VORT_APPLY_EXEC `1122304` `1114112`
    `\m:num. word_add ((vd:num->int32) m) ((va:num->int32) m)` `vb:num->int32`
    `vb:num->int32` `va:num->int32`);;

let VE_VORT_UNAPPLY_LOOP_CORRECT_U = prove
 (parse_term c8b_spec_VE_VORT_UNAPPLY_LOOP_CORRECT_U,
  VORT_U_TAC `ve_vort_unapply_mc` VE_VORT_UNAPPLY_EXEC `1114112` `1122304`
    `\m:num. word_sub ((vb:num->int32) m) ((vd:num->int32) m)` `va:num->int32`
    `va:num->int32` `vb:num->int32`);;

let VE_VORT_APPLY_FREDKIN_U = prove
 (parse_term c8b_spec_VE_VORT_APPLY_FREDKIN_U,
  C8B_VORT_COMPOSE_TAC CONJUNCT1 VE_VORT_APPLY_LOOP_CORRECT_U `vb:num->int32`
    (REWRITE_TAC[WORD_ADD_SYM]));;

let VE_VORT_UNAPPLY_FREDKIN_U = prove
 (parse_term c8b_spec_VE_VORT_UNAPPLY_FREDKIN_U,
  C8B_VORT_COMPOSE_TAC CONJUNCT2 VE_VORT_UNAPPLY_LOOP_CORRECT_U `va:num->int32` ALL_TAC);;

let VA1_VABU_SAT = prove
 (parse_term c8b_spec_VA1_VABU_SAT,
  REPEAT GEN_TAC THEN
  EXISTS_TAC `(\j. read (bytes32 (word (1114112 + 4 * j))) (m:int64->byte)),
              (\j. read (bytes32 (word (1122304 + 4 * j))) (m:int64->byte))` THEN
  REWRITE_TAC[va1_vabu]);;
