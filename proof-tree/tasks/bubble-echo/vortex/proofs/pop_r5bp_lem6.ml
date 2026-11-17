(* ========================================================================= *)
(* Vortex pop R5 droplet birth (vortex-r5birth PROVE-birth r3, Claude Opus   *)
(* 5.5, 2026-11-11): lemma layer 6 on pop_r5bp_lem5b.ml: loop assembly       *)
(* (R5B_ITER1/LOOP1, R5B_ITER2/LOOP2, R5B_ITER3/LOOP3) and the exits         *)
(* R5B_FIN6085, R5B_FIN4391, R5B_FIN2612.                                    *)
(* ========================================================================= *)
(* r3: explicit-instance forms of R5B_ENS_EXISTS / R5B_ENS_DISJ (MATCH_MP_TAC did not match the goal pre) *)
let r5b_dest_ens w = let epq, c = dest_comb w in let ep, q = dest_comb epq in let _, p = dest_comb ep in (p, q, c);;
let R5B_EXISTS_TAC : tactic = fun (asl,w) ->
  let p, q, c = r5b_dest_ens w in
  let s, body = dest_abs p in let x, bx = dest_exists body in
  let th = CONV_RULE (TOP_DEPTH_CONV BETA_CONV) (ISPECL [list_mk_abs([x; s], bx); q; c] R5B_ENS_EXISTS) in
  MATCH_MP_TAC th (asl,w);;
let R5B_DISJ_TAC : tactic = fun (asl,w) ->
  let p, q, c = r5b_dest_ens w in
  let s, body = dest_abs p in let b1, b2 = dest_disj body in
  let th = CONV_RULE (TOP_DEPTH_CONV BETA_CONV) (ISPECL [mk_abs(s, b1); mk_abs(s, b2); q; c] R5B_ENS_DISJ) in
  MATCH_MP_TAC th (asl,w);;
let R5B_ENS_NOW = prove
 (mk_forall(`P:wasmstate->bool`, mk_forall(`Q:wasmstate->bool`,
   mk_imp(`!s:wasmstate. P s ==> Q s`, r5b_ens `P:wasmstate->bool` `Q:wasmstate->bool`))),
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_SIMP_TAC[]);;

(* chain ensures theorems whose posts and pres agree syntactically *)
let r5b_chain ths = end_itlist (fun a b -> MATCH_MP R5B_ENS_TRANS (CONJ a b)) ths;;

let R5B_ENS_PRE_CONJ = prove
 (`!A c Q C. (c ==> ensures wasm A Q C) ==> ensures wasm (\s. A s /\ c) Q C`,
  REWRITE_TAC[ensures] THEN MESON_TAC[]);;

(* r3: move the state-free conjuncts of an ensures precondition into the assumptions *)
let R5B_PURE_TAC : tactic = fun (asl,w) ->
  let p, q, c = r5b_dest_ens w in
  let s, body = dest_abs p in
  let pure, rest = partition (fun t -> not (vfree_in s t)) (conjuncts body) in
  if pure = [] || rest = [] then failwith "R5B_PURE_TAC" else
  let p' = mk_abs(s, mk_conj(list_mk_conj rest, list_mk_conj pure)) in
  (MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC p' THEN CONJ_TAC THENL
    [X_GEN_TAC s THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_THEN(fun th -> REWRITE_TAC[th]);
     MATCH_MP_TAC R5B_ENS_PRE_CONJ THEN STRIP_TAC]) (asl,w);;
(* instantiate a lemma, proving its antecedent from the assumptions (accept, else arithmetic) *)
let r5b_inst2 asl th = let th1 = SPEC_ALL th in
  if is_imp (concl th1) then MP th1 (TAC_PROOF((asl, lhand(concl th1)),
     REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_ARITH_TAC)) else th1;;

(* zero steps *)
let r5b_inst asl th = let th1 = SPEC_ALL th in
  if is_imp (concl th1) then MP th1 (TAC_PROOF((asl, lhand(concl th1)), ASM_ARITH_TAC)) else th1;;
let r5b_isq_at asl th = r5b_inst asl (MP (SPEC `32` th) (ARITH_RULE `1 <= 32 /\ 32 <= 32`));;

let r5b_bd t = snd(dest_abs t);;
let r5b_trkn nn = [0,`word k:int32`; 1, mk_comb(`word:num->int32`, nn); 3,`word_add t (word 1):int32`];;
let r5b_mi_s nn = r5b_mi nn `read wmem (s:wasmstate)`;;
(* loop-1 head (pc 146) with count n and the memory invariant *)
let r5b_head1 kk nn = mk_abs(`s:wasmstate`,
  r5b_body_m 146 r5b_L1 [0, mk_comb(`word:num->int32`, kk); 1, mk_comb(`word:num->int32`, nn); 3,`word_add t (word 1):int32`] (r5b_mi_s nn));;
let r5b_exit1 = mk_abs(`s:wasmstate`, mk_exists(`n':num`,
  mk_conj(r5b_body_m 2612 [] [1,`word n':int32`; 3,`word_add t (word 1):int32`] (r5b_mi_s `n':num`), `n' <= 16384`)));;
let r5b_iter_post = mk_abs(`s:wasmstate`, mk_disj(
  mk_exists(`n':num`, mk_conj(r5b_bd(r5b_head1 `k + 1` `n':num`) , `k + 1 < 2048 /\ n' < 16384`)),
  r5b_bd r5b_exit1));;
let r5b_hyps1 = [`k < 2048`; `n < 16384`; r5b_zero_beyond];;
let r5b_iter1_stmt = list_mk_forall([`k:num`;`n:num`;`t:int32`;`di:num->int32`;`zq:num->int32`;`zp:num->int32`;`nd:int32`],
  mk_imp(list_mk_conj r5b_hyps1, r5b_ens (r5b_head1 `k:num` `n:num`) r5b_iter_post));;

(* weaken a post to the iteration post with witness n' := nn *)
let R5B_WEAK_TAC nn : tactic =
  X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
  FIRST [DISJ1_TAC THEN EXISTS_TAC nn THEN R5B_CLOSE1; DISJ2_TAC THEN EXISTS_TAC nn THEN R5B_CLOSE1];;

let R5B_ITER1 = prove(r5b_iter1_stmt,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* memory as a variable m0 with MI(n, m0) *)
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  EXISTS_TAC (mk_abs(`s:wasmstate`, mk_exists(`m0:int64->byte`,
     mk_conj(r5b_bd(r5b_pred 146 r5b_L1 r5b_trk1 []), r5b_mi `n:num` `m0:int64->byte`)))) THEN CONJ_TAC THENL
   [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_TAC THEN
    EXISTS_TAC `read wmem (s:wasmstate)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  R5B_EXISTS_TAC THEN X_GEN_TAC `m0:int64->byte` THEN
  MATCH_MP_TAC R5B_ENS_PRE_CONJ THEN DISCH_TAC THEN
  W(fun (asl,w) ->
    let segA = r5b_inst asl R5B_SEGA in
    MATCH_MP_TAC R5B_ENS_TRANS THEN EXISTS_TAC (rand(rator(concl segA))) THEN CONJ_TAC THENL
     [ACCEPT_TAC segA; R5B_DISJ_TAC THEN CONJ_TAC]) THENL
   [(* live bead *)
    W(fun (asl,w) ->
      let live = r5b_chain [r5b_inst asl R5B_SEGB; r5b_isq_at asl R5B_ISQ1; r5b_inst asl R5B_SEGC; r5b_isq_at asl R5B_ISQ2;
                            r5b_inst asl R5B_SEGD; r5b_isq_at asl R5B_ISQ3; r5b_inst asl R5B_SEGE] in
      MATCH_MP_TAC R5B_ENS_TRANS THEN EXISTS_TAC (rand(rator(concl live))) THEN CONJ_TAC THENL
       [ACCEPT_TAC live; ALL_TAC]) THEN
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    EXISTS_TAC (mk_abs(`s:wasmstate`, mk_exists(`m1:int64->byte`,
       mk_conj(subst [`m1:int64->byte`,`m0:int64->byte`] (r5b_bd(r5b_pred 2586 r5b_L1 (r5b_trkn `n + 1`) [])),
               r5b_born1_at `m0:int64->byte` `m1:int64->byte`)))) THEN CONJ_TAC THENL
     [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_TAC THEN
      EXISTS_TAC `read wmem (s:wasmstate)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    R5B_EXISTS_TAC THEN X_GEN_TAC `m1:int64->byte` THEN
    MATCH_MP_TAC R5B_ENS_PRE_CONJ THEN DISCH_TAC THEN
    SUBGOAL_THEN (r5b_mi `n + 1` `m1:int64->byte`) ASSUME_TAC THENL
     [MATCH_MP_TAC R5B_BIRTH_APPEND1 THEN EXISTS_TAC `k:num` THEN EXISTS_TAC `m0:int64->byte` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    (* born1 has served; drop it so its ND-cell clause cannot rewrite the m1 invariant *)
    FIRST_X_ASSUM(K ALL_TAC o check (fun th -> aconv (concl th) (r5b_born1_at `m0:int64->byte` `m1:int64->byte`))) THEN
    W(fun (asl,w) ->
      let b = INST [`m1:int64->byte`,`m0:int64->byte`; `n + 1`,`n:num`] (SPEC_ALL R5B_BACK1) in
      let b = MP b (TAC_PROOF((asl, lhand(concl b)), ASM_ARITH_TAC)) in
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC (rand(rator(concl b))) THEN CONJ_TAC THENL
       [R5B_WEAK_TAC `n + 1`; R5B_USE_TAC b]);
    (* skipped bead *)
    W(fun (asl,w) ->
      let b = MP (SPEC_ALL R5B_BACK1) (TAC_PROOF((asl, `k < 2048 /\ n <= 16384`), ASM_ARITH_TAC)) in
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC (rand(rator(concl b))) THEN CONJ_TAC THENL
       [R5B_WEAK_TAC `n:num`; R5B_USE_TAC b])]);;

(* loop 1: from the head at bead k (count n) to the exit at 2612, by induction on d = 2047 - k *)
let r5b_loop1_stmt = mk_forall(`d:num`, list_mk_forall([`k:num`;`n:num`;`t:int32`;`di:num->int32`;`zq:num->int32`;`zp:num->int32`;`nd:int32`],
  mk_imp(list_mk_conj [`k + d = 2047`; `n < 16384`; r5b_zero_beyond], r5b_ens (r5b_head1 `k:num` `n:num`) r5b_exit1)));;
let R5B_LOOP1 = prove(r5b_loop1_stmt,
  INDUCT_TAC THEN (REPEAT GEN_TAC THEN STRIP_TAC THEN
  W(fun (asl,w) -> let it = r5b_inst2 asl R5B_ITER1 in
    MATCH_MP_TAC R5B_ENS_TRANS THEN EXISTS_TAC (rand(rator(concl it))) THEN CONJ_TAC THENL [ACCEPT_TAC it; ALL_TAC]) THEN
  R5B_DISJ_TAC THEN CONJ_TAC THENL
   [R5B_EXISTS_TAC THEN X_GEN_TAC `n':num` THEN MATCH_MP_TAC R5B_ENS_PRE_CONJ THEN STRIP_TAC THEN
    FIRST [MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC;
           FIRST_X_ASSUM(MP_TAC o SPECL [`k + 1`; `n':num`; `t:int32`; `di:num->int32`; `zq:num->int32`; `zp:num->int32`; `nd:int32`]) THEN
           ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; REWRITE_TAC[]]];
    MATCH_MP_TAC R5B_ENS_NOW THEN REWRITE_TAC[]]));;
(* ---- R5 PROVE-birth: loop 2 assembled *)
let r5b_head2 kk nn = mk_abs(`s:wasmstate`,
  r5b_body_m 2706 r5b_L2 [15, mk_comb(`word:num->int32`, kk); 1, mk_comb(`word:num->int32`, nn); 3,`word_add t (word 1):int32`] (r5b_mi_s nn));;
let r5b_exit2 = mk_abs(`s:wasmstate`, mk_exists(`n':num`,
  mk_conj(r5b_body_m 4391 [Blk 6084] [1,`word n':int32`; 3,`word_add t (word 1):int32`] (r5b_mi_s `n':num`), `n' <= 16384`)));;
let r5b_iter2_post = mk_abs(`s:wasmstate`, mk_disj(
  mk_exists(`n':num`, mk_conj(r5b_bd(r5b_head2 `k + 1` `n':num`) , `k + 1 < 2048 /\ n' < 16384`)),
  r5b_bd r5b_exit2));;
let r5b_iter2_stmt = list_mk_forall([`k:num`;`n:num`;`t:int32`;`di:num->int32`;`zq:num->int32`;`zp:num->int32`;`nd:int32`],
  mk_imp(list_mk_conj r5b_hyps1, r5b_ens (r5b_head2 `k:num` `n:num`) r5b_iter2_post));;
let R5B_ITER2 = prove(r5b_iter2_stmt,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  EXISTS_TAC (mk_abs(`s:wasmstate`, mk_exists(`m0:int64->byte`,
     mk_conj(r5b_bd(r5b_pred 2706 r5b_L2 r5b_trk2 []), r5b_mi `n:num` `m0:int64->byte`)))) THEN CONJ_TAC THENL
   [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_TAC THEN
    EXISTS_TAC `read wmem (s:wasmstate)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  R5B_EXISTS_TAC THEN X_GEN_TAC `m0:int64->byte` THEN
  MATCH_MP_TAC R5B_ENS_PRE_CONJ THEN DISCH_TAC THEN
  W(fun (asl,w) ->
    let segF = r5b_inst asl R5B_SEGF in
    MATCH_MP_TAC R5B_ENS_TRANS THEN EXISTS_TAC (rand(rator(concl segF))) THEN CONJ_TAC THENL
     [ACCEPT_TAC segF; R5B_DISJ_TAC THEN CONJ_TAC]) THENL
   [W(fun (asl,w) ->
      let live = r5b_chain [r5b_inst asl R5B_SEGG; r5b_isq_at asl R5B_ISQ4; r5b_inst asl R5B_SEGH] in
      MATCH_MP_TAC R5B_ENS_TRANS THEN EXISTS_TAC (rand(rator(concl live))) THEN CONJ_TAC THENL
       [ACCEPT_TAC live; ALL_TAC]) THEN
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    EXISTS_TAC (mk_abs(`s:wasmstate`, mk_exists(`m1:int64->byte`,
       mk_conj(subst [`m1:int64->byte`,`m0:int64->byte`]
                 (r5b_bd(r5b_pred 4363 r5b_L2 [15,`word k:int32`; 1,`word (n + 1):int32`; 3,`word_add t (word 1):int32`] [])),
               r5b_born2_at `m0:int64->byte` `m1:int64->byte`)))) THEN CONJ_TAC THENL
     [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_TAC THEN
      EXISTS_TAC `read wmem (s:wasmstate)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    R5B_EXISTS_TAC THEN X_GEN_TAC `m1:int64->byte` THEN
    MATCH_MP_TAC R5B_ENS_PRE_CONJ THEN DISCH_TAC THEN
    SUBGOAL_THEN (r5b_mi `n + 1` `m1:int64->byte`) ASSUME_TAC THENL
     [MATCH_MP_TAC R5B_BIRTH_APPEND2 THEN EXISTS_TAC `m0:int64->byte` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(K ALL_TAC o check (fun th -> aconv (concl th) (r5b_born2_at `m0:int64->byte` `m1:int64->byte`))) THEN
    W(fun (asl,w) ->
      let b = INST [`m1:int64->byte`,`m0:int64->byte`; `n + 1`,`n:num`] (SPEC_ALL R5B_BACK2) in
      let b = MP b (TAC_PROOF((asl, lhand(concl b)), ASM_ARITH_TAC)) in
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC (rand(rator(concl b))) THEN CONJ_TAC THENL
       [R5B_WEAK_TAC `n + 1`; R5B_USE_TAC b]);
    W(fun (asl,w) ->
      let b = MP (SPEC_ALL R5B_BACK2) (TAC_PROOF((asl, `k < 2048 /\ n <= 16384`), ASM_ARITH_TAC)) in
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC (rand(rator(concl b))) THEN CONJ_TAC THENL
       [R5B_WEAK_TAC `n:num`; R5B_USE_TAC b])]);;
let r5b_loop2_stmt = mk_forall(`d:num`, list_mk_forall([`k:num`;`n:num`;`t:int32`;`di:num->int32`;`zq:num->int32`;`zp:num->int32`;`nd:int32`],
  mk_imp(list_mk_conj [`k + d = 2047`; `n < 16384`; r5b_zero_beyond], r5b_ens (r5b_head2 `k:num` `n:num`) r5b_exit2)));;
let R5B_LOOP2 = prove(r5b_loop2_stmt,
  INDUCT_TAC THEN (REPEAT GEN_TAC THEN STRIP_TAC THEN
  W(fun (asl,w) -> let it = r5b_inst2 asl R5B_ITER2 in
    MATCH_MP_TAC R5B_ENS_TRANS THEN EXISTS_TAC (rand(rator(concl it))) THEN CONJ_TAC THENL [ACCEPT_TAC it; ALL_TAC]) THEN
  R5B_DISJ_TAC THEN CONJ_TAC THENL
   [R5B_EXISTS_TAC THEN X_GEN_TAC `n':num` THEN MATCH_MP_TAC R5B_ENS_PRE_CONJ THEN STRIP_TAC THEN
    FIRST [MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC;
           FIRST_X_ASSUM(MP_TAC o SPECL [`k + 1`; `n':num`; `t:int32`; `di:num->int32`; `zq:num->int32`; `zp:num->int32`; `nd:int32`]) THEN
           ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; REWRITE_TAC[]]];
    MATCH_MP_TAC R5B_ENS_NOW THEN REWRITE_TAC[]]));;
(* ---- R5 PROVE-birth: loop 3 assembled *)
let r5b_head3 kk nn = mk_abs(`s:wasmstate`, r5b_body_m 4493 r5b_L3 (r5b_trk3 kk nn) (r5b_mi_s nn));;
let r5b_exit3 = mk_abs(`s:wasmstate`, mk_exists(`n':num`,
  mk_conj(r5b_body_m 6085 [] [14,`word n':int32`; 3,`word_add t (word 1):int32`] (r5b_mi_s `n':num`), `n' <= 16384`)));;
let r5b_iter3_post = mk_abs(`s:wasmstate`, mk_disj(
  mk_exists(`n':num`, mk_conj(r5b_bd(r5b_head3 `k + 1` `n':num`) , `k + 1 < 2048 /\ n' < 16384`)),
  r5b_bd r5b_exit3));;
let r5b_iter3_stmt = list_mk_forall([`k:num`;`n:num`;`t:int32`;`di:num->int32`;`zq:num->int32`;`zp:num->int32`;`nd:int32`],
  mk_imp(list_mk_conj r5b_hyps1, r5b_ens (r5b_head3 `k:num` `n:num`) r5b_iter3_post));;
let R5B_ITER3 = prove(r5b_iter3_stmt,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  EXISTS_TAC (mk_abs(`s:wasmstate`, mk_exists(`m0:int64->byte`,
     mk_conj(r5b_bd(r5b_pred 4493 r5b_L3 (r5b_trk3 `k:num` `n:num`) []), r5b_mi `n:num` `m0:int64->byte`)))) THEN CONJ_TAC THENL
   [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_TAC THEN
    EXISTS_TAC `read wmem (s:wasmstate)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  R5B_EXISTS_TAC THEN X_GEN_TAC `m0:int64->byte` THEN
  MATCH_MP_TAC R5B_ENS_PRE_CONJ THEN DISCH_TAC THEN
  W(fun (asl,w) ->
    let segF = r5b_inst asl R5B_SEGI in
    MATCH_MP_TAC R5B_ENS_TRANS THEN EXISTS_TAC (rand(rator(concl segF))) THEN CONJ_TAC THENL
     [ACCEPT_TAC segF; R5B_DISJ_TAC THEN CONJ_TAC]) THENL
   [W(fun (asl,w) ->
      let live = r5b_inst asl R5B_SEGJ in
      MATCH_MP_TAC R5B_ENS_TRANS THEN EXISTS_TAC (rand(rator(concl live))) THEN CONJ_TAC THENL
       [ACCEPT_TAC live; ALL_TAC]) THEN
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    EXISTS_TAC (mk_abs(`s:wasmstate`, mk_exists(`m1:int64->byte`,
       mk_conj(subst [`m1:int64->byte`,`m0:int64->byte`]
                 (r5b_bd(r5b_pred 6027 r5b_L3 (r5b_trk3 `k:num` `n + 1`) [])),
               r5b_born2_at `m0:int64->byte` `m1:int64->byte`)))) THEN CONJ_TAC THENL
     [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_TAC THEN
      EXISTS_TAC `read wmem (s:wasmstate)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    R5B_EXISTS_TAC THEN X_GEN_TAC `m1:int64->byte` THEN
    MATCH_MP_TAC R5B_ENS_PRE_CONJ THEN DISCH_TAC THEN
    SUBGOAL_THEN (r5b_mi `n + 1` `m1:int64->byte`) ASSUME_TAC THENL
     [MATCH_MP_TAC R5B_BIRTH_APPEND2 THEN EXISTS_TAC `m0:int64->byte` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(K ALL_TAC o check (fun th -> aconv (concl th) (r5b_born2_at `m0:int64->byte` `m1:int64->byte`))) THEN
    W(fun (asl,w) ->
      let b = INST [`m1:int64->byte`,`m0:int64->byte`; `n + 1`,`n:num`] (SPEC_ALL R5B_BACK3) in
      let b = MP b (TAC_PROOF((asl, lhand(concl b)), ASM_ARITH_TAC)) in
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC (rand(rator(concl b))) THEN CONJ_TAC THENL
       [R5B_WEAK_TAC `n + 1`; R5B_USE_TAC b]);
    W(fun (asl,w) ->
      let b = MP (SPEC_ALL R5B_BACK3) (TAC_PROOF((asl, `k < 2048 /\ n <= 16384`), ASM_ARITH_TAC)) in
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC (rand(rator(concl b))) THEN CONJ_TAC THENL
       [R5B_WEAK_TAC `n:num`; R5B_USE_TAC b])]);;
let r5b_loop3_stmt = mk_forall(`d:num`, list_mk_forall([`k:num`;`n:num`;`t:int32`;`di:num->int32`;`zq:num->int32`;`zp:num->int32`;`nd:int32`],
  mk_imp(list_mk_conj [`k + d = 2047`; `n < 16384`; r5b_zero_beyond], r5b_ens (r5b_head3 `k:num` `n:num`) r5b_exit3)));;
let R5B_LOOP3 = prove(r5b_loop3_stmt,
  INDUCT_TAC THEN (REPEAT GEN_TAC THEN STRIP_TAC THEN
  W(fun (asl,w) -> let it = r5b_inst2 asl R5B_ITER3 in
    MATCH_MP_TAC R5B_ENS_TRANS THEN EXISTS_TAC (rand(rator(concl it))) THEN CONJ_TAC THENL [ACCEPT_TAC it; ALL_TAC]) THEN
  R5B_DISJ_TAC THEN CONJ_TAC THENL
   [R5B_EXISTS_TAC THEN X_GEN_TAC `n':num` THEN MATCH_MP_TAC R5B_ENS_PRE_CONJ THEN STRIP_TAC THEN
    FIRST [MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC;
           FIRST_X_ASSUM(MP_TAC o SPECL [`k + 1`; `n':num`; `t:int32`; `di:num->int32`; `zq:num->int32`; `zp:num->int32`; `nd:int32`]) THEN
           ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; REWRITE_TAC[]]];
    MATCH_MP_TAC R5B_ENS_NOW THEN REWRITE_TAC[]]));;
(* the spec post of va1_birth_ok, as a predicate over di zq zp nd t *)
let r5b_final_post = `\s. read wstatus s = WDone /\ (?r. read wstack s = [I32 r]) /\
   (?L. ALL (\r. r 6 = word_add t (word 1) /\ r 10 = word 0 /\ r 11 = word 0) L /\
        val nd + LENGTH L <= 16384 /\ va1_bs (va1_push L (di,zq,zp,nd)) (read wmem s))`;;
let r5b_fin_stmt pre = list_mk_forall([`t:int32`;`di:num->int32`;`zq:num->int32`;`zp:num->int32`;`nd:int32`],
  mk_imp(r5b_zero_beyond, r5b_ens pre r5b_final_post));;

(* weakening into a pre with an existential count, witness nn *)
let R5B_PREW_TAC nn th : tactic = fun (asl,w) ->
  let c = concl th in let p = rand(rator(rator c)) in
  (MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC p THEN CONJ_TAC THENL
    [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
     (if nn = `T` then ALL_TAC else EXISTS_TAC nn) THEN R5B_CLOSE1;
     ACCEPT_TAC th]) (asl,w);;
(* memory as a variable: ensures (\s. B(read wmem s)) Q from !m0. MI-free B with read wmem s = m0 *)
let R5B_MEMVAR_TAC (pred_m0:term) (fact_m0:term) : tactic =
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  EXISTS_TAC (mk_abs(`s:wasmstate`, mk_exists(`m0:int64->byte`, mk_conj(r5b_bd pred_m0, fact_m0)))) THEN CONJ_TAC THENL
   [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_TAC THEN
    EXISTS_TAC `read wmem (s:wasmstate)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  R5B_EXISTS_TAC THEN X_GEN_TAC `m0:int64->byte` THEN
  MATCH_MP_TAC R5B_ENS_PRE_CONJ THEN DISCH_TAC;;

(* 6085 (exit of loop 3 or skip) -> spec post *)
let R5B_FIN6085 = prove(r5b_fin_stmt r5b_exit3,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  R5B_EXISTS_TAC THEN X_GEN_TAC `n':num` THEN MATCH_MP_TAC R5B_ENS_PRE_CONJ THEN DISCH_TAC THEN
  R5B_MEMVAR_TAC (r5b_pred 6085 [] [14,`word n':int32`; 3,`word_add t (word 1):int32`] []) (r5b_mi `n':num` `m0:int64->byte`) THEN
  MP_TAC(SPECL [`n':num`; `m0:int64->byte`] R5B_FINAL_MEM) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  W(fun (asl,w) -> let e = INST [`n':num`,`n:num`] (SPEC_ALL R5B_EPI) in
    let e = MP e (TAC_PROOF((asl, lhand(concl e)), ASM_ARITH_TAC)) in
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC (rand(rator(concl e))) THEN CONJ_TAC THENL
     [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ACCEPT_TAC e]));;

(* 4391 (exit of loop 2) -> spec post *)
let R5B_FIN4391 = prove(r5b_fin_stmt r5b_exit2,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  R5B_EXISTS_TAC THEN X_GEN_TAC `n':num` THEN MATCH_MP_TAC R5B_ENS_PRE_CONJ THEN DISCH_TAC THEN
  R5B_MEMVAR_TAC (r5b_pred 4391 [Blk 6084] [1,`word n':int32`; 3,`word_add t (word 1):int32`] []) (r5b_mi `n':num` `m0:int64->byte`) THEN
  W(fun (asl,w) -> let e = INST [`n':num`,`n:num`] (SPEC_ALL R5B_ENTRY3) in
    let e = MP e (TAC_PROOF((asl, lhand(concl e)), ASM_ARITH_TAC)) in
    MATCH_MP_TAC R5B_ENS_TRANS THEN EXISTS_TAC (rand(rator(concl e))) THEN CONJ_TAC THENL
     [ACCEPT_TAC e; R5B_DISJ_TAC THEN CONJ_TAC]) THENL
   [R5B_PURE_TAC THEN
    W(fun (asl,w) -> let l = SPECL [`2047`; `0`; `n':num`; `t:int32`; `di:num->int32`; `zq:num->int32`; `zp:num->int32`; `nd:int32`] R5B_LOOP3 in
      let l = MP l (TAC_PROOF((asl, lhand(concl l)), ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC)) in
      let f = MP (SPEC_ALL R5B_FIN6085) (ASSUME r5b_zero_beyond) in
      MATCH_MP_TAC R5B_ENS_TRANS THEN EXISTS_TAC (rand(rator(concl l))) THEN CONJ_TAC THENL
       [R5B_PREW_TAC `T` l; ACCEPT_TAC f]);
    R5B_PURE_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `n' = 16384`)) THEN
    W(fun (asl,w) -> let f = MP (SPEC_ALL R5B_FIN6085) (ASSUME r5b_zero_beyond) in R5B_PREW_TAC `16384` f)]);;
(* 2612 (exit of loop 1) -> spec post *)
let R5B_FIN2612 = prove(r5b_fin_stmt r5b_exit1,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  R5B_EXISTS_TAC THEN X_GEN_TAC `n':num` THEN MATCH_MP_TAC R5B_ENS_PRE_CONJ THEN DISCH_TAC THEN
  R5B_MEMVAR_TAC (r5b_pred 2612 [] [1,`word n':int32`; 3,`word_add t (word 1):int32`] []) (r5b_mi `n':num` `m0:int64->byte`) THEN
  W(fun (asl,w) -> let e = INST [`n':num`,`n:num`] (SPEC_ALL R5B_ENTRY2) in
    let e = MP e (TAC_PROOF((asl, lhand(concl e)), ASM_ARITH_TAC)) in
    MATCH_MP_TAC R5B_ENS_TRANS THEN EXISTS_TAC (rand(rator(concl e))) THEN CONJ_TAC THENL
     [ACCEPT_TAC e; R5B_DISJ_TAC THEN CONJ_TAC]) THENL
   [R5B_PURE_TAC THEN
    W(fun (asl,w) -> let l = SPECL [`2047`; `0`; `n':num`; `t:int32`; `di:num->int32`; `zq:num->int32`; `zp:num->int32`; `nd:int32`] R5B_LOOP2 in
      let l = MP l (TAC_PROOF((asl, lhand(concl l)), ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC)) in
      let f = MP (SPEC_ALL R5B_FIN4391) (ASSUME r5b_zero_beyond) in
      MATCH_MP_TAC R5B_ENS_TRANS THEN EXISTS_TAC (rand(rator(concl l))) THEN CONJ_TAC THENL
       [R5B_PREW_TAC `T` l; ACCEPT_TAC f]);
    R5B_PURE_TAC THEN
    W(fun (asl,w) -> let f = MP (SPEC_ALL R5B_FIN6085) (ASSUME r5b_zero_beyond) in R5B_PREW_TAC `n':num` f)]);;
