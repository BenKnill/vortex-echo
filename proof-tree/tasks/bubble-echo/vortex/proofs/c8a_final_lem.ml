(* vortex-chain C8a (Claude Opus 5.5, 2026-11-15), row A7 support: the route lemmas of the final leaf. C8A_PRO (13 ->
   146 | 2612), C8A_ENTRY2V (2612 -> 2706 | 6085), C8A_ENTRY3V (4391 -> 4493 | 6085), C8A_FINAL_MEMV (the epilogue's ND
   write gives va1_bs of the pushed list), C8A_T3 (4391 with list L -> done, list va1_fold3 2048 L), C8A_T2 (2612 with
   list L -> done), the fold cap facts c8a_cap1-3. *)
let C8A_CLOSEA defs =
  RULE_ASSUM_TAC(REWRITE_RULE C8A_NORM) THEN
  ASM_REWRITE_TAC[injectivity "wval"; R5B_EX_EQ] THEN REWRITE_TAC defs THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC C8A_NORM THEN ASM_REWRITE_TAC C8A_NORM THEN
  CONV_TAC(DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV)) THEN ASM_REWRITE_TAC[] THEN
  TRY(REPEAT CONJ_TAC THEN ASM_ARITH_TAC) THEN NO_TAC;;
let C8A_FINA : tactic = ENSURES_FINAL_STATE_TAC THEN
  FIRST [DISJ1_TAC THEN R5B_CLOSE1; DISJ2_TAC THEN R5B_CLOSE1; DISJ1_TAC THEN C8A_CLOSEA [WORD_VAL]; DISJ2_TAC THEN C8A_CLOSEA [WORD_VAL]];;
let c8a_base1_0 = map (fun (l,v) -> (l, subst [`0`,`k:num`] v)) c8a_base1;;
let c8a_e2pre = [1,`word n:int32`; 2,`t:int32`; 3,`word_add t (word 1):int32`; 4,`(mdl:num->int32) 2`];;
let c8a_e3pre = [1,`word n:int32`; 3,`word_add t (word 1):int32`; 4,`(mdl:num->int32) 2`];;
let c8a_pro = list_mk_forall([`m0:int64->byte`;`nd:int32`;`t:int32`;`mdl:num->int32`],
   mk_imp(`read (bytes32 (word 16400)) (m0:int64->byte) = nd /\ read (bytes32 (word 16392)) m0 = t /\
           read (bytes32 (word 16648)) m0 = (mdl:num->int32) 2 /\ val (nd:int32) <= 16384`,
    r5b_ens (r5b_pred 13 [] [] [])
     (mk_abs(`s:wasmstate`, mk_disj(
        r5b_body 146 r5b_L1 (c8a_setn 1 `word (val (nd:int32)):int32` c8a_base1_0) [`val (nd:int32) < 16384`],
        r5b_body 2612 [] (map (fun (l,v) -> (l, subst [`val (nd:int32)`,`n:num`] v)) c8a_e2pre) [`val (nd:int32) = 16384`])))));;
let C8A_PRO = prove(c8a_pro,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(if val (nd:int32) < 16384 then nd else word 16384) = word (val nd) /\
                (if ~(val (nd:int32) < 16384) then word 16384 else nd) = word (val nd)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[WORD_VAL] THEN CONJ_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `val (nd:int32) = 16384` (fun th -> REWRITE_TAC[GSYM th; WORD_VAL]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  R5B_INIT_TAC THEN R5B_RUN R5B_EXEC [146; 2612] THEN C8A_FINA);;
let c8a_seg0v p q = list_mk_forall([`m0:int64->byte`;`n:num`;`t:int32`;`mdl:num->int32`], mk_imp(`n <= 16384`, r5b_ens p q));;
let C8A_ENTRY2V = prove(c8a_seg0v (r5b_pred 2612 [] c8a_e2pre [])
   (mk_abs(`s:wasmstate`, mk_disj(
      r5b_body 2706 r5b_L2 (map (fun (l,v) -> (l, subst [`0`,`k:num`] v)) c8a_base2) [`n < 16384`],
      r5b_body 6085 [] [14,`word n:int32`; 3,`word_add t (word 1):int32`] [`n = 16384`]))),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val (word n:int32) = n` ASSUME_TAC THENL [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  R5B_INIT_TAC THEN R5B_RUN R5B_EXEC [2706; 6085] THEN C8A_FINA);;
let C8A_ENTRY3V = prove(c8a_seg0v (r5b_pred 4391 [Blk 6084] c8a_e3pre [])
   (mk_abs(`s:wasmstate`, mk_disj(
      r5b_body 4493 r5b_L3 (c8a_setn 14 `word n:int32` (c8a_base3_at `0`)) [`n < 16384`],
      r5b_body 6085 [] [14,`word 16384:int32`; 3,`word_add t (word 1):int32`] [`n = 16384`]))),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val (word n:int32) = n` ASSUME_TAC THENL [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  R5B_INIT_TAC THEN R5B_RUN R5B_EXEC [4493; 6085] THEN C8A_FINA);;
let c8a_finmem = mk_imp(list_mk_conj [c8a_miv `L:(num->int32)list` `m0:int64->byte`; `val (nd:int32) + LENGTH (L:(num->int32)list) = n`; `n <= 16384`],
   `va1_bs (va1_push (L:(num->int32)list) (di,zq,zp,nd)) (write (bytes32 (word 16400)) (word n) (m0:int64->byte))`);;
let C8A_FINAL_MEMV = prove(c8a_finmem,
  STRIP_TAC THEN REWRITE_TAC[PL5_BS_R5B] THEN REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC R5B_W32S_W32 THEN ASM_REWRITE_TAC[] THEN ARITH_TAC) THEN
  REWRITE_TAC[CAP_B32_SAME; R5B_PUSH_ND] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `val (nd:int32) + LENGTH (L:(num->int32)list) = n` then SUBST1_TAC(SYM th) else NO_TAC) THEN
  REWRITE_TAC[WORD_ADD; WORD_VAL]);;
(* weakening that also reduces the fold base cases and the empty list *)
let C8A_WKM : tactic =
  X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  REWRITE_TAC[CONJUNCT1 va1_fold1; CONJUNCT1 va1_fold2; CONJUNCT1 va1_fold3; LENGTH; ADD_CLAUSES; FST] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  ASM_REWRITE_TAC[injectivity "wval"; R5B_EX_EQ] THEN TRY ASM_ARITH_TAC THEN NO_TAC;;
let C8A_THENM th : tactic = fun (asl,w) ->
  let p', q', _ = r5b_dest_ens (concl th) in
  (MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC p' THEN CONJ_TAC THENL
    [FIRST [C8A_WK; C8A_WKM]; MATCH_MP_TAC R5B_ENS_TRANS THEN EXISTS_TAC q' THEN CONJ_TAC THENL [ACCEPT_TAC th; ALL_TAC]]) (asl,w);;
let c8a_final L = mk_abs(`s:wasmstate`, mk_conj(`read wstatus s = WDone /\ (?r. read wstack s = [I32 r])`,
   subst [L,`L:(num->int32)list`] `va1_bs (va1_push (L:(num->int32)list) (di,zq,zp,nd)) (read wmem (s:wasmstate))`));;
let c8a_nL = `val (nd:int32) + LENGTH (L:(num->int32)list)`;;
let c8a_atL pc lbls trk = mk_abs(`s:wasmstate`, r5b_body_m pc lbls (c8a_setn 1 (c8a_wn c8a_nL) trk)
                                   (c8a_mivL `L:(num->int32)list` `read wmem (s:wasmstate)`));;
(* memory as a variable: ensures (\s. body_m ... (P (read wmem s))) Q  from  !m0. P m0 ==> ensures (pred with m0) Q *)
let C8A_MEMVAR_TAC m0 : tactic = fun (asl,w) ->
  let p, q, c = r5b_dest_ens w in
  let s, b = dest_abs p in
  let cs = conjuncts b in
  let memc = filter (fun t -> can (find_term ((=) `read wmem (s:wasmstate)`)) t &&
                              not (is_eq t && lhs t = `read wmem (s:wasmstate)`)) cs in
  let rest = filter (fun t -> not (mem t memc)) cs in
  let sub t = subst [m0, `read wmem (s:wasmstate)`] t in
  let p' = mk_abs(s, mk_exists(m0, list_mk_conj(rest @ [mk_eq(`read wmem (s:wasmstate)`, m0)] @ map sub memc))) in
  (MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC p' THEN CONJ_TAC THENL
    [X_GEN_TAC s THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_TAC THEN
     EXISTS_TAC `read wmem (s:wasmstate)` THEN ASM_REWRITE_TAC[];
     R5B_EXISTS_TAC THEN X_GEN_TAC m0 THEN R5B_PURE_TAC]) (asl,w);;
let C8A_ENDV : tactic =
  MATCH_MP_TAC R5B_ENS_NOW THEN X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC C8A_FINAL_MEMV THEN ASM_REWRITE_TAC[] THEN TRY ASM_ARITH_TAC;;
let c8a_inst3 asl th = let th1 = SPEC_ALL th in
  if is_imp (concl th1) then MP th1 (TAC_PROOF((asl, lhand(concl th1)),
     REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
     REWRITE_TAC[CONJUNCT1 va1_fold1; CONJUNCT1 va1_fold2; CONJUNCT1 va1_fold3; LENGTH; ADD_CLAUSES; FST] THEN
     TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_ARITH_TAC)) else th1;;
let C8A_SAMEPOST : tactic =
  MATCH_MP_TAC R5B_ENS_NOW THEN X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[CONJ_ASSOC];;
let c8a_cap3 = prove(`!mdl hp tbl t ra rb nd (L:(num->int32)list). 16384 <= val nd + LENGTH L ==> va1_fold3 mdl hp tbl t ra rb nd 2048 L = L`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;`t:int32`;`ra:num->int32`;`rb:num->int32`;`nd:int32`;`0`;`L:(num->int32)list`;`2048`] C8A_FOLD3_CAP) THEN
  ASM_REWRITE_TAC[CONJUNCT1 va1_fold3; ADD_CLAUSES]);;
let c8a_cap2 = prove(`!mdl hp tbl t rb nd (L:(num->int32)list). 16384 <= val nd + LENGTH L ==> va1_fold2 mdl hp tbl t rb nd 2048 L = L`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;`t:int32`;`rb:num->int32`;`nd:int32`;`0`;`L:(num->int32)list`;`2048`] C8A_FOLD2_CAP) THEN
  ASM_REWRITE_TAC[CONJUNCT1 va1_fold2; ADD_CLAUSES]);;
let c8a_t3 = list_mk_forall([`L:(num->int32)list`;`t:int32`;`di:num->int32`;`zq:num->int32`;`zp:num->int32`;`nd:int32`;`mdl:num->int32`;
   `hp:num->int32`;`tbl:num->int32`;`rb:num->int32`;`ra:num->int32`],
  mk_imp(mk_conj(mk_binop `(<=):num->num->bool` c8a_nL `16384`, c8a_zb),
    r5b_ens (c8a_atL 4391 [Blk 6084] c8a_e3pre) (c8a_final `va1_fold3 mdl hp tbl t ra rb nd 2048 L`)));;
let C8A_T3 = prove(c8a_t3,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C8A_MEMVAR_TAC `m0:int64->byte` THEN
  W(fun (asl,w) -> C8A_THEN (r5b_inst2 asl (INST [c8a_nL,`n:num`] (SPEC_ALL C8A_ENTRY3V)))) THEN
  R5B_DISJ_TAC THEN CONJ_TAC THENL
   [R5B_PURE_TAC THEN
    W(fun (asl,w) -> C8A_THENM (c8a_inst3 asl (INST [`L:(num->int32)list`,`L0:(num->int32)list`]
                       (SPECL (`2047` :: `0` :: tl c8a_iter3v_vars) C8A_LOOP3V)))) THEN
    C8A_MEMVAR_TAC `m1:int64->byte` THEN
    W(fun (asl,w) -> C8A_THEN (r5b_inst2 asl (INST [subst [`L:(num->int32)list`,`L0:(num->int32)list`] (c8a_n3 `2048`),`n:num`; `m1:int64->byte`,`m0:int64->byte`] (SPEC_ALL R5B_EPI)))) THEN C8A_ENDV;
    R5B_PURE_TAC THEN
    W(fun (asl,w) -> C8A_THEN (r5b_inst2 asl (INST [`16384`,`n:num`] (SPEC_ALL R5B_EPI)))) THEN
    W(fun (asl,w) -> REWRITE_TAC[r5b_inst2 asl (SPEC_ALL c8a_cap3)]) THEN C8A_ENDV]);;
let c8a_t2 = list_mk_forall([`L:(num->int32)list`;`t:int32`;`di:num->int32`;`zq:num->int32`;`zp:num->int32`;`nd:int32`;`mdl:num->int32`;
   `hp:num->int32`;`tbl:num->int32`;`rb:num->int32`;`ra:num->int32`],
  mk_imp(mk_conj(mk_binop `(<=):num->num->bool` c8a_nL `16384`, c8a_zb),
    r5b_ens (c8a_atL 2612 [] c8a_e2pre) (c8a_final `va1_fold3 mdl hp tbl t ra rb nd 2048 (va1_fold2 mdl hp tbl t rb nd 2048 L)`)));;
let C8A_T2 = prove(c8a_t2,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C8A_MEMVAR_TAC `m0:int64->byte` THEN
  W(fun (asl,w) -> C8A_THEN (r5b_inst2 asl (INST [c8a_nL,`n:num`] (SPEC_ALL C8A_ENTRY2V)))) THEN
  R5B_DISJ_TAC THEN CONJ_TAC THENL
   [R5B_PURE_TAC THEN
    W(fun (asl,w) -> C8A_THENM (c8a_inst3 asl (INST [`L:(num->int32)list`,`L0:(num->int32)list`]
                       (SPECL (`2047` :: `0` :: tl c8a_iter2v_vars) C8A_LOOP2V)))) THEN
    R5B_PURE_TAC THEN
    W(fun (asl,w) -> C8A_THEN (c8a_inst3 asl (INST [subst [`L:(num->int32)list`,`L0:(num->int32)list`] (c8a_L2f `2048`), `L:(num->int32)list`]
                       (SPEC_ALL C8A_T3)))) THEN C8A_SAMEPOST;
    R5B_PURE_TAC THEN
    W(fun (asl,w) -> C8A_THEN (r5b_inst2 asl (INST [c8a_nL,`n:num`] (SPEC_ALL R5B_EPI)))) THEN
    W(fun (asl,w) -> REWRITE_TAC[r5b_inst2 asl (SPEC_ALL c8a_cap2)]) THEN
    W(fun (asl,w) -> REWRITE_TAC[r5b_inst2 asl (SPEC_ALL c8a_cap3)]) THEN C8A_ENDV]);;
let c8a_cap1 = prove(`!mdl hp tbl t rb nd (zq:num->int32) (zp:num->int32). 16384 <= val nd ==>
     va1_fold1 mdl hp tbl t rb nd 2048 ([],zq,zp) = ([],zq,zp)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;`t:int32`;`rb:num->int32`;`nd:int32`;`0`;
     `([],zq,zp):(num->int32)list#(num->int32)#(num->int32)`;`2048`] C8A_FOLD1_CAP) THEN
  ASM_REWRITE_TAC[CONJUNCT1 va1_fold1; ADD_CLAUSES; LENGTH; FST]);;
let c8a_pre0 = mk_abs(`s:wasmstate`, mk_exists(`m0:int64->byte`, list_mk_conj
     [r5b_bd(r5b_pred 13 [] [] []); `read (bytes32 (word 16400)) (m0:int64->byte) = nd`;
      `read (bytes32 (word 16392)) (m0:int64->byte) = t`; `read (bytes32 (word 16648)) (m0:int64->byte) = (mdl:num->int32) 2`;
      c8a_mivL `[]:(num->int32)list` `m0:int64->byte`]));;
