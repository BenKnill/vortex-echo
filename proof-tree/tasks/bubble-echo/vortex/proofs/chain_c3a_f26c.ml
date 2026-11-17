needs "ve_vort.ml";;
needs "ve_tick.ml";;
needs "ve_vk.ml";;
needs "va1_code.ml";;
needs "va1_seq_final2.ml";;
needs "pop_design_defs.ml";;
needs "pop_design_stmts.ml";;
needs "pop_l2_cdrift.ml";;
needs "pop_l3_jdrift.ml";;
needs "pop_l4_drop.ml";;
needs "pop_l1_rimd.ml";;
needs "pop_l1_rim.ml";;
needs "pop_l5_unbirth.ml";;
needs "pop_h1_hol.ml";;
needs "pop_n1_sat.ml";;
needs "pop_q0_calls.ml";;
needs "pop_q1_untick.ml";;
needs "pop_q2_forward.ml";;
needs "pop_r5_jig_defs.ml";;
needs "pop_r5jig_dec.ml";;
needs "pop_r5jig_lem.ml";;
needs "pop_r5_corr_defs.ml";;
needs "pop_r5c_lem.ml";;
needs "pop_r5b_bdec.ml";;
needs "pop_r5bp_lem.ml";;
needs "pop_r5bp_lem2.ml";;
needs "pop_r5bp_lem3.ml";;
needs "pop_r5bp_lem4.ml";;
needs "pop_r5bp_lem5b.ml";;
needs "pop_r5bp_lem6.ml";;
needs "pop_s0_end.ml";;
needs "pop_r5_r4c_final.ml";;
needs "chain_c1_host.ml";;
needs "chain_c3a_defs.ml";;
needs "chain_c3a_f26a.ml";;
needs "chain_c3a_f26b.ml";;
(* ========================================================================= *)
(* Vortex chain, rung C3a, layer 4: f26 assembled (C3A, Claude Opus 5.5,     *)
(* 2026-11-13): entry (pc 5..69), the check loop (layer 2), the 26 header    *)
(* stores (309..556), loop 2, pc 646..652, loop 3 (layer 3), the tail (ND := *)
(* 0, return local 0). The memory atoms a loop does not touch are carried    *)
(* around it by C3_ENSURES_CARRY and component reasoning on its frame (the   *)
(* C1 KEEPS method, chain_c1_np.ml). Result: VA1_F26_OK.                     *)
(* ========================================================================= *)

let C3_ENSURES_CARRY = prove
 (`!(step:A->A->bool) P Q C R.
     ensures step P Q C /\ (!s s'. R s /\ C s s' ==> R s')
     ==> ensures step (\s. P s /\ R s) (\s. Q s /\ R s) C`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures] THEN STRIP_TAC THEN
  X_GEN_TAC `s:A` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  MATCH_MP_TAC C1_EV_MONO_CONJ THEN EXISTS_TAC `\s'. (Q:A->bool) s' /\ C (s:A) s'` THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]);;

(* ---- component frames (verbatim method of chain_c1_np.ml C1_*_KEEPS) ---- *)
let C3_SEQ_KEEPS = prove
 (`!(d:(A,C)component) (r1:A->A->bool) (r2:A->A->bool).
     (!s s'. r1 s s' ==> read d s' = read d s) /\
     (!s s'. r2 s s' ==> read d s' = read d s)
     ==> !s s'. (r1 ,, r2) s s' ==> read d s' = read d s`,
  REWRITE_TAC[seq] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN MESON_TAC[]);;
let C3_ASSIGNS_KEEPS = prove
 (`!(c:(A,B)component) (d:(A,C)component).
     (!y s. read d (write c y s) = read d s)
     ==> !s s'. ASSIGNS c s s' ==> read d s' = read d s`,
  REWRITE_TAC[ASSIGNS_THM] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN MESON_TAC[]);;
let C3_COMP_TAC =
  REPEAT GEN_TAC THEN REWRITE_TAC[wlocal; READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE] THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN REWRITE_TAC[];;
let C3_KEEPS_TAC (comptac:tactic) =
  REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
  REPEAT(MATCH_MP_TAC C3_SEQ_KEEPS THEN CONJ_TAC) THEN
  MATCH_MP_TAC C3_ASSIGNS_KEEPS THEN comptac;;
let C3_B32_COMP_TAC =
  C3_COMP_TAC THEN
  TRY(MATCH_MP_TAC B32_BYTES_OTHER THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

let c3_keep32 lo hi cf = subst [mk_small_numeral lo,`LO:num`; mk_small_numeral hi,`HI:num`; cf,`CF:wasmstate->wasmstate->bool`]
 `!a. (a + 4 <= LO \/ HI <= a) /\ a + 4 < 2 EXP 64
      ==> !s s'. CF s s' ==> read (bytes32 (word a)) (read wmem s') = read (bytes32 (word a)) (read wmem s)`;;
let C3_KEEP32_TAC =
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  C3_KEEPS_TAC C3_B32_COMP_TAC;;
let C3_L2_KEEP32 = prove(c3_keep32 1130496 1179648 C3_LOOP2_FRAME, C3_KEEP32_TAC);;
let C3_L3_KEEP32 = prove(c3_keep32 1179648 1966080 C3_LOOP3_FRAME, C3_KEEP32_TAC);;

(* carry: every atom is a bytes32 read at an address outside the frame *)
let C3_CARRY_TAC (kth:thm) : tactic =
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[va1_pop; va1_w32s]) THEN REWRITE_TAC[va1_pop; va1_w32s] THEN
  REPEAT CONJ_TAC THEN TRY(GEN_TAC THEN DISCH_TAC) THEN
  W(fun (asl,w) ->
    let a = rand(rand(rand(rator(lhs w)))) in
    MP_TAC(SPEC a kth) THEN ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> FIRST_ASSUM(fun cth -> REWRITE_TAC[MATCH_MP th cth])) THEN
    ASM_MESON_TAC[]);;

let c3_r2 = `\m. va1_pop (word 4294967295) ap m /\ read (bytes32 (word 16404)) m = word_add (h:int32) r /\
   va1_w32s 16408 26 (\k. if k < 24 then word 0 else (hp:num->int32) k) m /\
   va1_w32s 1179648 196608 (di:num->int32) m /\ read (bytes32 (word 16400)) m = (nd:int32)`;;
let c3_r3 = `\m. va1_pop (word 4294967295) ap m /\ read (bytes32 (word 16404)) m = word_add (h:int32) r /\
   va1_w32s 16408 26 (\k. if k < 24 then word 0 else (hp:num->int32) k) m /\
   va1_w32s 1130496 2048 (\k. word 0) m /\ va1_w32s 1138688 2048 (\k. word 0) m /\
   va1_w32s 1146880 2048 (\k. word 0) m /\ va1_w32s 1155072 2048 (\k. word 0) m /\
   va1_w32s 1163264 2048 (\k. word 0) m /\ va1_w32s 1171456 2048 (\k. word 0) m /\
   read (bytes32 (word 16400)) m = (nd:int32)`;;

let C3_S_L2 = prove
 ((let lth = C3_LOOP2 in let _,[step;pp;qq;cc] = strip_comb(concl lth) in
   let s = `s:wasmstate` in
   let r = mk_abs(s, rhs(concl(BETA_CONV(mk_comb(c3_r2, mk_comb(`read wmem`, s)))))) in
   rand(concl(ISPECL [step;pp;qq;cc;r] C3_ENSURES_CARRY))),
  MATCH_MP_TAC C3_ENSURES_CARRY THEN CONJ_TAC THENL
   [ACCEPT_TAC C3_LOOP2; C3_CARRY_TAC C3_L2_KEEP32]);;
let C3_S_L3 = prove
 ((let lth = C3_LOOP3 in let _,[step;pp;qq;cc] = strip_comb(concl lth) in
   let s = `s:wasmstate` in
   let r = mk_abs(s, rhs(concl(BETA_CONV(mk_comb(c3_r3, mk_comb(`read wmem`, s)))))) in
   rand(concl(ISPECL [step;pp;qq;cc;r] C3_ENSURES_CARRY))),
  MATCH_MP_TAC C3_ENSURES_CARRY THEN CONJ_TAC THENL
   [ACCEPT_TAC C3_LOOP3; C3_CARRY_TAC C3_L3_KEEP32]);;

(* ---- reads through numeric bytes32 write chains --------------------------- *)
let C3_R32_CONV : conv = fun tm ->
  match tm with
    Comb(Comb(Const("read",_),Comb(Const("bytes32",_),Comb(Const("word",_),x))),
         Comb(Comb(Comb(Const("write",_),Comb(Const("bytes32",_),Comb(Const("word",_),a))),v),m))
      when is_numeral x && is_numeral a ->
      if dest_numeral x = dest_numeral a then
        ISPECL [mk_comb(`word:num->int64`,x); v; m] CAP_B32_SAME
      else
        let th = ISPECL [x; a; v; m] VK_R32_W32 in
        MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))))
  | _ -> failwith "C3_R32_CONV";;

let rec C3_CHAIN32_TAC : tactic = fun g ->
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         MATCH_MP_TAC PL5_W32S_W32 THEN CONJ_TAC THENL [ALL_TAC; CONV_TAC NUM_REDUCE_CONV] THEN
         C3_CHAIN32_TAC] g;;

(* a numeric atom: unfold va1_pop / bounded va1_w32s into reads, then read *)
let C3_NUM_ATOM_TAC : tactic =
  REWRITE_TAC[va1_pop; va1_bs; va1_w32s] THEN
  TRY(CONV_TAC EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(TOP_DEPTH_CONV C3_R32_CONV) THEN ASM_REWRITE_TAC[];;

let C3_ATOM_TAC : tactic = FIRST [C3_CHAIN32_TAC; C3_NUM_ATOM_TAC];;

let C3_HDR_FACTS_TAC : tactic = fun (asl,w) ->
  let th = find (fun th -> let c = concl th in try let h,a = strip_comb c in
     fst(dest_const h) = "va1_w32s" && dest_small_numeral(hd a) = 16408 with _ -> false) (map snd asl) in
  let inst k a = let t = SPECL [`16408`; `26`; `hp:num->int32`; rand(concl th); mk_small_numeral k; mk_small_numeral a] C3_W32S_AT in
                 MP t (CONJ th (EQT_ELIM(NUM_REDUCE_CONV(rand(lhand(concl t)))))) in
  (ASSUME_TAC (inst 24 16504) THEN ASSUME_TAC (inst 25 16508)) (asl,w);;

let c3_fillr r tm = rhs(concl(TOP_DEPTH_CONV BETA_CONV (vsubst [r, `R2:(int64->byte)->bool`] tm)));;

(* ---- 309..556: healErr += err, P := -1, 24 header words := 0, local3 := -8192 *)
let c3_stores_tm = c3_fill (c3_fillr c3_r2 (subst [C3_F26_FRAME,`CF:wasmstate->wasmstate->bool`]
 `ensures wasm
   (\s. read wcode s = va1_f26_mc /\ read wpc s = word 309 /\ read wstatus s = WRunning /\
        read wmemsize s = 4194304 /\ read warity s = 1 /\ read wlabels s = [0,726,0] /\
        read wstack s = [] /\ C3ATOMS (read wmem s) /\ read (wlocal 0) s = I32 (r:int32))
   (\s. read wcode s = va1_f26_mc /\ read wpc s = word 556 /\ read wstatus s = WRunning /\
        read wmemsize s = 4194304 /\ read warity s = 1 /\ read wlabels s = [0,726,0] /\
        read wstack s = [] /\ read (wlocal 3) s = I32 (word 4294959104) /\ read (wlocal 0) s = I32 r /\
        va1_w32s 1130496 2048 (ra:num->int32) (read wmem s) /\ va1_w32s 1138688 2048 (rb:num->int32) (read wmem s) /\
        va1_w32s 1146880 2048 (jq:num->int32) (read wmem s) /\ va1_w32s 1155072 2048 (jp:num->int32) (read wmem s) /\
        va1_w32s 1163264 2048 (zq:num->int32) (read wmem s) /\ va1_w32s 1171456 2048 (zp:num->int32) (read wmem s) /\
        R2 (read wmem s))
   CF`));;

let C3_S_STORES = prove(c3_stores_tm,
  ENSURES_INIT_TAC "s0" THEN ABBREV_TAC `mm = read wmem s0` THEN C3_HDR_FACTS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[va1_pop]) THEN
  C3_STEPS_TO C3A_F26_EXEC 556 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN C3_ATOM_TAC);;

(* ---- entry 5..69, pc 646..652, tail 716..WDone, and the assembly ---------- *)
let c3_bt t = rhs(concl(TOP_DEPTH_CONV BETA_CONV t));;
let c3_parts th = let _,[_;p;q;c] = strip_comb(concl th) in c3_bt p, c3_bt q, c;;

let c3_entry_tm =
  let _,[_;cpre;_;_] = strip_comb c3_check_tm in
  mk_imp(`~(p:int32 = word 4294967295) /\ wasm_decl_vals va1_f26_mc = SOME decls`,
    list_mk_comb(`ensures wasm`, [`PRE26:wasmstate->bool`; cpre; C3_F26_FRAME]));;
let c3_entry_tm = subst [`(\s. read wcode s = va1_f26_mc /\ read wpc s = word 5 /\ read wstatus s = WRunning /\                read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\                read wmemsize s = 4194304 /\ read wlocals s = wcall_locals [] decls /\                va1_pop p ap (read wmem s) /\ va1_mdl mdl (read wmem s) /\                read (bytes32 (word 16404)) (read wmem s) = h /\                va1_w32s 16408 26 hp (read wmem s) /\ va1_w32s 65536 262144 tbl (read wmem s) /\                va1_w32s 1130496 2048 ra (read wmem s) /\ va1_w32s 1138688 2048 rb (read wmem s) /\                va1_w32s 1146880 2048 jq (read wmem s) /\ va1_w32s 1155072 2048 jp (read wmem s) /\                va1_bs (di,zq,zp,nd) (read wmem s))`, `PRE26:wasmstate->bool`] c3_entry_tm;;

let C3_STEPSX_TAC execth (xths:thm list) snums =
  MAP_EVERY (fun s (asl,w) ->
     let mths = filter (fun th -> is_memfact (concl th)) (map snd asl) in
     WASM_SINGLE_STEP_TAC execth (READ_COMPONENT_COMPOSE :: C3_COND_I64 :: C3_COND_I32 :: xths @ mths) s (asl,w))
   (statenames "s" snums);;
let rec C3_STEPSX_TO execth xths pc : tactic = fun (asl,w) ->
  let s = rand w in
  let cur = dest_small_numeral(rand(rhs(concl(find_read_th "wpc" s (map snd asl))))) in
  if cur = pc then ALL_TAC (asl,w) else
  let n = fst(dest_var s) in
  let k = int_of_string(String.sub n 1 (String.length n - 1)) + 1 in
  (C3_STEPSX_TAC execth xths [k] THEN C3_STEPSX_TO execth xths pc) (asl,w);;

let C3_S_ENTRY = prove(c3_entry_tm,
  STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN ABBREV_TAC `mm = read wmem s0` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[va1_bs; va1_pop]) THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `va1_mdl mdl m`) (concl th) then
     ASSUME_TAC(CONV_RULE NUM_REDUCE_CONV (SPEC `2` (REWRITE_RULE[va1_mdl] th))) else NO_TAC) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(LAND_CONV NUM_REDUCE_CONV)) o REWRITE_RULE[ARITH]) THEN
  C3_STEPSX_TO C3A_F26_EXEC [ASSUME `~(p:int32 = word 4294967295)`] 69 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[va1_pop]);;

let c3_mid_tm =
  let _,q2,_ = c3_parts C3_S_L2 and p3,_,_ = c3_parts C3_S_L3 in
  list_mk_comb(`ensures wasm`, [q2; p3; C3_F26_FRAME]);;
let C3_S_MID = prove(c3_mid_tm,
  ENSURES_INIT_TAC "s0" THEN ABBREV_TAC `mm = read wmem s0` THEN
  C3_STEPS_TAC C3A_F26_EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

let c3_tail_tm =
  let _,q3,_ = c3_parts C3_S_L3 in
  list_mk_comb(`ensures wasm`, [q3;
   `\s. read wstatus s = WDone /\ read wstack s = [I32 (r:int32)] /\
        va1_pop (word 4294967295) ap (read wmem s) /\
        read (bytes32 (word 16404)) (read wmem s) = word_add h r /\
        va1_w32s 16408 26 (\k. if k < 24 then word 0 else hp k) (read wmem s) /\
        va1_w32s 1130496 2048 (\k. word 0) (read wmem s) /\ va1_w32s 1138688 2048 (\k. word 0) (read wmem s) /\
        va1_w32s 1146880 2048 (\k. word 0) (read wmem s) /\ va1_w32s 1155072 2048 (\k. word 0) (read wmem s) /\
        va1_bs ((\k. word 0),(\k. word 0),(\k. word 0),word 0) (read wmem s)`;
   C3_F26_FRAME]);;
let C3_S_TAIL = prove(c3_tail_tm,
  ENSURES_INIT_TAC "s0" THEN ABBREV_TAC `mm = read wmem s0` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[va1_pop]) THEN
  C3_STEPS_TAC C3A_F26_EXEC (1--6) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[va1_bs] THEN
  REPEAT CONJ_TAC THEN C3_ATOM_TAC);;

let C3_IMP_TAC (ths:thm list) =
  GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC ths THEN STRIP_TAC THEN ASM_REWRITE_TAC[];;
let C3_USE_TAC (ths:thm list) (th:thm) : tactic =
  let p,q,c = c3_parts th in
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC c THEN CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC p THEN CONJ_TAC THENL [C3_IMP_TAC []; ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC q THEN CONJ_TAC THENL
   [C3_IMP_TAC ths;
    FIRST [ACCEPT_TAC th;
           CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ACCEPT_TAC (CONV_RULE(TOP_DEPTH_CONV BETA_CONV) th)]];;
let c3_mid th = let _,q,_ = c3_parts th in let s,b = dest_abs q in mk_abs(s, list_mk_conj(tl(tl(conjuncts b))));;
let c3_r = `word_add nd (word (nsum (0..2047) (va1_mis mdl tbl ((ra:num->int32),(rb:num->int32),(jq:num->int32),(jp:num->int32),(zq:num->int32),(zp:num->int32))))):int32`;;
let c3_ri th = INST [c3_r,`r:int32`] th;;

let VA1_F26_OK = prove
 (`!p ap mdl hp tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32) h decls.
     ~(p = word 4294967295) /\ wasm_decl_vals va1_f26_mc = SOME decls
     ==> ensures wasm
          (\s. read wcode s = va1_f26_mc /\ read wpc s = word 5 /\ read wstatus s = WRunning /\
               read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\ read wlocals s = wcall_locals [] decls /\
               va1_pop p ap (read wmem s) /\ va1_mdl mdl (read wmem s) /\
               read (bytes32 (word 16404)) (read wmem s) = h /\
               va1_w32s 16408 26 hp (read wmem s) /\ va1_w32s 65536 262144 tbl (read wmem s) /\
               va1_w32s 1130496 2048 ra (read wmem s) /\ va1_w32s 1138688 2048 rb (read wmem s) /\
               va1_w32s 1146880 2048 jq (read wmem s) /\ va1_w32s 1155072 2048 jp (read wmem s) /\
               va1_bs (di,zq,zp,nd) (read wmem s))
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (va1_bad mdl tbl (ra,rb,jq,jp,zq,zp,nd))] /\
               va1_pop (word 4294967295) ap (read wmem s) /\
               read (bytes32 (word 16404)) (read wmem s) = word_add h (va1_bad mdl tbl (ra,rb,jq,jp,zq,zp,nd)) /\
               va1_w32s 16408 26 (\k. if k < 24 then word 0 else hp k) (read wmem s) /\
               va1_w32s 1130496 2048 (\k. word 0) (read wmem s) /\ va1_w32s 1138688 2048 (\k. word 0) (read wmem s) /\
               va1_w32s 1146880 2048 (\k. word 0) (read wmem s) /\ va1_w32s 1155072 2048 (\k. word 0) (read wmem s) /\
               va1_bs ((\k. word 0),(\k. word 0),(\k. word 0),word 0) (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocal 0; wlocal 1; wlocal 2; wlocal 3; wlocal 4; wlocal 5] ,,
           MAYCHANGE [wmem :> bytes(word 16396,116)] ,, MAYCHANGE [wmem :> bytes(word 1130496,835584)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let eth = MP C3_S_ENTRY (CONJ (ASSUME `~(p:int32 = word 4294967295)`) (ASSUME `wasm_decl_vals va1_f26_mc = SOME decls`)) in
  ENSURES_SEQUENCE_TAC `69` (c3_mid eth) THEN CONJ_TAC THENL [C3_USE_TAC [] eth; ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `309` (c3_mid C3_F26_CHECK) THEN CONJ_TAC THENL [C3_USE_TAC [] C3_F26_CHECK; ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `556` (c3_mid (c3_ri C3_S_STORES)) THEN CONJ_TAC THENL [C3_USE_TAC [] (c3_ri C3_S_STORES); ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `646` (c3_mid (c3_ri C3_S_L2)) THEN CONJ_TAC THENL [C3_USE_TAC [] (c3_ri C3_S_L2); ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `652` (c3_mid (c3_ri C3_S_MID)) THEN CONJ_TAC THENL [C3_USE_TAC [] (c3_ri C3_S_MID); ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `716` (c3_mid (c3_ri C3_S_L3)) THEN CONJ_TAC THENL [C3_USE_TAC [] (c3_ri C3_S_L3); ALL_TAC] THEN
  C3_USE_TAC [va1_bad; ETA_AX] (c3_ri C3_S_TAIL));;
