needs "ve_vort.ml";;
needs "ve_tick.ml";;
needs "ve_vk.ml";;
needs "va1_code.ml";;
needs "va1_seq_final2.ml";;
needs "pop_design_defs.ml";;
needs "pop_design_stmts.ml";;
(* ========================================================================= *)
(* Vortex pop, segment Q0 (SEGMENT PROVER Q0, Claude Opus 5.5, 2026-11-11):  *)
(* the 18 call-site lemmas VA1P_CALL_F9 .. F24, F27, F28 of the frozen       *)
(* statement strings pop_spec_Q0_CALL_Fnn (pop_design_stmts.ml 97f899dc).  *)
(* Each is proved from the callee's leaf theorem (a contract premise         *)
(* va1_*_ok, or VE_VORT_*_FREDKIN + VE_VK_OK / VE_TICK_*_CORRECT for         *)
(* f9/f10/f27/f28) through the call rule of wasm_call.ml, generalising       *)
(* VA1_CALL_TAC (va1_seq_final2.ml) to 1 parameter / 1 result and to the     *)
(* 11-conjunct state predicate va1_st, whose frame is carried atom by atom   *)
(* by one disjointness conversion (Q0_FRAME_CONV).                          *)
(* TAIL layer (after pop_h1_hol.ml, pop_n1_sat.ml in the R2/R3 chains).       *)
(* ========================================================================= *)

(* ---- small list / state algebra ---------------------------------------- *)

let Q0_WTAKE_0 = prove
 (`!l:A list. wtake 0 l = []`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[wtake]);;

let Q0_WTAKE_1 = prove
 (`!x:A. wtake 1 [x] = [x]`,
  REWRITE_TAC[wtake] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let Q0_WDROP_1 = prove
 (`!x:A. wdrop 1 [x] = []`,
  REWRITE_TAC[wdrop] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[wdrop]);;

(* write wmem of a write chain over the old memory = component writes *)
let Q0_WMEM_PEEL = prove
 (`!(d:(int64->byte,A)component) y M (s:wasmstate).
     write wmem (write d y M) s = write (wmem :> d) y (write wmem M s)`,
  REWRITE_TAC[WRITE_COMPONENT_COMPOSE; WMEM_SVC]);;

let Q0_WMEM_ID = prove
 (`!s:wasmstate. write wmem (read wmem s) s = s`,
  REWRITE_TAC[WMEM_SVC]);;

(* a write of the unchanged stack over a memory write is no write *)
let Q0_WSTACK_ID = prove
 (`!M (s:wasmstate). write wstack (read wstack s) (write wmem M s) = write wmem M s`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `read wstack (s:wasmstate) = read wstack (write wmem M s)` SUBST1_TAC THENL
   [CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN REFL_TAC;
    REWRITE_TAC[WSTACK_SVC]]);;

(* the return state of a done callee that kept memory size and globals *)
let Q0_WCALL_RETURN = prove
 (`!npc np c1 s.
     read wstatus c1 = WDone /\
     read wmemsize c1 = read wmemsize s /\ read wglobals c1 = read wglobals s
     ==> wcall_return npc np c1 s =
         write wpc (word npc)
          (write wstack (APPEND (read wstack c1) (wdrop np (read wstack s)))
            (write wmem (read wmem c1) s))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[wcall_return] THEN
  REWRITE_TAC[WGLOBALS_SVC; WMEMSIZE_SVC]);;

(* the call rule, simulation form, any parameter count *)
let Q0_WASMC_CALLN_STEP = prove
 (`!fs f code np nr e decls (P:wasmstate->bool) Q C n s R.
     ensures wasm P Q C /\
     (!c. Q c ==> ~(read wstatus c = WRunning)) /\
     fs f = (code,np,nr) /\ wasm_entry code = SOME e /\
     wasm_decl_vals code = SOME decls /\
     read wstatus s = WRunning /\
     wasm_decode (read wcode s) (val (read wpc s)) = SOME (Wcall f,n) /\
     np <= LENGTH (read wstack s) /\
     P (wcall_entry code np nr (read wstack s) e decls s) /\
     (!c1. Q c1 /\ C (wcall_entry code np nr (read wstack s) e decls s) c1
           ==> R (wcall_return (val (read wpc s) + n) np c1 s))
     ==> eventually (wasmc fs) R s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`fs:num->byte list#num#num`; `f:num`; `code:byte list`;
    `np:num`; `nr:num`; `e:num`; `decls:wval list`; `P:wasmstate->bool`;
    `Q:wasmstate->bool`; `C:wasmstate->wasmstate->bool`;
    `\x:wasmstate. x = s`; `R:wasmstate->bool`;
    `\x:wasmstate y:wasmstate. T`; `n:num`] WASMC_CALL_ENSURES) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THEN REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      let c = concl th in is_eq c && rhs c = `s:wasmstate` && is_var(lhs c))) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[ensures] THEN DISCH_THEN(MP_TAC o SPEC `s:wasmstate`) THEN
    REWRITE_TAC[ETA_AX]]);;

(* ---- frame lemmas: one per state atom, writes of bytes(word b,len) ------- *)

let Q0_ARITH_TAC =
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_ARITH_TAC;;

let Q0_W32S_WRITE = prove
 (`!base n (f:num->int32) b len (y:num) (m:int64->byte).
     (base + 4 * n <= b \/ b + len <= base) /\ base + 4 * n < 2 EXP 64 /\
     b + len < 2 EXP 64
     ==> (va1_w32s base n f (write (bytes(word b,len)) y m) <=> va1_w32s base n f m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[va1_w32s] THEN
  SUBGOAL_THEN
   `!k. k < n ==> read (bytes32 (word (base + 4 * k))) (write (bytes(word b,len)) y m) =
                  read (bytes32 (word (base + 4 * k))) m`
   (fun th -> SIMP_TAC[th]) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC B32_BYTES_OTHER THEN Q0_ARITH_TAC);;

let Q0_TICK_WRITE = prove
 (`!t b len (y:num) (m:int64->byte).
     (16396 <= b \/ b + len <= 16392) /\ b + len < 2 EXP 64
     ==> (va1_tick t (write (bytes(word b,len)) y m) <=> va1_tick t m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[va1_tick] THEN
  SUBGOAL_THEN `read (bytes32 (word 16392)) (write (bytes(word b,len)) y m) =
                read (bytes32 (word 16392)) m` (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC B32_BYTES_OTHER THEN Q0_ARITH_TAC);;

let Q0_POP_WRITE = prove
 (`!pt ap b len (y:num) (m:int64->byte).
     (16400 <= b \/ b + len <= 16396) /\ (16516 <= b \/ b + len <= 16512) /\
     b + len < 2 EXP 64
     ==> (va1_pop pt ap (write (bytes(word b,len)) y m) <=> va1_pop pt ap m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[va1_pop] THEN
  SUBGOAL_THEN `read (bytes32 (word 16396)) (write (bytes(word b,len)) y m) =
                read (bytes32 (word 16396)) m /\
                read (bytes32 (word 16512)) (write (bytes(word b,len)) y m) =
                read (bytes32 (word 16512)) m` (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THEN MATCH_MP_TAC B32_BYTES_OTHER THEN Q0_ARITH_TAC);;

let Q0_MDL_WRITE = prove
 (`!mdl b len (y:num) (m:int64->byte).
     (20736 <= b \/ b + len <= 16640) /\ b + len < 2 EXP 64
     ==> (va1_mdl mdl (write (bytes(word b,len)) y m) <=> va1_mdl mdl m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[va1_mdl] THEN
  SUBGOAL_THEN
   `!k. k < 1024 ==> read (bytes32 (word (16640 + 4 * k))) (write (bytes(word b,len)) y m) =
                     read (bytes32 (word (16640 + 4 * k))) m`
   (fun th -> SIMP_TAC[th]) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC B32_BYTES_OTHER THEN Q0_ARITH_TAC);;

let Q0_VAB_WRITE = prove
 (`!N. N <= 640
       ==> !x b len (y:num) (m:int64->byte).
             (1130496 <= b \/ b + len <= 1114112) /\ b + len < 2 EXP 64
             ==> (va1_vab N x (write (bytes(word b,len)) y m) <=> va1_vab N x m)`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[va1_vab] THEN
  SUBGOAL_THEN
   `(!j. j < 3 * N
         ==> read (bytes32 (word (1114112 + 4 * j))) (write (bytes(word b,len)) y m) =
             read (bytes32 (word (1114112 + 4 * j))) m) /\
    (!j. j < 3 * N
         ==> read (bytes32 (word (1122304 + 4 * j))) (write (bytes(word b,len)) y m) =
             read (bytes32 (word (1122304 + 4 * j))) m)`
   (fun th -> SIMP_TAC[th]) THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC B32_BYTES_OTHER THEN Q0_ARITH_TAC);;

(* one peel: P .. (write (bytes(word b,len)) y m) --> P .. m when the atom's *)
(* region and [b,b+len) are disjoint (side condition decided on numerals)   *)
let Q0_FRAME1_CONV (ths:thm list) : conv = fun tm ->
  let is_wbytes t =
    try let w,args = strip_comb t in
        fst(dest_const w) = "write" && length args = 3 &&
        (let c = hd args in fst(dest_const(rator c)) = "bytes")
    with Failure _ -> false in
  if not (is_comb tm && is_wbytes (rand tm)) then failwith "Q0_FRAME1_CONV" else
  tryfind (fun th ->
    let th1 = PART_MATCH (lhs o rand) th tm in
    let side = lhand(concl th1) in
    let sth = EQT_ELIM((NUM_REDUCE_CONV THENC REWRITE_CONV[]) side) in
    MP th1 sth) ths;;

let Q0_FRAME_THS =
  [Q0_W32S_WRITE; Q0_TICK_WRITE; Q0_POP_WRITE; Q0_MDL_WRITE; B32_BYTES_OTHER];;

(* close one conjunct of the post state: an atom the callee leaves alone     *)
(* (peel the writes, then the precondition fact), or the callee's own result  *)
let Q0_CLOSE_TAC : tactic = fun (asl,w) ->
  let nth = try let th = find (fun th -> let c = concl th in
                  try fst(dest_const(fst(dest_comb(rator c)))) = "<=" &&
                      rand c = `640` && is_var(lhand c) with Failure _ -> false) (map snd asl) in
                [MP (SPEC (lhand(concl th)) Q0_VAB_WRITE) th]
            with Failure _ -> [] in
  let ths = Q0_FRAME_THS @ map (fun th -> SPEC_ALL th) nth in
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         CONV_TAC(TOP_DEPTH_CONV(Q0_FRAME1_CONV ths)) THEN FIRST_ASSUM ACCEPT_TAC;
         REWRITE_TAC[va1_vab; va1_tick; PAIR] THEN ASM_SIMP_TAC[PAIR]] (asl,w);;

(* ---- the call-site tactic ------------------------------------------------ *)
(* lth = |- ensures wasm P Q C for the callee (hypotheses: premises that the  *)
(* goal's antecedent provides), cth = WASM_CALLEE_RULE of its code, f the    *)
(* function index, np/nr its parameter / result counts.                       *)

(* on failure, print which step failed and its goal (diagnostics only) *)
let Q0_DBG (name:string) (tac:tactic) : tactic = fun g ->
  try tac g with Failure m ->
    (Printf.printf "\n@@DBG %s failed: %s\n%!" name m; print_goal g; failwith m);;

let q0_is_head_const name tm =
  try fst(dest_const(fst(strip_comb tm))) = name with Failure _ -> false;;

let Q0_CALL_TAC (lth:thm) (cth:thm) (f:term) (np:term) (nr:term) : tactic =
  let _,[_;pp;qq;cc] = strip_comb(concl lth) in
  let eth,dth = CONJ_PAIR cth in
  let code = rand(lhand(concl eth)) and e = rand(rand(concl eth))
  and decls = rand(rand(concl dth)) in
  let c0tm = list_mk_comb(`wcall_entry`,
     [code; np; nr; `read wstack (s0:wasmstate)`; e; decls; `s0:wasmstate`]) in
  let is_rmem_c1 th = let c = concl th in
     is_eq c && lhs c = `read wmem (c1:wasmstate)` in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[va1_st; va1_bs] o
                check (q0_is_head_const "va1_st" o concl)) THEN
  ABBREV_TAC `mm0 = read wmem (s0:wasmstate)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  (fun (asl,w) ->
     let fs = rand(rand(rator(rator w))) in
     MATCH_MP_TAC (ISPECL [fs; f; code; np; nr; e; decls; pp; qq; cc; `6`]
                     Q0_WASMC_CALLN_STEP) (asl,w)) THEN
  CONJ_TAC THENL [ACCEPT_TAC lth; ALL_TAC] THEN
  CONJ_TAC THENL
   [CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN MESON_TAC[distinctness "wstat"];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ACCEPT_TAC eth; ALL_TAC] THEN
  CONJ_TAC THENL [ACCEPT_TAC dth; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[LE_0; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  CONJ_TAC THENL
   [Q0_DBG "callee precondition"
     (CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC[WCALL_ENTRY_READS; READ_COMPONENT_COMPOSE] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[va1_tick; va1_pop; va1_mdl; va1_vab]) THEN
      REWRITE_TAC[va1_tick; va1_pop; va1_mdl; va1_vab; va1_bs] THEN
      ASM_REWRITE_TAC[Q0_WTAKE_0; Q0_WTAKE_1] THEN ASM_SIMP_TAC[PAIR] THEN NO_TAC);
    ALL_TAC] THEN
  (* the continuation: every final callee state c1 *)
  Q0_DBG "X_GEN_TAC c1" (X_GEN_TAC `c1:wasmstate`) THEN
  ABBREV_TAC (mk_eq(`c0:wasmstate`, c0tm)) THEN
  SUBGOAL_THEN `read wmem (c0:wasmstate) = mm0 /\ read wmemsize c0 = 4194304 /\
                read wglobals c0 = (gl:num->wval)`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c0" THEN ASM_REWRITE_TAC[WCALL_ENTRY_READS]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (STRIP_ASSUME_TAC o CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) MP_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [MAYCHANGE; SEQ_ID] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [GSYM SEQ_ASSOC] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_SEQ] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
  CAP_MEM_UPDATE_TAC THEN ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `val (read wpc (s0:wasmstate)) = cp` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN
  W(fun (asl,w) ->
     let rth = SPECL [`cp + 6`; np; `c1:wasmstate`; `s0:wasmstate`] Q0_WCALL_RETURN in
     MP_TAC rth THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  FIRST_X_ASSUM(fun th -> if is_rmem_c1 th
    then REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC) THEN
  (* the stack after the call *)
  W(fun (asl,w) ->
     let sths = filter (fun th -> let c = concl th in
        is_eq c && (lhs c = `read wstack (c1:wasmstate)` ||
                    lhs c = `read wstack (s0:wasmstate)`)) (map snd asl) in
     REWRITE_TAC(sths @ [APPEND; APPEND_NIL; Q0_WDROP_1; WDROP_0])) THEN
  REWRITE_TAC[Q0_WSTACK_ID] THEN
  FIRST_ASSUM(fun th -> if concl th = `read wmem (s0:wasmstate) = mm0`
    then REWRITE_TAC[SYM th] else NO_TAC) THEN
  REWRITE_TAC[Q0_WMEM_PEEL; Q0_WMEM_ID] THEN
  VA1_GEN_STATE_TAC `s1:wasmstate` THEN
  Q0_DBG "X_GEN_TAC s1" (X_GEN_TAC `s1:wasmstate`) THEN
  CAP_MEM_UPDATE_TAC THEN ASSUMPTION_STATE_UPDATE_TAC THEN MAYCHANGE_STATE_UPDATE_TAC THEN
  DISCH_THEN(fun th ->
    let thl = STATE_UPDATE_NEW_RULE th in
    if thl = [] then ALL_TAC else MP_TAC(end_itlist CONJ thl) THEN STRIP_TAC) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CONJ_TAC THENL [ALL_TAC; MONOTONE_MAYCHANGE_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(EXISTS_TAC `r:int32` THEN REFL_TAC) THEN
  TRY(EXISTS_TAC `L:(num->int32)list`) THEN
  REWRITE_TAC[va1_st; va1_bs] THEN
  REPEAT CONJ_TAC THEN Q0_CLOSE_TAC;;

(* ---- leaf theorems from the contracts ----------------------------------- *)

(* okth = |- c <=> body (c a contract premise), sel picks the export,      *)
(* vars instantiate its variables (then decls), ants = its other premises  *)
let Q0_CONTRACT (okth:thm) (sel:thm->thm) (vars:term list) (ants:term list) (cth:thm) =
  let body = EQ_MP okth (ASSUME (lhs(concl okth))) in
  let dth = CONJUNCT2 cth in
  let decls = rand(rand(concl dth)) in
  let th1 = SPECL (vars @ [decls]) (sel body) in
  MP th1 (end_itlist CONJ (map ASSUME ants @ [dth]));;

let Q0_VORT_LEAF (th:thm) =
  let th1 = MP (SPEC `ve_vk` th) VE_VK_OK in
  let th2 = SPECL [`N:num`; `mdl:num->int32`; `FST (x:(num->int32)#(num->int32))`;
                   `SND (x:(num->int32)#(num->int32))`] th1 in
  MP th2 (end_itlist CONJ (map ASSUME
    [`(mdl:num->int32) 1 = word N`; `1 <= N`; `N <= 640`]));;

let q0_tbl = `tbl:num->int32` and q0_ra = `ra:num->int32` and q0_rb = `rb:num->int32`
and q0_jq = `jq:num->int32` and q0_jp = `jp:num->int32` and q0_di = `di:num->int32`
and q0_zq = `zq:num->int32` and q0_zp = `zp:num->int32` and q0_nd = `nd:int32`
and q0_mdl = `mdl:num->int32` and q0_hp = `hp:num->int32` and q0_t = `t:int32`
and q0_p = `p:int32` and q0_ap = `ap:int32` and q0_sub = `sub:num`;;
let q0_CK = `CK:(num->int32)->(num->int32)->(num->int32)->int32->int32->num->(num->int32)->(num->int32)->num->int32`;;
let q0_JK = `JK:(num->int32)->(num->int32)->(num->int32)->int32->int32->(num->int32)->(num->int32)->num->int32`;;

(* ---- the 18 call-site lemmas -------------------------------------------- *)

let VA1P_CALL_F15 = prove(parse_term pop_spec_VA1P_CALL_F15,
  Q0_CALL_TAC (Q0_CONTRACT va1_rim_ok CONJUNCT1 [q0_tbl; q0_ra; q0_rb] [] VA1_F15_CALLEE)
    VA1_F15_CALLEE `15` `0` `0`);;

let VA1P_CALL_F16 = prove(parse_term pop_spec_VA1P_CALL_F16,
  Q0_CALL_TAC (Q0_CONTRACT va1_rim_ok CONJUNCT2 [q0_tbl; q0_ra; q0_rb] [] VA1_F16_CALLEE)
    VA1_F16_CALLEE `16` `0` `0`);;

let VA1P_CALL_F19 = prove(parse_term pop_spec_VA1P_CALL_F19,
  Q0_CALL_TAC (Q0_CONTRACT va1_cdrift_ok CONJUNCT1 [q0_rb; q0_zq; q0_zp] [] VA1_F19_CALLEE)
    VA1_F19_CALLEE `19` `0` `0`);;

let VA1P_CALL_F20 = prove(parse_term pop_spec_VA1P_CALL_F20,
  Q0_CALL_TAC (Q0_CONTRACT va1_cdrift_ok CONJUNCT2 [q0_rb; q0_zq; q0_zp] [] VA1_F20_CALLEE)
    VA1_F20_CALLEE `20` `0` `0`);;

let VA1P_CALL_F23 = prove(parse_term pop_spec_VA1P_CALL_F23,
  Q0_CALL_TAC (Q0_CONTRACT va1_jdrift_ok CONJUNCT1 [q0_mdl; q0_jq; q0_jp] [] VA1_F23_CALLEE)
    VA1_F23_CALLEE `23` `0` `0`);;

let VA1P_CALL_F24 = prove(parse_term pop_spec_VA1P_CALL_F24,
  Q0_CALL_TAC (Q0_CONTRACT va1_jdrift_ok CONJUNCT2 [q0_mdl; q0_jq; q0_jp] [] VA1_F24_CALLEE)
    VA1_F24_CALLEE `24` `0` `0`);;

let VA1P_CALL_F11 = prove(parse_term pop_spec_VA1P_CALL_F11,
  Q0_CALL_TAC (Q0_CONTRACT va1_drop_ok CONJUNCT1 [q0_di; q0_nd] [] VA1_F11_CALLEE)
    VA1_F11_CALLEE `11` `0` `0`);;

let VA1P_CALL_F12 = prove(parse_term pop_spec_VA1P_CALL_F12,
  Q0_CALL_TAC (Q0_CONTRACT va1_drop_ok CONJUNCT2 [q0_di; q0_nd] [] VA1_F12_CALLEE)
    VA1_F12_CALLEE `12` `0` `0`);;

let VA1P_CALL_F21 = prove(parse_term pop_spec_VA1P_CALL_F21,
  Q0_CALL_TAC (Q0_CONTRACT (SPEC q0_JK va1_jigk_ok) CONJUNCT1
                   [q0_mdl; q0_hp; q0_tbl; q0_t; q0_p; q0_ap; q0_jq; q0_rb; q0_jp]
                   [`va1_pop_window t p`] VA1_F21_CALLEE)
    VA1_F21_CALLEE `21` `0` `0`);;

let VA1P_CALL_F22 = prove(parse_term pop_spec_VA1P_CALL_F22,
  Q0_CALL_TAC (Q0_CONTRACT (SPEC q0_JK va1_jigk_ok) CONJUNCT2
                   [q0_mdl; q0_hp; q0_tbl; q0_t; q0_p; q0_ap; q0_jq; q0_rb; q0_jp]
                   [`va1_pop_window t p`] VA1_F22_CALLEE)
    VA1_F22_CALLEE `22` `0` `0`);;

let VA1P_CALL_F17 = prove(parse_term pop_spec_VA1P_CALL_F17,
  Q0_CALL_TAC (Q0_CONTRACT (SPEC q0_CK va1_corrk_ok) CONJUNCT1
                   [q0_sub; q0_mdl; q0_hp; q0_tbl; q0_t; q0_p; q0_ap; q0_zq; q0_rb; q0_zp]
                   [`sub < 4`; `va1_pop_window t p`] VA1_F17_CALLEE)
    VA1_F17_CALLEE `17` `1` `0`);;

let VA1P_CALL_F18 = prove(parse_term pop_spec_VA1P_CALL_F18,
  Q0_CALL_TAC (Q0_CONTRACT (SPEC q0_CK va1_corrk_ok) CONJUNCT2
                   [q0_sub; q0_mdl; q0_hp; q0_tbl; q0_t; q0_p; q0_ap; q0_zq; q0_rb; q0_zp]
                   [`sub < 4`; `va1_pop_window t p`] VA1_F18_CALLEE)
    VA1_F18_CALLEE `18` `1` `0`);;

let VA1P_CALL_F13 = prove(parse_term pop_spec_VA1P_CALL_F13,
  Q0_CALL_TAC (Q0_CONTRACT va1_birth_ok I
                   [q0_mdl; q0_hp; q0_tbl; q0_t; q0_p; q0_ap; q0_ra; q0_rb; q0_di; q0_zq; q0_zp; q0_nd]
                   [`va1_pop_window t p`; `va1_log_ok t di nd`] VA1_F13_CALLEE)
    VA1_F13_CALLEE `13` `0` `1`);;

let VA1P_CALL_F14 = prove(parse_term pop_spec_VA1P_CALL_F14,
  Q0_CALL_TAC (Q0_CONTRACT va1_unbirth_ok I [q0_t; q0_di; q0_zq; q0_zp; q0_nd]
                   [`val (nd:int32) <= 16384`] VA1_F14_CALLEE)
    VA1_F14_CALLEE `14` `0` `1`);;

let VA1P_CALL_F9 = prove(parse_term pop_spec_VA1P_CALL_F9,
  REWRITE_TAC[VA1_F9_IS_VORT_APPLY] THEN
  Q0_CALL_TAC (Q0_VORT_LEAF VE_VORT_APPLY_FREDKIN) VE_VORT_APPLY_CALLEE `9` `0` `0`);;

let VA1P_CALL_F10 = prove(parse_term pop_spec_VA1P_CALL_F10,
  REWRITE_TAC[VA1_F10_IS_VORT_UNAPPLY] THEN
  Q0_CALL_TAC (Q0_VORT_LEAF VE_VORT_UNAPPLY_FREDKIN) VE_VORT_UNAPPLY_CALLEE `10` `0` `0`);;

let VA1P_CALL_F27 = prove(parse_term pop_spec_VA1P_CALL_F27,
  REWRITE_TAC[VA1_F27_IS_TICK_INC] THEN
  Q0_CALL_TAC (SPEC q0_t VE_TICK_INC_CORRECT) VE_TICK_INC_CALLEE `27` `0` `0`);;

let VA1P_CALL_F28 = prove(parse_term pop_spec_VA1P_CALL_F28,
  REWRITE_TAC[VA1_F28_IS_TICK_DEC] THEN
  Q0_CALL_TAC (SPEC q0_t VE_TICK_DEC_CORRECT) VE_TICK_DEC_CALLEE `28` `0` `0`);;
