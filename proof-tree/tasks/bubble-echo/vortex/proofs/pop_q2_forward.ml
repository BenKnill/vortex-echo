needs "ve_vort.ml";;
needs "ve_tick.ml";;
needs "ve_vk.ml";;
needs "va1_code.ml";;
needs "va1_seq_final2.ml";;
needs "pop_design_defs.ml";;
needs "pop_design_stmts.ml";;
needs "pop_h1_hol.ml";;
needs "pop_n1_sat.ml";;
needs "pop_q0_calls.ml";;
(* ========================================================================= *)
(* Vortex pop, segment Q2 (SEGMENT PROVER Q2, Claude Opus 5.5, 2026-11-11):  *)
(* rung R3, the forward pop tick VA1_TICK_FORWARD_POP_COND of the frozen     *)
(* statement string pop_spec_VA1_TICK_FORWARD_POP_COND (pop_design_stmts.ml  *)
(* 97f899dc), spec pop_design_r3_forward.spec (0a0913b1).                    *)
(*                                                                           *)
(* tick_forward (f35) of vortex_a1.wasm in the pop window: pc 13 load P,     *)
(* pc 22 eq -1 (false), pc 27 load T, pc 36 ge_u (true: br_if 1 to pc 133),  *)
(* local 2 := 0, pc 145 ge_u against P + 520 (false), then the 15 calls      *)
(* 15, 21, 23, [const s, 17, 19] s = 0..3, 11, 13 (+ drop), 9, 27, local 2   *)
(* := 1, pc 254 load P, ne -1 (true: br_if 0 to the outer end), return 1.    *)
(* Each call goes through the Q0 call-site lemma VA1P_CALL_Fnn, instantiated *)
(* by matching its va1_st precondition against the current va1_st fact; the  *)
(* new tuple components are abbreviated at once (small terms), the births    *)
(* tuple after f13 is split into four variables, and the end identifies the  *)
(* abbreviations with va1_pop_fwd unfolded on the literal tuple.             *)
(* No definitions, no parser changes in this file (spec-locked leaf).        *)
(* ========================================================================= *)

let q2_is_head name tm =
  try fst(dest_const(fst(strip_comb tm))) = name with Failure _ -> false;;

(* on failure, print which step failed and its goal (diagnostics only) *)
let Q2_DBG (name:string) (tac:tactic) : tactic = fun g ->
  try tac g with Failure m ->
    (Printf.printf "\n@@DBG %s failed: %s\n%!" name m; print_goal g; failwith m);;

(* the header facts the branch tests read, from the whole-state predicate *)
let Q2_ST_TP = prove
 (`!t p ap mdl N x hp tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32)
    (bs:(num->int32)#(num->int32)#(num->int32)#int32) m.
     va1_st t p ap mdl N x hp tbl (ra,rb,jq,jp,bs) m
     ==> read (bytes32 (word 16392)) m = t /\ read (bytes32 (word 16396)) m = p`,
  REWRITE_TAC[va1_st; va1_tick; va1_pop] THEN SIMP_TAC[]);;

(* a births state is a literal 4-tuple *)
let Q2_BS_SURJ = prove
 (`!bs:(num->int32)#(num->int32)#(num->int32)#int32.
     ?d z w n. bs = (d,z,w,n)`,
  GEN_TAC THEN MAP_EVERY EXISTS_TAC
   [`FST (bs:(num->int32)#(num->int32)#(num->int32)#int32)`;
    `FST (SND (bs:(num->int32)#(num->int32)#(num->int32)#int32))`;
    `FST (SND (SND (bs:(num->int32)#(num->int32)#(num->int32)#int32)))`;
    `SND (SND (SND (bs:(num->int32)#(num->int32)#(num->int32)#int32)))`] THEN
  REWRITE_TAC[PAIR]);;

(* four corrugation substeps unrolled *)
let Q2_KD4 = prove
 (`!K D s. ve_kd_fwdn K D 4 s =
           ve_kd_fwd (K 3) (D 3) (ve_kd_fwd (K 2) (D 2)
             (ve_kd_fwd (K 1) (D 1) (ve_kd_fwd (K 0) (D 0) s)))`,
  REWRITE_TAC[ARITH_RULE `4 = SUC 3 /\ 3 = SUC 2 /\ 2 = SUC 1 /\ 1 = SUC 0`;
              VA1P_KD_FWDN_CLAUSES]);;

(* ---- a step that also rewrites with the state-free hypotheses (S0's) ---- *)
let Q2_MSTEP_TAC execth sname (asl,w) =
  let notstate th =
    not (exists (fun v -> type_of v = `:wasmstate`) (frees (concl th))) in
  let mths = filter (fun th -> is_memfact (concl th) || notstate th) (map snd asl) in
  (CAPC_STEP_TAC execth
     (READ_COMPONENT_COMPOSE :: VA1_GTU_MAX :: GE :: BITVAL_CLAUSES :: mths) sname THEN
   CAP_DISCARD_OLD_TAC sname) (asl,w);;

(* ---- name the current memory; header reads from its va1_st fact ---------- *)
let Q2_MEMNAME_TAC (mmname:string) : tactic = fun (asl,w) ->
  let s = rand w in
  let mmv = mk_var(mmname,`:int64->byte`) in
  (ABBREV_TAC (mk_eq(mmv, mk_comb(`read wmem`, s))) THEN
   POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
   (fun (asl,w) ->
      let hs = filter (fun th -> let c = concl th in
        q2_is_head "va1_st" c && rand c = mmv) (map snd asl) in
      MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP Q2_ST_TP th)) hs (asl,w)))
  (asl,w);;

(* ---- abbreviate the non-variable components of the va1_st fact on mm ---- *)
let q2_ctr = ref 0;;
let q2_fresh ty =
  (q2_ctr := !q2_ctr + 1; mk_var("q2v" ^ string_of_int (!q2_ctr), ty));;

let Q2_ABBREV_TAC (mm:term) : tactic = fun (asl,w) ->
  let th = find (fun th -> let c = concl th in q2_is_head "va1_st" c && rand c = mm)
             (map snd asl) in
  let _,args = strip_comb (concl th) in
  let x = el 5 args and ps = el 8 args in
  let ra,r1 = dest_pair ps in let rb,r2 = dest_pair r1 in
  let jq,r3 = dest_pair r2 in let jp,bs = dest_pair r3 in
  let abbrev c =
    if is_var c then ALL_TAC else
    ABBREV_TAC (mk_eq(q2_fresh (type_of c), c)) in
  let bstac =
    if is_pair bs then
      let di,b1 = dest_pair bs in let zq,b2 = dest_pair b1 in
      let zp,nd = dest_pair b2 in
      MAP_EVERY abbrev [di; zq; zp; nd]
    else
      let d = q2_fresh `:num->int32` and z = q2_fresh `:num->int32`
      and zz = q2_fresh `:num->int32` and n = q2_fresh `:int32` in
      MP_TAC (ISPEC bs Q2_BS_SURJ) THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [d; z; zz; n] THEN
      DISCH_THEN(fun eth -> SUBST_ALL_TAC eth THEN ASSUME_TAC eth) in
  (MAP_EVERY abbrev [x; ra; rb; jq; jp] THEN bstac) (asl,w);;

(* ---- a call: instantiate VA1P_CALL_Fnn by matching its va1_st pattern --- *)
let Q2_CALLSITE_TAC (callth:thm) (dth:thm) (pc:int) (sname:string)
                    (mmname:string) : tactic = fun (asl,w) ->
  let s = rand w in
  let ths = map snd asl in
  let fs = rand(rand(rator(rator w))) in
  let mm = rhs(concl(find_read_th "wmem" s ths)) in
  let mc = rhs(concl(find_read_th "wcode" s ths)) in
  let gl = rhs(concl(find_read_th "wglobals" s ths)) in
  let stfact = concl(find (fun th -> let c = concl th in
                 q2_is_head "va1_st" c && rand c = mm) ths) in
  let vars,body = strip_forall(concl callth) in
  let ens = rand body in
  let _,[_;pp;_;_] = strip_comb ens in
  let pst = find_term (q2_is_head "va1_st") (snd(dest_abs pp)) in
  let _,theta,_ = term_match [] (rator pst) (rator stfact) in
  let subv () =
    let stk = rhs(concl(find_read_th "wstack" s ths)) in
    rand(rand(rand(rator stk))) in
  let inst v =
    try rev_assoc v theta with Failure _ ->
    match fst(dest_var v) with
      "fs" -> fs | "mc" -> mc | "cp" -> mk_small_numeral pc | "gl" -> gl
    | "sub" -> subv () | _ -> v in
  let th = CONV_RULE(DEPTH_CONV NUM_ADD_CONV) (SPECL (map inst vars) callth) in
  let sv = mk_var(sname,`:wasmstate`) in
  let mmv = mk_var(mmname,`:int64->byte`) in
  (MP_TAC th THEN ANTS_TAC THENL
    [Q2_DBG "call antecedent"
      (ASM_REWRITE_TAC[dth] THEN CONV_TAC NUM_REDUCE_CONV THEN
       ASM_REWRITE_TAC[] THEN NO_TAC); ALL_TAC] THEN
   MATCH_MP_TAC WASMC_BIGSTEP_LEMMA THEN CONJ_TAC THENL
    [Q2_DBG "call precondition"
      (BETA_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC);
     BETA_TAC THEN X_GEN_TAC sv THEN
     REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
     GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [MAYCHANGE; SEQ_ID] THEN
     GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [GSYM SEQ_ASSOC] THEN
     GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_SEQ] THEN
     GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_THM] THEN
     REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
     ASSUMPTION_STATE_UPDATE_TAC THEN MAYCHANGE_STATE_UPDATE_TAC THEN
     DISCH_THEN(K ALL_TAC) THEN CAP_DISCARD_OLD_TAC sname THEN
     Q2_MEMNAME_TAC mmname THEN Q2_ABBREV_TAC mmv]) (asl,w);;

(* ---- run: ordinary steps and call sites until WDone or a stop pc --------- *)
let rec Q2_RUN_TAC execth (calls:(int*thm)list) (stops:int list) : tactic =
  fun (asl,w) ->
  let s = rand w in
  let ths = map snd asl in
  let is_done = exists (fun th ->
    concl th = mk_eq(mk_comb(`read wstatus`,s),`WDone`)) ths in
  if is_done then ALL_TAC (asl,w) else
  let pc = dest_small_numeral(rand(rhs(concl(find_read_th "wpc" s ths)))) in
  if mem pc stops then ALL_TAC (asl,w) else
  let n = fst(dest_var s) in
  let k = int_of_string(String.sub n 1 (String.length n - 1)) + 1 in
  let sname = "s"^string_of_int k in
  let dth = match (try (snd execth).(pc) with _ -> None) with
      Some th -> th
    | None -> failwith ("Q2_RUN_TAC: no decode at pc "^string_of_int pc) in
  let i = fst(dest_pair(rand(rhs(concl dth)))) in
  let step =
    if is_comb i && is_const(rator i) && fst(dest_const(rator i)) = "Wcall" then
      Q2_CALLSITE_TAC (assoc (dest_small_numeral(rand i)) calls) dth pc sname
        ("mm"^string_of_int k)
    else Q2_MSTEP_TAC execth sname in
  (step THEN Q2_RUN_TAC execth calls stops) (asl,w);;

let Q2_CALLS =
  [15,VA1P_CALL_F15; 21,VA1P_CALL_F21; 23,VA1P_CALL_F23; 17,VA1P_CALL_F17;
   19,VA1P_CALL_F19; 11,VA1P_CALL_F11; 13,VA1P_CALL_F13; 9,VA1P_CALL_F9;
   27,VA1P_CALL_F27];;

(* ---- the end: the abbreviated tuple is va1_pop_fwd on the literal tuple --- *)
(* abbreviation hypotheses: c = v with v a q2v variable                       *)
let q2_is_abbrev th =
  let c = concl th in
  is_eq c && (let r = rhs c in
    (is_var r && String.length (fst(dest_var r)) > 3 &&
     String.sub (fst(dest_var r)) 0 3 = "q2v") ||
    (is_pair r && is_var (fst(dest_pair r)) &&
     String.sub (fst(dest_var (fst(dest_pair r)))) 0 3 = "q2v"));;

let Q2_FINAL_TAC : tactic = fun (asl,w) ->
  let ths = map snd asl in
  let abs = filter q2_is_abbrev ths in
  let vabs = filter (fun th -> is_var(rhs(concl th))) abs
  and tabs = filter (fun th -> not (is_var(rhs(concl th)))) abs in
  (REWRITE_TAC(map SYM tabs) THEN
   REPEAT(CHANGED_TAC(REWRITE_TAC(map SYM vabs))) THEN
   REWRITE_TAC[va1_pop_fwd; LET_DEF; LET_END_DEF; Q2_KD4; ve_kd_fwd;
               ve_fredkin_fwd; FST; SND; PAIR_EQ] THEN
   CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC[FST; SND; PAIR_EQ]) (asl,w);;

let VA1_TICK_FORWARD_POP_COND = prove
 (parse_term pop_spec_VA1_TICK_FORWARD_POP_COND,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP VA1_WINDOW_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP VA1_LOG_OK_DROP) THEN
  ENSURES_INIT_TAC "s0" THEN Q2_MEMNAME_TAC "mm0" THEN
  Q2_RUN_TAC VA1_TICK_FORWARD_EXEC Q2_CALLS [] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `L:(num->int32)list` THEN ASM_REWRITE_TAC[] THEN
  W(fun (asl,w) ->
    let th = find (fun th -> let c = concl th in
               q2_is_head "va1_st" c && rand c = rand w) (map snd asl) in
    let ps = el 8 (snd(strip_comb(concl th))) in
    let lhs = el 8 (snd(strip_comb w)) in
    SUBGOAL_THEN (mk_eq(lhs,ps)) SUBST1_TAC THENL
     [Q2_FINAL_TAC; ACCEPT_TAC th]));;
