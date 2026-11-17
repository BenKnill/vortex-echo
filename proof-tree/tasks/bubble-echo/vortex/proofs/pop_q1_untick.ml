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
(* Vortex pop, segment Q1 (SEGMENT PROVER Q1, Claude Opus 5.5, 2026-11-11):  *)
(* rung R2, VA1_TICK_POP_INVERSE_COND (frozen string pop_spec_* of          *)
(* pop_design_stmts.ml 97f899dc; spec pop_design_r2_untick.spec 45d9cd9c).  *)
(*                                                                           *)
(* tick_backward (f36) of vortex_a1.wasm on a pop tick, through the Q0     *)
(* call-site lemmas VA1P_CALL_F10 .. F28 (leaf contracts as premises).      *)
(* Path (T1 = t+1 in memory, window: T1 <> 0, P <> -1, T1 <> P, T1 >u P):  *)
(* pc 19 br_if (T1 = 0) not taken, pc 35 (P = -1) not taken, pc 42         *)
(* (T1 <> P) taken to pc 131: call 28 (tick_dec), call 10 (vort_un), pc 150 *)
(* (T1 >u P) taken to pc 246: call 14 (unbirth) + drop, call 12 (drop_un), *)
(* 4 x [call 20 (corr undrift), call 18 (corr unkick, sub 3..0)], call 24   *)
(* (jig undrift), call 22 (jig unkick), call 16 (rim_un); local 0 := 1 at   *)
(* pc 293; return local 0.                                                   *)
(* VA1Q1_TICK_BACKWARD_POP: the run from any explicit pop state, post =    *)
(* the backward composite. The frozen goal follows by pre/post weakening   *)
(* and the inverse lemmas (H1 + ve_generic). No definitions in this file.  *)
(* ========================================================================= *)

(* ---- header facts carried by va1_st ---------------------------------- *)

let VA1Q1_ST_HDR = prove
 (`!ps t p ap mdl N x hp tbl m.
     va1_st t p ap mdl N x hp tbl ps m
     ==> read (bytes32 (word 16392)) m = t /\ read (bytes32 (word 16396)) m = p /\
         read (bytes32 (word 16512)) m = ap`,
  REWRITE_TAC[FORALL_PAIR_THM; va1_st; va1_tick; va1_pop] THEN MESON_TAC[]);;

let VA1Q1_TUPLE4 = prove
 (`!q:A#B#C#D. q = (FST q,FST(SND q),FST(SND(SND q)),SND(SND(SND q)))`,
  REWRITE_TAC[PAIR]);;

let VA1Q1_DEC_INC = WORD_RULE `!t:int32. word_sub (word_add t (word 1)) (word 1) = t`;;

let va1q1_head tm = try fst(dest_const(fst(strip_comb tm))) with Failure _ -> "";;

(* name the memory; on the first memory also extract the header facts *)
let VA1Q1_MEMNAME_TAC (hdr:bool) (mmname:string) : tactic = fun (asl,w) ->
  let s = rand w in
  let mmv = mk_var(mmname,`:int64->byte`) in
  (ABBREV_TAC (mk_eq(mmv, mk_comb(`read wmem`, s))) THEN
   POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
   (fun (asl,w) ->
      if not hdr then ALL_TAC (asl,w) else
      let hs = filter (fun th -> let c = concl th in
                 va1q1_head c = "va1_st" && rand c = mmv) (map snd asl) in
      MAP_EVERY (fun th -> STRIP_ASSUME_TAC(MATCH_MP VA1Q1_ST_HDR th)) hs (asl,w)))
  (asl,w);;

(* after a call: T restored form, births state as an explicit 4-tuple *)
let VA1Q1_NORM_TAC (mm:term) : tactic = fun (asl,w) ->
  let ths = filter (fun th -> let c = concl th in
              va1q1_head c = "va1_st" && rand c = mm) (map snd asl) in
  match ths with
    [th] ->
      let th1 = REWRITE_RULE[VA1Q1_DEC_INC] th in
      let ps = rand(rator(concl th1)) in
      let bs = snd(dest_pair(snd(dest_pair(snd(dest_pair(snd(dest_pair ps))))))) in
      let split = not (is_pair bs && is_pair(snd(dest_pair bs)) &&
                       is_pair(snd(dest_pair(snd(dest_pair bs))))) in
      let th2 = if split then PURE_ONCE_REWRITE_RULE[ISPEC bs VA1Q1_TUPLE4] th1 else th1 in
      (* the births state as four fresh variables (REWRITE's basic PAIR rule *)
      (* would fold an FST/SND tuple back, so the projections are abbreviated) *)
      let abbrevs =
        if not split then ALL_TAC else
        let r = rand(concl(ISPEC bs VA1Q1_TUPLE4)) in
        let c1,r1 = dest_pair r in let c2,r2 = dest_pair r1 in let c3,c4 = dest_pair r2 in
        MAP_EVERY (fun (n,c) -> ABBREV_TAC (mk_eq(mk_var(n,type_of c),c)))
          ["diU",c1; "zqU",c2; "zpU",c3; "ndU",c4] in
      if concl th2 = concl th then ALL_TAC (asl,w) else
      (UNDISCH_THEN (concl th) (K ALL_TAC) THEN ASSUME_TAC th2 THEN abbrevs) (asl,w)
  | _ -> ALL_TAC (asl,w);;

(* ---- a call site: instantiate VA1P_CALL_Fnn by matching its precondition *)
(* against the current facts (state predicate, stack, code, pc, globals)   *)

let VA1Q1_CALLSITE_TAC (callth:thm) (dth:thm) (sname:string) (mmname:string) : tactic =
  fun (asl,w) ->
  let s = rand w in
  let ths = map snd asl in
  let fs = rand(rand(rator(rator w))) in
  let mm = rhs(concl(find_read_th "wmem" s ths)) in
  let th0 = SPEC_ALL callth in
  let fsv = rand(rand(rator(rator(rator(rand(concl th0)))))) in
  let th0 = INST [fs,fsv] th0 in
  let ens = rand(concl th0) in
  let _,args = strip_comb ens in
  let pre = el 1 args in
  let sv,body = dest_abs pre in
  let body = subst [mm, mk_comb(`read wmem`,sv)] body in
  let body = subst [s, sv] body in
  let cjs = conjuncts body in
  let rec matchall th cjs =
    match cjs with
      [] -> th
    | c::rest ->
        let cands = mapfilter (fun a -> term_match [] c (concl a)) ths in
        (match cands with
           [] -> matchall th rest
         | i::_ ->
             let th' = INSTANTIATE i th in
             matchall th' (map (instantiate i) rest)) in
  let th1 = matchall th0 cjs in
  let th2 = CONV_RULE(DEPTH_CONV NUM_ADD_CONV) th1 in
  let sv' = mk_var(sname,`:wasmstate`) in
  (MP_TAC th2 THEN ANTS_TAC THENL
    [ASM_REWRITE_TAC[dth] THEN CONV_TAC NUM_REDUCE_CONV THEN NO_TAC; ALL_TAC] THEN
   MATCH_MP_TAC WASMC_BIGSTEP_LEMMA THEN CONJ_TAC THENL
    [BETA_TAC THEN ASM_REWRITE_TAC[] THEN FAIL_TAC "call-site precondition residual";
     BETA_TAC THEN X_GEN_TAC sv' THEN
     REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
     GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [MAYCHANGE; SEQ_ID] THEN
     GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [GSYM SEQ_ASSOC] THEN
     GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_SEQ] THEN
     GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_THM] THEN
     REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
     ASSUMPTION_STATE_UPDATE_TAC THEN MAYCHANGE_STATE_UPDATE_TAC THEN
     DISCH_THEN(K ALL_TAC) THEN CAP_DISCARD_OLD_TAC sname THEN
     VA1Q1_MEMNAME_TAC false mmname THEN
     VA1Q1_NORM_TAC (mk_var(mmname,`:int64->byte`))]) (asl,w);;

(* ---- run: ordinary steps and call sites until WDone or a stop pc -------- *)

let rec VA1Q1_RUN_TAC execth (calls:(int*thm)list) (stops:int list) : tactic =
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
    | None -> failwith ("VA1Q1_RUN_TAC: no decode at pc "^string_of_int pc) in
  let i = fst(dest_pair(rand(rhs(concl dth)))) in
  let step =
    if is_comb i && is_const(rator i) && fst(dest_const(rator i)) = "Wcall" then
      VA1Q1_CALLSITE_TAC (assoc (dest_small_numeral(rand i)) calls) dth sname
        ("mm"^string_of_int k)
    else CAPC_MSTEP_TAC execth sname in
  (step THEN VA1Q1_RUN_TAC execth calls stops) (asl,w);;

let VA1Q1_CALLS =
  [10,VA1P_CALL_F10; 12,VA1P_CALL_F12; 14,VA1P_CALL_F14; 16,VA1P_CALL_F16;
   18,VA1P_CALL_F18; 20,VA1P_CALL_F20; 22,VA1P_CALL_F22; 24,VA1P_CALL_F24;
   28,VA1P_CALL_F28];;

(* ---- the backward pop run from any explicit state ----------------------- *)

let va1q1_gen_tm = `!(CK:(num->int32)->(num->int32)->(num->int32)->int32->int32->num->(num->int32)->(num->int32)->num->int32)
  (JK:(num->int32)->(num->int32)->(num->int32)->int32->int32->(num->int32)->(num->int32)->num->int32)
  fs gl t p ap mdl N y hp tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32)
  (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32).
     va1_rim_ok /\ va1_cdrift_ok /\ va1_jdrift_ok /\ va1_drop_ok /\ va1_unbirth_ok /\
     va1_corrk_ok CK /\ va1_jigk_ok JK /\
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
     fs 10 = (va1_f10_mc,0,0) /\ fs 12 = (va1_f12_mc,0,0) /\ fs 14 = (va1_f14_mc,0,1) /\
     fs 16 = (va1_f16_mc,0,0) /\ fs 18 = (va1_f18_mc,1,0) /\ fs 20 = (va1_f20_mc,0,0) /\
     fs 22 = (va1_f22_mc,0,0) /\ fs 24 = (va1_f24_mc,0,0) /\ fs 28 = (va1_f28_mc,0,0) /\
     va1_pop_window t p /\ val nd <= 16384
     ==> ensures (wasmc fs)
          (\s. read wcode s = va1_tick_backward_mc /\ read wpc s = word 3 /\
             read wstatus s = WRunning /\ read wstack s = [] /\
             read wlabels s = [] /\ read warity s = 1 /\
             read wmemsize s = 4194304 /\ read wglobals s = gl /\
             va1_st (word_add t (word 1)) p ap mdl N y hp tbl
                    (ra,rb,jq,jp,di,zq,zp,nd) (read wmem s))
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 1)] /\
             va1_st t p ap mdl N (ve_fredkin_bwd (ve_vk mdl) y) hp tbl
               (FST (ve_fredkin_bwd (va1_rimd tbl) (ra,rb)),
                SND (ve_fredkin_bwd (va1_rimd tbl) (ra,rb)),
                FST (ve_kd_bwd (JK mdl hp tbl t p rb) (va1_jdrift mdl) (jq,jp)),
                SND (ve_kd_bwd (JK mdl hp tbl t p rb) (va1_jdrift mdl) (jq,jp)),
                va1_drop_bwd (SND(SND(SND(va1_unb (word_add t (word 1)) (val nd) (di,zq,zp,nd)))))
                             (FST(va1_unb (word_add t (word 1)) (val nd) (di,zq,zp,nd))),
                FST (ve_kd_bwdn (\i. CK mdl hp tbl t p i rb) (\i. va1_cdrift rb) 4
                       (FST(SND(va1_unb (word_add t (word 1)) (val nd) (di,zq,zp,nd))),
                        FST(SND(SND(va1_unb (word_add t (word 1)) (val nd) (di,zq,zp,nd)))))),
                SND (ve_kd_bwdn (\i. CK mdl hp tbl t p i rb) (\i. va1_cdrift rb) 4
                       (FST(SND(va1_unb (word_add t (word 1)) (val nd) (di,zq,zp,nd))),
                        FST(SND(SND(va1_unb (word_add t (word 1)) (val nd) (di,zq,zp,nd)))))),
                SND(SND(SND(va1_unb (word_add t (word 1)) (val nd) (di,zq,zp,nd)))))
               (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
           MAYCHANGE [wstatus] ,, MAYCHANGE [wlocal 0; wlocal 1] ,,
           MAYCHANGE [wmem :> bytes(word 16392,4)] ,, MAYCHANGE [wmem :> bytes(word 16400,4)] ,,
           MAYCHANGE [wmem :> bytes(word 1114112,851968)] ,,
           MAYCHANGE [wmem :> bytes(word 1966080,73728)])`;;

(* ve_kd_bwdn on a numeral: unrolled *)
let rec VA1Q1_KDN_CONV tm =
  match tm with
    Comb(Comb(Comb(Comb(Const("ve_kd_bwdn",_),k),d),n),x) when is_numeral n ->
      if dest_small_numeral n = 0 then
        GEN_REWRITE_CONV I [CONJUNCT1 VA1P_KD_BWDN_CLAUSES] tm
      else
        (RATOR_CONV(RAND_CONV num_CONV) THENC
         GEN_REWRITE_CONV I [CONJUNCT2 VA1P_KD_BWDN_CLAUSES] THENC
         ONCE_DEPTH_CONV VA1Q1_KDN_CONV) tm
  | _ -> failwith "VA1Q1_KDN_CONV";;

(* the final state fact (run form) implies the stated post (composite form) *)
let VA1Q1_CLOSE_TAC : tactic = fun (asl,w) ->
  let mm = rand w in
  let th = find (fun th -> let c = concl th in
             va1q1_head c = "va1_st" && rand c = mm) (map snd asl) in
  (MP_TAC th THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   CONV_TAC(ONCE_DEPTH_CONV VA1Q1_KDN_CONV) THEN
   REWRITE_TAC[ve_kd_bwd; LET_DEF; LET_END_DEF] THEN
   CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND] THEN
   CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[]) (asl,w);;

let VA1Q1_TICK_BACKWARD_POP = prove
 (va1q1_gen_tm,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP VA1_WINDOW_FACTS) THEN
  ENSURES_INIT_TAC "s0" THEN VA1Q1_MEMNAME_TAC true "mm0" THEN
  VA1Q1_RUN_TAC VA1_TICK_BACKWARD_EXEC VA1Q1_CALLS [] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  VA1Q1_CLOSE_TAC);;

(* ---- the frozen R2 goal: the forward pop model image, then the inverses -- *)

let VA1Q1_TUPLE8 = prove
 (`!q:A#B#C#D#E#F#G#H.
     q = (FST q,FST(SND q),FST(SND(SND q)),FST(SND(SND(SND q))),
          FST(SND(SND(SND(SND q)))),FST(SND(SND(SND(SND(SND q))))),
          FST(SND(SND(SND(SND(SND(SND q)))))),SND(SND(SND(SND(SND(SND(SND q)))))))`,
  REWRITE_TAC[PAIR]);;

let VA1Q1_VAL_ADD = prove
 (`!(nd:int32) n. val nd + n <= 16384 ==> val (word_add nd (word n):int32) = val nd + n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `n MOD 4294967296 = n` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let VA1_TICK_POP_INVERSE_COND = prove(parse_term pop_spec_VA1_TICK_POP_INVERSE_COND,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP VA1_WINDOW_FACTS) THEN
  SUBGOAL_THEN `val (word_add nd (word (LENGTH (L:(num->int32)list))):int32) = val nd + LENGTH L`
    ASSUME_TAC THENL [MATCH_MP_TAC VA1Q1_VAL_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!zq' zp'. va1_unb (word_add t (word 1)) (val nd + LENGTH L)
                (va1_push L (va1_drop_fwd nd di,zq',zp',nd)) =
              (va1_drop_fwd nd di,zq',zp',nd)`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC VA1_PUSH_UNB_INVERSE THEN
    ASM_SIMP_TAC[VA1_LOG_OK_DROP]; ALL_TAC] THEN
  W(fun (asl,w) ->
     let _,[_;pre;_;_] = strip_comb w in
     let st = last(conjuncts(snd(dest_abs pre))) in
     let _,stargs = strip_comb st in
     let y = el 5 stargs and pf = el 8 stargs in
     let rec tl t = if is_pair t then let a,b = dest_pair t in a::tl b else [t] in
     let projs = tl(rand(concl(ISPEC pf VA1Q1_TUPLE8))) in
     let fv = frees w @ freesl(map (concl o snd) asl) in
     let gv n = find (fun v -> fst(dest_var v) = n) fv in
     let inst = map gv ["CK";"JK";"fs";"gl";"t";"p";"ap";"mdl";"N"] @ [y] @
                map gv ["hp";"tbl"] @ projs in
     MP_TAC(SPECL inst VA1Q1_TICK_BACKWARD_POP)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[va1_pop_fwd; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND; VA1_PUSH_ND] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    let _,[_;p0;q0;_] = strip_comb(concl th) in
    MATCH_MP_TAC ENSURES_PREPOSTCONDITION_THM THEN
    MAP_EVERY EXISTS_TAC [p0;q0] THEN
    CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL [ALL_TAC; ACCEPT_TAC th]]) THENL
   [(* precondition: the projections of the model image fold back *)
    GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[PAIR];
    (* postcondition: every backward leaf undoes its forward partner *)
    GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> va1q1_head(concl th) = "va1_st")) THEN
    REWRITE_TAC[FREDKIN_STEP_INVERSE] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[va1_pop_fwd; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[FST; SND; PAIR] THEN
    ASM_REWRITE_TAC[VA1_PUSH_ND; FST; SND; PAIR; VA1_DROP_INVERSE;
                    FREDKIN_STEP_INVERSE; KICK_DRIFT_INVERSE; KICK_DRIFT_STEPS_INVERSE]]);;
