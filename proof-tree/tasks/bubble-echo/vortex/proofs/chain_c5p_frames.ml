(* Vortex chain rung C5' (lane vortex-chain-20261111-142342 c5p, Claude Opus 5.5, 2026-11-13): the G1 shim.        *)
(* Makes hol-hearth main's explicit-frame call model (wasmf, wasmn, wfsum, the wasmc -> wasmn transfer H2, the      *)
(* global-restore rule G3 and the H4/H5 tactics) available on the vortex chain WITHOUT a Hearth change and WITHOUT *)
(* replacing the vortex prefix copy of wasm_call.ml (091a9057), which would re-key the whole chain.                *)
(* Content, in order, all VERBATIM from hol-hearth main 6adb41ce as deployed on the shared runtime:                *)
(*   (1) wasm/proofs/wasm_call.ml (sha256 11d1dd37) lines 468-589: WASMC_MEM_UPDATE_TAC, WASMC_GEN_STATE_TAC,      *)
(*       WASMC_CALL0_SITE_TAC (OCaml tactics only: no constant, no theorem). Main's lines 1-467 define exactly the *)
(*       same constants and theorems as the vortex copy (lines 1-423 identical; 424-467 differ only in two tactics *)
(*       that add WASM_COMPACT_HYPS_TAC, which this shim does not redefine).                                         *)
(*   (2) wasm/proofs/wasm_frames.ml (sha256 25eb21a4) lines 113-1327 (everything after its two needs lines).       *)
(* Every theorem below is proved by the kernel when this file loads; the file adds no axiom.                        *)
needs "wasm/proofs/wasm_tactics.ml";;
needs "wasm_call.ml";;

(* ======== (1) main wasm_call.ml lines 468-589 ======== *)

(* ------------------------------------------------------------------------- *)
(* A call site as a caller-level ensures lemma (0 params). Goal shape, after *)
(* the lemma's hypotheses are stripped into the assumptions:                 *)
(*   ensures (wasmc fs) (\s. read wcode s = mc /\ read wpc s = word p /\ .. ) *)
(*                      (\s. .. read wpc s = word (p + n) ..) (frame)        *)
(* with fs f = (code,0,0), p < 2 EXP 64 and wasm_decode mc p = SOME          *)
(* (Wcall f,n) among the assumptions and read wmemsize / read wglobals facts *)
(* in the precondition. lth = |- ensures wasm P Q C (the callee leaf,        *)
(* instantiated), cth = WASM_CALLEE_RULE code_def. The callee's MAYCHANGE    *)
(* frame is expanded into a write chain; the caller's next state is          *)
(* write wpc .. (write (wmem :> d) .. s0), so the caller-level MAYCHANGE      *)
(* is accounted as for a step. close_tac finishes the postcondition, given   *)
(* the callee's postcondition facts (memory as `read (..) mmK`) and the      *)
(* memory names mm0 (caller entry) and the new memory equation.              *)
(* ------------------------------------------------------------------------- *)

let WASMC_MEM_UPDATE_TAC (asl,w) =
  let uth_tm = lhand w in
  let s = repeat rand (lhand uth_tm) in
  let ws = `:wasmstate` in
  let rec writes_wmem tm =
    match tm with
      Comb(Comb(Comb(Const("write",_),c),_),t) ->
        (match c with
           Comb(Comb(Const(":>",_),Const("wmem",_)),_) -> true
         | _ -> writes_wmem t)
    | _ -> false in
  if not (writes_wmem (lhand uth_tm)) then ALL_TAC (asl,w) else
  let rmem = mk_comb(`read wmem`,s) in
  let names = mapfilter (fun th -> let c = concl th in
      if is_eq c && lhs c = rmem &&
         not (can (find_term (fun t -> type_of t = ws)) (rhs c)) then th
      else fail()) (map snd asl) in
  if names = [] then ALL_TAC (asl,w) else
  (DISCH_THEN(fun uth ->
     let th0 = SYM(AP_TERM `read wmem` uth) in
     let th1 = CONV_RULE(RAND_CONV WMEM_READ_OVER_WRITES_CONV) th0 in
     let th2 = GEN_REWRITE_RULE (RAND_CONV o DEPTH_CONV) names th1 in
     MP_TAC uth THEN ASSUME_TAC th2)) (asl,w);;

let WASMC_GEN_STATE_TAC (s1:term) : tactic = fun (asl,w) ->
  let x = find_term (fun t -> can (term_match [] `write wpc (z:int64) (s:wasmstate)`) t) w in
  let gth = mk_forall(s1, mk_imp(mk_eq(x,s1), subst [s1,x] w)) in
  (SUBGOAL_THEN gth (fun th -> MATCH_MP_TAC th THEN REFL_TAC)) (asl,w);;

let WASMC_CALL0_SITE_TAC (lth:thm) (cth:thm) (f:term) (n:term)
                         (close_tac:tactic) : tactic =
  let _,[_;pp;qq;cc] = strip_comb(concl lth) in
  let eth,dth = CONJ_PAIR cth in
  let code = rand(lhand(concl eth)) and e = rand(rand(concl eth))
  and decls = rand(rand(concl dth)) in
  let c0tm = list_mk_comb(`wcall_entry`,
     [code; `0`; `0`; `read wstack (s0:wasmstate)`; e; decls; `s0:wasmstate`]) in
  let is_rmem_c1 th = let c = concl th in
     is_eq c && lhs c = `read wmem (c1:wasmstate)` in
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ABBREV_TAC `mm0 = read wmem (s0:wasmstate)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  (fun (asl,w) ->
     let fs = rand(rand(rator(rator w))) in
     MATCH_MP_TAC (ISPECL [fs; f; code; `0`; e; decls; pp; qq; cc; n]
                     WASMC_CALL0_STEP) (asl,w)) THEN
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
   [CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[WCALL_ENTRY_READS; READ_COMPONENT_COMPOSE] THEN
    ASM_SIMP_TAC[PAIR];
    ALL_TAC] THEN
  X_GEN_TAC `c1:wasmstate` THEN
  ABBREV_TAC (mk_eq(`c0:wasmstate`, c0tm)) THEN
  SUBGOAL_THEN `read wmem (c0:wasmstate) = mm0 /\
                read wmemsize c0 = read wmemsize (s0:wasmstate) /\
                read wglobals c0 = read wglobals (s0:wasmstate)`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c0" THEN ASM_REWRITE_TAC[WCALL_ENTRY_READS]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (STRIP_ASSUME_TAC o CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) MP_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [MAYCHANGE; SEQ_ID] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [GSYM SEQ_ASSOC] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_SEQ] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
  WASMC_MEM_UPDATE_TAC THEN ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC) THEN
  (fun (asl,w) ->
     let p = rand(rhs(concl(find_read_th "wpc" `s0:wasmstate` (map snd asl)))) in
     let gth = mk_eq(list_mk_comb(`wcall_return`,
                 [mk_binop `(+):num->num->num` `val (read wpc (s0:wasmstate))` n; `0`;
                  `c1:wasmstate`; `s0:wasmstate`]),
               list_mk_comb(`write wpc`,
                 [mk_comb(`word:num->int64`, mk_binop `(+):num->num->num` p n);
                  `write wmem (read wmem c1) (s0:wasmstate)`])) in
     (SUBGOAL_THEN gth SUBST1_TAC THENL
      [SUBGOAL_THEN (mk_eq(`val (read wpc (s0:wasmstate))`, p)) SUBST1_TAC THENL
        [ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN
       MATCH_MP_TAC WCALL_RETURN0 THEN ASM_REWRITE_TAC[];
       ALL_TAC]) (asl,w)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  FIRST_X_ASSUM(fun th -> if is_rmem_c1 th
    then REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if concl th = `read wmem (s0:wasmstate) = mm0`
    then REWRITE_TAC[SYM th] else NO_TAC) THEN
  REWRITE_TAC[WCALL_WRITE_MEM1; WCALL_WRITE_MEM2] THEN
  WASMC_GEN_STATE_TAC `s1:wasmstate` THEN
  X_GEN_TAC `s1:wasmstate` THEN
  WASMC_MEM_UPDATE_TAC THEN ASSUMPTION_STATE_UPDATE_TAC THEN MAYCHANGE_STATE_UPDATE_TAC THEN
  DISCH_THEN(fun th ->
    let thl = STATE_UPDATE_NEW_RULE th in
    if thl = [] then ALL_TAC else MP_TAC(end_itlist CONJ thl) THEN STRIP_TAC) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CONJ_TAC THENL [ALL_TAC; MONOTONE_MAYCHANGE_TAC] THEN
  close_tac;;

(* ======== (2) main wasm_frames.ml lines 113-1327 ======== *)

(* ------------------------------------------------------------------------- *)
(* The reference relation.                                                   *)
(* ------------------------------------------------------------------------- *)

let wasmf = new_definition
 `wasmf (fs:num->byte list#num#num)
        (x:wasmstate#(wasmstate#num#num)list)
        (y:wasmstate#(wasmstate#num#num)list) <=>
    (wasm (FST x) (FST y) /\ SND y = SND x) \/
    (read wstatus (FST x) = WRunning /\
     ?f n code np nr e decls.
       wasm_decode (read wcode (FST x)) (val (read wpc (FST x))) =
         SOME (Wcall f,n) /\
       fs f = (code,np,nr) /\ np <= LENGTH (read wstack (FST x)) /\
       wasm_entry code = SOME e /\ wasm_decl_vals code = SOME decls /\
       FST y = wcall_entry code np nr (read wstack (FST x)) e decls (FST x) /\
       SND y = CONS (FST x,val (read wpc (FST x)) + n,np) (SND x)) \/
    (~(read wstatus (FST x) = WRunning) /\
     ?c npc np k. SND x = CONS (c,npc,np) k /\
                  FST y = wcall_return npc np (FST x) c /\ SND y = k)`;;

(* ------------------------------------------------------------------------- *)
(* The three cases of a wasmf step.                                          *)
(* ------------------------------------------------------------------------- *)

(* a body that can take a wasm step: wasmf is that step, frames unchanged *)
let WASMF_WASM_STEP = prove
 (`!fs s k t k' u.
     wasm s u ==> (wasmf fs (s,k) (t,k') <=> wasm s t /\ k' = k)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[wasmf; FST; SND] THEN
  SUBGOAL_THEN `read wstatus s = WRunning` ASSUME_TAC THENL
   [ASM_MESON_TAC[WASM_FINAL]; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC(TAUT `~q ==> (p \/ q <=> p)`) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[WASM_WCALL_NO_STEP]);;

(* a body at `call f`: wasmf enters the callee and pushes the frame *)
let WASMF_CALL_STEP = prove
 (`!fs s k t k' f n.
     read wstatus s = WRunning /\
     wasm_decode (read wcode s) (val (read wpc s)) = SOME (Wcall f,n)
     ==> (wasmf fs (s,k) (t,k') <=>
          ?code np nr e decls.
            fs f = (code,np,nr) /\ np <= LENGTH (read wstack s) /\
            wasm_entry code = SOME e /\ wasm_decl_vals code = SOME decls /\
            t = wcall_entry code np nr (read wstack s) e decls s /\
            k' = CONS (s,val (read wpc s) + n,np) k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[wasmf; FST; SND] THEN
  ASM_REWRITE_TAC[option_INJ; PAIR_EQ; WCALL_INJ] THEN
  MP_TAC(SPECL [`s:wasmstate`; `t:wasmstate`; `f:num`; `n:num`]
    WASM_WCALL_NO_STEP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[]);;

(* a finished body with a frame above it: pop and resume the caller *)
let WASMF_RETURN_STEP = prove
 (`!fs s c npc np k t k'.
     ~(read wstatus s = WRunning)
     ==> (wasmf fs (s,CONS (c,npc,np) k) (t,k') <=>
          t = wcall_return npc np s c /\ k' = k)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[wasmf; FST; SND] THEN
  ASM_SIMP_TAC[WASM_FINAL; CONS_11; PAIR_EQ] THEN MESON_TAC[]);;

(* a finished body with no frame: final *)
let WASMF_FINAL = prove
 (`!fs s y. ~(read wstatus s = WRunning) ==> ~(wasmf fs (s,[]) y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[wasmf; FST; SND] THEN
  ASM_SIMP_TAC[WASM_FINAL; NOT_CONS_NIL; GSYM NOT_CONS_NIL]);;

(* ------------------------------------------------------------------------- *)
(* Determinism.                                                              *)
(* ------------------------------------------------------------------------- *)

let WASMF_DET = prove
 (`!fs x y z. wasmf fs x y /\ wasmf fs x z ==> y = z`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC [`s:wasmstate`; `k:(wasmstate#num#num)list`;
    `s1:wasmstate`; `k1:(wasmstate#num#num)list`;
    `s2:wasmstate`; `k2:(wasmstate#num#num)list`] THEN
  ASM_CASES_TAC `read wstatus s = WRunning` THENL
   [ASM_CASES_TAC
     `?f n. wasm_decode (read wcode s) (val (read wpc s)) = SOME (Wcall f,n)`
    THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `f:num` (X_CHOOSE_TAC `n:num`)) THEN
      ASM_SIMP_TAC[WASMF_CALL_STEP] THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (X_CHOOSE_THEN `code1:byte list` (X_CHOOSE_THEN `np1:num`
         (X_CHOOSE_THEN `nr1:num` (X_CHOOSE_THEN `e1:num`
           (X_CHOOSE_THEN `decls1:wval list` STRIP_ASSUME_TAC)))))
       (X_CHOOSE_THEN `code2:byte list` (X_CHOOSE_THEN `np2:num`
         (X_CHOOSE_THEN `nr2:num` (X_CHOOSE_THEN `e2:num`
           (X_CHOOSE_THEN `decls2:wval list` STRIP_ASSUME_TAC)))))) THEN
      SUBGOAL_THEN `code2:byte list = code1 /\ np2:num = np1 /\ nr2:num = nr1`
        (REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC) THENL
       [UNDISCH_TAC `(fs:num->byte list#num#num) f = (code1,np1,nr1)` THEN
        ASM_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `e2:num = e1 /\ decls2:wval list = decls1`
        (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
       [ASM_MESON_TAC[option_INJ]; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[wasmf; FST; SND] THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[WASM_DETERMINISTIC];
    REWRITE_TAC[wasmf; FST; SND] THEN ASM_SIMP_TAC[WASM_FINAL] THEN
    REPEAT STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      let c = concl th in is_eq c && lhs c = `k:(wasmstate#num#num)list`))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[CONS_11; PAIR_EQ]) THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Frame stacks below a run do not matter (append at the bottom).           *)
(* ------------------------------------------------------------------------- *)

let WASMF_APPEND = prove
 (`!fs x y k. wasmf fs x y
              ==> wasmf fs (FST x,APPEND (SND x) k) (FST y,APPEND (SND y) k)`,
  REWRITE_TAC[FORALL_PAIR_THM; wasmf; FST; SND] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[APPEND] THEN ASM_MESON_TAC[]);;

let RTC_WASMF_APPEND = prove
 (`!fs x y. RTC (wasmf fs) x y
            ==> !k. RTC (wasmf fs) (FST x,APPEND (SND x) k)
                                   (FST y,APPEND (SND y) k)`,
  GEN_TAC THEN MATCH_MP_TAC RTC_INDUCT THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[WASMF_APPEND; RTC_INC];
    REWRITE_TAC[RTC_REFL];
    MESON_TAC[RTC_TRANS]]);;

(* ------------------------------------------------------------------------- *)
(* Generic facts about eventually.                                          *)
(* ------------------------------------------------------------------------- *)

let EVENTUALLY_NOW = prove
 (`!(step:A->A->bool) P s. P s ==> eventually step P s`,
  MESON_TAC[eventually_RULES]);;

(* along a deterministic relation, eventually propagates back along a run *)
let EVENTUALLY_RTC_DET = prove
 (`!(R:A->A->bool) P.
     (!x y z. R x y /\ R x z ==> y = z)
     ==> !x y. RTC R x y ==> eventually R P y ==> eventually R P x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC RTC_INDUCT_R THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[eventually_CASES] THEN DISJ2_TAC THEN
  ASM_MESON_TAC[]);;

(* no eventually from a state with an infinite run avoiding P *)
let NOT_EVENTUALLY_INVARIANT = prove
 (`!(R:A->A->bool) P Inv.
     (!x. Inv x ==> ~P x /\ ?y. R x y /\ Inv y)
     ==> !x. Inv x ==> ~eventually R P x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!x:A. eventually R P x ==> ~Inv x`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC eventually_INDUCT THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Lifting: a call-free leaf theorem holds under wasmf, any frames below.   *)
(* ------------------------------------------------------------------------- *)

let WASMF_LIFT_EVENTUALLY = prove
 (`!fs (Q:wasmstate->bool) k s.
     eventually wasm Q s
     ==> eventually (wasmf fs) (\x. Q (FST x) /\ SND x = k) (s,k)`,
  REPEAT GEN_TAC THEN SPEC_TAC(`s:wasmstate`,`s:wasmstate`) THEN
  MATCH_MP_TAC eventually_INDUCT THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC EVENTUALLY_NOW THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  X_GEN_TAC `s:wasmstate` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:wasmstate`) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[eventually_CASES] THEN DISJ2_TAC THEN
  REWRITE_TAC[FORALL_PAIR_THM; EXISTS_PAIR_THM] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WASMF_WASM_STEP th]) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

let WASMF_LIFT = prove
 (`!fs (P:wasmstate->bool) Q C.
     ensures wasm P Q C
     ==> !k. ensures (wasmf fs) (\x. P (FST x) /\ SND x = k)
                                (\x. Q (FST x) /\ SND x = k)
                                (\x y. C (FST x) (FST y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures; FORALL_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC
   [`k:(wasmstate#num#num)list`; `s:wasmstate`; `k0:(wasmstate#num#num)list`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:wasmstate`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`fs:num->byte list#num#num`;
    `\s'. (Q:wasmstate->bool) s' /\ C (s:wasmstate) s'`;
    `k0:(wasmstate#num#num)list`; `s:wasmstate`] WASMF_LIFT_EVENTUALLY) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_MONO) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Callee summaries and the derived big-step relation wasmn.                *)
(* ------------------------------------------------------------------------- *)

(* a callee summary: from an empty frame stack (callees push their own)    *)
let wfsum = new_definition
 `wfsum (fs:num->byte list#num#num) (P:wasmstate->bool) Q C <=>
    ensures (wasmf fs) (\x. P (FST x) /\ SND x = [])
                       (\x. Q (FST x) /\ SND x = [])
                       (\x y. C (FST x) (FST y))`;;

let wasm_calln = new_definition
 `wasm_calln (fs:num->byte list#num#num) f npc (s:wasmstate) (s':wasmstate) <=>
    ?code np nr e decls c1.
      fs f = (code,np,nr) /\ np <= LENGTH (read wstack s) /\
      wasm_entry code = SOME e /\ wasm_decl_vals code = SOME decls /\
      RTC (wasmf fs) (wcall_entry code np nr (read wstack s) e decls s,[])
                     (c1,[]) /\
      ~(read wstatus c1 = WRunning) /\
      s' = wcall_return npc np c1 s`;;

let wasmn = new_definition
 `wasmn (fs:num->byte list#num#num) s s' <=>
    wasm s s' \/
    read wstatus s = WRunning /\
    ?f n. wasm_decode (read wcode s) (val (read wpc s)) = SOME (Wcall f,n) /\
          wasm_calln fs f (val (read wpc s) + n) s s'`;;

let WASMN_CALL = prove
 (`!fs f n s s'.
     read wstatus s = WRunning /\
     wasm_decode (read wcode s) (val (read wpc s)) = SOME (Wcall f,n)
     ==> (wasmn fs s s' <=> wasm_calln fs f (val (read wpc s) + n) s s')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wasmn] THEN
  MP_TAC(SPECL [`s:wasmstate`; `s':wasmstate`; `f:num`; `n:num`]
    WASM_WCALL_NO_STEP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[option_INJ; PAIR_EQ; WCALL_INJ] THEN MESON_TAC[]);;

let WASMN_NONCALL = prove
 (`!fs s s' mc pc i n.
     read wcode s = mc /\ read wpc s = word pc /\ pc < 2 EXP 64 /\
     wasm_decode mc pc = SOME (i,n) /\ (!f. ~(i = Wcall f))
     ==> (wasmn fs s s' <=> wasm s s')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wasmn] THEN
  ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT; option_INJ; PAIR_EQ] THEN
  ASM_MESON_TAC[]);;

let WASMN_FINAL = prove
 (`!fs s s'. ~(read wstatus s = WRunning) ==> ~(wasmn fs s s')`,
  SIMP_TAC[wasmn; WASM_FINAL]);;

let WASMN_WASM = prove
 (`!fs s s'. wasm s s' ==> wasmn fs s s'`,
  SIMP_TAC[wasmn]);;

(* ------------------------------------------------------------------------- *)
(* Transfer: wasmn theorems hold under the reference wasmf.                 *)
(* ------------------------------------------------------------------------- *)

let WASMN_TO_WASMF_EVENTUALLY = prove
 (`!fs (R:wasmstate->bool) s.
     eventually (wasmn fs) R s
     ==> !k. eventually (wasmf fs) (\x. R (FST x) /\ SND x = k) (s,k)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC eventually_INDUCT THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC EVENTUALLY_NOW THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  X_GEN_TAC `s:wasmstate` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `s':wasmstate`) (LABEL_TAC "ih")) THEN
  X_GEN_TAC `k:(wasmstate#num#num)list` THEN
  ASM_CASES_TAC `?u. wasm s u` THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `u:wasmstate`) THEN
    ONCE_REWRITE_TAC[eventually_CASES] THEN DISJ2_TAC THEN
    REWRITE_TAC[FORALL_PAIR_THM; EXISTS_PAIR_THM] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WASMF_WASM_STEP th]) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[WASMN_WASM];
    ALL_TAC] THEN
  (* the step from s is a call *)
  SUBGOAL_THEN
   `read wstatus s = WRunning /\
    ?f n. wasm_decode (read wcode s) (val (read wpc s)) = SOME (Wcall f,n) /\
          wasm_calln fs f (val (read wpc s) + n) s s'`
    MP_TAC THENL [ASM_MESON_TAC[wasmn]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `f:num` (X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wasm_calln] o check (fun th ->
    can (term_match [] `wasm_calln a b c d e`) (concl th))) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`code:byte list`; `np:num`; `nr:num`; `e:num`;
                       `decls:wval list`; `c1:wasmstate`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`s':wasmstate`]) THEN
  ANTS_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(MP_TAC o SPEC `k:(wasmstate#num#num)list`)] THEN
  MATCH_MP_TAC(MATCH_MP (ISPEC `wasmf fs` EVENTUALLY_RTC_DET)
                 (SPEC `fs:num->byte list#num#num` WASMF_DET)) THEN
  (* (s,k) -> (c0, frame::k) ->* (c1, frame::k) -> (s',k) *)
  MATCH_MP_TAC RTC_TRANS_R THEN
  EXISTS_TAC `(wcall_entry code np nr (read wstack s) e decls s,
               CONS (s,val (read wpc s) + n,np) (k:(wasmstate#num#num)list))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[WASMF_CALL_STEP] THEN
    MAP_EVERY EXISTS_TAC [`code:byte list`; `np:num`; `nr:num`; `e:num`;
                          `decls:wval list`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC RTC_TRANS_L THEN
  EXISTS_TAC `(c1:wasmstate,
               CONS (s,val (read wpc s) + n,np) (k:(wasmstate#num#num)list))` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC
      `CONS (s,val (read wpc s) + n,np) (k:(wasmstate#num#num)list)` o
      MATCH_MP RTC_WASMF_APPEND) THEN
    REWRITE_TAC[FST; SND; APPEND];
    ASM_SIMP_TAC[WASMF_RETURN_STEP]]);;

let WASMN_TO_WASMF = prove
 (`!fs (P:wasmstate->bool) Q C.
     ensures (wasmn fs) P Q C
     ==> !k. ensures (wasmf fs) (\x. P (FST x) /\ SND x = k)
                                (\x. Q (FST x) /\ SND x = k)
                                (\x y. C (FST x) (FST y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures; FORALL_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC
   [`k:(wasmstate#num#num)list`; `s:wasmstate`; `k0:(wasmstate#num#num)list`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `k0:(wasmstate#num#num)list = k`)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:wasmstate`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `k:(wasmstate#num#num)list` o
    MATCH_MP WASMN_TO_WASMF_EVENTUALLY) THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_MONO) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN ASM_MESON_TAC[]);;

let WASMN_TO_WFSUM = prove
 (`!fs (P:wasmstate->bool) Q C. ensures (wasmn fs) P Q C ==> wfsum fs P Q C`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `[]:(wasmstate#num#num)list` o
    MATCH_MP WASMN_TO_WASMF) THEN
  REWRITE_TAC[wfsum]);;

let WASM_TO_WFSUM = prove
 (`!fs (P:wasmstate->bool) Q C. ensures wasm P Q C ==> wfsum fs P Q C`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPECL [`fs:num->byte list#num#num`;
    `[]:(wasmstate#num#num)list`] o MATCH_MP WASMF_LIFT) THEN
  REWRITE_TAC[wfsum]);;

(* ------------------------------------------------------------------------- *)
(* The call rule under wasmn (np params, nr results), ensures form.         *)
(* ------------------------------------------------------------------------- *)

let WASMN_CALL_ENSURES = prove
 (`!fs f code np nr e decls (P:wasmstate->bool) Q C Pre Post D n.
     wfsum fs P Q C /\
     (!c. Q c ==> ~(read wstatus c = WRunning)) /\
     fs f = (code,np,nr) /\ wasm_entry code = SOME e /\
     wasm_decl_vals code = SOME decls /\
     (!s. Pre s ==> read wstatus s = WRunning /\
                    wasm_decode (read wcode s) (val (read wpc s)) = SOME (Wcall f,n) /\
                    np <= LENGTH (read wstack s) /\
                    P (wcall_entry code np nr (read wstack s) e decls s)) /\
     (!s c1. Pre s /\ Q c1 /\ C (wcall_entry code np nr (read wstack s) e decls s) c1
             ==> Post (wcall_return (val (read wpc s) + n) np c1 s) /\
                 D s (wcall_return (val (read wpc s) + n) np c1 s))
     ==> ensures (wasmn fs) Pre Post D`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wfsum; ensures] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "leaf") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fin") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pre") (LABEL_TAC "post")) THEN
  X_GEN_TAC `s:wasmstate` THEN DISCH_TAC THEN
  REMOVE_THEN "pre" (MP_TAC o SPEC `s:wasmstate`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  ABBREV_TAC `c0 = wcall_entry code np nr (read wstack s) e decls s` THEN
  REMOVE_THEN "leaf" (MP_TAC o SPEC
    `(c0:wasmstate,[]:(wasmstate#num#num)list)`) THEN
  REWRITE_TAC[FST; SND] THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP EVENTUALLY_RTC_EXISTS) THEN
  REWRITE_TAC[EXISTS_PAIR_THM; FST; SND] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:wasmstate` (X_CHOOSE_THEN
    `k1:(wasmstate#num#num)list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `k1:(wasmstate#num#num)list = []`)) THEN
  ONCE_REWRITE_TAC[eventually_CASES] THEN DISJ2_TAC THEN
  SUBGOAL_THEN `!s'. wasmn fs s s' <=> wasm_calln fs f (val (read wpc s) + n) s s'`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC WASMN_CALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `wcall_return (val (read wpc s) + n) np c1 s` THEN
    REWRITE_TAC[wasm_calln] THEN
    MAP_EVERY EXISTS_TAC [`code:byte list`; `np:num`; `nr:num`; `e:num`;
                          `decls:wval list`; `c1:wasmstate`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "fin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `s':wasmstate` THEN REWRITE_TAC[wasm_calln; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`code':byte list`; `np':num`; `nr':num`; `e':num`;
                       `decls':wval list`; `c1':wasmstate`] THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    let c = concl th in is_eq c && is_var(rhs c) &&
      mem (fst(dest_var(rhs c))) ["code'"; "np'"; "nr'"]))) THEN
  SUBGOAL_THEN `e':num = e /\ decls':wval list = decls`
    (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [ASM_MESON_TAC[option_INJ]; ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th ->
    if is_eq(concl th) && rhs(concl th) = `c0:wasmstate` then th else
    REWRITE_RULE[ASSUME
      `wcall_entry code np nr (read wstack s) e decls s = c0`] th) THEN
  SUBGOAL_THEN `(Q:wasmstate->bool) c1' /\ C (c0:wasmstate) (c1':wasmstate)`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`wasmf fs`;
      `\x:wasmstate#(wasmstate#num#num)list.
         ((Q:wasmstate->bool) (FST x) /\ SND x = []) /\
         (C:wasmstate->wasmstate->bool) c0 (FST x)`]
      EVENTUALLY_RTC_FINAL) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[WASMF_FINAL];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `(c0:wasmstate,[]:(wasmstate#num#num)list)`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `(c1':wasmstate,[]:(wasmstate#num#num)list)`) THEN
    REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[WASMF_FINAL];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[eventually_CASES] THEN DISJ1_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "post" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "c0" THEN ASM_REWRITE_TAC[]);;

(* simulation form, inside a caller proof: through the call, continue with *)
(* eventually from the return state                                         *)
let WASMN_CALL_STEP = prove
 (`!fs f code np nr e decls (P:wasmstate->bool) Q C n s R.
     wfsum fs P Q C /\
     (!c. Q c ==> ~(read wstatus c = WRunning)) /\
     fs f = (code,np,nr) /\ wasm_entry code = SOME e /\
     wasm_decl_vals code = SOME decls /\
     read wstatus s = WRunning /\
     wasm_decode (read wcode s) (val (read wpc s)) = SOME (Wcall f,n) /\
     np <= LENGTH (read wstack s) /\
     P (wcall_entry code np nr (read wstack s) e decls s) /\
     (!c1. Q c1 /\ C (wcall_entry code np nr (read wstack s) e decls s) c1
           ==> eventually (wasmn fs) R (wcall_return (val (read wpc s) + n) np c1 s))
     ==> eventually (wasmn fs) R s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`fs:num->byte list#num#num`; `f:num`; `code:byte list`;
    `np:num`; `nr:num`; `e:num`; `decls:wval list`; `P:wasmstate->bool`;
    `Q:wasmstate->bool`; `C:wasmstate->wasmstate->bool`;
    `\x:wasmstate. x = s`; `eventually (wasmn fs) R`;
    `\x:wasmstate y:wasmstate. T`; `n:num`] WASMN_CALL_ENSURES) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THEN REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      let c = concl th in is_eq c && rhs c = `s:wasmstate` && is_var(lhs c))) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[ensures] THEN DISCH_THEN(MP_TAC o SPEC `s:wasmstate`) THEN
    REWRITE_TAC[ETA_AX; EVENTUALLY_EVENTUALLY]]);;

(* ------------------------------------------------------------------------- *)
(* Divergence regression (Sol, design s2): entry->return, entry->loop,      *)
(* loop->loop. State 0 = entry, 1 = return, 2 = loop.                       *)
(* ------------------------------------------------------------------------- *)

let div3 = new_definition
 `div3 (x:num) (y:num) <=>
    (x = 0 /\ y = 1) \/ (x = 0 /\ y = 2) \/ (x = 2 /\ y = 2)`;;

(* an existential finite execution from entry reaches return, which is final *)
let DIV3_EXISTS_RETURN = prove
 (`RTC div3 0 1 /\ !y. ~div3 1 y`,
  CONJ_TAC THENL
   [MATCH_MP_TAC RTC_INC THEN REWRITE_TAC[div3];
    REWRITE_TAC[div3] THEN ARITH_TAC]);;

(* but the small-step system does not eventually return from entry *)
let DIV3_NOT_EVENTUALLY = prove
 (`~eventually div3 (\x. x = 1) 0`,
  ONCE_REWRITE_TAC[eventually_CASES] THEN REWRITE_TAC[ARITH_EQ] THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_FORALL_THM; NOT_IMP] THEN DISJ2_TAC THEN
  EXISTS_TAC `2` THEN REWRITE_TAC[div3; ARITH_EQ] THEN
  MP_TAC(ISPECL [`div3`; `\x:num. x = 1`; `\x:num. x = 2`]
    NOT_EVENTUALLY_INVARIANT) THEN
  REWRITE_TAC[div3] THEN ANTS_TAC THENL
   [GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    MESON_TAC[];
    DISCH_THEN(MP_TAC o SPEC `2`) THEN REWRITE_TAC[]]);;

(* the existential big-step summary of div3 (one step to any reachable     *)
(* final state) DOES eventually reach return from entry: it hides the loop *)
let div3_big = new_definition
 `div3_big (x:num) (y:num) <=> RTC div3 x y /\ ~(x = y) /\ !z. ~div3 y z`;;

let DIV3_BIG_HIDES_LOOP = prove
 (`eventually div3_big (\x. x = 1) 0`,
  ONCE_REWRITE_TAC[eventually_CASES] THEN DISJ2_TAC THEN CONJ_TAC THENL
   [EXISTS_TAC `1` THEN REWRITE_TAC[div3_big; DIV3_EXISTS_RETURN; ARITH_EQ];
    ALL_TAC] THEN
  X_GEN_TAC `y:num` THEN REWRITE_TAC[div3_big] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[eventually_CASES] THEN DISJ1_TAC THEN
  ASM_CASES_TAC `y = 1` THEN ASM_REWRITE_TAC[] THEN
  (* any other final y: 0 and 2 both have successors *)
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th))) THEN
  ASM_CASES_TAC `y = 2` THENL
   [ASM_REWRITE_TAC[div3] THEN MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(K ALL_TAC) THEN
  (* RTC div3 0 y with y not 0,1,2 is impossible *)
  SUBGOAL_THEN `!a b. RTC div3 a b ==> a <= 2 ==> b <= 2` MP_TAC THENL
   [MATCH_MP_TAC RTC_INDUCT THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[div3] THEN REPEAT CONJ_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`0`; `y:num`]) THEN ASM_REWRITE_TAC[ARITH_LE] THEN
  UNDISCH_TAC `~(0 = y)` THEN UNDISCH_TAC `~(y = 1)` THEN UNDISCH_TAC `~(y = 2)` THEN
  ARITH_TAC);;

(* determinism is exactly what fails: the transfer premise is false here  *)
let DIV3_NONDETERMINISTIC = prove
 (`~(!x y z. div3 x y /\ div3 x z ==> y = z)`,
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  MAP_EVERY EXISTS_TAC [`0`; `1`; `2`] THEN REWRITE_TAC[div3] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Observations of a trapped state (Sol review r1). Wasm discards the       *)
(* operand stacks, locals and labels of every frame a trap unwinds; in this *)
(* model a trapped state keeps them (wcall_return restores the caller's     *)
(* saved state with status WTrapped). They are NOT observations: the        *)
(* observation of a trapped state is wtrap_obs (status, memory, memory size,*)
(* globals), and theorems about trapping runs state only these components.  *)
(* Unwinding preserves the observation exactly (WASMF_TRAPPED_RTC).         *)
(* ------------------------------------------------------------------------- *)

let wtrap_obs = new_definition
 `wtrap_obs (s:wasmstate) =
    (read wstatus s,read wmem s,read wmemsize s,read wglobals s)`;;

let WCALL_RETURN_TRAP_OBS = prove
 (`!npc np c1 s. read wstatus c1 = WTrapped
     ==> wtrap_obs (wcall_return npc np c1 s) = wtrap_obs c1`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[wtrap_obs; wcall_return; distinctness "wstat"] THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN REWRITE_TAC[]);;

let WASMF_TRAPPED_STEP = prove
 (`!fs x y. wasmf fs x y /\ read wstatus (FST x) = WTrapped
            ==> read wstatus (FST y) = WTrapped /\ wtrap_obs (FST y) = wtrap_obs (FST x)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; wasmf; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`s:wasmstate`; `k:(wasmstate#num#num)list`;
                       `t:wasmstate`; `k':(wasmstate#num#num)list`] THEN
  ASM_CASES_TAC `read wstatus s = WTrapped` THEN
  ASM_REWRITE_TAC[wasm; distinctness "wstat"] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[WCALL_RETURN_TRAP_OBS] THEN
  REWRITE_TAC[wcall_return] THEN ASM_REWRITE_TAC[distinctness "wstat"] THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN REWRITE_TAC[]);;

let WASMF_TRAPPED_RTC = prove
 (`!fs x y. RTC (wasmf fs) x y
            ==> read wstatus (FST x) = WTrapped
                ==> read wstatus (FST y) = WTrapped /\
                    wtrap_obs (FST y) = wtrap_obs (FST x)`,
  GEN_TAC THEN MATCH_MP_TAC RTC_INDUCT THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  MESON_TAC[WASMF_TRAPPED_STEP]);;

(* ------------------------------------------------------------------------- *)
(* An inline call step for wasmn simulations (np params, nr results).       *)
(*                                                                           *)
(* WASMN_CALL_TAC execth lth cth sname, on a goal                            *)
(*   eventually (wasmn fs) R s                                              *)
(* where s is at `call f` (decode from execth = the caller's exec rule),    *)
(* the assumptions give read wcode / wpc / wstatus / wstack of s and        *)
(* fs f = (code,np,nr); lth = |- wfsum fs P Q C (the callee summary,        *)
(* instantiated; from WASM_TO_WFSUM for a call-free leaf or WASMN_TO_WFSUM  *)
(* for a callee that calls) and cth = WASM_CALLEE_RULE code_def. It proves  *)
(* the callee precondition at the entry state (wcall_entry: parameters in  *)
(* locals 0..np-1, declared locals zero by type, the caller's memory,      *)
(* memory size and globals), expands the callee's MAYCHANGE frame, and     *)
(* continues at a fresh state sname = the caller after the return (results *)
(* replace the parameters on the caller's stack; the callee's memory). The *)
(* callee must leave memory size and globals unchanged (the frame must not *)
(* name wmemsize or wglobals); memory writes are carried over by name as   *)
(* in WASMC_CALL0_SITE_TAC (name the caller memory `read wmem s = mm`).    *)
(* ------------------------------------------------------------------------- *)

let EL_ALT = prove
 (`!n (l:A list). EL n l = if n = 0 then HD l else EL (n - 1) (TL l)`,
  INDUCT_TAC THEN REWRITE_TAC[EL; NOT_SUC; SUC_SUB1]);;

let WTAKE_0 = prove
 (`!l:A list. wtake 0 l = []`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[wtake]);;

let wcall_compset = wasm_mk_decode_compset [wcall_locals; EL_ALT; APPEND; WTAKE_0; WDROP_0];;

let WCALL_LIST_CONV = Compute.WEAK_CBV_CONV wcall_compset;;

let WCALL_LOCALS_EVAL_CONV tm =
  match strip_comb tm with
    Const("wcall_locals",_),[_;_;_] -> CHANGED_CONV WCALL_LIST_CONV tm
  | Const("wtake",_),[_;_] -> CHANGED_CONV WCALL_LIST_CONV tm
  | Const("wdrop",_),[_;_] -> CHANGED_CONV WCALL_LIST_CONV tm
  | Const("APPEND",_),[_;_] -> CHANGED_CONV WCALL_LIST_CONV tm
  | _ -> failwith "WCALL_LOCALS_EVAL_CONV";;

let WCALL_RETURN_N = prove
 (`!npc np c1 s.
     read wstatus c1 = WDone /\
     read wmemsize c1 = read wmemsize s /\ read wglobals c1 = read wglobals s
     ==> wcall_return npc np c1 s =
         write wpc (word npc)
          (write wstack (APPEND (read wstack c1) (wdrop np (read wstack s)))
            (write wmem (read wmem c1) s))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[wcall_return] THEN
  REWRITE_TAC[WGLOBALS_SVC; WMEMSIZE_SVC]);;

let WCALL_ENTRY_TAC =
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wlocal; wglobal; READ_COMPONENT_COMPOSE; READ_ELEMENT]) THEN
  REWRITE_TAC[wlocal; wglobal; READ_COMPONENT_COMPOSE; WCALL_ENTRY_READS] THEN
  REWRITE_TAC[READ_ELEMENT] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV WCALL_LOCALS_EVAL_CONV) THEN
  ASM_REWRITE_TAC[];;

(* generalize the state argument of an eventually goal to a fresh variable *)
let WASM_GEN_EVENTUALLY_STATE_TAC (sname:string) : tactic = fun (asl,w) ->
  let x = rand w in
  let sv = mk_var(sname,`:wasmstate`) in
  let gth = mk_forall(sv, mk_imp(mk_eq(x,sv), mk_comb(rator w, sv))) in
  (SUBGOAL_THEN gth (fun th -> MATCH_MP_TAC th THEN REFL_TAC) THEN
   X_GEN_TAC sv) (asl,w);;

(* DISCARD_OLD_WASMSTATE_TAC that counts only :wasmstate terms as states:  *)
(* a fact whose read arguments are state-free (read (bytes8 a) mm = v, or  *)
(* read c (write .. mm) = v, with mm a memory term) is kept; facts about   *)
(* other wasmstate terms than the new state are dropped as before.         *)
let WASMN_DISCARD_OLD_TAC s =
  let v = mk_var(s,`:wasmstate`) in
  let ws = `:wasmstate` in
  let rec svars bound tm =
    match tm with
      Comb(Comb(Const("read",_),_),x) ->
        if mem x bound then [] else
        if type_of x = ws then [x] else svars bound x
    | Comb(a,b) -> union (svars bound a) (svars bound b)
    | Abs(x,t) -> svars (x::bound) t
    | _ -> [] in
  DISCARD_ASSUMPTIONS_TAC(fun th ->
    let us = svars [] (concl th) in
    not(us = [] || us = [v]));;

(* callee entry locals by rewriting: a fallback for WCALL_ENTRY_TAC when    *)
(* the compset evaluator leaves wcall_locals/wtake terms (seen with three   *)
(* i32 arguments, app sprint M2)                                            *)
let WCALL_LOCALS_REWRITE_TAC : tactic =
  CONV_TAC(REPEATC(CHANGED_CONV(REWRITE_CONV[wtake; wcall_locals; LENGTH; HD; TL] THENC
                                DEPTH_CONV(NUM_RED_CONV ORELSEC EL_NUM_CONV)))) THEN
  REWRITE_TAC[HD; TL];;

let WASMN_CALL_GEN_TAC (_,decode_ths) (lth0:thm) (cth:thm) (cont:term->term->term->term->term->tactic) : tactic =
  fun (asl,w) ->
    let s = rand w in
    let stepr = rand(rator(rator w)) in
    let fs = rand stepr in
    let rr = rand(rator w) in
    let lth = if is_forall(concl lth0) then ISPEC fs lth0 else lth0 in
    let _,largs = strip_comb(concl lth) in
    let pp = el 1 largs and qq = el 2 largs and cc = el 3 largs in
    let eth,dth = CONJ_PAIR cth in
    let code = rand(lhand(concl eth)) and e = rand(rand(concl eth))
    and decls = rand(rand(concl dth)) in
    let ths = map snd asl in
    let pc_th = find_read_th "wpc" s ths
    and code_th = find_read_th "wcode" s ths
    and st_th = find_read_th "wstatus" s ths
    and stk_th = find_read_th "wstack" s ths in
    let pc_num = rand(rhs(concl pc_th)) in
    let pc = dest_small_numeral pc_num in
    let dec = match (try decode_ths.(pc) with _ -> None) with
        Some th -> th | None -> failwith "WASMN_CALL_TAC: no decode at pc" in
    let ins,n = dest_pair(rand(rhs(concl dec))) in
    let f = rand ins in
    let fsf = mk_comb(fs,f) in
    let fsth = try find (fun th -> let c = concl th in is_eq c && lhs c = fsf) ths
               with Failure _ -> failwith "WASMN_CALL_TAC: no fs f = .. assumption" in
    let _,npnr = dest_pair(rhs(concl fsth)) in
    let np,nr = dest_pair npnr in
    let sth = ISPECL [fs; f; code; np; nr; e; decls; pp; qq; cc; n; s; rr]
                WASMN_CALL_STEP in
    let c0tm = list_mk_comb(`wcall_entry`,
       [code; np; nr; mk_comb(`read wstack`,s); e; decls; s]) in
    (MATCH_MP_TAC sth THEN
     REPEAT CONJ_TAC THENL
      [ACCEPT_TAC lth;
       CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN MESON_TAC[distinctness "wstat"];
       ACCEPT_TAC fsth;
       ACCEPT_TAC eth;
       ACCEPT_TAC dth;
       ACCEPT_TAC st_th;
       REWRITE_TAC[code_th; pc_th; VAL_WORD; DIMINDEX_64] THEN
       CONV_TAC NUM_REDUCE_CONV THEN ACCEPT_TAC dec;
       REWRITE_TAC[stk_th; LENGTH] THEN ARITH_TAC;
       WCALL_ENTRY_TAC THEN TRY(WCALL_LOCALS_REWRITE_TAC THEN ASM_REWRITE_TAC[]);
       cont s pc_num n np c0tm]) (asl,w);;

(* continuation after a callee that returned (WDone) *)
(* name the callee entry memory after the caller's: rewrite the right-hand side of     *)
(* `read wmem c0 = read wmem s` with a caller fact `read wmem s = mm` (mm free of      *)
(* states), so WASMC_MEM_UPDATE_TAC can express the callee's writes over mm            *)
let WASMN_NAME_C0_MEM_TAC (s:term) : tactic = fun (asl,w) ->
  let rmem = mk_comb(`read wmem`,s) in
  let ws = `:wasmstate` in
  let names = mapfilter (fun th -> let c = concl th in
      if is_eq c && lhs c = rmem &&
         not (can (find_term (fun t -> type_of t = ws)) (rhs c)) then th
      else fail()) (map snd asl) in
  if names = [] then ALL_TAC (asl,w) else
  RULE_ASSUM_TAC(fun th -> let c = concl th in
    if is_eq c && lhs c = `read wmem (c0:wasmstate)` && rhs c = rmem
    then GEN_REWRITE_RULE RAND_CONV names th else th) (asl,w);;

let WASMN_DONE_CONT (sname:string) s pc_num n np c0tm : tactic =
  let npc = mk_binop `(+):num->num->num` pc_num n in
  let sv' = mk_var(sname,`:wasmstate`) in
  let pc_th_tm = mk_eq(mk_comb(`read wpc`,s), mk_comb(`word:num->int64`,pc_num)) in
  let is_rmem_c1 th = let c = concl th in
     is_eq c && lhs c = `read wmem (c1:wasmstate)` in
       X_GEN_TAC `c1:wasmstate` THEN
       ABBREV_TAC (mk_eq(`c0:wasmstate`, c0tm)) THEN
       SUBGOAL_THEN (subst [s,`s:wasmstate`]
          `read wmem (c0:wasmstate) = read wmem (s:wasmstate) /\
           read wmemsize c0 = read wmemsize (s:wasmstate) /\
           read wglobals c0 = read wglobals (s:wasmstate)`)
         STRIP_ASSUME_TAC THENL
        [EXPAND_TAC "c0" THEN REWRITE_TAC[WCALL_ENTRY_READS]; ALL_TAC] THEN
       WASMN_NAME_C0_MEM_TAC s THEN
       DISCH_THEN(CONJUNCTS_THEN2
         (STRIP_ASSUME_TAC o CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) MP_TAC) THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [MAYCHANGE; SEQ_ID] THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [GSYM SEQ_ASSOC] THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_SEQ] THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_THM] THEN
       REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
       WASMC_MEM_UPDATE_TAC THEN ASSUMPTION_STATE_UPDATE_TAC THEN
       DISCH_THEN(K ALL_TAC) THEN
       SUBGOAL_THEN
         (mk_eq(list_mk_comb(`wcall_return`,
                  [mk_binop `(+):num->num->num` (mk_comb(`val:int64->num`,
                     mk_comb(`read wpc`,s))) n; np; `c1:wasmstate`; s]),
                list_mk_comb(`write wpc`,
                  [mk_comb(`word:num->int64`, npc);
                   list_mk_comb(`write wstack`,
                     [list_mk_comb(`APPEND:wval list->wval list->wval list`,
                        [`read wstack (c1:wasmstate)`;
                         list_mk_comb(`wdrop:num->wval list->wval list`,
                                      [np; mk_comb(`read wstack`,s)])]);
                      list_mk_comb(`write wmem`, [`read wmem (c1:wasmstate)`; s])])])))
         SUBST1_TAC THENL
        [SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`, mk_comb(`read wpc`,s)), pc_num))
           SUBST1_TAC THENL
          [REWRITE_TAC[ASSUME pc_th_tm; VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV;
           ALL_TAC] THEN
         MATCH_MP_TAC WCALL_RETURN_N THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
       (* the callee's postcondition facts about c1's memory become facts about the     *)
       (* returned memory, read over its writes, so they survive when old states are   *)
       (* discarded (WASMN_DISCARD_OLD_TAC below keeps state-free facts; the profile's *)
       (* DISCARD_OLD_WASMSTATE_TAC drops them until its next re-vendor)                *)
       FIRST_X_ASSUM(fun th -> if is_rmem_c1 th then
         REWRITE_TAC[th] THEN
         RULE_ASSUM_TAC(fun a -> if free_in `c1:wasmstate` (concl a)
           then CONV_RULE(ONCE_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV)
                  (REWRITE_RULE[READ_COMPONENT_COMPOSE; th] a) else a)
         else NO_TAC) THEN
       REWRITE_TAC[WMEM_SVC; WCALL_WRITE_MEM1; WCALL_WRITE_MEM2] THEN
       ASM_REWRITE_TAC[] THEN
       CONV_TAC(ONCE_DEPTH_CONV WCALL_LOCALS_EVAL_CONV) THEN
       CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
       WASMC_GEN_STATE_TAC sv' THEN
       X_GEN_TAC sv' THEN
       WASMC_MEM_UPDATE_TAC THEN ASSUMPTION_STATE_UPDATE_TAC THEN
       MAYCHANGE_STATE_UPDATE_TAC THEN
       DISCH_THEN(fun th ->
         let thl = STATE_UPDATE_NEW_RULE th in
         if thl = [] then ALL_TAC else MP_TAC(end_itlist CONJ thl) THEN STRIP_TAC) THEN
       WASMN_DISCARD_OLD_TAC sname THEN WASM_COMPACT_HYPS_TAC;;

(* continuation after a callee that trapped: the caller traps with the    *)
(* callee's memory, memory size and globals (frame: the caller must allow *)
(* wstatus, wmem, wmemsize and wglobals to change)                         *)
let WASMN_TRAP_CONT (sname:string) s pc_num n np c0tm : tactic =
  X_GEN_TAC `c1:wasmstate` THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (STRIP_ASSUME_TAC o CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) (K ALL_TAC)) THEN
  REWRITE_TAC[wcall_return] THEN
  ASM_REWRITE_TAC[distinctness "wstat"] THEN
  WASM_GEN_EVENTUALLY_STATE_TAC sname THEN
  ASSUMPTION_STATE_UPDATE_TAC THEN MAYCHANGE_STATE_UPDATE_TAC THEN
  DISCH_THEN(fun th ->
    let thl = STATE_UPDATE_NEW_RULE th in
    if thl = [] then ALL_TAC else MP_TAC(end_itlist CONJ thl) THEN STRIP_TAC) THEN
  WASM_COMPACT_HYPS_TAC;;

let WASMN_CALL_TAC execth lth cth sname =
  WASMN_CALL_GEN_TAC execth lth cth (WASMN_DONE_CONT sname);;

(* continuation after a callee that returned and may have WRITTEN memory    *)
(* (app sprint 2026-11-08, M0/M2 calls_mem.ml). The caller must have named  *)
(* its memory (`read wmem s = mm`, mm a variable or any state-free term);   *)
(* the callee's postcondition facts about c1's memory are rewritten to      *)
(* state-free facts about the new memory before c1 goes, and the caller's   *)
(* new state is a component write (frames as for a store), so a caller      *)
(* frame that names only the written bytes (MAYCHANGE [wmem :> bytes ..])   *)
(* survives. WASMN_DONE_CONT also uses the memory name when there is one    *)
(* (WASMN_NAME_C0_MEM_TAC), but returns the callee's whole memory, so the   *)
(* caller's frame must then name all of wmem (header: which tactic to use). *)
let WASMN_DONE_MEM_CONT (sname:string) s pc_num n np c0tm : tactic =
  let npc = mk_binop `(+):num->num->num` pc_num n in
  let sv' = mk_var(sname,`:wasmstate`) in
  let pc_th_tm = mk_eq(mk_comb(`read wpc`,s), mk_comb(`word:num->int64`,pc_num)) in
  let rmem_s = mk_comb(`read wmem`,s) in
  let ws = `:wasmstate` in
  let is_rmem_c1 th = let c = concl th in
     is_eq c && lhs c = `read wmem (c1:wasmstate)` in
  fun (asl,w) ->
  let mth = try find (fun th -> let c = concl th in
                is_eq c && lhs c = rmem_s &&
                not (can (find_term (fun t -> type_of t = ws)) (rhs c))) (map snd asl)
            with Failure _ -> failwith "WASMN_CALL_MEM_TAC: name the caller memory first (read wmem s = mm)" in
  let not_mth th = not (concl th = concl mth) in
  (X_GEN_TAC `c1:wasmstate` THEN
   ABBREV_TAC (mk_eq(`c0:wasmstate`, c0tm)) THEN
   SUBGOAL_THEN (subst [s,`s:wasmstate`]
      `read wmem (c0:wasmstate) = read wmem (s:wasmstate) /\
       read wmemsize c0 = read wmemsize (s:wasmstate) /\
       read wglobals c0 = read wglobals (s:wasmstate)`)
     STRIP_ASSUME_TAC THENL
    [EXPAND_TAC "c0" THEN REWRITE_TAC[WCALL_ENTRY_READS]; ALL_TAC] THEN
   FIRST_X_ASSUM(fun th -> if concl th = mk_eq(`read wmem (c0:wasmstate)`, rmem_s)
     then MP_TAC th else NO_TAC) THEN
   GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [mth] THEN DISCH_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2
     (STRIP_ASSUME_TAC o CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) MP_TAC) THEN
   GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [MAYCHANGE; SEQ_ID] THEN
   GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [GSYM SEQ_ASSOC] THEN
   GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_SEQ] THEN
   GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_THM] THEN
   REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
   WASMC_MEM_UPDATE_TAC THEN ASSUMPTION_STATE_UPDATE_TAC THEN
   DISCH_THEN(K ALL_TAC) THEN
   (* callee facts about c1's memory -> state-free facts *)
   RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
   FIRST_ASSUM(fun rth -> if is_rmem_c1 rth then
       REPEAT(FIRST_X_ASSUM(fun th ->
         if not(concl th = concl rth) && free_in `read wmem (c1:wasmstate)` (concl th)
         then MP_TAC th else NO_TAC)) THEN
       REWRITE_TAC[rth] THEN REPEAT DISCH_TAC
     else NO_TAC) THEN
   SUBGOAL_THEN
     (mk_eq(list_mk_comb(`wcall_return`,
              [mk_binop `(+):num->num->num` (mk_comb(`val:int64->num`,
                 mk_comb(`read wpc`,s))) n; np; `c1:wasmstate`; s]),
            list_mk_comb(`write wpc`,
              [mk_comb(`word:num->int64`, npc);
               list_mk_comb(`write wstack`,
                 [list_mk_comb(`APPEND:wval list->wval list->wval list`,
                    [`read wstack (c1:wasmstate)`;
                     list_mk_comb(`wdrop:num->wval list->wval list`,
                                  [np; mk_comb(`read wstack`,s)])]);
                  list_mk_comb(`write wmem`, [`read wmem (c1:wasmstate)`; s])])])))
     SUBST1_TAC THENL
    [SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`, mk_comb(`read wpc`,s)), pc_num))
       SUBST1_TAC THENL
      [REWRITE_TAC[ASSUME pc_th_tm; VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV;
       ALL_TAC] THEN
     MATCH_MP_TAC WCALL_RETURN_N THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   FIRST_X_ASSUM(fun th -> if is_rmem_c1 th then REWRITE_TAC[th] else NO_TAC) THEN
   REWRITE_TAC[SYM mth] THEN
   REWRITE_TAC[WMEM_SVC; WCALL_WRITE_MEM1; WCALL_WRITE_MEM2] THEN
   (fun (asl,w) -> REWRITE_TAC (filter not_mth (map snd asl)) (asl,w)) THEN
   CONV_TAC(ONCE_DEPTH_CONV WCALL_LOCALS_EVAL_CONV) THEN
   CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
   WASMC_GEN_STATE_TAC sv' THEN
   X_GEN_TAC sv' THEN
   WASMC_MEM_UPDATE_TAC THEN
   ASSUMPTION_STATE_UPDATE_TAC THEN
   MAYCHANGE_STATE_UPDATE_TAC THEN
   DISCH_THEN(fun th ->
     let thl = STATE_UPDATE_NEW_RULE th in
     if thl = [] then ALL_TAC else MP_TAC(end_itlist CONJ thl) THEN STRIP_TAC) THEN
   WASMN_DISCARD_OLD_TAC sname THEN WASM_COMPACT_HYPS_TAC) (asl,w);;

let WASMN_CALL_MEM_TAC execth lth cth sname =
  WASMN_CALL_GEN_TAC execth lth cth (WASMN_DONE_MEM_CONT sname);;

let WASMN_CALL_TRAP_TAC execth lth cth sname =
  WASMN_CALL_GEN_TAC execth lth cth (WASMN_TRAP_CONT sname);;

(* ------------------------------------------------------------------------- *)
(* Non-call steps under wasmn (twins of WASMC_CONV / WASMC_STEP_TAC).       *)
(* ------------------------------------------------------------------------- *)

let WASMN_CONV (decode_ths:thm option array) (extra:thm list) (ths:thm list) tm =
  let fsm,s' = dest_comb tm in
  let fsm,s = dest_comb fsm in
  let fs = rand fsm in
  let eth = WASM_CONV decode_ths extra ths (mk_comb(mk_comb(`wasm`,s),s')) in
  let pc_th = find_read_th "wpc" s ths
  and code_th = find_read_th "wcode" s ths in
  let pc_num = rand(rhs(concl pc_th)) in
  let pc = dest_small_numeral pc_num in
  let dth = match (try decode_ths.(pc) with _ -> None) with
      Some th -> th | None -> failwith ("WASMN_CONV: no decode at pc "^string_of_int pc) in
  let i,n = dest_pair(rand(rhs(concl dth))) in
  let lt_th = EQT_ELIM(NUM_REDUCE_CONV(mk_binary "<" (pc_num,`2 EXP 64`))) in
  let nth = MP (ISPECL [fs; s; s'; rhs(concl code_th); pc_num; i; n] WASMN_NONCALL)
               (end_itlist CONJ [code_th; pc_th; lt_th; dth; WASMC_NONCALL_TH i]) in
  TRANS nth eth;;

let WASMN_BASIC_STEP_TAC =
  let ws_ty = `:wasmstate` in
  fun decode_ths extra sname (asl,w) ->
    let sv = rand w and sv' = mk_var(sname,ws_ty) in
    let stepr = rand(rator(rator w)) in
    let atm = mk_comb(mk_comb(stepr,sv),sv') in
    let eth = WASMN_CONV decode_ths extra (map snd asl) atm in
    let r = rhs(concl eth) in
    if not (is_eq r && rand r = sv') then
      failwith ("WASMN_BASIC_STEP_TAC: step did not reduce to a state update: "^
                string_of_term r) else
    (GEN_REWRITE_TAC I [eventually_CASES] THEN DISJ2_TAC THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC BINDER_CONV [eth] THEN CONV_TAC EXISTS_NONTRIVIAL_CONV;
      X_GEN_TAC sv' THEN GEN_REWRITE_TAC LAND_CONV [eth]]) (asl,w);;

let WASMN_STEP_TAC (_,decode_ths) extra sname =
  WASMN_BASIC_STEP_TAC decode_ths extra sname THEN
  WASM_MEM_UPDATE_TAC THEN
  ASSUMPTION_STATE_UPDATE_TAC THEN
  MAYCHANGE_STATE_UPDATE_TAC THEN
  DISCH_THEN(fun th ->
    let thl = STATE_UPDATE_NEW_RULE th in
    if thl = [] then ALL_TAC else
    MP_TAC(end_itlist CONJ thl) THEN
    CONV_TAC(LAND_CONV(DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV))) THEN
    STRIP_TAC);;

(* compacted after each step as WASMC_STEPS_TAC (WASM_COMPACT_HYPS_TAC, #165); *)
(* the call continuations above end with it too                              *)
let WASMN_STEPS_TAC execth snums =
  MAP_EVERY (fun s -> WASMN_STEP_TAC execth [] s THEN WASMN_DISCARD_OLD_TAC s THEN
                      WASM_COMPACT_HYPS_TAC)
            (statenames "s" snums);;



(* ------------------------------------------------------------------------- *)
(* From wasmc to wasmn (hol-hearth wasm tooling H2, 2026-11-11).             *)
(* wasmc fs (wasm_call.ml) runs a callee under plain wasm; wasmn fs runs it  *)
(* under wasmf, so every wasmc step is a wasmn step (WASMC_WASMN). wasmn fs  *)
(* is deterministic (WASMN_DET), so a total-correctness result transfers:   *)
(* eventually (wasmc fs) P s ==> eventually (wasmn fs) P s                   *)
(* (EVENTUALLY_WASMC_WASMN; ENSURES_WASMC_WASMN for leaves). The transfer is *)
(* the generic EVENTUALLY_SUBREL_DET: a sub-relation of a deterministic      *)
(* relation reaches every eventually-goal it reaches.                        *)
(* ------------------------------------------------------------------------- *)

let RTC_WASM_WASMF = prove
 (`!fs a b. RTC wasm a b ==> RTC (wasmf fs) (a,[]) (b,[])`,
  GEN_TAC THEN MATCH_MP_TAC RTC_INDUCT THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RTC_INC THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WASMF_WASM_STEP th]) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[RTC_REFL];
    MESON_TAC[RTC_TRANS]]);;

let WASMC_WASMN = prove
 (`!fs s s'. wasmc fs s s' ==> wasmn fs s s'`,
  REWRITE_TAC[wasmc; wasmn; wasm_call; wasm_calln] THEN MESON_TAC[RTC_WASM_WASMF]);;

(* a deterministic relation reaches at most one terminal state *)
let RTC_DET_FINAL = prove
 (`!(R:A->A->bool).
     (!x y z. R x y /\ R x z ==> y = z)
     ==> !x y. RTC R x y
               ==> !z. RTC R x z /\ (!u. ~R y u) /\ (!u. ~R z u) ==> y = z`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC RTC_INDUCT_R THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONJ_TAC THENL
   [MESON_TAC[RTC_CASES_R]; ASM_MESON_TAC[RTC_CASES_R]]);;

let WASM_CALLN_DET = prove
 (`!fs f npc s a b.
     wasm_calln fs f npc s a /\ wasm_calln fs f npc s b ==> a = b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wasm_calln] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `code1:byte list` (X_CHOOSE_THEN `np1:num` (X_CHOOSE_THEN `nr1:num`
     (X_CHOOSE_THEN `e1:num` (X_CHOOSE_THEN `decls1:wval list`
       (X_CHOOSE_THEN `c1:wasmstate` STRIP_ASSUME_TAC))))))
   (X_CHOOSE_THEN `code2:byte list` (X_CHOOSE_THEN `np2:num` (X_CHOOSE_THEN `nr2:num`
     (X_CHOOSE_THEN `e2:num` (X_CHOOSE_THEN `decls2:wval list`
       (X_CHOOSE_THEN `c2:wasmstate` STRIP_ASSUME_TAC))))))) THEN
  SUBGOAL_THEN `code2:byte list = code1 /\ np2:num = np1 /\ nr2:num = nr1`
    (REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [UNDISCH_TAC `(fs:num->byte list#num#num) f = (code1,np1,nr1)` THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `e2:num = e1 /\ decls2:wval list = decls1`
    (CONJUNCTS_THEN SUBST_ALL_TAC) THENL [ASM_MESON_TAC[option_INJ]; ALL_TAC] THEN
  SUBGOAL_THEN `c2:wasmstate = c1` SUBST_ALL_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  MP_TAC(MATCH_MP (ISPEC `wasmf fs` RTC_DET_FINAL) (SPEC `fs:num->byte list#num#num` WASMF_DET)) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`(wcall_entry code1 np1 nr1 (read wstack s) e1 decls1 s,[]:(wasmstate#num#num)list)`;
    `(c2:wasmstate,[]:(wasmstate#num#num)list)`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `(c1:wasmstate,[]:(wasmstate#num#num)list)`) THEN
  ASM_SIMP_TAC[WASMF_FINAL; PAIR_EQ]);;

let WASMN_DET = prove
 (`!fs s a b. wasmn fs s a /\ wasmn fs s b ==> a = b`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `?u. wasm s u` THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `u:wasmstate`) THEN REWRITE_TAC[wasmn] THEN
    SUBGOAL_THEN `!f n. ~(wasm_decode (read wcode s) (val (read wpc s)) = SOME (Wcall f,n))`
      (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[WASM_WCALL_NO_STEP]; MESON_TAC[WASM_DETERMINISTIC]];
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM]) THEN ASM_REWRITE_TAC[wasmn] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `f1:num` (X_CHOOSE_THEN `n1:num` STRIP_ASSUME_TAC)))
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `f2:num` (X_CHOOSE_THEN `n2:num` STRIP_ASSUME_TAC)))) THEN
    SUBGOAL_THEN `f2:num = f1 /\ n2:num = n1` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
     [UNDISCH_TAC `wasm_decode (read wcode s) (val (read wpc s)) = SOME (Wcall f1,n1)` THEN
      ASM_REWRITE_TAC[option_INJ; PAIR_EQ; WCALL_INJ] THEN MESON_TAC[];
      ASM_MESON_TAC[WASM_CALLN_DET]]]);;

let EVENTUALLY_SUBREL_DET = prove
 (`!(r1:A->A->bool) r2 P.
     (!x y. r1 x y ==> r2 x y) /\ (!x y z. r2 x y /\ r2 x z ==> y = z)
     ==> !s. eventually r1 P s ==> eventually r2 P s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC eventually_INDUCT THEN
  CONJ_TAC THENL [MESON_TAC[eventually_RULES]; ALL_TAC] THEN
  X_GEN_TAC `s:A` THEN DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `s1:A`) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[eventually_CASES] THEN DISJ2_TAC THEN ASM_MESON_TAC[]);;

let EVENTUALLY_WASMC_WASMN = prove
 (`!fs P s. eventually (wasmc fs) P s ==> eventually (wasmn fs) P s`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC EVENTUALLY_SUBREL_DET THEN
  REWRITE_TAC[WASMC_WASMN; WASMN_DET]);;

let ENSURES_WASMC_WASMN = prove
 (`!fs (P:wasmstate->bool) Q C. ensures (wasmc fs) P Q C ==> ensures (wasmn fs) P Q C`,
  REWRITE_TAC[ensures] THEN MESON_TAC[EVENTUALLY_WASMC_WASMN]);;

(* ------------------------------------------------------------------------- *)
(* A component written and then restored drops out of the frame (H2, G3).    *)
(* A callee that moves the stack pointer global and puts it back has a       *)
(* frame C ,, MAYCHANGE [c] with read c s' = read c s at the end; then C     *)
(* alone is a frame for it, provided C keeps c and c is a valid component.  *)
(* WASM_ENSURES_GLOBAL_RESTORED is the instance for wglobal k.              *)
(* ------------------------------------------------------------------------- *)

let MAYCHANGE_RESTORED = prove
 (`!(c:(A,B)component) (C:A->A->bool).
     strongly_valid_component c /\ (!s s'. C s s' ==> read c s' = read c s)
     ==> !s s'. (C ,, MAYCHANGE [c]) s s' /\ read c s' = read c s ==> C s s'`,
  REWRITE_TAC[STRONGLY_VALID_COMPONENT_UNWAP; read_over_write; write_over_read;
              write_over_write; MAYCHANGE; SEQ_ID; seq; ASSIGNS_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN MESON_TAC[]);;

let ENSURES_MAYCHANGE_RESTORED = prove
 (`!(step:A->A->bool) P Q C (c:(A,B)component).
     strongly_valid_component c /\ (!s s'. C s s' ==> read c s' = read c s) /\
     (!s s'. P s /\ Q s' /\ (C ,, MAYCHANGE [c]) s s' ==> read c s' = read c s) /\
     ensures step P Q (C ,, MAYCHANGE [c])
     ==> ensures step P Q C`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  REWRITE_TAC[ensures] THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `s:A` THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC(UNDISCH th)) THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_MONO) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN X_GEN_TAC `s':A` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(A,B)component`; `C:A->A->bool`] MAYCHANGE_RESTORED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let WASM_ENSURES_GLOBAL_RESTORED = prove
 (`!(step:wasmstate->wasmstate->bool) P Q C k.
     (!s s'. C s s' ==> read (wglobal k) s' = read (wglobal k) s) /\
     (!s s'. P s /\ Q s' /\ (C ,, MAYCHANGE [wglobal k]) s s'
             ==> read (wglobal k) s' = read (wglobal k) s) /\
     ensures step P Q (C ,, MAYCHANGE [wglobal k])
     ==> ensures step P Q C`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`step:wasmstate->wasmstate->bool`; `P:wasmstate->bool`;
                       `Q:wasmstate->bool`; `C:wasmstate->wasmstate->bool`; `wglobal k`]
                      ENSURES_MAYCHANGE_RESTORED) THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  REWRITE_TAC[wglobal] THEN MATCH_MP_TAC STRONGLY_VALID_COMPONENT_COMPOSE THEN
  REWRITE_TAC[STRONGLY_VALID_COMPONENT_ELEMENT] THEN
  REWRITE_TAC[strongly_valid_component; WGLOBALS_SVC]);;

(* ------------------------------------------------------------------------- *)
(* Loops whose bodies make calls (hol-hearth wasm tooling H4, 2026-11-11).   *)
(*                                                                           *)
(* WASMC_SITE_TAC sth sname: one caller-level step through a call site      *)
(*   lemma sth |- !v1 .. vk. ensures (wasmc fs) P Q C (all other premises    *)
(*   discharged; e.g. a WASMC_CALL0_SITE_TAC lemma at a fixed pc). The       *)
(*   values v1 .. vk are found by matching P's conjuncts, at the current    *)
(*   state, against the assumptions (so name them as P does, e.g.           *)
(*   read (wmem :> bytes32 (word 0)) s = n); then WASMC_BIGSTEP_TAC sname,   *)
(*   discarding old states and compacting hypotheses as WASMC_STEPS_TAC.    *)
(* WASMC_SIM_CALLS_TAC execth sites snums: WASMC_STEPS_TAC over snums, but  *)
(*   a state whose pc is a key of sites (pc, sth) steps by WASMC_SITE_TAC.  *)
(* WASMC_WHILE_UP_TAC k pc1 pc2 inv: s2n's ENSURES_WHILE_UP_TAC (generic in *)
(*   the step relation) with the ~(k = 0) side goal closed from the         *)
(*   assumptions; leaves entry, body, back-edge test and exit, in order.   *)
(*   The body goal is stepped with WASMC_SIM_CALLS_TAC.                     *)
(* Regression: wasm/demos/loop_calls.ml (a counted loop calling a leaf).     *)
(* ------------------------------------------------------------------------- *)

let WASMC_SITE_TAC (sth0:thm) (sname:string) : tactic = fun (asl,w) ->
  let s = rand w in
  (* freshen the lemma's binders away from the goal and assumptions: term_match *)
  (* drops identity bindings, so a binder named like the assumption's value    *)
  (* would otherwise get no instance                                           *)
  let vs0 = fst(strip_forall(concl sth0)) in
  let avoid = itlist (fun (_,th) acc -> union (frees(concl th)) acc) asl (frees w) in
  let vs1 = variants avoid vs0 in
  let sth = GENL vs1 (SPECL vs1 sth0) in
  let vs,body = strip_forall(concl sth) in
  let pp = el 1 (snd(strip_comb body)) in
  let pbody = rhs(concl(BETA_CONV(mk_comb(pp,s)))) in
  let conjs = conjuncts pbody in
  let asms = map (concl o snd) asl in
  let lconsts = subtract (frees pbody) vs in
  let inst = itlist (fun c acc ->
      let c' = subst acc c in
      if intersect (frees c') vs = [] then acc else
      try let _,tmin,_ = tryfind (fun a -> term_match lconsts c' a) asms in tmin @ acc
      with Failure _ -> acc) conjs [] in
  let vals = map (fun v -> try rev_assoc v inst with Failure _ ->
      failwith ("WASMC_SITE_TAC: no assumption gives "^fst(dest_var v))) vs in
  (MP_TAC(SPECL vals sth) THEN WASMC_BIGSTEP_TAC sname THEN
   DISCARD_OLD_WASMSTATE_TAC sname THEN WASM_COMPACT_HYPS_TAC) (asl,w);;

let WASMC_SIM_CALLS_TAC execth (sites:(int*thm) list) snums : tactic =
  MAP_EVERY (fun k -> fun (asl,w) ->
      let s = rand w in
      let pc_th = find (fun th -> let c = concl th in
          is_eq c && lhs c = mk_comb(`read wpc`,s)) (map snd asl) in
      let pc = dest_small_numeral(rand(rhs(concl pc_th))) in
      (match (try Some(assoc pc sites) with Failure _ -> None) with
         Some sth -> WASMC_SITE_TAC sth ("s"^string_of_int k)
       | None -> WASMC_STEPS_TAC execth [k]) (asl,w))
    snums;;

let WASMC_WHILE_UP_TAC k pc1 pc2 inv =
  ENSURES_WHILE_UP_TAC k pc1 pc2 inv THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* Float branches (hol-hearth wasm tooling H5, 2026-11-11).                  *)
(*                                                                           *)
(* A float compare leaves I32 (word (bitval (wfrel k a b))) on the stack and *)
(* a trapping trunc tests wftrap k a; a following br_if / if / trap test is *)
(* decided by WASM_CONV only when the atom (or its negation) is an           *)
(* assumption. WASM_F64_CASES_TAC splits on the first undecided wfrel or    *)
(* wftrap atom with state-free arguments, searching the assumptions newest  *)
(* first (so the value the last step pushed wins), then the goal, and in    *)
(* each term outer atoms before atoms nested in their operands; for full    *)
(* control use ASM_CASES_TAC on the atom directly.                          *)
(* (ASM_CASES_TAC), so each branch steps with the atom decided. The         *)
(* atom is never unfolded, so this works with the opaque float operations  *)
(* and with exact ones alike.                                                *)
(* WASM_F64_JOIN_TAC pc join: ENSURES_SEQUENCE_TAC at the join pc with the   *)
(* join assertion; state at the join what the rest needs, e.g. the exact    *)
(* value (local 0 = F64 (if wfrel k a b then u else v)) or only its type    *)
(* (?v. read (wlocal k) s = F64 v), so the paths do not multiply past the  *)
(* join. Regression: wasm/demos/f64_cases.ml.                               *)
(* ------------------------------------------------------------------------- *)

let WASM_F64_CASES_TAC : tactic = fun (asl,w) ->
  let ws = `:wasmstate` in
  let is_atom t =
    match strip_comb t with
      Const(("wfrel"|"wftrap") as n,_),args ->
        length args = (if n = "wfrel" then 3 else 2) &&
        not (can (find_term (fun u -> type_of u = ws)) t)
    | _ -> false in
  (* newest assumption first (the stack fact of the latest state), then the  *)
  (* goal; within one term, outer atoms before atoms inside their operands    *)
  let ordered tm =
    let ats = find_terms is_atom tm in
    let outer = filter (fun t -> not (exists (fun u -> u <> t && free_in t u) ats)) ats in
    outer @ subtract ats outer in
  let cands = List.concat (map (fun (_,th) -> ordered (concl th)) asl) @ ordered w in
  let decided t = exists (fun (_,th) -> let c = concl th in c = t || c = mk_neg t) asl in
  let t = try find (not o decided) cands
          with Failure _ -> failwith "WASM_F64_CASES_TAC: no undecided wfrel/wftrap atom" in
  ASM_CASES_TAC t (asl,w);;

let WASM_F64_JOIN_TAC (pc:term) (join:term) : tactic =
  ENSURES_SEQUENCE_TAC pc join;;
