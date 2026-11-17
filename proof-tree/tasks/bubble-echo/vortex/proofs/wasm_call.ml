(* ========================================================================= *)
(* Frame-free direct calls for the WASM model (lane hearth-call, 2026-11-07).*)
(*                                                                           *)
(* wasm.ml executes one function body: `call f` decodes to Wcall f and has  *)
(* no successor there (wasm_exec (Wcall f) = NONE). This file adds a        *)
(* module-level step relation                                               *)
(*                                                                           *)
(*   wasmc fs s s'  <=>  wasm s s'  \/  (a call step from s to s')          *)
(*                                                                           *)
(* where fs : num -> byte list # num # num maps a function index to its     *)
(* Code-section body bytes (as define_from_wasm binds them) and its         *)
(* parameter and result counts. A call step is big-step and frame-free: the *)
(* callee body runs under `wasm` to a final state, starting from the        *)
(* caller's memory, memory size and globals, with the parameters popped     *)
(* from the caller's stack into locals 0..np-1 and the declared locals zero *)
(* by type. On WDone the callee's results replace the parameters on the     *)
(* caller's stack and the caller continues after the call with the callee's *)
(* memory, memory size and globals; on a trap the caller traps (memory and  *)
(* globals as the callee left them). The caller's locals, labels and arity  *)
(* are untouched, so no frame stack is needed: no frame outlives the step.  *)
(*                                                                           *)
(* Scope: direct `call` only (no call_indirect, no tables); callees are     *)
(* run by `wasm`, so a callee that itself executes a call has no final      *)
(* state and the caller has no successor (one level of calls, no recursion).*)
(* A callee that runs forever gives the caller no successor either, so      *)
(* `ensures (wasmc fs)` is total correctness for the caller as for wasm.    *)
(* wasm.ml is not edited: every existing `wasm` theorem is unchanged, and a *)
(* callee's leaf theorem `ensures wasm P Q C` is used at a call site via    *)
(* WASMC_CALL_ENSURES / WASMC_CALL0_STEP. Non-call instructions step under *)
(* wasmc exactly as under wasm (WASMC_NONCALL); WASMC_STEP_TAC is the        *)
(* wasmc twin of WASM_STEP_TAC and WASMC_BIGSTEP_TAC of ARM_BIGSTEP_TAC.     *)
(* ========================================================================= *)

needs "wasm/proofs/wasm_tactics.ml";;

(* ------------------------------------------------------------------------- *)
(* Callee entry: declared locals zeroed by valtype, params into locals.      *)
(* ------------------------------------------------------------------------- *)

let wzero_of = new_definition
 `wzero_of (t:num) =
    if t = 0x7E then I64 (word 0) else if t = 0x7D then F32 (word 0)
    else if t = 0x7C then F64 (word 0) else I32 (word 0)`;;

let wdecl_vals = new_recursive_definition num_RECURSION
 `(wdecl_vals 0 (code:byte list) pc = SOME ([]:wval list)) /\
  (wdecl_vals (SUC k) code pc =
     wobind (wuleb (wdrop pc code)) (\p.
     wobind (whd (wdrop (pc + SND p) code)) (\t.
     wobind (wdecl_vals k code (pc + SND p + 1)) (\r.
       SOME (APPEND (REPLICATE (FST p) (wzero_of (val (t:byte)))) r)))))`;;

let wasm_decl_vals = new_definition
 `wasm_decl_vals (code:byte list) =
    wobind (wuleb code) (\p. wdecl_vals (FST p) code (SND p))`;;

(* args = the popped parameters, top of stack first: local k = EL (np-1-k) *)
let wcall_locals = new_definition
 `wcall_locals (args:wval list) (decls:wval list) (k:num) =
    if k < LENGTH args then EL (LENGTH args - 1 - k) args
    else if k - LENGTH args < LENGTH decls then EL (k - LENGTH args) decls
    else I32 (word 0)`;;

let wcall_entry = new_definition
 `wcall_entry (code:byte list) np nr (stk:wval list) e (decls:wval list)
              (s:wasmstate) =
    write wcode code
     (write wpc (word e)
       (write wstack []
         (write wlocals (wcall_locals (wtake np stk) decls)
           (write wlabels []
             (write warity nr
               (write wstatus WRunning s))))))`;;

(* the caller after the callee's final state c1 *)
let wcall_return = new_definition
 `wcall_return npc np (c1:wasmstate) (s:wasmstate) =
    if read wstatus c1 = WDone
    then write wpc (word npc)
          (write wstack (APPEND (read wstack c1) (wdrop np (read wstack s)))
            (write wmem (read wmem c1)
              (write wmemsize (read wmemsize c1)
                (write wglobals (read wglobals c1) s))))
    else write wstatus WTrapped
          (write wmem (read wmem c1)
            (write wmemsize (read wmemsize c1)
              (write wglobals (read wglobals c1) s)))`;;

let wasm_call = new_definition
 `wasm_call (fs:num->byte list#num#num) f npc (s:wasmstate) (s':wasmstate) <=>
    ?code np nr e decls c1.
      fs f = (code,np,nr) /\ np <= LENGTH (read wstack s) /\
      wasm_entry code = SOME e /\ wasm_decl_vals code = SOME decls /\
      RTC wasm (wcall_entry code np nr (read wstack s) e decls s) c1 /\
      ~(read wstatus c1 = WRunning) /\
      s' = wcall_return npc np c1 s`;;

let wasmc = new_definition
 `wasmc (fs:num->byte list#num#num) s s' <=>
    wasm s s' \/
    read wstatus s = WRunning /\
    ?f n. wasm_decode (read wcode s) (val (read wpc s)) = SOME (Wcall f,n) /\
          wasm_call fs f (val (read wpc s) + n) s s'`;;

(* ------------------------------------------------------------------------- *)
(* Basic facts.                                                              *)
(* ------------------------------------------------------------------------- *)

let WASM_EXEC_CALL = prove
 (`!f pc npc s. wasm_exec (Wcall f) pc npc s = NONE`,
  REWRITE_TAC[wasm_exec]);;

let WCALL_INJ = prove
 (`!a b. Wcall a = Wcall b <=> a = b`,
  REWRITE_TAC[injectivity "winstr"]);;

let WINSTR_DISTINCT = distinctness "winstr";;

let WASM_WCALL_NO_STEP = prove
 (`!s s' f n. wasm_decode (read wcode s) (val (read wpc s)) = SOME (Wcall f,n)
              ==> ~(wasm s s')`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[wasm] THEN
  ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THEN
  REWRITE_TAC[NOT_EXISTS_THM; DE_MORGAN_THM] THEN DISJ2_TAC THEN
  MAP_EVERY X_GEN_TAC [`i:winstr`; `m:num`] THEN
  ASM_CASES_TAC `Wcall f = i` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[WASM_EXEC_CALL; option_DISTINCT]);;

let WASMC_CALL_STEP = prove
 (`!fs f n s s'.
     read wstatus s = WRunning /\
     wasm_decode (read wcode s) (val (read wpc s)) = SOME (Wcall f,n)
     ==> (wasmc fs s s' <=> wasm_call fs f (val (read wpc s) + n) s s')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wasmc] THEN
  MP_TAC(SPECL [`s:wasmstate`; `s':wasmstate`; `f:num`; `n:num`]
    WASM_WCALL_NO_STEP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[option_INJ; PAIR_EQ; WCALL_INJ] THEN MESON_TAC[]);;

(* a non-call instruction: wasmc is wasm *)
let WASMC_NONCALL = prove
 (`!fs s s' mc pc i n.
     read wcode s = mc /\ read wpc s = word pc /\ pc < 2 EXP 64 /\
     wasm_decode mc pc = SOME (i,n) /\ (!f. ~(i = Wcall f))
     ==> (wasmc fs s s' <=> wasm s s')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wasmc] THEN
  ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT; option_INJ; PAIR_EQ] THEN
  ASM_MESON_TAC[]);;

let WASMC_FINAL = prove
 (`!fs s s'. ~(read wstatus s = WRunning) ==> ~(wasmc fs s s')`,
  SIMP_TAC[wasmc; WASM_FINAL]);;

(* ------------------------------------------------------------------------- *)
(* From `eventually` to a finite run, and back for final states.            *)
(* ------------------------------------------------------------------------- *)

let EVENTUALLY_RTC_EXISTS = prove
 (`!(step:A->A->bool) P s. eventually step P s ==> ?s'. RTC step s s' /\ P s'`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC eventually_INDUCT THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONJ_TAC THENL
   [MESON_TAC[RTC_REFL]; MESON_TAC[RTC_TRANS_R]]);;

let EVENTUALLY_RTC_FINAL = prove
 (`!(step:A->A->bool) P.
     (!t u. P t ==> ~step t u)
     ==> !s. eventually step P s
             ==> !s'. RTC step s s' /\ (!u. ~step s' u) ==> P s'`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC eventually_INDUCT THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONJ_TAC THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [RTC_CASES_R] o
    check (fun th -> can (term_match [] `RTC (step:A->A->bool) x y`) (concl th))) THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Reads of the callee entry state.                                          *)
(* ------------------------------------------------------------------------- *)

let WCALL_ENTRY_READS = prove
 (`!code np nr stk e decls s.
     read wcode (wcall_entry code np nr stk e decls s) = code /\
     read wpc (wcall_entry code np nr stk e decls s) = word e /\
     read wstack (wcall_entry code np nr stk e decls s) = [] /\
     read wlabels (wcall_entry code np nr stk e decls s) = [] /\
     read warity (wcall_entry code np nr stk e decls s) = nr /\
     read wstatus (wcall_entry code np nr stk e decls s) = WRunning /\
     read wlocals (wcall_entry code np nr stk e decls s) =
       wcall_locals (wtake np stk) decls /\
     read wmem (wcall_entry code np nr stk e decls s) = read wmem s /\
     read wmemsize (wcall_entry code np nr stk e decls s) = read wmemsize s /\
     read wglobals (wcall_entry code np nr stk e decls s) = read wglobals s`,
  REWRITE_TAC[wcall_entry] THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The call rule, ensures form: a leaf theorem about the callee body gives  *)
(* an ensures step for the caller at a `call f` instruction.                 *)
(* ------------------------------------------------------------------------- *)

let WASMC_CALL_ENSURES = prove
 (`!fs f code np nr e decls (P:wasmstate->bool) Q C Pre Post D n.
     ensures wasm P Q C /\
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
     ==> ensures (wasmc fs) Pre Post D`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "leaf") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fin") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pre") (LABEL_TAC "post")) THEN
  X_GEN_TAC `s:wasmstate` THEN DISCH_TAC THEN
  REMOVE_THEN "pre" (MP_TAC o SPEC `s:wasmstate`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  REMOVE_THEN "leaf" (MP_TAC o SPEC
    `wcall_entry code np nr (read wstack s) e decls s`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `c1:wasmstate` STRIP_ASSUME_TAC o
    MATCH_MP EVENTUALLY_RTC_EXISTS) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV BETA_CONV)) THEN
  ONCE_REWRITE_TAC[eventually_CASES] THEN DISJ2_TAC THEN
  SUBGOAL_THEN `!s'. wasmc fs s s' <=> wasm_call fs f (val (read wpc s) + n) s s'`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC WASMC_CALL_STEP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `wcall_return (val (read wpc s) + n) np c1 s` THEN
    REWRITE_TAC[wasm_call] THEN
    MAP_EVERY EXISTS_TAC [`code:byte list`; `np:num`; `nr:num`; `e:num`;
                          `decls:wval list`; `c1:wasmstate`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "fin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `s':wasmstate` THEN REWRITE_TAC[wasm_call; LEFT_IMP_EXISTS_THM] THEN
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
  SUBGOAL_THEN `(Q:wasmstate->bool) c1' /\
                C (wcall_entry code np nr (read wstack s) e decls s) c1'`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`wasm`; `\c. (Q:wasmstate->bool) c /\
                     C (wcall_entry code np nr (read wstack s) e decls s) c`]
      EVENTUALLY_RTC_FINAL) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[WASM_FINAL]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `wcall_entry code np nr (read wstack s) e decls s`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[WASM_FINAL];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[eventually_CASES] THEN DISJ1_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "post" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The call rule, simulation form (0 params): from a state at a `call f`,   *)
(* the callee leaf moves to a state satisfying R if every final callee     *)
(* state it allows does.                                                     *)
(* ------------------------------------------------------------------------- *)

let WASMC_CALL0_STEP = prove
 (`!fs f code nr e decls (P:wasmstate->bool) Q C n s R.
     ensures wasm P Q C /\
     (!c. Q c ==> ~(read wstatus c = WRunning)) /\
     fs f = (code,0,nr) /\ wasm_entry code = SOME e /\
     wasm_decl_vals code = SOME decls /\
     read wstatus s = WRunning /\
     wasm_decode (read wcode s) (val (read wpc s)) = SOME (Wcall f,n) /\
     P (wcall_entry code 0 nr (read wstack s) e decls s) /\
     (!c1. Q c1 /\ C (wcall_entry code 0 nr (read wstack s) e decls s) c1
           ==> R (wcall_return (val (read wpc s) + n) 0 c1 s))
     ==> eventually (wasmc fs) R s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`fs:num->byte list#num#num`; `f:num`; `code:byte list`;
    `0`; `nr:num`; `e:num`; `decls:wval list`; `P:wasmstate->bool`;
    `Q:wasmstate->bool`; `C:wasmstate->wasmstate->bool`;
    `\x:wasmstate. x = s`; `R:wasmstate->bool`;
    `\x:wasmstate y:wasmstate. T`; `n:num`] WASMC_CALL_ENSURES) THEN
  ASM_REWRITE_TAC[LE_0] THEN ANTS_TAC THENL
   [CONJ_TAC THEN REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      let c = concl th in is_eq c && rhs c = `s:wasmstate` && is_var(lhs c))) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[ensures] THEN DISCH_THEN(MP_TAC o SPEC `s:wasmstate`) THEN
    REWRITE_TAC[ETA_AX]]);;

(* ------------------------------------------------------------------------- *)
(* Callee facts computed from the bytes: entry pc and declared locals.      *)
(* ------------------------------------------------------------------------- *)

let WDECL_VALS_ALT = prove
 (`!k code pc. wdecl_vals k (code:byte list) pc =
     if k = 0 then SOME [] else
     wobind (wuleb (wdrop pc code)) (\p.
     wobind (whd (wdrop (pc + SND p) code)) (\t.
     wobind (wdecl_vals (k - 1) code (pc + SND p + 1)) (\r.
       SOME (APPEND (REPLICATE (FST p) (wzero_of (val (t:byte)))) r))))`,
  INDUCT_TAC THEN REWRITE_TAC[wdecl_vals; NOT_SUC; SUC_SUB1]);;

let REPLICATE_ALT = prove
 (`!n (x:A). REPLICATE n x = if n = 0 then [] else CONS x (REPLICATE (n - 1) x)`,
  INDUCT_TAC THEN REWRITE_TAC[REPLICATE; NOT_SUC; SUC_SUB1]);;

let wasm_call_compset =
  wasm_mk_decode_compset [WDECL_VALS_ALT; wasm_decl_vals; wzero_of;
                          REPLICATE_ALT; APPEND];;

let WASM_CALL_CONV = Compute.WEAK_CBV_CONV wasm_call_compset;;

(* |- wasm_entry mc = SOME e /\ wasm_decl_vals mc = SOME decls *)
let WASM_CALLEE_RULE (mc_def:thm) =
  let mc = lhs(concl mc_def) in
  let ev t = (ONCE_REWRITE_CONV[mc_def] THENC WASM_CALL_CONV) (mk_comb(t,mc)) in
  CONJ (ev `wasm_entry`) (ev `wasm_decl_vals`);;

(* ------------------------------------------------------------------------- *)
(* Return-state algebra for 0-param 0-result callees.                       *)
(* ------------------------------------------------------------------------- *)

let WSVC tm = REWRITE_RULE[strongly_valid_component] (STRONGLY_VALID_COMPONENT_CONV tm);;
let WMEM_SVC = WSVC `strongly_valid_component (wmem:(wasmstate,int64->byte)component)`;;
let WSTACK_SVC = WSVC `strongly_valid_component (wstack:(wasmstate,wval list)component)`;;
let WMEMSIZE_SVC = WSVC `strongly_valid_component (wmemsize:(wasmstate,num)component)`;;
let WGLOBALS_SVC = WSVC `strongly_valid_component (wglobals:(wasmstate,num->wval)component)`;;

(* a done callee that left the stack empty and memory size and globals as  *)
(* they were: the caller moves on with the callee's memory                  *)
let WCALL_RETURN0 = prove
 (`!npc c1 s.
     read wstatus c1 = WDone /\ read wstack c1 = [] /\
     read wmemsize c1 = read wmemsize s /\ read wglobals c1 = read wglobals s
     ==> wcall_return npc 0 c1 s = write wpc (word npc) (write wmem (read wmem c1) s)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[wcall_return; APPEND; WDROP_0] THEN
  REWRITE_TAC[WGLOBALS_SVC; WMEMSIZE_SVC] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `read wstack s = read wstack (write wmem (read wmem c1) s)`
    SUBST1_TAC THENL
   [CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN REFL_TAC;
    REWRITE_TAC[WSTACK_SVC]]);;

(* the callee's memory as a chain of writes of the caller's memory becomes  *)
(* a chain of component writes on the caller state, for frames              *)
let WCALL_WRITE_MEM1 = prove
 (`!(d:(int64->byte,A)component) y (s:wasmstate).
     write wmem (write d y (read wmem s)) s = write (wmem :> d) y s`,
  REWRITE_TAC[WRITE_COMPONENT_COMPOSE]);;

let WCALL_WRITE_MEM2 = prove
 (`!(d1:(int64->byte,A)component) (d2:(int64->byte,B)component) y1 y2 (s:wasmstate).
     write wmem (write d2 y2 (write d1 y1 (read wmem s))) s =
     write (wmem :> d2) y2 (write (wmem :> d1) y1 s)`,
  REWRITE_TAC[WRITE_COMPONENT_COMPOSE] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[WMEM_SVC]);;

(* ------------------------------------------------------------------------- *)
(* Stepping a non-call instruction under wasmc (twin of WASM_STEP_TAC).     *)
(* ------------------------------------------------------------------------- *)

let WASMC_NONCALL_TH (i:term) =
  prove(mk_forall(`f:num`, mk_neg(mk_eq(i, `Wcall f`))),
        GEN_TAC THEN REWRITE_TAC[WINSTR_DISTINCT; GSYM WINSTR_DISTINCT]);;

(* tm = `wasmc fs s s'` *)
let WASMC_CONV (decode_ths:thm option array) (extra:thm list) (ths:thm list) tm =
  let fsm,s' = dest_comb tm in
  let fsm,s = dest_comb fsm in
  let fs = rand fsm in
  let eth = WASM_CONV decode_ths extra ths (mk_comb(mk_comb(`wasm`,s),s')) in
  let pc_th = find_read_th "wpc" s ths
  and code_th = find_read_th "wcode" s ths in
  let pc_num = rand(rhs(concl pc_th)) in
  let pc = dest_small_numeral pc_num in
  let dth = match (try decode_ths.(pc) with _ -> None) with
      Some th -> th | None -> failwith ("WASMC_CONV: no decode at pc "^string_of_int pc) in
  let i,n = dest_pair(rand(rhs(concl dth))) in
  let lt_th = EQT_ELIM(NUM_REDUCE_CONV(mk_binary "<" (pc_num,`2 EXP 64`))) in
  let nth = MP (ISPECL [fs; s; s'; rhs(concl code_th); pc_num; i; n] WASMC_NONCALL)
               (end_itlist CONJ [code_th; pc_th; lt_th; dth; WASMC_NONCALL_TH i]) in
  TRANS nth eth;;

let WASMC_BASIC_STEP_TAC =
  let ws_ty = `:wasmstate` in
  fun decode_ths extra sname (asl,w) ->
    let sv = rand w and sv' = mk_var(sname,ws_ty) in
    let stepr = rand(rator(rator w)) in
    let atm = mk_comb(mk_comb(stepr,sv),sv') in
    let eth = WASMC_CONV decode_ths extra (map snd asl) atm in
    let r = rhs(concl eth) in
    if not (is_eq r && rand r = sv') then
      failwith ("WASMC_BASIC_STEP_TAC: step did not reduce to a state update: "^
                string_of_term r) else
    (GEN_REWRITE_TAC I [eventually_CASES] THEN DISJ2_TAC THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC BINDER_CONV [eth] THEN CONV_TAC EXISTS_NONTRIVIAL_CONV;
      X_GEN_TAC sv' THEN GEN_REWRITE_TAC LAND_CONV [eth]]) (asl,w);;

let WASMC_STEP_TAC (_,decode_ths) extra sname =
  WASMC_BASIC_STEP_TAC decode_ths extra sname THEN
  WASM_MEM_UPDATE_TAC THEN
  ASSUMPTION_STATE_UPDATE_TAC THEN
  MAYCHANGE_STATE_UPDATE_TAC THEN
  DISCH_THEN(fun th ->
    let thl = STATE_UPDATE_NEW_RULE th in
    if thl = [] then ALL_TAC else
    MP_TAC(end_itlist CONJ thl) THEN
    CONV_TAC(LAND_CONV(DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV))) THEN
    STRIP_TAC);;

let WASMC_STEPS_TAC execth snums =
  MAP_EVERY (fun s -> WASMC_STEP_TAC execth [] s THEN DISCARD_OLD_WASMSTATE_TAC s)
            (statenames "s" snums);;

(* ------------------------------------------------------------------------- *)
(* Through a caller-level ensures lemma (e.g. a call site) in the middle of *)
(* a simulation: the twin of ARM_BIGSTEP_TAC. Goal:                          *)
(*   ensures (wasmc fs) P Q C ==> eventually (wasmc fs) R s                 *)
(* Leaves (1) P s and (2) the continuation at the new state sname, with Q's *)
(* conjuncts assumed and the MAYCHANGE frame C folded into the running      *)
(* MAYCHANGE assumption (so ENSURES_FINAL_STATE_TAC accounts for it); facts *)
(* about components the frame leaves alone are carried to sname. Old-state  *)
(* facts are not discarded here (callers choose how memory is named).       *)
(* ------------------------------------------------------------------------- *)

let WASMC_BIGSTEP_LEMMA = prove
 (`P s /\ (!s':S. Q s' /\ C s s' ==> eventually step R s')
   ==> ensures step P Q C ==> eventually step R s`,
  STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [ensures] THEN
  DISCH_THEN(MP_TAC o SPEC `s:S`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[]
   `(!s:S. eventually step P s ==> eventually step Q s)
    ==> eventually step P s ==> eventually step Q s`) THEN
  GEN_REWRITE_TAC I [EVENTUALLY_IMP_EVENTUALLY] THEN
  ASM_REWRITE_TAC[]);;

let WASMC_BIGSTEP_TAC sname =
  let sv = mk_var(sname,`:wasmstate`) in
  MATCH_MP_TAC WASMC_BIGSTEP_LEMMA THEN CONJ_TAC THENL
   [BETA_TAC THEN ASM_REWRITE_TAC[];
    BETA_TAC THEN X_GEN_TAC sv THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [MAYCHANGE; SEQ_ID] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [GSYM SEQ_ASSOC] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_SEQ] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_THM] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    ASSUMPTION_STATE_UPDATE_TAC THEN MAYCHANGE_STATE_UPDATE_TAC THEN
    DISCH_THEN(K ALL_TAC)];;
