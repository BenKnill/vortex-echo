(* ========================================================================= *)
(* Vortex chain rung C5 part 2b (lane vortex-chain-20261111-142342 c5, Claude *)
(* Opus 5.5, 2026-11-13), layer B: inline call steps, the f33 step/forget    *)
(* driver, memory and counter lemmas, and VA1_C5_CELL (one table cell, pc    *)
(* 433 -> 1187). The call-step block is copied from hol-hearth 6adb41ce      *)
(* wasm/demos/call_params.ml (the CP_ tactics) and wasm/proofs/wasm_call.ml *)
(* (WASMC_MEM_UPDATE_TAC, WASMC_GEN_STATE_TAC); C5_DONE_CONT adds naming of *)
(* the callee entry memory. Stable layer: never edit.                        *)
(* ========================================================================= *)
needs "chain_c5_punct_a.ml";;
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

let CP_CALL_STEP = prove
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
           ==> eventually (wasmc fs) R (wcall_return (val (read wpc s) + n) np c1 s))
     ==> eventually (wasmc fs) R s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`fs:num->byte list#num#num`; `f:num`; `code:byte list`;
    `np:num`; `nr:num`; `e:num`; `decls:wval list`; `P:wasmstate->bool`;
    `Q:wasmstate->bool`; `C:wasmstate->wasmstate->bool`;
    `\x:wasmstate. x = s`; `eventually (wasmc fs) R`;
    `\x:wasmstate y:wasmstate. T`; `n:num`] WASMC_CALL_ENSURES) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THEN REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      let c = concl th in is_eq c && rhs c = `s:wasmstate` && is_var(lhs c))) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[ensures] THEN DISCH_THEN(MP_TAC o SPEC `s:wasmstate`) THEN
    REWRITE_TAC[ETA_AX; EVENTUALLY_EVENTUALLY]]);;

let CP_EL_ALT = prove
 (`!n (l:A list). EL n l = if n = 0 then HD l else EL (n - 1) (TL l)`,
  INDUCT_TAC THEN REWRITE_TAC[EL; NOT_SUC; SUC_SUB1]);;

let CP_WTAKE_0 = prove
 (`!l:A list. wtake 0 l = []`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[wtake]);;

let cp_call_compset =
  wasm_mk_decode_compset [wcall_locals; CP_EL_ALT; APPEND; CP_WTAKE_0; WDROP_0];;

let CP_CALL_LIST_CONV = Compute.WEAK_CBV_CONV cp_call_compset;;

let CP_LOCALS_EVAL_CONV tm =
  match strip_comb tm with
    Const("wcall_locals",_),[_;_;_] -> CHANGED_CONV CP_CALL_LIST_CONV tm
  | Const("wtake",_),[_;_] -> CHANGED_CONV CP_CALL_LIST_CONV tm
  | Const("wdrop",_),[_;_] -> CHANGED_CONV CP_CALL_LIST_CONV tm
  | Const("APPEND",_),[_;_] -> CHANGED_CONV CP_CALL_LIST_CONV tm
  | _ -> failwith "CP_LOCALS_EVAL_CONV";;

let CP_WCALL_RETURN_N = prove
 (`!npc np c1 s.
     read wstatus c1 = WDone /\
     read wmemsize c1 = read wmemsize s /\ read wglobals c1 = read wglobals s
     ==> wcall_return npc np c1 s =
         write wpc (word npc)
          (write wstack (APPEND (read wstack c1) (wdrop np (read wstack s)))
            (write wmem (read wmem c1) s))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[wcall_return] THEN
  REWRITE_TAC[WGLOBALS_SVC; WMEMSIZE_SVC]);;

let CP_ENTRY_TAC =
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wlocal; wglobal; READ_COMPONENT_COMPOSE; READ_ELEMENT]) THEN
  REWRITE_TAC[wlocal; wglobal; READ_COMPONENT_COMPOSE; WCALL_ENTRY_READS] THEN
  REWRITE_TAC[READ_ELEMENT] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV CP_LOCALS_EVAL_CONV) THEN
  ASM_REWRITE_TAC[];;

let CP_GEN_EVENTUALLY_STATE_TAC (sname:string) : tactic = fun (asl,w) ->
  let x = rand w in
  let sv = mk_var(sname,`:wasmstate`) in
  let gth = mk_forall(sv, mk_imp(mk_eq(x,sv), mk_comb(rator w, sv))) in
  (SUBGOAL_THEN gth (fun th -> MATCH_MP_TAC th THEN REFL_TAC) THEN
   X_GEN_TAC sv) (asl,w);;

(* CP_CALL_GEN_TAC execth lth cth cont on a goal `eventually (wasmc fs) R s`  *)
(* with s at `call f` (decode from execth), read wcode/wpc/wstatus/wstack   *)
(* facts of s and fs f = (code,np,nr) among the assumptions; lth =          *)
(* |- ensures wasm P Q C (the callee leaf, instantiated), cth =             *)
(* WASM_CALLEE_RULE code_def. It proves the callee precondition at the      *)
(* entry state and hands the return to cont.                                 *)
let CP_CALL_GEN_TAC (_,decode_ths) (lth:thm)
    (cth:thm) (cont:term->term->term->term->term->tactic) : tactic =
  fun (asl,w) ->
    let s = rand w in
    let stepr = rand(rator(rator w)) in
    let fs = rand stepr in
    let rr = rand(rator w) in
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
        Some th -> th | None -> failwith "CP_CALL_TAC: no decode at pc" in
    let ins,n = dest_pair(rand(rhs(concl dec))) in
    let f = rand ins in
    let fsf = mk_comb(fs,f) in
    let fsth = try find (fun th -> let c = concl th in is_eq c && lhs c = fsf) ths
               with Failure _ -> failwith "CP_CALL_TAC: no fs f = .. assumption" in
    let _,npnr = dest_pair(rhs(concl fsth)) in
    let np,nr = dest_pair npnr in
    let sth = ISPECL [fs; f; code; np; nr; e; decls; pp; qq; cc; n; s; rr] CP_CALL_STEP in
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
       CP_ENTRY_TAC;
       cont s pc_num n np c0tm]) (asl,w);;

(* after a callee that returned (WDone): continue at sname = the caller     *)
(* with the results in place of the parameters and the callee's memory; the *)
(* callee's frame must not name wmemsize or wglobals                        *)
let CP_DONE_CONT (sname:string) s pc_num n np c0tm : tactic =
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
         MATCH_MP_TAC CP_WCALL_RETURN_N THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
       FIRST_X_ASSUM(fun th -> if is_rmem_c1 th then REWRITE_TAC[th] else NO_TAC) THEN
       REWRITE_TAC[WMEM_SVC; WCALL_WRITE_MEM1; WCALL_WRITE_MEM2] THEN
       ASM_REWRITE_TAC[] THEN
       CONV_TAC(ONCE_DEPTH_CONV CP_LOCALS_EVAL_CONV) THEN
       CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
       WASMC_GEN_STATE_TAC sv' THEN
       X_GEN_TAC sv' THEN
       WASMC_MEM_UPDATE_TAC THEN ASSUMPTION_STATE_UPDATE_TAC THEN
       MAYCHANGE_STATE_UPDATE_TAC THEN
       DISCH_THEN(fun th ->
         let thl = STATE_UPDATE_NEW_RULE th in
         if thl = [] then ALL_TAC else MP_TAC(end_itlist CONJ thl) THEN STRIP_TAC) THEN
       DISCARD_OLD_WASMSTATE_TAC sname THEN WASM_COMPACT_HYPS_TAC;;

(* after a callee that trapped: the caller traps with the callee's memory,  *)
(* memory size and globals (the caller's frame must allow wstatus, wmem,    *)
(* wmemsize and wglobals)                                                    *)
let CP_TRAP_CONT (sname:string) s pc_num n np c0tm : tactic =
  X_GEN_TAC `c1:wasmstate` THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (STRIP_ASSUME_TAC o CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) (K ALL_TAC)) THEN
  REWRITE_TAC[wcall_return] THEN
  ASM_REWRITE_TAC[distinctness "wstat"] THEN
  CP_GEN_EVENTUALLY_STATE_TAC sname THEN
  ASSUMPTION_STATE_UPDATE_TAC THEN MAYCHANGE_STATE_UPDATE_TAC THEN
  DISCH_THEN(fun th ->
    let thl = STATE_UPDATE_NEW_RULE th in
    if thl = [] then ALL_TAC else MP_TAC(end_itlist CONJ thl) THEN STRIP_TAC) THEN
  WASM_COMPACT_HYPS_TAC;;

let CP_CALL_TAC execth lth cth sname =
  CP_CALL_GEN_TAC execth lth cth (CP_DONE_CONT sname);;

let CP_CALL_TRAP_TAC execth lth cth sname =
  CP_CALL_GEN_TAC execth lth cth (CP_TRAP_CONT sname);;

(* ------------------------------------------------------------------------- *)
(* (a) Two distinct parameters, a scalar result, an underlying caller stack; *)
(* (b) zeroed typed locals.                                                   *)
(* ------------------------------------------------------------------------- *)


let C5_DONE_CONT (sname:string) s pc_num n np c0tm : tactic =
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
       (fun (asl,w) ->
          let mth = find_read_th "wmem" s (map snd asl) in
          RULE_ASSUM_TAC(fun th -> let c = concl th in
            if is_eq c && lhs c = `read wmem (c0:wasmstate)` then REWRITE_RULE[mth] th else th) (asl,w)) THEN
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
         MATCH_MP_TAC CP_WCALL_RETURN_N THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
       FIRST_X_ASSUM(fun th -> if is_rmem_c1 th then REWRITE_TAC[th] else NO_TAC) THEN
       REWRITE_TAC[WMEM_SVC; WCALL_WRITE_MEM1; WCALL_WRITE_MEM2] THEN
       ASM_REWRITE_TAC[] THEN
       CONV_TAC(ONCE_DEPTH_CONV CP_LOCALS_EVAL_CONV) THEN
       CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
       WASMC_GEN_STATE_TAC sv' THEN
       X_GEN_TAC sv' THEN
       WASMC_MEM_UPDATE_TAC THEN ASSUMPTION_STATE_UPDATE_TAC THEN
       MAYCHANGE_STATE_UPDATE_TAC THEN
       DISCH_THEN(fun th ->
         let thl = STATE_UPDATE_NEW_RULE th in
         if thl = [] then ALL_TAC else MP_TAC(end_itlist CONJ thl) THEN STRIP_TAC) THEN
       DISCARD_OLD_WASMSTATE_TAC sname THEN WASM_COMPACT_HYPS_TAC;;

(* after a callee that trapped: the caller traps with the callee's memory,  *)
(* memory size and globals (the caller's frame must allow wstatus, wmem,    *)
(* wmemsize and wglobals)                                                    *)

let C5_CALL_TAC execth lth cth sname = CP_CALL_GEN_TAC execth lth cth (C5_DONE_CONT sname);;
let C5_F32_CALL_TAC sname : tactic = fun (asl,w) ->
  let s = rand w in
  let stk = rhs(concl(find_read_th "wstack" s (map snd asl))) in
  let k = rand(rand(rator stk)) and x = rand(rand(rator(rand stk))) in
  C5_CALL_TAC C5_F33_EXEC (SPECL [x;k] VA1_F32_CORRECT) VA1_F32_CALLEE sname (asl,w);;
let C5_F34_CALL_TAC sname = C5_CALL_TAC C5_F33_EXEC VA1_F34_CORRECT VA1_F34_CALLEE sname;;

let c5_extra = ref ([]:thm list);;
let C5T_STEP exec sname : tactic = fun (asl,w) ->
  let s = rand w in
  let mths = map snd (filter (fun (_,th) -> c5_is_rd `wmem` s (concl th)) asl) in
  let sf = map snd (filter (fun (_,th) -> let c = concl th in
      c5_statefree c && not (is_forall c) && not (is_imp c)) asl) in
  (WASMC_BASIC_STEP_TAC (snd exec) (READ_COMPONENT_COMPOSE :: (!c5_extra @ mths @ sf)) sname THEN
   WASMC_MEM_UPDATE_TAC THEN ASSUMPTION_STATE_UPDATE_TAC THEN MAYCHANGE_STATE_UPDATE_TAC THEN
   DISCH_THEN(fun th ->
     let thl = STATE_UPDATE_NEW_RULE th in
     if thl = [] then ALL_TAC else
     MP_TAC(end_itlist CONJ thl) THEN
     CONV_TAC(LAND_CONV(DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV))) THEN STRIP_TAC) THEN
   DISCARD_OLD_WASMSTATE_TAC sname) (asl,w);;
let VA1_C5_OR3 = prove
 (`!a0 a1 a2:int32. ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0) ==> ~(word_or (word_or a1 a0) a2 = word 0)`,
  REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN BITBLAST_TAC);;

let c5_pc asl s = dest_small_numeral(rand(rhs(concl(find_read_th "wpc" s (map snd asl)))));;
let c5_running asl s = try rhs(concl(find_read_th "wstatus" s (map snd asl))) = `WRunning` with Failure _ -> false;;
let c5_call_pcs32 = [220;232;256;268;363;378;451;466];;
let rec c5_tsize t = if is_numeral t then 1 else match t with Comb(a,b) -> c5_tsize a + c5_tsize b | Abs(_,b) -> 1 + c5_tsize b | _ -> 1;;
let c5_fthresh = ref 25;;
let c5_vctr = ref 0;;
(* forget big float payloads of the current state's stack and locals: generalize them to fresh variables *)
let C5_FORGET_TAC : tactic = fun (asl,w) ->
  let s = rand w in
  let vals = List.concat (map (fun (_,th) -> let c = concl th in
     if is_eq c && (match lhs c with Comb(Comb(Const("read",_),comp),s') ->
                      s' = s && (comp = `wstack` || (is_comb comp && rator comp = `wlocal`)) | _ -> false)
     then (let r = rhs c in
           let elems = if is_list r then dest_list r else [r] in
           mapfilter (fun e -> let h,a = strip_comb e in
                        if h = `F64` && length a = 1 then hd a else fail()) elems)
     else []) asl) in
  let big = setify (filter (fun v -> c5_tsize v > !c5_fthresh && frees v <> []) vals) in
  let big = sort (fun a b -> c5_tsize a > c5_tsize b) big in
  MAP_EVERY (fun t -> fun (asl,w) ->
     if not (exists (fun (_,th) -> free_in t (concl th)) asl) then ALL_TAC (asl,w) else
     (incr c5_vctr;
      let v = mk_var("fv" ^ string_of_int !c5_vctr, type_of t) in
      let hs = filter (fun (_,th) -> free_in t (concl th)) asl in
      (MAP_EVERY (fun (_,th) -> UNDISCH_TAC (concl th)) hs THEN
       SPEC_TAC(t,v) THEN GEN_TAC THEN REPEAT DISCH_TAC) (asl,w))) big (asl,w);;
let rec C5_DRIVE stops : tactic = fun (asl,w) ->
  let s = rand w in
  if not (c5_running asl s) then ALL_TAC (asl,w) else
  let pc = c5_pc asl s in
  if mem pc stops then ALL_TAC (asl,w) else
  (incr c5_ctr; let sn = "r" ^ string_of_int !c5_ctr in
   (if pc = 180 then C5_F34_CALL_TAC sn
    else if mem pc c5_call_pcs32 then C5_F32_CALL_TAC sn
    else C5T_STEP C5_F33_EXEC sn) THEN C5_FORGET_TAC THEN C5_DRIVE stops) (asl,w);;

let VA1_C5_FRAME_W32 = prove
 (`!m0 m b (y:int32). va1_f33_frame m0 m /\ 65536 <= b /\ b + 4 <= 1114112
     ==> va1_f33_frame m0 (write (bytes32 (word b)) y m)`,
  REWRITE_TAC[va1_f33_frame] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:num`; `b:num`; `y:int32`; `m:int64->byte`] VA1_C5_B8_W32_OTHER) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;
let VA1_C5_W4_ADD = prove
 (`!i. word_add (word (4 * i)) (word 4):int32 = word (4 * (i + 1))`,
  REWRITE_TAC[GSYM WORD_ADD; ARITH_RULE `4 * i + 4 = 4 * (i + 1)`]);;
let VA1_C5_W4_NE = prove
 (`!i. 0 < i /\ i < 128 ==> ~(word (4 * i):int32 = word 512)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int32->num`) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `(4 * i) MOD 4294967296 = 4 * i` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;
let VA1_C5_K_NE = prove
 (`!k. 0 < k /\ k < 2048 ==> ~(word k:int32 = word 2048)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int32->num`) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `k MOD 4294967296 = k` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;
let VA1_C5_ADDR = prove
 (`!k j. k < 2048 /\ j < 128
     ==> val (word_add (word (65536 + 512 * k)) (word (4 * j)):int32) = 65536 + 512 * k + 4 * j /\
         (65536 + 512 * k + 4 * j + 4 <= 4194304 <=> T)`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_32; GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let va1_c5_iv = new_definition
 `va1_c5_iv (a0:int32) (a1:int32) (a2:int32) (m:int64->byte) (k:num) (i:num) (s:wasmstate) <=>
    read wcode s = va1_puncture_mc /\ read wstatus s = WRunning /\
    read wstack s = (if read wpc s = word 433 then [] else [I32 (word (bitval (~(word (4 * i) = (word 512:int32)))))]) /\
    read wlabels s = [0,431,0; 0,333,0; 0,1241,0] /\ read warity s = 1 /\ read wmemsize s = 4194304 /\
    read (wglobal 0) s = I32 (word 16288) /\ read (wlocal 0) s = I32 a0 /\ read (wlocal 1) s = I32 a1 /\
    read (wlocal 2) s = I32 a2 /\ read (wlocal 3) s = I32 (word 16288) /\
    read (wlocal 4) s = I32 (word (4 * i)) /\ read (wlocal 11) s = I32 (word (65536 + 512 * k)) /\
    read (wlocal 23) s = I32 (word k) /\ va1_f33_frame m (read wmem s) /\
    (?v. read (wlocal 8) s = F64 v) /\ (?v. read (wlocal 9) s = F64 v) /\ (?v. read (wlocal 10) s = F64 v) /\
    (?v. read (wlocal 12) s = F64 v) /\ (?v. read (wlocal 13) s = F64 v) /\ (?v. read (wlocal 14) s = F64 v) /\
    (?v. read (wlocal 15) s = F64 v) /\ (?v. read (wlocal 16) s = F64 v) /\ (?v. read (wlocal 17) s = F64 v) /\
    (?v. read (wlocal 18) s = F64 v) /\ (?v. read (wlocal 19) s = F64 v) /\ (?v. read (wlocal 20) s = F64 v) /\
    (?v. read (wlocal 21) s = F64 v) /\ (?v. read (wlocal 22) s = F64 v) /\ (?v. read (wlocal 24) s = F64 v) /\
    (?v. read (wlocal 25) s = F64 v) /\ (?v. read (wlocal 26) s = F64 v) /\ (?v. read (wlocal 27) s = F64 v)`;;

(* cell assertions: state at pc with stack/labels text, cell indices kk jj (terms as text), float locals fl *)
let c5_A pc stk lbl kk jj fl =
  parse_term (Printf.sprintf
  "\\s. read wcode s = va1_puncture_mc /\\ read wpc s = word %d /\\ read wstatus s = WRunning /\\
   %s /\\ read wlabels s = %s /\\ read warity s = 1 /\\ read wmemsize s = 4194304 /\\
   read (wglobal 0) s = I32 (word 16288) /\\ read (wlocal 0) s = I32 a0 /\\ read (wlocal 1) s = I32 a1 /\\
   read (wlocal 2) s = I32 a2 /\\ read (wlocal 3) s = I32 (word 16288) /\\
   read (wlocal 4) s = I32 (word (4 * %s)) /\\ read (wlocal 11) s = I32 (word (65536 + 512 * %s)) /\\
   read (wlocal 23) s = I32 (word %s) /\\ va1_f33_frame m (read wmem s)%s"
   pc stk lbl jj kk kk
   (String.concat "" (map (fun l -> Printf.sprintf " /\\ (?v. read (wlocal %d) s = F64 v)" l) fl)));;
let c5_L3 = "[0,431,0; 0,333,0; 0,1241,0]";;
let c5_inner_f64 = [8;9;10;12;13;14;15;16;17;18;19;20;21;22;24;25;26;27];;
let c5_cell_frame = `MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
  MAYCHANGE [wlocals] ,, MAYCHANGE [wglobal 0] ,, MAYCHANGE [wmem]`;;
(* start a segment: beta, split conjuncts, choose existentials, name memory *)
let C5_SEG_INIT_TAC =
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[va1_c5_iv]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_TAC o check (is_exists o concl))) THEN
  (fun (asl,w) -> let pth = find_read_th "wpc" `s0:wasmstate` (map snd asl) in
     RULE_ASSUM_TAC(fun th -> if can (find_term is_cond) (concl th) then
        CONV_RULE(DEPTH_CONV WORD_RED_CONV) (REWRITE_RULE[pth] th) else th) (asl,w)) THEN
  ABBREV_TAC `mm = read wmem (s0:wasmstate)`;;
(* close: existentials from assumptions *)
let C5_EX_TAC : tactic = fun (asl,w) ->
  let vs,b = strip_exists w in
  if vs = [] then failwith "C5_EX_TAC" else
  let lc = subtract (frees b) vs in
  let th = find (fun th -> can (term_match lc b) (concl th)) (map snd asl) in
  let _,ins,_ = term_match lc b (concl th) in
  (MAP_EVERY (fun v -> EXISTS_TAC (rev_assoc v ins)) vs THEN ACCEPT_TAC th) (asl,w);;
let C5_REFL_EX_TAC : tactic = fun (asl,w) ->
  let vs,b = strip_exists w in
  let _,ins,_ = term_match (subtract (frees b) vs) (rhs b) (lhs b) in
  (MAP_EVERY (fun v -> EXISTS_TAC (rev_assoc v ins)) vs THEN REFL_TAC) (asl,w);;
let C5_SEG_CLOSE_TAC =
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[va1_c5_iv] THEN REPEAT CONJ_TAC THEN TRY C5_EX_TAC THEN
  ASM_REWRITE_TAC[VA1_C5_W4_ADD] THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
  TRY C5_REFL_EX_TAC THEN
  TRY(ASM_REWRITE_TAC[] THEN TRY COND_CASES_TAC THEN REWRITE_TAC[CONS_11; injectivity "wval"] THEN MESON_TAC[]) THEN
  TRY(MATCH_MP_TAC VA1_C5_FRAME_W32 THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let C5_GUARD_TAC : tactic = fun (asl,w) ->
  let news = mapfilter (fun (_,th) -> let t = MATCH_MP VA1_F64_TRUNC_GUARD th in
     if exists (fun (_,a) -> concl a = concl t) asl then fail() else t) asl in
  MAP_EVERY ASSUME_TAC news (asl,w);;
let rec C5_DRIVE4 stops : tactic = fun (asl,w) ->
  let s = rand w in
  if not (c5_running asl s) then ALL_TAC (asl,w) else
  let pc = c5_pc asl s in
  if mem pc stops then ALL_TAC (asl,w) else
  (incr c5_ctr; let sn = "r" ^ string_of_int !c5_ctr in
   let one = if pc = 180 then C5_F34_CALL_TAC sn
     else if mem pc c5_call_pcs32 then C5_F32_CALL_TAC sn
     else C5T_STEP C5_F33_EXEC sn in
   C5_GUARD_TAC THEN (one ORELSE (WASM_F64_CASES_TAC THEN one)) THEN C5_FORGET_TAC THEN C5_DRIVE4 stops) (asl,w);;
let c5_ngoals_tac (tac:tactic) : tactic = fun g -> tac g;;
let C5_SEG_TAC stop =
  C5_SEG_INIT_TAC THEN
  MP_TAC(SPECL [`k:num`; `i:num`] VA1_C5_ADDR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C5_DRIVE4 [stop] THEN C5_SEG_CLOSE_TAC;;

let c5_mid pc stk lbl fl ext =
  let t = c5_A pc stk lbl "k" "i" fl in
  let s,b = dest_abs t in
  let c1,r = dest_conj b in let _,r2 = dest_conj r in
  let b' = mk_conj(c1, r2) in
  if ext = "" then mk_abs(s,b') else mk_abs(s, mk_conj(b', parse_term ext));;
let c5_f559 = [5;28;29;30] @ c5_inner_f64;;
let c5_f629 = [5;6;7;28;29;30;31] @ c5_inner_f64;;
let c5_L5 = "[0,1088,0; 0,1152,0; 0,431,0; 0,333,0; 0,1241,0]";;
let C5_SEQ_TAC pc asrt =
  let s,b = dest_abs asrt in
  let q = mk_abs(s, mk_conj(mk_eq(mk_comb(`read wpc`,s), mk_comb(`word:num->int64`, mk_small_numeral pc)), b)) in
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN EXISTS_TAC q THEN
  CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; CONJ_TAC];;
let VA1_C5_CELL = prove
 (`!fs a0 a1 a2 m k i. fs 32 = (va1_f32_mc,2,1) /\ k < 2048 /\ i < 128
     ==> ensures (wasmc fs)
          (\s. read wpc s = word 433 /\ va1_c5_iv a0 a1 a2 m k i s)
          (\s. read wpc s = word 1187 /\ va1_c5_iv a0 a1 a2 m k (i + 1) s)
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocals] ,, MAYCHANGE [wglobal 0] ,, MAYCHANGE [wmem])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C5_SEQ_TAC 559 (c5_mid 559 "read wstack s = []" c5_L3 c5_f559 "") THENL [C5_SEG_TAC 559; ALL_TAC] THEN
  C5_SEQ_TAC 629 (c5_mid 629 "read wstack s = []" c5_L3 c5_f629 "") THENL [C5_SEG_TAC 629; ALL_TAC] THEN
  C5_SEQ_TAC 994 (c5_mid 994 "(?p q. read wstack s = [F64 p; F64 q])" c5_L5 c5_f629 "") THENL [C5_SEG_TAC 994; ALL_TAC] THEN
  C5_SEQ_TAC 1152 (c5_mid 1152 "read wstack s = []" c5_L3 c5_f629 "?v. read (wlocal 32) s = I32 v") THENL [C5_SEG_TAC 1152; C5_SEG_TAC 1187]);;
