(* Vortex chain rung C5 (lane vortex-chain-20261111-142342 c5, Claude Opus 5.5, 2026-11-13): tactics.            *)
(* The five tactics below are copied VERBATIM from hol-hearth main 6adb41ce wasm/proofs/wasm_frames.ml (tooling     *)
(* H4/H5, PR #178), which is deployed on the shared runtime but cannot be loaded here: it needs main's full        *)
(* wasm_call.ml, while the vortex chain uses its own prefix copy (wasm_call.ml 091a9057) and loading both would    *)
(* redefine wasmc. They are OCaml tactics only (no constants, no theorems), built on the prefix's WASMC_BIGSTEP_TAC *)
(* and the profile's DISCARD_OLD_WASMSTATE_TAC / WASM_COMPACT_HYPS_TAC / ENSURES_WHILE_UP_TAC / ENSURES_SEQUENCE_TAC.*)
needs "chain_c5_dec.ml";;

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
