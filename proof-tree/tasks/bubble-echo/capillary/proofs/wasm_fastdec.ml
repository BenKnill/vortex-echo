(* ========================================================================= *)
(* Bubble Echo stage 2: linear-cost decode tables for long WASM bodies.     *)
(* ========================================================================= *)

needs "wasm/proofs/wasm_tactics.ml";;

(* ------------------------------------------------------------------------- *)
(* Linear-cost decode tables for long WASM bodies.                           *)
(*                                                                           *)
(* WASM_MK_EXEC_RULE evaluates wasm_decode mc pc on the unfolded byte list,  *)
(* so each wdrop pc costs pc numeral steps and each block scan repeats them  *)
(* (quadratic; minutes for an 800-byte body). Here the code constant mc is   *)
(* never unfolded: the compset gets one theorem |- wdrop k mc = suffix_k     *)
(* per byte offset k (each derived from the previous by WDROP_NEXT) and      *)
(* |- LENGTH mc = n. The resulting theorems are the same statements          *)
(* |- wasm_decode mc pc = SOME (i,len), proved by kernel inference.          *)
(* ------------------------------------------------------------------------- *)

let WDROP_0 = prove
 (`!l:A list. wdrop 0 l = l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[wdrop]);;

let WDROP_NEXT = prove
 (`!l n (x:A) y. wdrop n l = CONS x y ==> wdrop (n + 1) l = y`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[wdrop; NOT_CONS_NIL] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN
  COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[CONS_11; WDROP_0] THEN MESON_TAC[];
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`n - 1`; `x:A`; `y:A list`]) THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[SUB_ADD; ARITH_RULE `~(n = 0) ==> 1 <= n`]]);;

let wdrop_table (mc_def:thm) =
  let mc = lhs(concl mc_def) in
  let th0 = TRANS (ISPEC mc WDROP_0) mc_def in
  let norm = CONV_RULE(LAND_CONV(LAND_CONV NUM_ADD_CONV)) in
  let rec go th acc =
    let r = rhs(concl th) in
    if is_cons r then let th' = norm (MATCH_MP WDROP_NEXT th) in go th' (th::acc)
    else rev (th::acc) in
  go th0 [];;

let fast_decode_compset (mc_def:thm) =
  let mc = lhs(concl mc_def) in
  let lth = (REWRITE_CONV[mc_def] THENC LENGTH_CONV) (mk_comb(`LENGTH:byte list->num`,mc)) in
  let cs = Compute.bool_compset () in
  Compute.set_skip cs `COND:bool->A->A->A` (Some 1);
  Compute.add_thms
   ([wobind; whd; wdrop; wtake; wuleb; wsleb; wblocktype; wmemarg; wrelop_of;
     wdecode_op; wdecode_raw; WSCAN_ALT; WELSE_SCAN_ALT; WULEBS_ALT;
     wblock_arity; wasm_decode; WDECLS_ALT; wasm_entry;
     FST; SND; HD; TL; LENGTH; lth] @ wdrop_table mc_def) cs;
  List.iter (fun (t,n,c) -> Compute.add_conv (t,n,c) cs)
   [`(+):num->num->num`,2,NUM_ADD_CONV;
    `(-):num->num->num`,2,NUM_SUB_CONV;
    `( * ):num->num->num`,2,NUM_MULT_CONV;
    `(<):num->num->bool`,2,NUM_LT_CONV;
    `(<=):num->num->bool`,2,NUM_LE_CONV;
    `(=):num->num->bool`,2,NUM_EQ_CONV;
    `SUC`,1,NUM_SUC_CONV;
    `val:byte->num`,1,WORD_RED_CONV;
    `int_add`,2,INT_ADD_CONV;
    `int_sub`,2,INT_SUB_CONV;
    `int_mul`,2,INT_MUL_CONV;
    `int_neg`,1,INT_NEG_CONV;
    `iword:int->int32`,1,WORD_RED_CONV;
    `iword:int->int64`,1,WORD_RED_CONV];
  lth,cs;;

let FAST_MK_EXEC_RULE (mc_def:thm) (entry:int) : thm * (thm option array) =
  let mc = lhs(concl mc_def) in
  let lth,cs = fast_decode_compset mc_def in
  let conv = Compute.WEAK_CBV_CONV cs in
  let len = dest_small_numeral(rhs(concl lth)) in
  let arr = Array.make len None in
  let dec = `wasm_decode` in
  let rec sweep pc =
    if pc >= len then () else
    let th = conv (list_mk_comb(dec,[mc;mk_small_numeral pc])) in
    let r = rhs(concl th) in
    if not (is_comb r && fst(dest_const(rator r)) = "SOME") then
      failwith ("FAST_MK_EXEC_RULE: no decode at offset "^string_of_int pc^
                ": "^string_of_term r) else
    let _,n = dest_pair(rand r) in
    arr.(pc) <- Some th;
    sweep (pc + dest_small_numeral n) in
  sweep entry; (lth,arr);;

