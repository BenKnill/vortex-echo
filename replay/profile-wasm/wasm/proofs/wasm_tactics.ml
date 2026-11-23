(* ========================================================================= *)
(* Decoding by evaluation and forward symbolic execution for the WASM       *)
(* model, in the style of ARM_MK_EXEC_RULE / ARM_STEPS_TAC (s2n-bignum).    *)
(* ========================================================================= *)

needs "wasm.ml";;

let wasm_print_log = ref false;;

(* ------------------------------------------------------------------------- *)
(* Fuel recursion in a numeral-friendly form for call-by-value evaluation.  *)
(* ------------------------------------------------------------------------- *)

let WSCAN_ALT = prove
 (`!f code pc d.
     wscan f (code:byte list) pc d =
     if f = 0 then NONE else
     wobind (whd (wdrop pc code)) (\b. wobind (wdecode_raw code pc) (\p.
       if val b = 0x02 \/ val b = 0x03 \/ val b = 0x04
       then wscan (f - 1) code (pc + SND p) (d + 1)
       else if val b = 0x0B then
         (if d = 0 then SOME (pc + SND p)
          else wscan (f - 1) code (pc + SND p) (d - 1))
       else wscan (f - 1) code (pc + SND p) d))`,
  INDUCT_TAC THEN REWRITE_TAC[wscan; NOT_SUC; SUC_SUB1]);;

let WELSE_SCAN_ALT = prove
 (`!f code pc d.
     welse_scan f (code:byte list) pc d =
     if f = 0 then NONE else
     wobind (whd (wdrop pc code)) (\b. wobind (wdecode_raw code pc) (\p.
       if val b = 0x02 \/ val b = 0x03 \/ val b = 0x04
       then welse_scan (f - 1) code (pc + SND p) (d + 1)
       else if val b = 0x0B then
         (if d = 0 then SOME pc else welse_scan (f - 1) code (pc + SND p) (d - 1))
       else if val b = 0x05 /\ d = 0 then SOME (pc + SND p)
       else welse_scan (f - 1) code (pc + SND p) d))`,
  INDUCT_TAC THEN REWRITE_TAC[welse_scan; NOT_SUC; SUC_SUB1]);;

let WULEBS_ALT = prove
 (`!n l. wulebs n (l:byte list) =
     if n = 0 then SOME ([],0) else
     wobind (wuleb l) (\p. wobind (wulebs (n - 1) (wdrop (SND p) l))
       (\q. SOME (CONS (FST p) (FST q), SND p + SND q)))`,
  INDUCT_TAC THEN REWRITE_TAC[wulebs; NOT_SUC; SUC_SUB1]);;

let WBYTES_LE_ALT = prove
 (`!n l. wbytes_le n (l:byte list) =
     if n = 0 then SOME 0 else
     wobind (whd l) (\b. wobind (wbytes_le (n - 1) (wdrop 1 l))
       (\v. SOME (val b + 256 * v)))`,
  INDUCT_TAC THEN REWRITE_TAC[wbytes_le; NOT_SUC; SUC_SUB1]);;

(* ------------------------------------------------------------------------- *)
(* A compset (HOL Light Compute, call-by-value, lazy COND) for decoding.    *)
(* ------------------------------------------------------------------------- *)

let WDECLS_ALT = prove
 (`!k code pc. wdecls k (code:byte list) pc =
     if k = 0 then SOME pc else
     wobind (wuleb (wdrop pc code)) (\p. wdecls (k - 1) code (pc + SND p + 1))`,
  INDUCT_TAC THEN REWRITE_TAC[wdecls; NOT_SUC; SUC_SUB1]);;

let wasm_decode_thms =
  [wobind; whd; wdrop; wtake; wuleb; wsleb; wblocktype; wmemarg; wrelop_of;
   wdecode_op; wdecode_raw; WSCAN_ALT; WELSE_SCAN_ALT; WULEBS_ALT;
   WBYTES_LE_ALT;
   wblock_arity; wasm_decode;
   WDECLS_ALT; wasm_entry;
   FST; SND; HD; TL; LENGTH];;

let wasm_mk_decode_compset (extra:thm list) =
  let cs = Compute.bool_compset () in
  Compute.set_skip cs `COND:bool->A->A->A` (Some 1);
  Compute.add_thms (wasm_decode_thms @ extra) cs;
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
  cs;;

let wasm_decode_compset = wasm_mk_decode_compset [];;

let WASM_DECODE_CONV = Compute.WEAK_CBV_CONV wasm_decode_compset;;

(* ------------------------------------------------------------------------- *)
(* Precompute decodes for a code constant by a sweep from entry pc.        *)
(* Both rules return (|- LENGTH mc = n, array of                            *)
(* |- wasm_decode mc pc = SOME(i,len)) with the same statements.            *)
(*                                                                           *)
(* Reference rule: evaluates on the unfolded byte list, so each wdrop pc     *)
(* costs pc numeral steps, and every block scan repeats them. Its cost       *)
(* grows roughly with the cube of the body length (387 bytes: 376 s on       *)
(* bluestar26; 1737 bytes did not finish in 7200 s). Kept as the reference   *)
(* the fast rule must agree with (wasm/demos/exec_rule_agree.ml checks this  *)
(* on the demo bodies).                                                      *)
(* ------------------------------------------------------------------------- *)

let WASM_MK_EXEC_RULE_REFERENCE (mc_def:thm) (entry:int)
    : thm * (thm option array) =
  let mc = lhs(concl mc_def) in
  let lth = (REWRITE_CONV[mc_def] THENC WASM_DECODE_CONV)
              (mk_comb(`LENGTH:byte list->num`,mc)) in
  let len = dest_small_numeral(rhs(concl lth)) in
  let arr = Array.make len None in
  let dec = `wasm_decode` in
  let rec sweep pc =
    if pc >= len then () else
    let tm = list_mk_comb(dec,[mc;mk_small_numeral pc]) in
    let th = (ONCE_REWRITE_CONV[mc_def] THENC WASM_DECODE_CONV) tm in
    let r = rhs(concl th) in
    if not (is_comb r && fst(dest_const(rator r)) = "SOME") then
      failwith ("WASM_MK_EXEC_RULE_REFERENCE: no decode at offset "^
                string_of_int pc^": "^string_of_term r) else
    let _,n = dest_pair(rand r) in
    let th' = CONV_RULE(RAND_CONV(SUBS_CONV[SYM mc_def])) th in
    arr.(pc) <- Some th';
    sweep (pc + dest_small_numeral n) in
  sweep entry; (lth,arr);;

(* ------------------------------------------------------------------------- *)
(* Fast rule (per-offset tables): the code constant mc is never unfolded. A  *)
(* fresh decode compset gets |- LENGTH mc = n and one theorem                *)
(* |- wdrop k mc = suffix_k per offset k <= n, each derived from the         *)
(* previous one by WDROP_NEXT, so a wdrop lookup is one rewrite instead of   *)
(* a walk down the list. Compute still tries those rules in turn, so the     *)
(* cost grows roughly with the square of the body length (387 bytes: 12 s;   *)
(* 1737 bytes: 280 s). Every theorem is a kernel inference (Compute is a     *)
(* derived rule): no new axioms and no new constants. A code constant whose  *)
(* definition is not a literal byte list falls back to the reference rule.   *)
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
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n - 1`; `x:A`; `y:A list`]) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[SUB_ADD; ARITH_RULE `~(n = 0) ==> 1 <= n`]]);;

(* [|- wdrop 0 mc = l; |- wdrop 1 mc = TL l; ...; |- wdrop n mc = []] *)
let wasm_wdrop_table (mc_def:thm) =
  let mc = lhs(concl mc_def) in
  let th0 = TRANS (ISPEC mc WDROP_0) mc_def in
  let norm = CONV_RULE(LAND_CONV(LAND_CONV NUM_ADD_CONV)) in
  let rec go th acc =
    if is_cons(rhs(concl th))
    then go (norm (MATCH_MP WDROP_NEXT th)) (th::acc)
    else rev (th::acc) in
  go th0 [];;

let wasm_fast_decode_compset (mc_def:thm) =
  let mc = lhs(concl mc_def) in
  let lth = (REWRITE_CONV[mc_def] THENC LENGTH_CONV)
              (mk_comb(`LENGTH:byte list->num`,mc)) in
  lth,wasm_mk_decode_compset (lth :: wasm_wdrop_table mc_def);;

let WASM_FAST_MK_EXEC_RULE (mc_def:thm) (entry:int)
    : thm * (thm option array) =
  if not (is_list(rhs(concl mc_def)))
  then WASM_MK_EXEC_RULE_REFERENCE mc_def entry else
  let mc = lhs(concl mc_def) in
  let lth,cs = wasm_fast_decode_compset mc_def in
  let conv = Compute.WEAK_CBV_CONV cs in
  let len = dest_small_numeral(rhs(concl lth)) in
  let arr = Array.make len None in
  let dec = `wasm_decode` in
  let rec sweep pc =
    if pc >= len then () else
    let th = conv (list_mk_comb(dec,[mc;mk_small_numeral pc])) in
    let r = rhs(concl th) in
    if not (is_comb r && fst(dest_const(rator r)) = "SOME") then
      failwith ("WASM_FAST_MK_EXEC_RULE: no decode at offset "^
                string_of_int pc^": "^string_of_term r) else
    let _,n = dest_pair(rand r) in
    arr.(pc) <- Some th;
    sweep (pc + dest_small_numeral n) in
  sweep entry; (lth,arr);;

(* The default decode rule for demos and stepping tactics. *)
let WASM_MK_EXEC_RULE = WASM_FAST_MK_EXEC_RULE;;

(* ------------------------------------------------------------------------- *)
(* One step from a state with known pc, code and running status.            *)
(* ------------------------------------------------------------------------- *)

let WASM_STEP_THM = prove
 (`read wstatus s = WRunning ==> read wcode s = mc ==> read wpc s = word pc ==>
   pc < 2 EXP 64 ==> wasm_decode mc pc = SOME (i,n) ==>
   (wasm s s' <=> wasm_exec i pc (pc + n) s = SOME s')`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[wasm; VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT; option_INJ; PAIR_EQ] THEN MESON_TAC[]);;

let EL_NUM_CONV =
  let [el0;elsuc] = CONJUNCTS EL in
  let rec conv tm =
    match tm with
      Comb(Comb(Const("EL",_),n),l) when is_numeral n ->
        if dest_numeral n =/ num 0 then GEN_REWRITE_CONV I [el0] tm
        else (RATOR_CONV(RAND_CONV num_CONV) THENC GEN_REWRITE_CONV I [elsuc]
              THENC RAND_CONV(GEN_REWRITE_CONV I [TL]) THENC conv) tm
    | _ -> failwith "EL_NUM_CONV" in
  conv;;

let WASM_EXEC_RULES = ref
 [wpop; wpop_i32; wpop_i64; wpop_f32; wpop_f64; wasm_branch; wasm_return; wdrop; wtake;
  LENGTH; HD; TL; APPEND; FST; SND; wbinop_sem; wrelop_sem; wbinop_trap;
  wunop_sem;
  NOT_CONS_NIL; CONS_11; COND_CLAUSES; option_INJ; option_DISTINCT;
  DIMINDEX_32; DIMINDEX_64; DIMINDEX_8; BITVAL_CLAUSES; WORD_BITVAL_EQ_0;
  ADD_CLAUSES; WORD_VAL; WORD_SUB_REFL; WORD_ADD_0; WORD_SUB_0];;

(* Signed division on integer literals (div_s / rem_s on concrete values):  *)
(* unfold wtdiv only when both arguments are literals, then evaluate.        *)
(* (lane WASM2T, 2026-11-04: DBG's lockstep found these left unreduced.)    *)
let WTDIV_LIT_CONV tm =
  match tm with
    Comb(Comb(Const("wtdiv",_),x),y) when is_intconst x && is_intconst y ->
      (REWR_CONV wtdiv THENC INT_REDUCE_CONV THENC REWRITE_CONV[] THENC
       INT_REDUCE_CONV) tm
  | _ -> failwith "WTDIV_LIT_CONV";;

(* Integer literal arithmetic (signed comparisons, ival results, wtdiv)     *)
(* runs alongside the num and word evaluation.                              *)
let WASM_REDUCE_CONV extra =
  let base = REWRITE_CONV (extra @ !WASM_EXEC_RULES) in
  let red = DEPTH_CONV (NUM_RED_CONV ORELSEC EL_NUM_CONV ORELSEC
                        WORD_RED_CONV ORELSEC INT_RED_CONV ORELSEC
                        WTDIV_LIT_CONV ORELSEC BETA_CONV) in
  REPEATC (CHANGED_CONV (base THENC red));;

(* ------------------------------------------------------------------------- *)
(* Linear arithmetic over addresses (lane WASM2T). Address and bound terms  *)
(* mention val of i32 words such as val(word_sub sp (word 4)); ARITH_RULE   *)
(* treats those as opaque atoms. wasm_arith_prove adds, for each such atom, *)
(* its range (val t < 2^32) and, where the antecedents allow, its linear    *)
(* form (val x - k, val x + k, or val x + k - 2^32), innermost atoms first. *)
(* ------------------------------------------------------------------------- *)

let WVAL_WORD_SUB_LIN = prove
 (`!x:int32 k. k <= val x ==> val(word_sub x (word k)) + k = val x`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `x:int32` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_32] THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(word k:int32) = k` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN MATCH_MP_TAC MOD_LT THEN
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[VAL_WORD_SUB_CASES; SUB_ADD]]);;

let WVAL_WORD_ADD_LIN = prove
 (`!x:int32 k. val x + k < 4294967296 ==> val(word_add x (word k)) = val x + k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC MOD_DOWN_CONV THEN MATCH_MP_TAC MOD_LT THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let WVAL_WORD_ADD_WRAP_LIN = prove
 (`!x:int32 k. k < 4294967296 /\ 4294967296 <= val x + k
               ==> val(word_add x (word k)) + 4294967296 = val x + k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word k:int32) = k` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN MATCH_MP_TAC MOD_LT THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_WORD_ADD_CASES; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[GSYM NOT_LE] THEN
  ASM_SIMP_TAC[SUB_ADD]);;

let wasm_arith_prove =
  let i32 = `:int32` and val32 = `val:int32->num` in
  let is_val32 t = is_comb t && rator t = val32 in
  (* facts are additive (no truncated subtraction, which ARITH_RULE handles *)
  (* poorly); each rule comes with the path to its val atom                 *)
  let lin_rules = [WVAL_WORD_SUB_LIN,(lhand o lhand o rand);
                   WVAL_WORD_ADD_LIN,(lhand o rand);
                   WVAL_WORD_ADD_WRAP_LIN,(lhand o lhand o rand)] in
  let reduce_prove t =
    let eq = NUM_REDUCE_CONV t in
    let t' = rhs(concl eq) in
    if t' = `T` then EQT_ELIM eq else EQ_MP (SYM eq) (ARITH_RULE t') in
  let prove_from hyps t =
    if hyps = [] then reduce_prove t else
    let th = reduce_prove (mk_imp(list_mk_conj(map concl hyps),t)) in
    MP th (end_itlist CONJ hyps) in
  fun (ants:thm list) (t:term) ->
    (* plain linear arithmetic first (as before lane WASM2T), then with the *)
    (* address atoms' ranges and linear forms                               *)
    try prove_from ants t with Failure _ ->
    let rec tsize t = match t with
        Comb(a,b) -> tsize a + tsize b | Abs(_,b) -> 1 + tsize b | _ -> 1 in
    (* with each val (word_sub x (word k)) / val (word_add x (word k)) also *)
    (* val x, so nested pushes linearise from the inside out                *)
    let rec close acc = function
        [] -> acc
      | a::rest ->
          if mem a acc then close acc rest else
          let x = rand a in
          let more = if is_comb x && is_comb(rator x) &&
                        (match rator(rator x) with
                           Const(("word_sub"|"word_add"),_) -> true | _ -> false)
                     then [mk_comb(val32,lhand x)] else [] in
          close (a::acc) (more @ rest) in
    let atoms = sort (fun a b -> tsize a < tsize b)
      (close [] (find_terms is_val32 (list_mk_conj(t::map concl ants)))) in
    let bound a = CONV_RULE NUM_REDUCE_CONV
      (REWRITE_RULE[DIMINDEX_32] (ISPEC (rand a) VAL_BOUND)) in
    let facts = ref (map bound atoms) in
    List.iter (fun a ->
      let x = rand a in
      if type_of x = i32 && is_comb x && is_comb(rator x) &&
         (match rator(rator x) with
            Const(("word_sub"|"word_add"),_) -> true | _ -> false) &&
         (let k = rand x in is_comb k && is_numeral(rand k))
      then
        let rec try_rules = function
            [] -> ()
          | (r,path)::rs ->
              (try let r' = PART_MATCH path r a in
                   let ant = lhand(concl r') in
                   let ath = prove_from (ants @ !facts) ant in
                   facts := MP r' ath :: !facts
               with Failure _ -> try_rules rs) in
        try_rules lin_rules) atoms;
    prove_from (ants @ !facts) t;;

(* Antecedents usable by wasm_arith_prove: state-free num relations. *)
let wasm_is_numrel t =
  let t = if is_neg t then rand t else t in
  (try let op,_ = dest_const(rator(rator t)) in
       mem op ["<";"<=";">";">=";"="] && type_of(rand t) = `:num`
   with Failure _ -> false) ||
  (is_disj t && let a,b = dest_disj t in
                let r u = try let op,_ = dest_const(rator(rator u)) in
                              mem op ["<";"<=";"="] && type_of(rand u) = `:num`
                          with Failure _ -> false in r a && r b);;

let wasm_is_intrel t =
  let t = if is_neg t then rand t else t in
  try let op,_ = dest_const(rator(rator t)) in
      mem op ["int_lt";"int_le";"int_gt";"int_ge";"="] &&
      type_of(rand t) = `:int`
  with Failure _ -> false;;

(* ------------------------------------------------------------------------- *)
(* Non-aliasing of byte-sized memory components at addresses word E with    *)
(* E a num expression (lane WASM2T). Two components are orthogonal when     *)
(* their byte ranges are disjoint and neither wraps past 2^64.              *)
(* ------------------------------------------------------------------------- *)

let WMEM_BYTES_ORTH = prove
 (`!e1 e2 m n.
     (e1 + m <= e2 \/ e2 + n <= e1) /\ e1 + m <= 2 EXP 64 /\ e2 + n <= 2 EXP 64
     ==> orthogonal_components (bytes(word e1:int64,m)) (bytes(word e2,n))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ORTHOGONAL_COMPONENTS_BYTES; nonoverlapping_modulo;
              DIMINDEX_64; NOT_EXISTS_THM; VAL_WORD; CONG] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
  REWRITE_TAC[TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`] THEN STRIP_TAC THEN
  (SUBGOAL_THEN `e1 MOD 2 EXP 64 = e1 /\ e2 MOD 2 EXP 64 = e2 /\
                 (e1 + i) MOD 2 EXP 64 = e1 + i /\
                 (e2 + j) MOD 2 EXP 64 = e2 + j`
    (fun th -> REWRITE_TAC[th]) THENL
    [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
     ASM_ARITH_TAC]));;

let wmem_sizes = ["bytes8",1; "bytes16",2; "bytes32",4; "bytes64",8];;

(* |- !e1 e2. (e1 + m <= e2 \/ e2 + n <= e1) /\ e1 + m <= 2 EXP 64 /\      *)
(*            e2 + n <= 2 EXP 64 ==> orthogonal_components (P (word e1))   *)
(*                                                         (Q (word e2))   *)
let WMEM_ORTH_THMS =
  let mk (p,m) (q,n) =
    let tm = parse_term
      ("!e1 e2. (e1 + "^string_of_int m^" <= e2 \\/ e2 + "^string_of_int n^
       " <= e1) /\\ e1 + "^string_of_int m^" <= 2 EXP 64 /\\ e2 + "^
       string_of_int n^" <= 2 EXP 64 ==> orthogonal_components ("^p^
       " (word e1:int64)) ("^q^" (word e2:int64))") in
    let pd = assoc p ["bytes8",bytes8; "bytes16",bytes16; "bytes32",bytes32;
                      "bytes64",bytes64]
    and qd = assoc q ["bytes8",bytes8; "bytes16",bytes16; "bytes32",bytes32;
                      "bytes64",bytes64] in
    (p,q),prove(tm,
      REWRITE_TAC[pd; qd] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_LEFT THEN
      MATCH_MP_TAC WMEM_BYTES_ORTH THEN ASM_REWRITE_TAC[]) in
  allpairs mk wmem_sizes wmem_sizes;;

(* c = P (word e1), d = Q (word e2): |- orthogonal_components c d *)
let wmem_orth ants c d =
  match c,d with
    Comb(Const(p,_),Comb(Const("word",_),e1)),
    Comb(Const(q,_),Comb(Const("word",_),e2)) ->
      let th = SPECL [e1;e2] (assoc (p,q) WMEM_ORTH_THMS) in
      MP th (wasm_arith_prove ants (lhand(concl th)))
  | _ -> failwith "wmem_orth";;

(* |- c = c' for c = P (word e), c' = P (word e') with e = e' provable. *)
let wmem_same ants c c' =
  match c,c' with
    Comb(Const(p,_),Comb(Const("word",_),e1)),
    Comb(Const(q,_),Comb(Const("word",_),e2)) when p = q ->
      if e1 = e2 then REFL c else
      AP_TERM (rator c) (AP_TERM (rator(rand c))
        (wasm_arith_prove ants (mk_eq(e1,e2))))
  | _ -> failwith "wmem_same";;

(* Facts |- read (wmem :> c) s = v about the memory of state s. *)
let wmem_comp_facts s ths =
  mapfilter (fun th ->
    let c = concl th in
    match c with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
           Comb(Comb(Const(":>",_),Const("wmem",_)),comp)),s')),_)
        when s' = s && is_comb comp &&
             (match rator comp with
                Const(p,_) -> can (assoc p) wmem_sizes | _ -> false) -> (comp,th)
    | _ -> fail()) ths;;

(* tm = read (wmem :> c) s with no fact for exactly c: use a fact for a     *)
(* component c' of the same width at a provably equal address.              *)
let WMEM_LOAD_CONV ants facts s tm =
  match tm with
    Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),Const("wmem",_)),c)),s')
      when s' = s ->
      let rec go = function
          [] -> failwith "WMEM_LOAD_CONV"
        | (c',fth)::rest ->
            (try let eq = wmem_same ants c c' in
                 (RATOR_CONV(RAND_CONV(RAND_CONV(K eq))) THENC K fth) tm
             with Failure _ -> go rest) in
      go facts
  | _ -> failwith "WMEM_LOAD_CONV";;

(* is th of the form |- read c s = t for state variable s? *)
let is_read_of s th =
  let c = concl th in
  is_eq c &&
  (match lhs c with
     Comb(Comb(Const("read",_),_),s') -> s' = s
   | _ -> false);;

let find_read_th name s ths =
  try find (fun th -> is_read_of s th &&
             (match rator(lhs(concl th)) with
                Comb(_,Const(n,_)) -> n = name | _ -> false)) ths
  with Failure _ -> failwith ("WASM_CONV: no `read "^name^" s = ..` assumption");;

(* tm = `wasm s s'`; ths = assumptions; extra = user rewrites (e.g. guards) *)
let WASM_CONV (decode_ths:thm option array) (extra:thm list) (ths:thm list) tm =
  let s = rand(rator tm) in
  let pc_th = find_read_th "wpc" s ths
  and code_th = find_read_th "wcode" s ths
  and st_th = find_read_th "wstatus" s ths in
  let pc_num = rand(rhs(concl pc_th)) in
  let pc = try dest_small_numeral pc_num with Failure _ ->
    failwith ("WASM_CONV: pc not a numeral: "^string_of_term(concl pc_th)) in
  let dth = match (try decode_ths.(pc) with _ -> None) with
      Some th -> th
    | None -> failwith ("WASM_CONV: no decode at pc "^string_of_int pc) in
  let lt_th = EQT_ELIM(NUM_REDUCE_CONV(mk_binary "<" (pc_num,`2 EXP 64`))) in
  (* L-4: WASM_STEP_THM's free variables (s, s', mc, pc, i, n) are renamed  *)
  (* away from every variable of the goal and its assumptions before        *)
  (* MATCH_MP, so goal variables with those names are no longer frozen.     *)
  let step_th, s'_var =
    let g = GEN_ALL WASM_STEP_THM in
    let vs = fst(strip_forall(concl g)) in
    let avoid = itlist (fun th acc -> union (frees(concl th))
                          (union (freesl(hyp th)) acc)) (dth::ths) (frees tm) in
    let vs' = variants avoid vs in
    SPECL vs' g, assoc `s':wasmstate` (zip vs vs') in
  let th0 = MATCH_MP (MATCH_MP (MATCH_MP (MATCH_MP (MATCH_MP step_th st_th)
                code_th) pc_th) lt_th) dth in
  let th1 = SPEC (rand tm) (GEN s'_var th0) in
  let _ = if !wasm_print_log then
    Printf.printf "pc %d: %s\n%!" pc
      (string_of_term(hd(snd(strip_comb(lhand(rhs(concl th1))))))) in
  let readths = filter (is_read_of s) ths in
  (* state-free assumptions (e.g. guard facts) are used as rewrites too *)
  let pureths = filter (fun th -> let c = concl th in
      not (can (find_term (fun t -> is_const t &&
             (let n = fst(dest_const t) in n = "read" || n = "MAYCHANGE" ||
              n = ",,"))) c) &&
      not (is_var c)) ths in
  let rules = readths @ pureths @ extra in
  let ants = filter (fun th -> wasm_is_numrel(concl th)) pureths in
  let iants = filter (fun th -> wasm_is_intrel(concl th)) pureths in
  (* a control/trap guard left undecided by rewriting: try linear arithmetic *)
  (* from the state-free assumptions (num, with the address atoms made       *)
  (* linear, then int), and reduce again                                     *)
  let iprove t =
    if iants = [] then INT_ARITH t else
    MP (INT_ARITH (mk_imp(list_mk_conj(map concl iants),t)))
       (end_itlist CONJ iants) in
  let try_prove t =
    try wasm_arith_prove ants t with Failure _ -> iprove t in
  (* A guard is first decided, in both polarities, by plain linear          *)
  (* arithmetic from the non-disjunctive num assumptions (the pre-WASM2T    *)
  (* rule); only if neither polarity is proved does the full chain above    *)
  (* run. wasm_arith_prove's first attempt hands ARITH_RULE the disjunctive *)
  (* assumptions as well, and its case splits took 773.6 s of 799.8 s      *)
  (* profiled on App M1 (tooling sprint 3 lane W, W-C); with this order all *)
  (* 59 of App M1's guards were decided here (W-C2 probe, eval 100.7 s).    *)
  (* Either way the result is a theorem g = T or g = F, so the rewritten    *)
  (* goal is the same whenever the assumptions are consistent.              *)
  let pants = filter (fun th -> not (is_disj(concl th))) ants in
  let plain_prove t =
    if pants = [] then ARITH_RULE t else
    MP (ARITH_RULE (mk_imp(list_mk_conj(map concl pants),t)))
       (end_itlist CONJ pants) in
  let decide g = try EQT_INTRO(plain_prove g) with Failure _ ->
                 try EQF_INTRO(plain_prove (mk_neg g)) with Failure _ ->
                 try EQT_INTRO(try_prove g) with Failure _ ->
                 try EQF_INTRO(try_prove (mk_neg g)) with Failure _ ->
                 failwith "guard" in
  let guard_conv tm =
    match tm with
      Comb(Comb(Const("=",_),l),_) when is_cond l ->
        let g = lhand(rator l) in
        let gth = decide g in
        (LAND_CONV(RATOR_CONV(LAND_CONV(K gth))) THENC
         WASM_REDUCE_CONV rules THENC
         GEN_REWRITE_CONV TRY_CONV [option_INJ]) tm
    | _ -> REFL tm in
  (* a load from an address that matches a memory fact only up to linear    *)
  (* arithmetic (e.g. sp - 4 + 4 against sp): rewrite it by that fact        *)
  let mfacts = wmem_comp_facts s ths in
  let load_conv =
    if mfacts = [] then ALL_CONV else
    TRY_CONV(CHANGED_CONV(DEPTH_CONV(WMEM_LOAD_CONV ants mfacts s)) THENC
             WASM_REDUCE_CONV rules THENC
             GEN_REWRITE_CONV TRY_CONV [option_INJ] THENC
             TRY_CONV guard_conv) in
  (* a conditional inside the update (the pc of an `if` on a comparison)   *)
  (* whose guard the state-free num or int assumptions decide             *)
  let inner_cond_conv tm =
    match tm with
      Comb(Comb(Comb(Const("COND",_),g),_),_)
        when wasm_is_numrel g || wasm_is_intrel g ->
        (RATOR_CONV(RATOR_CONV(RAND_CONV(K(decide g)))) THENC
         GEN_REWRITE_CONV I [COND_CLAUSES]) tm
    | _ -> failwith "inner_cond_conv" in
  let cond_pass =
    if ants = [] && iants = [] then ALL_CONV else
    TRY_CONV(CHANGED_CONV(ONCE_DEPTH_CONV inner_cond_conv) THENC
             WASM_REDUCE_CONV rules THENC
             GEN_REWRITE_CONV TRY_CONV [option_INJ] THENC
             TRY_CONV guard_conv) in
  let conv =
    LAND_CONV (GEN_REWRITE_CONV I [wasm_exec]) THENC
    WASM_REDUCE_CONV rules THENC
    GEN_REWRITE_CONV TRY_CONV [option_INJ] THENC
    TRY_CONV guard_conv THENC load_conv THENC cond_pass in
  CONV_RULE (RAND_CONV conv) th1;;

(* ------------------------------------------------------------------------- *)
(* Stepping tactics.                                                         *)
(* ------------------------------------------------------------------------- *)

let WASM_BASIC_STEP_TAC =
  let wasm_tm = `wasm` and ws_ty = `:wasmstate` in
  fun decode_ths extra sname (asl,w) ->
    let sv = rand w and sv' = mk_var(sname,ws_ty) in
    let atm = mk_comb(mk_comb(wasm_tm,sv),sv') in
    let eth = WASM_CONV decode_ths extra (map snd asl) atm in
    let r = rhs(concl eth) in
    if not (is_eq r && rand r = sv') then
      failwith ("WASM_BASIC_STEP_TAC: step did not reduce to a state update: "^
                string_of_term r) else
    (GEN_REWRITE_TAC I [eventually_CASES] THEN DISJ2_TAC THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC BINDER_CONV [eth] THEN CONV_TAC EXISTS_NONTRIVIAL_CONV;
      X_GEN_TAC sv' THEN GEN_REWRITE_TAC LAND_CONV [eth]]) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Memory transport for a store step. s2n's assumption update only keeps    *)
(* facts about components a step leaves alone (its "memorable" path is     *)
(* keyed on a component named memory), so a fact about wmem dies at a       *)
(* store. A memory can be named: an assumption `read wmem s = mm` (mm a     *)
(* variable) becomes, across a step that writes wmem :> d with y,           *)
(* `read wmem s' = write d y mm`, free of the old state.                    *)
(* ------------------------------------------------------------------------- *)

let WMEM_READ_WRITE_SUB = prove
 (`!d y (s:wasmstate).
     read wmem (write (wmem :> d) y s) = write d y (read wmem s)`,
  REWRITE_TAC[WRITE_COMPONENT_COMPOSE] THEN
  REPEAT GEN_TAC THEN READ_OVER_WRITE_TAC);;

let WRITE_BYTES8_APPLY = prove
 (`!(addr:int64) (y:byte) (f:int64->byte) x.
     write (bytes8 addr) y f x = if x = addr then y else f x`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM READ_ELEMENT] THEN
  REWRITE_TAC[READ_ELEMENT_WRITE_BYTES8; READ_ELEMENT]);;

let rec WMEM_READ_OVER_WRITES_CONV tm =
  match tm with
    Comb(Comb(Const("read",_),Const("wmem",_)),
         Comb(Comb(Comb(Const("write",_),c),_),_)) ->
      (match c with
         Comb(Comb(Const(":>",_),Const("wmem",_)),_) ->
           (GEN_REWRITE_CONV I [WMEM_READ_WRITE_SUB] THENC
            RAND_CONV WMEM_READ_OVER_WRITES_CONV) tm
       | _ -> (COMPONENT_READ_OVER_WRITE_CONV THENC
               WMEM_READ_OVER_WRITES_CONV) tm)
  | _ -> REFL tm;;

let WASM_MEM_UPDATE_TAC (asl,w) =
  let uth_tm = lhand w in
  let s = repeat rand (lhand uth_tm) in
  let rec writes_wmem tm =
    match tm with
      Comb(Comb(Comb(Const("write",_),c),_),t) ->
        (match c with
           Comb(Comb(Const(":>",_),Const("wmem",_)),_) -> true
         | Const("wmem",_) -> true  (* whole-memory write: memory.fill/copy *)
         | _ -> writes_wmem t)
    | _ -> false in
  if not (writes_wmem (lhand uth_tm)) then ALL_TAC (asl,w) else
  let rmem = mk_comb(`read wmem`,s) in
  (* The memory may be named by a variable, or (lane WASM2T) by any         *)
  (* state-free term, such as the write chain an earlier store left: the    *)
  (* fact then grows by one write per store instead of being dropped.       *)
  let state_free t =
    not (exists (fun v -> type_of v = `:wasmstate`) (frees t)) &&
    not (can (find_term (fun u -> is_const u && fst(dest_const u) = "read")) t) in
  let names = mapfilter (fun th -> let c = concl th in
      if is_eq c && rhs c = rmem && is_var(lhs c) then SYM th
      else if is_eq c && lhs c = rmem && state_free(rhs c) then th
      else fail()) (map snd asl) in
  if names = [] then ALL_TAC (asl,w) else
  (DISCH_THEN(fun uth ->
     let th0 = SYM(AP_TERM `read wmem` uth) in
     let th1 = CONV_RULE(RAND_CONV WMEM_READ_OVER_WRITES_CONV) th0 in
     let th2 = GEN_REWRITE_RULE (RAND_CONV o ONCE_DEPTH_CONV) names th1 in
     MP_TAC uth THEN ASSUME_TAC th2)) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Component memory facts across a store (lane WASM2T). A fact              *)
(* |- read (wmem :> c) s = v survives a step whose update writes            *)
(* wmem :> d1, ..., wmem :> dk when each di is c itself (the fact then      *)
(* takes the stored value) or provably disjoint from c, using the state-    *)
(* free num assumptions (wasm_arith_prove). Each stored component also      *)
(* gets a fact with its new value. Facts it cannot carry are dropped, as    *)
(* before. A whole-memory write (memory.fill/copy) carries nothing.         *)
(* ------------------------------------------------------------------------- *)

let rec WMEM_MEM_READ_CONV ants facts s tm =
  match tm with
    Comb(Comb(Const("read",_),c),Comb(Comb(Comb(Const("write",_),d),_),_)) ->
      if c = d then COMPONENT_READ_OVER_WRITE_CONV tm else
      let oth = wmem_orth ants c d in
      (REWR_CONV (MATCH_MP READ_WRITE_ORTHOGONAL_COMPONENTS oth) THENC
       WMEM_MEM_READ_CONV ants facts s) tm
  | Comb(Comb(Const("read",_),c),Comb(Comb(Const("read",_),Const("wmem",_)),s'))
      when s' = s ->
      let fth = assoc c facts in
      (GEN_REWRITE_CONV I [GSYM READ_COMPONENT_COMPOSE] THENC K fth) tm
  | _ -> failwith "WMEM_MEM_READ_CONV";;

let WASM_MEMFACT_UPDATE_TAC (asl,w) =
  let uth_tm = lhand w in
  let s = repeat rand (lhand uth_tm) in
  let rec stores tm acc =
    match tm with
      Comb(Comb(Comb(Const("write",_),c),_),t) ->
        (match c with
           Comb(Comb(Const(":>",_),Const("wmem",_)),d) -> stores t (d::acc)
         | Const("wmem",_) -> failwith "whole"
         | _ -> stores t acc)
    | _ -> acc in
  let ds = try stores (lhand uth_tm) [] with Failure _ -> [] in
  if ds = [] then ALL_TAC (asl,w) else
  let ths = map snd asl in
  let facts = wmem_comp_facts s ths in
  let ants = filter (fun th -> wasm_is_numrel(concl th) &&
                     not (exists (fun v -> type_of v = `:wasmstate`)
                                 (frees(concl th)))) ths in
  let comps = setify (ds @ map fst facts) in
  (DISCH_THEN(fun uth ->
     let derive c =
       let rc = mk_icomb(`read`, mk_icomb(mk_icomb(`(:>)`,`wmem`),c)) in
       let th0 = SYM(AP_TERM rc uth) in
       let th1 = CONV_RULE(RAND_CONV
         (GEN_REWRITE_CONV I [READ_COMPONENT_COMPOSE] THENC
          RAND_CONV WMEM_READ_OVER_WRITES_CONV THENC
          WMEM_MEM_READ_CONV ants facts s)) th0 in
       if can (find_term (fun u -> is_const u && fst(dest_const u) = "read"))
              (rhs(concl th1)) then failwith "derive" else th1 in
     let newths = mapfilter derive comps in
     MP_TAC uth THEN MAP_EVERY ASSUME_TAC newths)) (asl,w);;

let WASM_STEP_TAC (_,decode_ths) extra sname =
  WASM_BASIC_STEP_TAC decode_ths extra sname THEN
  WASM_MEMFACT_UPDATE_TAC THEN
  WASM_MEM_UPDATE_TAC THEN
  ASSUMPTION_STATE_UPDATE_TAC THEN
  MAYCHANGE_STATE_UPDATE_TAC THEN
  DISCH_THEN(fun th ->
    let thl = STATE_UPDATE_NEW_RULE th in
    if thl = [] then ALL_TAC else
    MP_TAC(end_itlist CONJ thl) THEN
    CONV_TAC(LAND_CONV(DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV))) THEN
    STRIP_TAC);;

(* Drop assumptions about states other than s. Only :wasmstate terms count *)
(* as states: a fact whose read arguments are state-free (read (bytes8 a) mm *)
(* = v, or read c (write .. mm) = v, with mm a memory term) is kept, since   *)
(* it holds in every state (fix 2026-11-08, tooling sprint 2 lane 2; before  *)
(* it, such facts were dropped, found by app sprint M0's memory-writing     *)
(* callee).                                                                  *)
let DISCARD_OLD_WASMSTATE_TAC s =
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

(* L-4 (part 2): a loaded value read from the OLD state's memory, e.g.     *)
(* word_zx (read (wmem :> bytes8 (word E)) s0) after i32.load8_u with no     *)
(* memory fact for E, made the new stack fact mention s0, so the discard of *)
(* old-state facts dropped it and the next pop failed ("step did not reduce *)
(* to a state update"). Abbreviate each such old-state read in facts about  *)
(* the new state by a fresh variable first, so the fact survives.            *)
let WASM_KEEP_LOADED_TAC sname (asl,w) =
  let v = mk_var(sname,`:wasmstate`) in
  let rec reads acc tm =
    match tm with
      Comb(Comb(Const("read",_),_),s) when is_var s && type_of s = `:wasmstate` &&
                                           s <> v -> insert tm acc
    | Comb(a,b) -> reads (reads acc a) b
    | Abs(_,b) -> reads acc b
    | _ -> acc in
  let mentions_new tm = vfree_in v tm in
  let cands = itlist (fun (_,th) acc ->
      let c = concl th in
      if mentions_new c then reads acc c else acc) asl [] in
  let cands = filter (fun t -> not (exists (fun (_,th) -> concl th = mk_eq(t,t)) asl)) cands in
  if cands = [] then ALL_TAC (asl,w) else
  let avoid = itlist (union o frees o concl o snd) asl (frees w) in
  let _,tac = itlist (fun t (av,tac) ->
      let x = variant av (mk_var("wld",type_of t)) in
      (x::av, tac THEN ABBREV_TAC (mk_eq(x,t)))) cands (avoid,ALL_TAC) in
  tac (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Small assumption hypotheses (perf/si-fast-20261109). A fact carried       *)
(* across a step is rederived from the step's update theorem, an ASSUME of   *)
(* the update equation, so it gains that equation as a hypothesis           *)
(* (ASSUMPTION_STATE_UPDATE_TAC, MAYCHANGE_STATE_UPDATE_TAC). After k steps  *)
(* a long-lived assumption carries about k hypotheses, some of them large   *)
(* (an update equation holds every value the step wrote). Inferences on     *)
(* these theorems (term_union, INST) handle all of those hypotheses, so the *)
(* cost of a step rises with the number of steps before it: in 285 steps of *)
(* the holwasm dispatch it rose from 0.05 s to 8 s. This tactic replaces    *)
(* each assumption that has hypotheses other than its own conclusion by     *)
(* ASSUME of that conclusion, which removes that accumulated overhead (step *)
(* cost still depends on the size of the state, e.g. a long labels list).   *)
(* The justification restores the original theorems with PROVE_HYP, so the *)
(* goals are unchanged and the final theorem is the same.                   *)
(* ------------------------------------------------------------------------- *)

let WASM_COMPACT_HYPS_TAC : tactic = fun (asl,w) ->
  let small th = match hyp th with
      [] -> true
    | [h] -> aconv h (concl th)
    | _ -> false in
  let big = filter (fun (_,th) -> not (small th)) asl in
  if big = [] then ALL_TAC (asl,w) else
  let asl' = map (fun (l,th) -> if small th then (l,th) else (l,ASSUME(concl th))) asl in
  null_meta,[asl',w],
  (fun i ths -> match ths with
     [th] -> itlist (fun (_,ath) acc -> PROVE_HYP (INSTANTIATE_ALL i ath) acc) big th
   | _ -> failwith "WASM_COMPACT_HYPS_TAC: justification");;

let WASM_SINGLE_STEP_TAC execth extra s =
  WASM_STEP_TAC execth extra s THEN
  WASM_KEEP_LOADED_TAC s THEN
  DISCARD_OLD_WASMSTATE_TAC s THEN
  WASM_COMPACT_HYPS_TAC;;

let WASM_STEPS_TAC execth snums =
  MAP_EVERY (WASM_SINGLE_STEP_TAC execth []) (statenames "s" snums);;

let WASM_XSTEPS_TAC execth extra snums =
  MAP_EVERY (WASM_SINGLE_STEP_TAC execth extra) (statenames "s" snums);;

let WASM_SIM_TAC execth snums =
  ENSURES_INIT_TAC "s0" THEN
  WASM_STEPS_TAC execth snums THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* Prove |- wasm_entry mc = SOME n (entry offset computed from the bytes).  *)
(* ------------------------------------------------------------------------- *)

let WASM_ENTRY_TAC (mc_def:thm) =
  CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[mc_def] THENC WASM_DECODE_CONV)) THEN
  REFL_TAC;;

(* ------------------------------------------------------------------------- *)
(* Access tactics (tooling sprint 2, lane 1). An access theorem is proved as *)
(* one guarded ensures over the plain step,                                   *)
(*     ensures (\s s'. G s /\ wasm s s') P Q C,                              *)
(* where G s bounds the events of the instruction at s. Loops, frames and    *)
(* MAYCHANGE tactics run unchanged; WASM_ACCESS_STEP_TAC discharges G before *)
(* each step (evaluating the events with wasm_access_event_defs, then the     *)
(* bound with wasm_access_guard_defs and linear arithmetic). WASMT_GUARD_CLOSE *)
(* turns the guarded theorem into a traced one over wasmt, WASM_ACCESS_ERASE  *)
(* into the plain functional one. An overlay (another event function, another *)
(* bounds predicate) extends the three refs.                                  *)
(* ------------------------------------------------------------------------- *)

let wasm_access_event_defs = ref [wasm_mem_events; wasm_instr_events; wasm_ldst; wasm_ev_top];;
let wasm_access_event_consts = ref ["wasm_mem_events"];;
let wasm_access_guard_defs = ref [ALL; EX];;

let WASM_GUARD_STEP = prove
 (`!(G:wasmstate->bool) R s.
     G s /\ (?s'. wasm s s') /\
     (!s'. wasm s s' ==> eventually (\s s'. G s /\ wasm s s') R s')
     ==> eventually (\s s'. G s /\ wasm s s') R s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(CONJUNCT2(SPEC_ALL eventually_RULES)) THEN
  ASM_MESON_TAC[]);;

let WASM_ACCESS_ERASE = prove
 (`!(G:wasmstate->bool) P Q C.
     ensures (\s s'. G s /\ wasm s s') P Q C ==> ensures wasm P Q C`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures] THEN DISCH_TAC THEN
  X_GEN_TAC `s:wasmstate` THEN DISCH_TAC THEN
  MATCH_MP_TAC EVENTUALLY_GUARD_ERASE THEN EXISTS_TAC `G:wasmstate->bool` THEN
  ASM_SIMP_TAC[]);;

let WASMT_GUARD_CLOSE = prove
 (`!(G:wasmstate->bool) (Inv:(bool#num#num)list->bool) P Q C.
     (!s t. G s /\ Inv t ==> Inv (APPEND t (wasm_mem_events s))) /\
     ensures (\s s'. G s /\ wasm s s') P Q C
     ==> ensures wasmt (\x. P (FST x) /\ Inv (SND x))
                       (\x. Q (FST x) /\ Inv (SND x)) (\x y. T)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ensures; FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`s:wasmstate`; `t:(bool#num#num)list`] THEN STRIP_TAC THEN
  REWRITE_TAC[WASMT_ALT] THEN
  MP_TAC(ISPECL [`wasm`; `G:wasmstate->bool`;
                 `\s:wasmstate t:(bool#num#num)list. APPEND t (wasm_mem_events s)`;
                 `Inv:(bool#num#num)list->bool`;
                 `\s':wasmstate. Q s' /\ C (s:wasmstate) s'`] EVENTUALLY_GUARD_TRACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s:wasmstate`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:wasmstate` o REWRITE_RULE[ensures]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `t:(bool#num#num)list`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_MONO) THEN
  SIMP_TAC[]);;

let WASM_EVENTS_CONV (decode_ths:thm option array) (ths:thm list) tm =
  let s = rand tm in
  let pc_th = find_read_th "wpc" s ths
  and code_th = find_read_th "wcode" s ths in
  let pc = dest_small_numeral(rand(rhs(concl pc_th))) in
  let dth = match (try decode_ths.(pc) with _ -> None) with
      Some th -> th
    | None -> failwith ("WASM_EVENTS_CONV: no decode at pc "^string_of_int pc) in
  let vth = (REWRITE_CONV[VAL_WORD; DIMINDEX_64] THENC NUM_REDUCE_CONV)
              (mk_comb(`val:int64->num`, rhs(concl pc_th))) in
  let readths = filter (is_read_of s) ths in
  (REWRITE_CONV(!wasm_access_event_defs @ [code_th; pc_th; vth]) THENC
   REWRITE_CONV[dth] THENC
   REWRITE_CONV(!wasm_access_event_defs) THENC
   REWRITE_CONV(!wasm_access_event_defs @ readths) THENC
   REWRITE_CONV[EL; HD; TL] THENC
   DEPTH_CONV(NUM_RED_CONV ORELSEC EL_NUM_CONV) THENC
   REWRITE_CONV[HD; TL; ADD_CLAUSES]) tm;;

(* Discharge the guard at the current state: evaluate its events, then the *)
(* range arithmetic from the state-free num assumptions (wasm_arith_prove, *)
(* address atoms linearised), falling back to ASM_ARITH_TAC.              *)
let WASM_ACCESS_ARITH_TAC (asl,w) =
  let ths = map snd asl in
  let ants = filter (fun th -> let c = concl th in wasm_is_numrel c &&
                       not (exists (fun v -> type_of v = `:wasmstate`) (frees c))) ths in
  (ACCEPT_TAC (wasm_arith_prove ants w) ORELSE ASM_ARITH_TAC) (asl,w);;

let WASM_ACCESS_GUARD_TAC decode_ths (asl,w) =
  let ths = map snd asl in
  let ev = find_term (fun t -> match t with
      Comb(Const(c,_),_) -> mem c !wasm_access_event_consts | _ -> false) w in
  let eth = WASM_EVENTS_CONV decode_ths ths ev in
  (GEN_REWRITE_TAC ONCE_DEPTH_CONV [eth] THEN
   REWRITE_TAC(!wasm_access_guard_defs) THEN
   CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[] THEN
   REPEAT CONJ_TAC THEN
   (WASM_ACCESS_ARITH_TAC ORELSE
    (fun (_,g) -> failwith ("WASM_ACCESS_GUARD: event not inside the allowed ranges: "^
                            string_of_term g)))) (asl,w);;

let WASM_ACCESS_BASIC_STEP_TAC =
  let wasm_tm = `wasm` and ws_ty = `:wasmstate` in
  fun decode_ths extra sname (asl,w) ->
    let sv = rand w and sv' = mk_var(sname,ws_ty) in
    let atm = mk_comb(mk_comb(wasm_tm,sv),sv') in
    let eth = WASM_CONV decode_ths extra (map snd asl) atm in
    let r = rhs(concl eth) in
    if not (is_eq r && rand r = sv') then
      failwith ("WASM_ACCESS_BASIC_STEP_TAC: step did not reduce to a state update: "^
                string_of_term r) else
    (MATCH_MP_TAC WASM_GUARD_STEP THEN REPEAT CONJ_TAC THENL
     [BETA_TAC THEN WASM_ACCESS_GUARD_TAC decode_ths;
      GEN_REWRITE_TAC BINDER_CONV [eth] THEN CONV_TAC EXISTS_NONTRIVIAL_CONV;
      X_GEN_TAC sv' THEN GEN_REWRITE_TAC LAND_CONV [eth]]) (asl,w);;

let WASM_ACCESS_STEP_TAC (_,decode_ths) extra sname =
  WASM_ACCESS_BASIC_STEP_TAC decode_ths extra sname THEN
  WASM_MEMFACT_UPDATE_TAC THEN
  WASM_MEM_UPDATE_TAC THEN
  ASSUMPTION_STATE_UPDATE_TAC THEN
  MAYCHANGE_STATE_UPDATE_TAC THEN
  DISCH_THEN(fun th ->
    let thl = STATE_UPDATE_NEW_RULE th in
    if thl = [] then ALL_TAC else
    MP_TAC(end_itlist CONJ thl) THEN
    CONV_TAC(LAND_CONV(DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV))) THEN
    STRIP_TAC);;

let WASM_ACCESS_SINGLE_STEP_TAC execth extra s =
  WASM_ACCESS_STEP_TAC execth extra s THEN
  WASM_KEEP_LOADED_TAC s THEN
  DISCARD_OLD_WASMSTATE_TAC s;;

let WASM_ACCESS_STEPS_TAC execth snums =
  MAP_EVERY (WASM_ACCESS_SINGLE_STEP_TAC execth []) (statenames "s" snums);;

let WASM_ACCESS_XSTEPS_TAC execth extra snums =
  MAP_EVERY (WASM_ACCESS_SINGLE_STEP_TAC execth extra) (statenames "s" snums);;

let WASM_ACCESS_SIM_TAC execth snums =
  ENSURES_INIT_TAC "s0" THEN
  WASM_ACCESS_STEPS_TAC execth snums THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* Traced stepping on pair states (x = (s,t)): one step of wasmt (events    *)
(* appended; more relations can be added to wasm_traced_step_thms). The events of the stepping     *)
(* state are evaluated before the old state is discarded.                    *)
(* ------------------------------------------------------------------------- *)

let WASMT_STEP = prove
 (`!R s t.
     (?s'. wasm s s') /\
     (!s'. wasm s s' ==> eventually wasmt R (s',APPEND t (wasm_mem_events s)))
     ==> eventually wasmt R (s,t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(CONJUNCT2(SPEC_ALL eventually_RULES)) THEN
  REWRITE_TAC[FORALL_PAIR_THM; EXISTS_PAIR_THM; wasmt; FST; SND] THEN
  ASM_MESON_TAC[]);;

let wasm_traced_step_thms = ref [WASMT_STEP];;

let WASM_TRACED_STEP_TAC (_,decode_ths) extra sname (asl,w) =
  let x = rand w in
  let sv = lhand x and sv' = mk_var(sname,`:wasmstate`) in
  let eth = WASM_CONV decode_ths extra (map snd asl) (mk_comb(mk_comb(`wasm`,sv),sv')) in
  let r = rhs(concl eth) in
  if not (is_eq r && rand r = sv') then
    failwith ("WASM_TRACED_STEP_TAC: step did not reduce: "^string_of_term r) else
  let ev = find_term (fun t -> match t with
      Comb(Const(c,_),s) -> mem c !wasm_access_event_consts && s = sv | _ -> false) in
  (FIRST (map MATCH_MP_TAC !wasm_traced_step_thms) THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC BINDER_CONV [eth] THEN CONV_TAC EXISTS_NONTRIVIAL_CONV;
    X_GEN_TAC sv' THEN
    (fun (asl,w) ->
       let evth = WASM_EVENTS_CONV decode_ths (map snd asl) (ev w) in
       GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [evth] (asl,w)) THEN
    REWRITE_TAC[APPEND] THEN
    GEN_REWRITE_TAC LAND_CONV [eth] THEN
    WASM_MEMFACT_UPDATE_TAC THEN WASM_MEM_UPDATE_TAC THEN
    ASSUMPTION_STATE_UPDATE_TAC THEN MAYCHANGE_STATE_UPDATE_TAC THEN
    DISCH_THEN(fun th ->
      let thl = STATE_UPDATE_NEW_RULE th in
      if thl = [] then ALL_TAC else
      MP_TAC(end_itlist CONJ thl) THEN
      CONV_TAC(LAND_CONV(DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV))) THEN
      STRIP_TAC) THEN
    WASM_KEEP_LOADED_TAC sname THEN
    DISCARD_OLD_WASMSTATE_TAC sname]) (asl,w);;

let WASM_TRACED_STEPS_TAC execth snums =
  MAP_EVERY (WASM_TRACED_STEP_TAC execth []) (statenames "s" snums);;

(* Open a traced ensures on pair states: x = (s0,t0). *)
let WASM_TRACED_INIT_TAC =
  REWRITE_TAC[ensures; FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`s0:wasmstate`; `t0:(bool#num#num)list`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `t0:(bool#num#num)list`)) THEN
  ASSUME_TAC(ISPEC `s0:wasmstate` MAYCHANGE_STARTER);;

let WASM_TRACED_FINAL_TAC =
  MATCH_MP_TAC(CONJUNCT1(SPEC_ALL eventually_RULES)) THEN
  REWRITE_TAC[FST; SND] THEN ASM_REWRITE_TAC[ADD_CLAUSES];;


(* ------------------------------------------------------------------------- *)
(* WF_CONV: evaluate the exact float operations of wasm.ml (wfrel, wftrap,   *)
(* and wfcvt at its exact opcodes) on numeral bit patterns, e.g.            *)
(*   WF_CONV `wftrap 176 (word 4890909195324358656:int64)` = |- ... <=> T. *)
(* Used by wasm/conformance/conf_float.ml (hol-hearth wasm tooling H1).     *)
(* ------------------------------------------------------------------------- *)

let WF_RED_CONV =
  WORD_RED_CONV ORELSEC NUM_RED_CONV ORELSEC INT_RED_CONV ORELSEC BITSIZE_CONV;;

let WF_CONV =
  let base = [wfrel; wftrap; wfcvt; wf_nan; wf_inf; wf_key; wf_trunc; wf_mag;
              wf_exp; wf_frac; wf_sign; wf_ebits; wf_fbits; wf_tlo; wf_thi; wf_tbits;
              wf_tidx; wf_of_int; DIMINDEX_32; DIMINDEX_64] in
  let tidy = [NUM_OF_INT_OF_NUM; INT_ABS_NUM; INT_ABS_NEG; INT_NEG_NEG] in
  REWRITE_CONV (base @ tidy) THENC DEPTH_CONV WF_RED_CONV THENC
  REPEATC(CHANGED_CONV(ONCE_DEPTH_CONV let_CONV THENC DEPTH_CONV WF_RED_CONV THENC
                       REWRITE_CONV tidy));;
