(* ========================================================================= *)
(* Decoding large function bodies in linear time (lane WASM2, 2026-11-04).  *)
(*                                                                           *)
(* WASM_MK_EXEC_RULE decodes each offset by evaluation; a block's decode     *)
(* scans forward to its matching end (wscan), so a body of n bytes costs     *)
(* about n^2 (1737 bytes: 280 s) and the 15381-byte bytecode interpreter of  *)
(* hol.wasm is out of reach. This rule produces the same theorems            *)
(*   |- wasm_decode mc pc = SOME (i,len)                                     *)
(* for every instruction offset pc reachable by the linear sweep, but        *)
(* proves the block/if continuations compositionally:                        *)
(*                                                                           *)
(*   1. |- wdrop k mc = CONS b_k (wdrop (k+1) mc) for every k (one linear    *)
(*      pass over the literal body);                                         *)
(*   2. each instruction is decoded by evaluation on a window of exactly     *)
(*      its own bytes, the rest of the body staying the opaque term          *)
(*      wdrop (k+len) mc;                                                    *)
(*   3. scan facts for balanced regions,                                     *)
(*        R(p,q,k):  !f d. wscan (f + k) mc p d = wscan f mc q d,            *)
(*      and the welse_scan analogues, are composed bottom-up over the block  *)
(*      structure (generic lemmas below, proved once), so each block's       *)
(*      continuation costs O(1) inferences after its body.                   *)
(*                                                                           *)
(* Everything is kernel inference from the definitions in wasm.ml: no new    *)
(* axioms, no new constants. Requires the body to be a literal byte list     *)
(* (as define_from_wasm makes it).                                           *)
(* ========================================================================= *)

needs "wasm_tactics.ml";;

(* ------------------------------------------------------------------------- *)
(* Generic lemmas.                                                           *)
(* ------------------------------------------------------------------------- *)

let WDROP_CONS_NEXT = prove
 (`!l n (x:A) y. wdrop n l = CONS x y ==> wdrop n l = CONS x (wdrop (n + 1) l)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WDROP_NEXT th]) THEN
  ASM_REWRITE_TAC[]);;

let WSCAN_STEP = prove
 (`!code p b t i n f d.
     wdrop p code = CONS b t /\ wdecode_raw code p = SOME (i,n)
     ==> wscan (f + 1) code p d =
         if val b = 2 \/ val b = 3 \/ val b = 4
         then wscan f code (p + n) (d + 1)
         else if val b = 11 then
           (if d = 0 then SOME (p + n) else wscan f code (p + n) (d - 1))
         else wscan f code (p + n) d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM ADD1; wscan] THEN
  ASM_REWRITE_TAC[whd; wobind; SND]);;

let WELSE_STEP = prove
 (`!code p b t i n f d.
     wdrop p code = CONS b t /\ wdecode_raw code p = SOME (i,n)
     ==> welse_scan (f + 1) code p d =
         if val b = 2 \/ val b = 3 \/ val b = 4
         then welse_scan f code (p + n) (d + 1)
         else if val b = 11 then
           (if d = 0 then SOME p else welse_scan f code (p + n) (d - 1))
         else if val b = 5 /\ d = 0 then SOME (p + n)
         else welse_scan f code (p + n) d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM ADD1; welse_scan] THEN
  ASM_REWRITE_TAC[whd; wobind; SND]);;

let WSCAN_SEQ = prove
 (`!code p q r k1 k2.
     (!f d. wscan (f + k1) code p d = wscan f code q d) /\
     (!f d. wscan (f + k2) code q d = wscan f code r d)
     ==> (!f d. wscan (f + (k1 + k2)) code p d = wscan f code r d)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[ARITH_RULE `f + (k1 + k2) = (f + k2) + k1`] THEN
  ASM_REWRITE_TAC[]);;

let WSCAN_NEST = prove
 (`!code p p1 q q1 k.
     (!f d. wscan (f + 1) code p d = wscan f code p1 (d + 1)) /\
     (!f d. wscan (f + k) code p1 d = wscan f code q d) /\
     (!f d. wscan (f + 1) code q (d + 1) = wscan f code q1 d)
     ==> (!f d. wscan (f + (k + 2)) code p d = wscan f code q1 d)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[ARITH_RULE `f + (k + 2) = ((f + 1) + k) + 1`] THEN
  ASM_REWRITE_TAC[]);;

let WSCAN_EMPTY = prove
 (`!code p. !f d. wscan (f + 0) code p d = wscan f code p d`,
  REWRITE_TAC[ADD_CLAUSES]);;

let WSCAN_CONT = prove
 (`!code p q r k.
     (!f d. wscan (f + k) code p d = wscan f code q d) /\
     (!f. wscan (f + 1) code q 0 = SOME r) /\
     k + 1 <= LENGTH (code:byte list)
     ==> wscan (LENGTH code) code p 0 = SOME r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (code:byte list) = ((LENGTH code - (k + 1)) + 1) + k`
   SUBST1_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]);;

let WELSE_SEQ0 = prove
 (`!code p q r k1 k2.
     (!f d. welse_scan (f + k1) code p d = welse_scan f code q d) /\
     (!f d. welse_scan (f + k2) code q d = welse_scan f code r d)
     ==> (!f d. welse_scan (f + (k1 + k2)) code p d = welse_scan f code r d)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[ARITH_RULE `f + (k1 + k2) = (f + k2) + k1`] THEN
  ASM_REWRITE_TAC[]);;

let WELSE_SEQ1 = prove
 (`!code p q r k1 k2.
     (!f d. welse_scan (f + k1) code p (d + 1) = welse_scan f code q (d + 1)) /\
     (!f d. welse_scan (f + k2) code q (d + 1) = welse_scan f code r (d + 1))
     ==> (!f d. welse_scan (f + (k1 + k2)) code p (d + 1) =
                welse_scan f code r (d + 1))`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[ARITH_RULE `f + (k1 + k2) = (f + k2) + k1`] THEN
  ASM_REWRITE_TAC[]);;

let WELSE_NEST = prove
 (`!code p p1 q q1 k.
     (!f d. welse_scan (f + 1) code p d = welse_scan f code p1 (d + 1)) /\
     (!f d. welse_scan (f + k) code p1 (d + 1) = welse_scan f code q (d + 1)) /\
     (!f d. welse_scan (f + 1) code q (d + 1) = welse_scan f code q1 d)
     ==> (!f d. welse_scan (f + (k + 2)) code p d = welse_scan f code q1 d)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[ARITH_RULE `f + (k + 2) = ((f + 1) + k) + 1`] THEN
  ASM_REWRITE_TAC[]);;

let WELSE_EMPTY0 = prove
 (`!code p. !f d. welse_scan (f + 0) code p d = welse_scan f code p d`,
  REWRITE_TAC[ADD_CLAUSES]);;

let WELSE_EMPTY1 = prove
 (`!code p. !f d. welse_scan (f + 0) code p (d + 1) = welse_scan f code p (d + 1)`,
  REWRITE_TAC[ADD_CLAUSES]);;

let WELSE_CONT = prove
 (`!code p q r k.
     (!f d. welse_scan (f + k) code p d = welse_scan f code q d) /\
     (!f. welse_scan (f + 1) code q 0 = SOME r) /\
     k + 1 <= LENGTH (code:byte list)
     ==> welse_scan (LENGTH code) code p 0 = SOME r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (code:byte list) = ((LENGTH code - (k + 1)) + 1) + k`
   SUBST1_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]);;

let WASM_DECODE_PLAIN = prove
 (`!code pc i n b t.
     wdecode_raw code pc = SOME (i,n) /\ wdrop pc code = CONS b t /\
     ~(val b = 2) /\ ~(val b = 4)
     ==> wasm_decode code pc = SOME (i,n)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[wasm_decode; wobind; HD]);;

let WASM_DECODE_BLOCK = prove
 (`!code pc a z n b t p1 e.
     wdecode_raw code pc = SOME (Wblock a z,n) /\ wdrop pc code = CONS b t /\
     val b = 2 /\ pc + n = p1 /\ wscan (LENGTH code) code p1 0 = SOME e
     ==> wasm_decode code pc = SOME (Wblock a e,n)`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[wasm_decode; wobind; HD; FST; SND; wblock_arity]);;

let WASM_DECODE_IF = prove
 (`!code pc a z1 z2 n b t p1 e e1.
     wdecode_raw code pc = SOME (Wif a z1 z2,n) /\ wdrop pc code = CONS b t /\
     val b = 4 /\ pc + n = p1 /\
     wscan (LENGTH code) code p1 0 = SOME e /\
     welse_scan (LENGTH code) code p1 0 = SOME e1
     ==> wasm_decode code pc = SOME (Wif a e1 e,n)`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[wasm_decode; wobind; HD; FST; SND; wblock_arity; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* The rule.                                                                 *)
(* ------------------------------------------------------------------------- *)

(* instruction length from the bytes (mirrors wdecode_op; checked below     *)
(* against the length the logic computes)                                   *)
let wasm_ilen (bs:int array) (k:int) : int =
  let leblen j = let rec go i = if bs.(i) land 0x80 = 0 then i - j + 1
                                else go (i + 1) in go j in
  let op = bs.(k) in
  if op = 0x02 || op = 0x03 || op = 0x04 || op = 0x3F || op = 0x40 then 2
  else if op = 0x0C || op = 0x0D || op = 0x10 || (0x20 <= op && op <= 0x24)
  then 1 + leblen (k + 1)
  else if op = 0x0E then
    let c = ref 0 and sh = ref 0 and i = ref (k + 1) in
    while bs.(!i) land 0x80 <> 0 do
      c := !c lor ((bs.(!i) land 0x7f) lsl !sh); sh := !sh + 7; incr i done;
    c := !c lor ((bs.(!i) land 0x7f) lsl !sh); incr i;
    for j = 0 to !c do ignore j; i := !i + leblen !i done;
    !i - k
  else if op = 0x11 then let a = leblen (k + 1) in 1 + a + leblen (k + 1 + a)
  else if 0x28 <= op && op <= 0x3E then
    let a = leblen (k + 1) in 1 + a + leblen (k + 1 + a)
  else if op = 0x41 || op = 0x42 then 1 + leblen (k + 1)
  else if op = 0x43 then 5
  else if op = 0x44 then 9
  else if op = 0xFC then
    let a = leblen (k + 1) in
    let sub = (* the whole LEB128 value: padded encodings are valid *)
      let rec go i sh acc =
        let b = bs.(i) in let acc = acc lor ((b land 0x7f) lsl sh) in
        if b land 0x80 = 0 then acc else go (i + 1) (sh + 7) acc in
      go (k + 1) 0 0 in
    1 + a + (if sub = 10 then 2 else if sub = 11 then 1
             else if sub < 8 then 0  (* trunc_sat (lane hearth-f64) *)
             else failwith "wasm_ilen: unsupported 0xFC sub-opcode")
  else 1;;

let wasm_bytes_of_list (tm:term) : int array =
  Array.of_list (map (fun t -> dest_small_numeral(rand t)) (dest_list tm));;

let wasm_bignum_norm = CONV_RULE(DEPTH_CONV NUM_ADD_CONV);;

let wasm_step_simp =
  REWRITE_RULE[COND_CLAUSES] o
  CONV_RULE(DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV));;

let WASM_BIG_MK_EXEC_RULE (mc_def:thm) (entry:int)
    : thm * (thm option array) =
  let mc = lhs(concl mc_def) in
  let bs = wasm_bytes_of_list (rhs(concl mc_def)) in
  let len = Array.length bs in
  let lth = (REWRITE_CONV[mc_def] THENC LENGTH_CONV)
              (mk_comb(`LENGTH:byte list->num`,mc)) in
  (* 1. cons table *)
  let ctab =
    let sfx = Array.of_list (wasm_wdrop_table mc_def) in
    Array.init len (fun k ->
      wasm_bignum_norm (MATCH_MP WDROP_CONS_NEXT sfx.(k))) in
  let wdrop_tm = `wdrop:num->byte list->byte list` in
  (* 2. windows and raw decodes *)
  let rec window k m =
    if m = 0 then REFL (list_mk_comb(wdrop_tm,[mk_small_numeral k; mc])) else
    let c = ctab.(k) in
    let h = rator(rhs(concl c)) in
    TRANS c (AP_TERM h (window (k + 1) (m - 1))) in
  let raw_tm = `wdecode_raw` in
  let raw k =
    let n = wasm_ilen bs k in
    let tm = list_mk_comb(raw_tm,[mc; mk_small_numeral k]) in
    let th = (GEN_REWRITE_CONV I [wdecode_raw] THENC
              PURE_REWRITE_CONV[window k n] THENC WASM_DECODE_CONV) tm in
    let r = rhs(concl th) in
    let ok = try let _,nn = dest_pair(rand r) in
                 fst(dest_const(rator r)) = "SOME" && dest_small_numeral nn = n
             with Failure _ -> false in
    if not ok then failwith ("WASM_BIG_MK_EXEC_RULE: no decode at offset "^
                             string_of_int k^": "^string_of_term r) else th in
  (* 3. per-instruction scan steps *)
  let wscan_step k rth = wasm_step_simp (MATCH_MP WSCAN_STEP (CONJ ctab.(k) rth))
  and welse_step k rth = wasm_step_simp (MATCH_MP WELSE_STEP (CONJ ctab.(k) rth)) in
  let fv = `f:num` and dv = `d:num` and one = `1` and zero = `0` in
  let at_suc th = (* !f d. P f (d + 1) from !f d. P f d (d conditional) *)
    GENL [fv;dv] (CONV_RULE(DEPTH_CONV NUM_RED_CONV THENC
                           REWRITE_CONV[ADD_EQ_0; ARITH_EQ; ADD_SUB])
                   (SPECL [fv; mk_binary "+" (dv,one)] th))
  and at_zero th =
    GEN fv (CONV_RULE(REWRITE_CONV[COND_CLAUSES]) (SPECL [fv; zero] th)) in
  let e0_to_e1 th = GENL [fv;dv] (SPECL [fv; mk_binary "+" (dv,one)] th) in
  let arr = Array.make len None in
  let lth_le k = (* |- k + 1 <= LENGTH mc *)
    EQT_ELIM((LAND_CONV NUM_ADD_CONV THENC RAND_CONV(K lth) THENC NUM_LE_CONV)
              (mk_binary "<=" (mk_binary "+" (mk_small_numeral k,one),
                               mk_comb(`LENGTH:byte list->num`,mc)))) in
  let kof th = (* k from !f d. wscan (f + k) mc p d = .. *)
    let _,args = strip_comb(lhs(snd(strip_forall(concl th)))) in
    dest_small_numeral(rand(hd args)) in
  let seq lem empty p ths =
    match ths with
      [] -> ISPECL [mc; mk_small_numeral p] empty
    | h::t -> List.fold_left
                (fun acc th -> wasm_bignum_norm (MATCH_MP lem (CONJ acc th))) h t in
  let decode_plain k rth =
    let b = lhand(rhs(concl ctab.(k))) in
    let vb = WORD_RED_CONV (mk_comb(`val:byte->num`,b)) in
    let ne n = EQF_ELIM(CONV_RULE(RAND_CONV NUM_EQ_CONV)
                 (AP_THM (AP_TERM `(=):num->num->bool` vb) (mk_small_numeral n))) in
    MATCH_MP WASM_DECODE_PLAIN (end_itlist CONJ [rth; ctab.(k); ne 2; ne 4]) in
  let valb k = WORD_RED_CONV (mk_comb(`val:byte->num`,lhand(rhs(concl ctab.(k))))) in
  (* parse a body starting at pos: returns (items, end offset) where each   *)
  (* item is (start, stop, r, e0 option, e1)                                 *)
  let rec parse pos acc =
    if pos >= len then failwith "WASM_BIG_MK_EXEC_RULE: ran off the body" else
    let op = bs.(pos) in
    if op = 0x0B then (rev acc, pos) else
    let rth = raw pos in
    let n = wasm_ilen bs pos in
    if op = 0x02 || op = 0x03 || op = 0x04 then
      let r_open = wscan_step pos rth and e_open = welse_step pos rth in
      let items, q = parse (pos + n) [] in
      let rq = raw q in
      let r_end = wscan_step q rq and e_end = welse_step q rq in
      let body_r = seq WSCAN_SEQ WSCAN_EMPTY (pos + n)
                     (map (fun (_,_,r,_,_) -> r) items)
      and body_e1 = seq WELSE_SEQ1 WELSE_EMPTY1 (pos + n)
                     (map (fun (_,_,_,_,e1) -> e1) items) in
      let nest_r = wasm_bignum_norm
        (MATCH_MP WSCAN_NEST (end_itlist CONJ [r_open; body_r; at_suc r_end]))
      and nest_e0 = wasm_bignum_norm
        (MATCH_MP WELSE_NEST (end_itlist CONJ [e_open; body_e1; at_suc e_end])) in
      arr.(q) <- Some (decode_plain q rq);
      let p1th = NUM_ADD_CONV (mk_binary "+" (mk_small_numeral pos,
                                              mk_small_numeral n)) in
      let cont () =
        let k = kof body_r in
        MATCH_MP WSCAN_CONT (end_itlist CONJ [body_r; at_zero r_end; lth_le k]) in
      (if op = 0x03 then arr.(pos) <- Some (decode_plain pos rth)
       else if op = 0x02 then
         arr.(pos) <- Some (MATCH_MP WASM_DECODE_BLOCK
                       (end_itlist CONJ [rth; ctab.(pos); valb pos; p1th; cont ()]))
       else
         let rec prefix l = match l with
             [] -> [], None
           | ((s,_,_,None,_)::_) -> [], Some s
           | ((_,_,_,Some e0,_)::t) -> let a,b = prefix t in e0::a, b in
         let pre, els = prefix items in
         let pre_e0 = seq WELSE_SEQ0 WELSE_EMPTY0 (pos + n) pre in
         let fin = match els with
             Some s -> at_zero (welse_step s (raw s))
           | None -> at_zero e_end in
         let k = kof pre_e0 in
         let e1th = MATCH_MP WELSE_CONT (end_itlist CONJ [pre_e0; fin; lth_le k]) in
         arr.(pos) <- Some (MATCH_MP WASM_DECODE_IF
                       (end_itlist CONJ [rth; ctab.(pos); valb pos; p1th; cont (); e1th])));
      parse (q + 1) ((pos, q + 1, nest_r, Some nest_e0, e0_to_e1 nest_e0)::acc)
    else if op = 0x05 then
      let r = wscan_step pos rth and e = welse_step pos rth in
      arr.(pos) <- Some (decode_plain pos rth);
      parse (pos + n) ((pos, pos + n, r, None, at_suc e)::acc)
    else
      let r = wscan_step pos rth and e = welse_step pos rth in
      arr.(pos) <- Some (decode_plain pos rth);
      parse (pos + n) ((pos, pos + n, r, Some e, e0_to_e1 e)::acc) in
  let _, q = parse entry [] in
  arr.(q) <- Some (decode_plain q (raw q));
  if q + 1 <> len then failwith "WASM_BIG_MK_EXEC_RULE: trailing bytes after the body" else
  (lth, arr);;
