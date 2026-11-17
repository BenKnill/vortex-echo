(* ========================================================================= *)
(* Bubble Echo v4 one-film: windowed linear-cost decode tables for the      *)
(* of2_core export bodies (1.5-2 KB each). A copy of the window functions   *)
(* of capillary/proofs/cap_driver_m3_dec.ml (same code; that file also      *)
(* loads the capillary driver bindings): each wdrop table entry keeps 32     *)
(* bytes and an opaque select term for the rest, found by a hash on the    *)
(* offset. The results are the profile's |- wasm_decode mc pc = SOME (i,len) *)
(* theorems, proved by kernel inference.                                     *)
(* ========================================================================= *)

needs "../../capillary/proofs/wasm_fastdec.ml";;

let wdrop_window_table (mc_def:thm) (w:int) =
  let ths = Array.of_list (wdrop_table mc_def) in
  let len = Array.length ths - 1 in
  (* |- (@l. l = wdrop k mc) = suffix_k : the select term is opaque to the compset *)
  let tail k = TRANS (ISPEC (lhs(concl ths.(k))) SELECT_REFL) ths.(k) in
  let entry k =
    if k + w > len then ths.(k) else
    let rec build j th =
      if j < k then th else
      let s = rhs(concl ths.(j)) in
      let b = rand(rator s) in
      build (j - 1) (AP_TERM (mk_comb(rator(rator s),b)) th) in
    TRANS ths.(k) (SYM (build (k + w - 1) (tail (k + w)))) in
  map entry (0--len);;

let window_decode_compset (mc_def:thm) (w:int) =
  let mc = lhs(concl mc_def) in
  let lth = (REWRITE_CONV[mc_def] THENC LENGTH_CONV) (mk_comb(`LENGTH:byte list->num`,mc)) in
  let tab = wdrop_window_table mc_def w in
  (* the table is consulted through a hash on the offset, not as rewrite rules *)
  let htbl = Hashtbl.create 16384 in
  List.iteri (fun k th -> Hashtbl.add htbl k th) tab;
  let wdrop_conv tm =
    match tm with
      Comb(Comb(_,k),c) when c = mc && is_numeral k ->
        (try Hashtbl.find htbl (dest_small_numeral k) with Not_found -> failwith "wdrop_conv")
    | _ -> failwith "wdrop_conv" in
  let cs = Compute.bool_compset () in
  Compute.set_skip cs `COND:bool->A->A->A` (Some 1);
  Compute.add_thms
   ([wobind; whd; wdrop; wtake; wuleb; wsleb; wblocktype; wmemarg; wrelop_of;
     wdecode_op; wdecode_raw; WSCAN_ALT; WELSE_SCAN_ALT; WULEBS_ALT;
     wblock_arity; wasm_decode; WDECLS_ALT; wasm_entry;
     FST; SND; HD; TL; LENGTH; lth]) cs;
  List.iter (fun (t,n,c) -> Compute.add_conv (t,n,c) cs)
   [`wdrop:num->byte list->byte list`,2,wdrop_conv;
    `(+):num->num->num`,2,NUM_ADD_CONV;
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

let FAST_MK_EXEC_RANGES (mc_def:thm) (ranges:(int*int) list) : thm * (thm option array) =
  let mc = lhs(concl mc_def) in
  let lth,cs = window_decode_compset mc_def 32 in
  let conv = Compute.WEAK_CBV_CONV cs in
  let len = dest_small_numeral(rhs(concl lth)) in
  let arr = Array.make len None in
  let dec = `wasm_decode` in
  let rec sweep pc hi =
    if pc >= hi then () else
    let th = conv (list_mk_comb(dec,[mc;mk_small_numeral pc])) in
    let r = rhs(concl th) in
    if not (is_comb r && fst(dest_const(rator r)) = "SOME") || hyp(th) <> [] then
      failwith ("FAST_MK_EXEC_RANGES: no closed decode at offset "^string_of_int pc) else
    let _,n = dest_pair(rand r) in
    arr.(pc) <- Some th;
    sweep (pc + dest_small_numeral n) hi in
  List.iter (fun (lo,hi) -> sweep lo hi) ranges; (lth,arr);;
