(* ========================================================================= *)
(* Vortex pop R5 droplet birth (vortex-r5birth PROVE-birth r3, Claude Opus   *)
(* 5.5, 2026-11-11): lemma layer 5 on pop_r5bp_lem4.ml: the three record-    *)
(* store segments R5B_SEGE (pinch-off, parent debit), R5B_SEGH (spray) and   *)
(* R5B_SEGJ (antipode).                                                      *)
(* r3 fix: the r1 R5B_ADDR_NORM_CONV never failed (NUM_NORMALIZE_CONV returns *)
(* REFL on a normal form), so DEPTH_CONV of it did not terminate.            *)
(* lem5b = lem5 with r5b_close_extra read when the tactic runs (lem5 read it *)
(* at definition time, before R5B_OR65536 was added: SEGH NO_TAC).         *)
(* ========================================================================= *)
let R5B_ADDR_NORM_CONV tm =
  match tm with Comb(Const("word",_),x) when type_of x = `:num` && not (is_numeral x) ->
    let th = RAND_CONV NUM_NORMALIZE_CONV tm in
    if rand(concl th) = tm then failwith "R5B_ADDR_NORM_CONV: unchanged" else th
  | _ -> failwith "R5B_ADDR_NORM_CONV";;
let R5B_MEMCLOSE_TAC : tactic =
  REPEAT CONJ_TAC THEN
  TRY(GEN_TAC THEN DISCH_TAC) THEN
  W(fun (asl,w) -> if can (find_term ((=) `i:num = k`)) w then
      ASM_CASES_TAC `i:num = k` THENL [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[]; ASM_REWRITE_TAC[]]
    else ALL_TAC) THEN
  REPEAT R5B_PEEL_TAC THEN CONV_TAC(ONCE_DEPTH_CONV R5B_ADDR_NORM_CONV) THEN (fun g -> ASM_REWRITE_TAC !r5b_close_extra g) THEN
  TRY VK_ARITH_TAC THEN NO_TAC;;
(* spray/antipode record word 7 = k | 65536 *)
let R5B_VOR32 = prove(`!x y:int32. val y <= val (word_or x y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM WORD_ULE] THEN BITBLAST_TAC);;
let R5B_OR65536 = prove(`!x:int32. 65536 <= val (word_or x (word 65536))`,
  GEN_TAC THEN MP_TAC(ISPECL [`x:int32`; `word 65536:int32`] R5B_VOR32) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV);;
let () = r5b_close_extra := [R5B_OR65536];;
(* ---- generalization that KEEPS the defining equation of a value containing a load from a non-constant address
   (the parent ZQ[k]/ZP[k] of the pinch-off debit); R5B_ABSIMP_TAC then peels each such load to its m0 read *)
let r5b_protected3 v = can (find_term (fun t -> match t with
    Comb(Comb(Const("read",_),Comb(Const("bytes32",_),Comb(Const("word",_),a))),_) -> not (is_numeral a)
  | _ -> false)) v;;
let R5B_GEN_TAC3 : tactic = fun (asl,w) ->
  if !r5b_abbrev_thresh = 0 then ALL_TAC (asl,w) else
  let s = rand w in
  let vals = List.concat (map (fun (_,th) -> let c = concl th in
     if is_eq c && (match lhs c with Comb(Comb(Const("read",_),comp),s') ->
                      s' = s && (comp = `wstack` || (is_comb comp && rator comp = `wlocal`)) | _ -> false)
     then (let r = rhs c in
           let elems = if is_list r then dest_list r else [r] in
           mapfilter (fun e -> let h,a = strip_comb e in
                        if (h = `I32` || h = `I64`) && length a = 1 then hd a else fail()) elems)
     else []) asl) in
  let big = setify (filter (fun v -> r5b_tsize v > !r5b_abbrev_thresh && not (is_var v)) vals) in
  let big = sort (fun a b -> r5b_tsize a > r5b_tsize b) big in
  MAP_EVERY (fun v -> fun g -> incr r5b_vctr;
       let nv = mk_var("ab" ^ string_of_int !r5b_vctr, type_of v) in
       if r5b_protected3 v then ABBREV_TAC (mk_eq(nv, v)) g else
       (ABBREV_TAC (mk_eq(nv, v)) THEN
        REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> let c = concl th in is_eq c && rhs c = nv)))) g) big (asl,w);;
let rec R5B_RUN3 exec stops : tactic = fun (asl,w) ->
  let s = rand w in
  if r5b_status asl s <> `WRunning` then ALL_TAC (asl,w) else
  let pc = r5b_pc asl s in
  if mem pc stops then ALL_TAC (asl,w) else
  let sn = r5b_fresh() in
  ((R5B_STEP1 exec sn ORELSE R5B_GSTEP exec sn) THEN R5B_GEN_TAC3 THEN R5B_RUN3 exec stops) (asl,w);;
let r5b_isab_load c = is_eq c && is_var (rhs c) &&
  (let nm = fst(dest_var(rhs c)) in String.length nm > 2 && String.sub nm 0 2 = "ab") &&
  (match lhs c with Comb(Comb(Const("read",_),Comb(Const("bytes32",_),_)),Comb(Comb(Comb(Const("write",_),_),_),_)) -> true
   | _ -> false);;
let rec r5b_wbase m = match m with Comb(Comb(Comb(Const("write",_),_),_),m') -> r5b_wbase m' | _ -> m;;
let R5B_ABSIMP1 : tactic =
  FIRST_X_ASSUM (fun th ->
    let c = concl th in if not (r5b_isab_load c) then failwith "R5B_ABSIMP1" else
    let l = lhs c and v = rhs c in
    let ra, m = dest_comb l in
    let target = mk_comb(ra, r5b_wbase m) in
    SUBGOAL_THEN (mk_eq(v, target)) SUBST_ALL_TAC THENL
     [SUBST1_TAC (SYM th) THEN REPEAT R5B_PEEL_TAC THEN REWRITE_TAC[]; ALL_TAC]);;
let R5B_ABSIMP_TAC = REPEAT R5B_ABSIMP1;;
(* ---- 2018 -> 2586, born pinch-off bead: record stores words 7,6,9,8,2,1,0,5,4,3, ZQ[k] -= w8, ZP[k] -= w9, n++ *)
let r5b_segE_stmt = list_mk_forall([`m0:int64->byte`;`k:num`;`n:num`;`t:int32`],
  mk_imp(`k < 2048 /\ n < 16384`,
   r5b_ens (r5b_pred 2018 r5b_L1B r5b_trk1x [])
     (mk_abs(`s:wasmstate`, r5b_body_m 2586 r5b_L1 [0,`word k:int32`; 1,`word (n + 1):int32`; 3,`word_add t (word 1):int32`]
                              (r5b_born1_at `m0:int64->byte` `read wmem (s:wasmstate)`)))));;
let R5B_SEGE = r5b_with_thresh 60 (fun () -> prove(r5b_segE_stmt,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val (word (48 * n):int32) = 48 * n /\ val (word (4 * k):int32) = 4 * k /\
                val (word (4 * k + 1163264):int32) = 4 * k + 1163264` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  R5B_INIT_TAC THEN r5b_time "segE" (R5B_RUN3 R5B_EXEC [2586]) THEN
  ENSURES_FINAL_STATE_TAC THEN R5B_CLOSE_TAC THEN R5B_ABSIMP_TAC THEN R5B_MEMCLOSE_TAC)) ();;
(* ---- 3063 -> 4363, born spray bead: i64 zero store of words 8,9, word 7 = k | 65536, word 6 = T+1, n++ *)
let r5b_segH_stmt = list_mk_forall([`m0:int64->byte`;`k:num`;`n:num`;`t:int32`],
  mk_imp(`k < 2048 /\ n < 16384`,
   r5b_ens (r5b_pred 3063 r5b_L2B r5b_trk2 [])
     (mk_abs(`s:wasmstate`, r5b_body_m 4363 r5b_L2 [15,`word k:int32`; 1,`word (n + 1):int32`; 3,`word_add t (word 1):int32`]
                              (r5b_born2_at `m0:int64->byte` `read wmem (s:wasmstate)`)))));;
g r5b_segH_stmt;;
let R5B_SEGH = r5b_with_thresh 60 (fun () -> prove(r5b_segH_stmt,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val (word (48 * n):int32) = 48 * n` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  R5B_INIT_TAC THEN r5b_time "segH" (R5B_RUN R5B_EXEC [4363]) THEN
  ENSURES_FINAL_STATE_TAC THEN R5B_CLOSE_TAC THEN R5B_MEMCLOSE_TAC)) ();;
(* ---- 4700 -> 6027, born antipode bead (loop 3) *)
let r5b_segJ_stmt = list_mk_forall([`m0:int64->byte`;`k:num`;`n:num`;`t:int32`],
  mk_imp(`k < 2048 /\ n < 16384`,
   r5b_ens (r5b_pred 4700 r5b_L3B (r5b_trk3 `k:num` `n:num`) [])
     (mk_abs(`s:wasmstate`, r5b_body_m 6027 r5b_L3 (r5b_trk3 `k:num` `n + 1`)
                              (r5b_born2_at `m0:int64->byte` `read wmem (s:wasmstate)`)))));;
g r5b_segJ_stmt;;
let R5B_SEGJ = r5b_with_thresh 60 (fun () -> prove(r5b_segJ_stmt,
  REPEAT GEN_TAC THEN STRIP_TAC THEN r5b_val3_tac THEN
  SUBGOAL_THEN `word_add (word k) (word 131072):int32 = word (k + 131072) /\ val (word (k + 131072):int32) = k + 131072`
    STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [REWRITE_TAC[GSYM WORD_ADD]; MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC]; ALL_TAC] THEN
  R5B_INIT_TAC THEN r5b_time "segJ" (R5B_RUN R5B_EXEC [6027]) THEN
  ENSURES_FINAL_STATE_TAC THEN R5B_CLOSE_TAC THEN R5B_MEMCLOSE_TAC)) ();;
