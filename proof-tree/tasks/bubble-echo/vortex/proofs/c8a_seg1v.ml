(* vortex-chain C8a (Claude Opus 5.5, 2026-11-14), row A3: loop-1 (pinch-off) value segments of f13: SEGA 146->469|2586,
   SEGB 469->573, SEGC 627->1755, SEGD 1809->1964, SEGE 2018->2586 (record stores + parent debit), BACK1 2586->146|2612.
   Exploration helpers c8a_resid/C8A_CLOSE1N kept for debugging. *)
let c8a_mem1 = `va1_w32s 1138688 2048 rb m0 /\ va1_w32s 1163264 2048 zq m0 /\ va1_w32s 1171456 2048 zp m0 /\
                va1_w32s 65536 262144 tbl m0 /\ va1_mdl mdl m0 /\ va1_w32s 16408 26 hp m0`;;

let C8A_AND2047 = prove(`!x:int32. val (word_and x (word 2047)) = val x MOD 2048`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `2047 = 2 EXP 11 - 1`; ARITH_RULE `2048 = 2 EXP 11`; VAL_WORD_AND_MASK_WORD]);;
let C8A_NB_TAC =
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SHL; C8A_AND2047; VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `k < 2048 ==> k < 4294967296 /\ k + 1 < 4294967296`] THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2048 * 2097152`; MOD_MOD] THEN
  REWRITE_TAC[ARITH_RULE `k + 2048 * 2097151 + 2047 = 2097151 * 2048 + (k + 2047)`;
              ARITH_RULE `k + 4294967295 = 2097151 * 2048 + (k + 2047)`; MOD_MULT_ADD] THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(SPECL [`k + 2047`; `2048`] MOD_LT_EQ) THEN MP_TAC(SPECL [`k + 1`; `2048`] MOD_LT_EQ) THEN ARITH_TAC;;
let C8A_NBM = prove(`!k. k < 2048 ==> val (word_shl (word_and (word_add (word k) (word 4294967295)) (word 2047)) 2:int32) = 4 * ((k + 2047) MOD 2048)`, C8A_NB_TAC);;
let C8A_NBP = prove(`!k. k < 2048 ==> val (word_shl (word_and (word (k + 1)) (word 2047)) 2:int32) = 4 * ((k + 1) MOD 2048)`, C8A_NB_TAC);;

let C8A_BAND1 = prove(`!r:int32. ~(val (word_add r (word 4244776699)) < 4248132142) ==> 3355443 <= val r /\ val r <= 50190596`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `r:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MOD_ADD_CASES; ARITH_RULE `4244776699 < 4294967296`] THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;
let C8A_TBLADDR = prove(`!k r:int32. k < 2048 /\ val r <= 52371633 ==>
   val (word_add (word_shl (word k) 9) (word_and (word_ushr r 17) (word 32764)):int32) =
   512 * k + 4 * (val (word_and (word_ushr r 17) (word 32764):int32) DIV 4)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP R5C_J) THEN
  ABBREV_TAC `J = val (word_and (word_ushr r 17) (word 32764):int32) DIV 4` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_SHL; VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `k MOD 4294967296 = k /\ (4 * J) MOD 4294967296 = 4 * J` (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(512 * k) MOD 4294967296 = 512 * k` SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let C8A_MOD_LT = prove(`!a. a MOD 2048 < 2048`, GEN_TAC THEN REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC);;
let C8A_LOAD_TAC (addr:term) (i:term) (f:term) (base:int) (w32:term) : tactic =
  let fact = subst [addr,`A:num`; mk_comb(f,i),`V:int32`] `read (bytes32 (word A)) (m0:int64->byte) = V` in
  SUBGOAL_THEN fact ASSUME_TAC THENL
   [SUBGOAL_THEN (mk_eq(addr, subst [i,`i:num`] (mk_binop `(+):num->num->num` (mk_small_numeral base) `4 * i`))) SUBST1_TAC THENL
     [ASM_SIMP_TAC[C8A_NBM; C8A_NBP] THEN ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC i (REWRITE_RULE[va1_w32s; va1_mdl] (ASSUME w32))) THEN
    ANTS_TAC THENL [REWRITE_TAC[C8A_MOD_LT] THEN ASM_ARITH_TAC; REWRITE_TAC[]]; ALL_TAC];;
let C8A_L1_LOADS =
  VK_VAL_TAC `4 * k` THEN
  C8A_LOAD_TAC `4 * k + 1138688` `k:num` `rb:num->int32` 1138688 `va1_w32s 1138688 2048 rb m0` THEN
  C8A_LOAD_TAC `4 * k + 1163264` `k:num` `zq:num->int32` 1163264 `va1_w32s 1163264 2048 zq m0` THEN
  C8A_LOAD_TAC `val (word_shl (word_and (word_add (word k) (word 4294967295)) (word 2047)) 2:int32) + 1163264` `(k + 2047) MOD 2048` `zq:num->int32` 1163264 `va1_w32s 1163264 2048 zq m0` THEN
  C8A_LOAD_TAC `val (word_shl (word_and (word (k + 1)) (word 2047)) 2:int32) + 1163264` `(k + 1) MOD 2048` `zq:num->int32` 1163264 `va1_w32s 1163264 2048 zq m0` THEN
  C8A_LOAD_TAC `16648` `2` `mdl:num->int32` 16640 `va1_mdl mdl m0`;;

let c8a_trk1v = r5b_trk1x @ [12, `(rb:num->int32) k`; 17, `va1_ck_spd tbl (rb k) k`; 18, `word_sx ((zq:num->int32) k):int64`;
                              20, `va1_b_tubearg (rb k) (va1_ck_spd tbl (rb k) k)`];;
let c8a_seg1v p q = list_mk_forall([`m0:int64->byte`;`k:num`;`n:num`;`t:int32`;`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;
   `rb:num->int32`;`zq:num->int32`;`zp:num->int32`], mk_imp(mk_conj(`k < 2048 /\ n < 16384`, c8a_mem1), r5b_ens p q));;
let c8a_segA = c8a_seg1v (r5b_pred 146 r5b_L1 r5b_trk1 [])
     (mk_abs(`s:wasmstate`, mk_disj(r5b_body 469 r5b_L1B c8a_trk1v [`va1_b1_ok mdl tbl rb zq k`],
                                    r5b_body 2586 r5b_L1 r5b_trk1 [`~va1_b1_ok mdl tbl rb zq k`])));;
let c8a_jj = `val (word_and (word_ushr ((rb:num->int32) k) 17) (word 32764):int32) DIV 4`;;
let C8A_TBL_LOADS : tactic = fun (asl,w) ->
  try let bth = find (fun th -> concl th = `~(val (word_add ((rb:num->int32) k) (word 4244776699)) < 4248132142)`) (map snd asl) in
    (ASSUME_TAC (MATCH_MP C8A_BAND1 bth) THEN
     SUBGOAL_THEN `val ((rb:num->int32) k) <= 52371633` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     MP_TAC(SPECL [`k:num`; `(rb:num->int32) k`] C8A_TBLADDR) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
     FIRST_ASSUM(ASSUME_TAC o CONJUNCT2 o MATCH_MP R5C_J) THEN
     C8A_LOAD_TAC `val (word_add (word_shl (word k) 9) (word_and (word_ushr ((rb:num->int32) k) 17) (word 32764)):int32) + 65536`
        (mk_binop `(+):num->num->num` `128 * k` c8a_jj) `tbl:num->int32` 65536 `va1_w32s 65536 262144 tbl m0` THEN
     C8A_LOAD_TAC `val (word_add (word_shl (word k) 9) (word_and (word_ushr ((rb:num->int32) k) 17) (word 32764)):int32) + 65540`
        (mk_binop `(+):num->num->num` `128 * k` (mk_binop `(+):num->num->num` c8a_jj `1`)) `tbl:num->int32` 65536 `va1_w32s 65536 262144 tbl m0`) (asl,w)
  with Failure _ -> ALL_TAC (asl,w);;
let C8A_CLOSE1 defs =
  ASM_REWRITE_TAC[injectivity "wval"; R5B_EX_EQ] THEN REWRITE_TAC defs THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[COND_SWAP] THEN ASM_REWRITE_TAC[COND_SWAP] THEN
  CONV_TAC(DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV)) THEN ASM_REWRITE_TAC[] THEN NO_TAC;;
let C8A_SEGA_DEFS = [va1_b1_ok; va1_ck_spd; va1_ck_zpq; va1_ck_hfin; va1_b_tubearg];;

let C8A_NORM = [COND_SWAP; INT_GT; INT_GE; GT; GE; GSYM INT_NOT_LT; GSYM NOT_LT];;
let C8A_CLOSE1 defs =
  RULE_ASSUM_TAC(REWRITE_RULE C8A_NORM) THEN
  ASM_REWRITE_TAC[injectivity "wval"; R5B_EX_EQ] THEN REWRITE_TAC defs THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC C8A_NORM THEN ASM_REWRITE_TAC C8A_NORM THEN
  CONV_TAC(DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV)) THEN ASM_REWRITE_TAC[] THEN NO_TAC;;
let C8A_FIN defs = ENSURES_FINAL_STATE_TAC THEN FIRST [DISJ2_TAC THEN C8A_CLOSE1 defs; DISJ1_TAC THEN C8A_CLOSE1 defs];;

let C8A_HP_LOADS =
  MAP_EVERY (fun i -> C8A_LOAD_TAC (mk_small_numeral (16408 + 4 * i)) (mk_small_numeral i) `hp:num->int32` 16408 `va1_w32s 16408 26 hp m0`) (3--11);;
let c8a_hpl = map (fun (l,i) -> (l, subst [mk_small_numeral i,`i:num`] `word_sx ((hp:num->int32) i):int64`))
  [21,11; 22,10; 23,9; 24,8; 25,7; 26,6; 27,5; 28,4; 29,3];;
let c8a_isq0 = [13,`word 32:int32`; 30,`word 0:int64`; 16,`word 4611686018427387904:int64`];;
let c8a_segB = c8a_seg1v (r5b_pred 469 r5b_L1B c8a_trk1v [`va1_b1_ok mdl tbl rb zq k`])
   (r5b_pred 573 (Lp 571 :: r5b_L1B) (c8a_trk1v @ c8a_isq0 @ c8a_hpl) [`va1_b1_ok mdl tbl rb zq k`]);;

let c8a_letvals defth =
  let rec go acc tm =
    if is_let tm then
      let bs, body = dest_let tm in
      let sub = map (fun (n,t) -> (t, mk_var(n, type_of t))) acc in
      go (acc @ map (fun (v,e) -> (fst(dest_var v), vsubst sub e)) bs) body
    else acc in
  go [] (rhs(concl(SPEC_ALL defth)));;
let c8a_V1 = c8a_letvals va1_b1_rec;;
let c8a_v1 n = assoc n c8a_V1;;
let c8a_base1 = [0,`word k:int32`; 1,`word n:int32`; 2,`t:int32`; 3,`word_add t (word 1):int32`; 4,`(mdl:num->int32) 2`;
  5,`word_shl (word_add t (word 1)) 12:int32`;
  6,`word_add (word_mul ((mdl:num->int32) 2) (word 3266489909)) (word 3979268358):int32`;
  7,`word_add (word_mul ((mdl:num->int32) 2) (word 3266489909)) (word 712778449):int32`;
  8,`word_add (word_mul ((mdl:num->int32) 2) (word 3266489909)) (word 46416558):int32`;
  9,`word_add (word_mul ((mdl:num->int32) 2) (word 3266489909)) (word 1074893945):int32`;
  10,`word_add (word_mul ((mdl:num->int32) 2) (word 3266489909)) (word 2103371332):int32`];;
let c8a_base1x = c8a_base1 @ [11,`word (4 * k):int32`; 19,`word (4 * k + 1163264):int32`];;
let c8a_trk1v = c8a_base1x @ [12, `(rb:num->int32) k`; 17, `va1_ck_spd tbl (rb k) k`; 18, `word_sx ((zq:num->int32) k):int64`;
                              20, `va1_b_tubearg (rb k) (va1_ck_spd tbl (rb k) k)`];;
let c8a_segA = c8a_seg1v (r5b_pred 146 r5b_L1 c8a_base1 [])
     (mk_abs(`s:wasmstate`, mk_disj(r5b_body 469 r5b_L1B c8a_trk1v [`va1_b1_ok mdl tbl rb zq k`],
                                    r5b_body 2586 r5b_L1 c8a_base1 [`~va1_b1_ok mdl tbl rb zq k`])));;
let c8a_segB = c8a_seg1v (r5b_pred 469 r5b_L1B c8a_trk1v [`va1_b1_ok mdl tbl rb zq k`])
   (r5b_pred 573 (Lp 571 :: r5b_L1B) (c8a_trk1v @ c8a_isq0 @ c8a_hpl) [`va1_b1_ok mdl tbl rb zq k`]);;

let c8a_trk1v = c8a_trk1v @ [14, c8a_v1 "x"];;
let c8a_segA = c8a_seg1v (r5b_pred 146 r5b_L1 c8a_base1 [])
     (mk_abs(`s:wasmstate`, mk_disj(r5b_body 469 r5b_L1B c8a_trk1v [`va1_b1_ok mdl tbl rb zq k`],
                                    r5b_body 2586 r5b_L1 c8a_base1 [`~va1_b1_ok mdl tbl rb zq k`])));;
let c8a_segB = c8a_seg1v (r5b_pred 469 r5b_L1B c8a_trk1v [`va1_b1_ok mdl tbl rb zq k`])
   (r5b_pred 573 (Lp 571 :: r5b_L1B) (c8a_trk1v @ c8a_isq0 @ c8a_hpl) [`va1_b1_ok mdl tbl rb zq k`]);;
let c8a_c_pre = c8a_base1x @ [12, `(rb:num->int32) k`; 17, c8a_v1 "spd"; 18, c8a_v1 "zz"; 14, c8a_v1 "x"; 30, c8a_v1 "sq1"] @ c8a_hpl;;
let c8a_c1 = c8a_base1x @ [12, `(rb:num->int32) k`; 17, c8a_v1 "spd"; 18, c8a_v1 "zz"; 14, c8a_v1 "x"; 30, c8a_v1 "sq1"] @
   [16, c8a_v1 "sk"; 31, c8a_v1 "ck"; 35, c8a_v1 "dy"] @ filter (fun (l,_) -> l <> 22 && l <> 25) c8a_hpl @
   [22, `word_sx ((hp:num->int32) 10):int64`; 25, `word_sx ((hp:num->int32) 7):int64`; 20, `word 0:int64`];;
(* first piece: 627 -> 1086 (bead sin/cos, dy) *)
let c8a_segC1 = c8a_seg1v (r5b_pred 627 r5b_L1B c8a_c_pre [`va1_b1_ok mdl tbl rb zq k`])
   (r5b_pred 1086 r5b_L1B c8a_c1 [`va1_b1_ok mdl tbl rb zq k`]);;
let C8A_SEGC_DEFS = [va1_b_bsin; va1_b_bcos; va1_b_rsinm; va1_b_rcos; va1_b_sinf; va1_ck_tstep; va1_ck_ph; va1_ck_hfin];;

let c8a_s1 = rand(c8a_v1 "sqp");;
let c8a_c_post = c8a_base1x @ [17, c8a_v1 "spd"; 18, c8a_v1 "zz"; 14, c8a_v1 "x"; 30, c8a_v1 "sq1";
   22, c8a_v1 "sp"; 37, c8a_v1 "ny"; 28, c8a_v1 "ty"; 38, c8a_v1 "ey"; 25, c8a_v1 "nx"; 29, c8a_v1 "tx"; 26, c8a_v1 "ex";
   23, c8a_v1 "nz"; 27, c8a_v1 "tz"; 21, c8a_v1 "ez"; 39, c8a_v1 "p1"; 40, c8a_v1 "p0"; 24, c8a_v1 "p2";
   31, c8a_s1; 20, `word 0:int64`; 16, `word 4611686018427387904:int64`; 13, `word 32:int32`];;
let c8a_segC = c8a_seg1v (r5b_pred 627 r5b_L1B c8a_c_pre [`va1_b1_ok mdl tbl rb zq k`])
   (r5b_pred 1755 (Lp 1753 :: r5b_L1B) c8a_c_post [`va1_b1_ok mdl tbl rb zq k`]);;

let C8A_CLOSE1N defs =
  RULE_ASSUM_TAC(REWRITE_RULE C8A_NORM) THEN
  ASM_REWRITE_TAC[injectivity "wval"; R5B_EX_EQ] THEN REWRITE_TAC defs THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC C8A_NORM THEN ASM_REWRITE_TAC C8A_NORM THEN
  CONV_TAC(DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV)) THEN ASM_REWRITE_TAC[];;
let c8a_resid () = let (_,w) = top_realgoal() in
  List.iteri (fun i c -> if i < 3 then begin
     print_string ("@@R" ^ string_of_int i ^ " ");
     (if is_eq c then (match r5c_diff (lhs c) (rhs c) with Some(a,b) -> (print_term a; print_string "\n   VS  "; print_term b) | None -> print_term c)
      else print_term c); print_newline() end) (conjuncts w);;
let rec C8A_RUN exec stops : tactic = fun (asl,w) ->
  let s = rand w in
  if r5b_status asl s <> `WRunning` then ALL_TAC (asl,w) else
  let pc = r5b_pc asl s in
  if mem pc stops then ALL_TAC (asl,w) else
  let sn = r5b_fresh() in
  ((R5B_STEP1 exec sn ORELSE R5B_GSTEP exec sn) THEN R5C_AUTOAB_TAC THEN C8A_RUN exec stops) (asl,w);;
let C8A_CLOSEX defs =
  ASM_REWRITE_TAC[injectivity "wval"; R5B_EX_EQ] THEN R5C_EXPAND_TAC THEN C8A_CLOSE1 defs;;

let c8a_is_clamp v = is_cond v && (let _,(a,b) = dest_cond v in
   let one t = (try rand t = `1` && fst(dest_const(rator t)) = "word" with _ -> false) in one a || one b);;
let rec C8A_AUTOAB_TAC : tactic = fun g ->
  let vs = filter (fun v -> not(is_var v) && not (c8a_is_clamp v) &&
                     not (is_comb v && is_const(rator v) && fst(dest_const(rator v)) = "word") &&
                     (r5c_tsize v > 12 || can (find_term is_cond) v) &&
                     not (can (find_term c8a_is_clamp) v && r5c_tsize v <= 12)) (r5c_state_vals g) in
  if vs = [] then ALL_TAC g else
  let v = snd(hd(sort (fun (a,_) (b,_) -> a < b) (map (fun v -> r5c_tsize v, v) vs))) in
  (incr r5c_abn;
   (ABBREV_TAC (mk_eq(mk_var("a_" ^ string_of_int !r5c_abn, type_of v), v)) THEN C8A_AUTOAB_TAC) g);;
let rec C8A_RUN exec stops : tactic = fun (asl,w) ->
  let s = rand w in
  if r5b_status asl s <> `WRunning` then ALL_TAC (asl,w) else
  let pc = r5b_pc asl s in
  if mem pc stops then ALL_TAC (asl,w) else
  let sn = r5b_fresh() in
  ((R5B_STEP1 exec sn ORELSE R5B_GSTEP exec sn) THEN C8A_AUTOAB_TAC THEN C8A_RUN exec stops) (asl,w);;
let c8a_s2 = rand(c8a_v1 "sqq");;
let c8a_geo1 = [37, c8a_v1 "ny"; 28, c8a_v1 "ty"; 38, c8a_v1 "ey"; 25, c8a_v1 "nx"; 29, c8a_v1 "tx"; 26, c8a_v1 "ex";
   23, c8a_v1 "nz"; 27, c8a_v1 "tz"; 21, c8a_v1 "ez"; 39, c8a_v1 "p1"; 40, c8a_v1 "p0"; 24, c8a_v1 "p2"];;
let c8a_d_pre = c8a_base1x @ [17, c8a_v1 "spd"; 18, c8a_v1 "zz"; 14, c8a_v1 "x"; 30, c8a_v1 "sq1"; 22, c8a_v1 "sp"; 20, c8a_v1 "sqp"] @ c8a_geo1;;
let c8a_d_post = c8a_base1x @ [17, c8a_v1 "spd"; 18, c8a_v1 "zz"; 30, c8a_v1 "sq1"; 20, c8a_v1 "sqp"] @ c8a_geo1 @
   [22, c8a_v1 "q1"; 35, c8a_v1 "q0"; 41, c8a_v1 "q2"; 34, c8a_s2; 31, `word 0:int64`; 16, `word 4611686018427387904:int64`; 13, `word 32:int32`];;
let c8a_segD = c8a_seg1v (r5b_pred 1809 r5b_L1B c8a_d_pre [`va1_b1_ok mdl tbl rb zq k`])
   (r5b_pred 1964 (Lp 1962 :: r5b_L1B) c8a_d_post [`va1_b1_ok mdl tbl rb zq k`]);;
let c8a_w1 = [c8a_v1 "w0"; c8a_v1 "w1"; c8a_v1 "w2"; c8a_v1 "w3"; c8a_v1 "w4"; c8a_v1 "w5"; `word_add t (word 1):int32`; `word k:int32`;
              c8a_v1 "dzw"; c8a_v1 "de"];;
let c8a_born1v m0 m =
  let b = rhs(concl(TOP_DEPTH_CONV BETA_CONV (list_mk_comb(r5b_born1, [m0; m])))) in
  let cs = conjuncts b in
  let frame = el 0 cs and zqc = el 3 cs and zpc = el 4 cs and ndc = el 5 cs in
  let words = map (fun (j,v) -> subst [mk_small_numeral j,`j:num`; v,`V:int32`; m,`m:int64->byte`]
                     `read (bytes32 (word (1179648 + 4 * (12 * n + j)))) (m:int64->byte) = V`) (zip (0--9) c8a_w1) in
  list_mk_conj([frame] @ words @ [zqc; zpc; ndc]);;
let c8a_e_pre = c8a_base1x @ [17, c8a_v1 "spd"; 18, c8a_v1 "zz"; 30, c8a_v1 "sq1"; 20, c8a_v1 "sqp"; 31, c8a_v1 "sqq"] @ c8a_geo1 @
   [22, c8a_v1 "q1"; 35, c8a_v1 "q0"; 41, c8a_v1 "q2"];;
let c8a_base1n1 = map (fun (l,v) -> if l = 1 then (1, `word (n + 1):int32`) else (l,v)) c8a_base1;;
let c8a_segE = c8a_seg1v (r5b_pred 2018 r5b_L1B c8a_e_pre [`va1_b1_ok mdl tbl rb zq k`])
   (mk_abs(`s:wasmstate`, r5b_body_m 2586 r5b_L1 c8a_base1n1 (c8a_born1v `m0:int64->byte` `read wmem (s:wasmstate)`)));;
let C8A_WDEFS = [va1_b_bsin; va1_b_bcos; va1_b_rsinm; va1_b_rcos; va1_b_sinf; va1_ck_tstep; va1_ck_ph; va1_ck_hfin];;
let C8A_WORD_CLOSE = REPEAT R5B_PEEL_TAC THEN CONV_TAC(DEPTH_CONV R5B_ADDR_NORM_CONV) THEN C8A_CLOSE1 C8A_WDEFS;;
let rec C8A_EXPAND_ALL : tactic = fun (asl,w) ->
  let fv = frees w in
  let cands = filter (fun (_,th) -> let c = concl th in is_eq c && is_var (rhs c) && mem (rhs c) fv &&
                       (let n = fst(dest_var(rhs c)) in String.length n > 2 && String.sub n 0 2 = "a_")) asl in
  match cands with [] -> ALL_TAC (asl,w) | (_,th)::_ -> (SUBST1_TAC (SYM th) THEN C8A_EXPAND_ALL) (asl,w);;
let C8A_SEGA = prove(c8a_segA,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN R5B_INIT_TAC THEN C8A_L1_LOADS THEN R5B_RUN R5B_EXEC [345; 2586] THEN
  C8A_TBL_LOADS THEN R5B_RUN R5B_EXEC [469; 2586] THEN C8A_FIN C8A_SEGA_DEFS);;
let C8A_SEGB = prove(c8a_segB,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN R5B_INIT_TAC THEN C8A_HP_LOADS THEN R5B_RUN R5B_EXEC [573] THEN
  ENSURES_FINAL_STATE_TAC THEN C8A_CLOSE1 []);;
let C8A_SEGC = prove(c8a_segC,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN R5B_INIT_TAC THEN C8A_RUN R5B_EXEC [1755] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[injectivity "wval"; R5B_EX_EQ] THEN R5C_EXPAND_TAC THEN C8A_CLOSE1 C8A_SEGC_DEFS);;
let C8A_SEGD = prove(c8a_segD,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN R5B_INIT_TAC THEN C8A_RUN R5B_EXEC [1964] THEN
  ENSURES_FINAL_STATE_TAC THEN C8A_CLOSEX [va1_ck_hfin; va1_b_isqrt]);;
let C8A_SEGE = prove(c8a_segE,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN `val (word (48 * n):int32) = 48 * n /\ val (word (4 * k):int32) = 4 * k /\
                val (word (4 * k + 1163264):int32) = 4 * k + 1163264` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  C8A_LOAD_TAC `4 * k + 1171456` `k:num` `zp:num->int32` 1171456 `va1_w32s 1171456 2048 zp m0` THEN
  R5B_INIT_TAC THEN C8A_RUN R5B_EXEC [2586] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[injectivity "wval"; R5B_EX_EQ] THEN R5C_EXPAND_TAC THEN
  REPEAT CONJ_TAC THEN FIRST [R5B_MEMCLOSE_TAC; C8A_WORD_CLOSE; C8A_EXPAND_ALL THEN R5B_MEMCLOSE_TAC]);;
let c8a_base1k1 = map (fun (l,v) -> if l = 0 then (0, `word (k + 1):int32`) else (l,v)) c8a_base1;;
let c8a_back1 = list_mk_forall([`m0:int64->byte`;`k:num`;`n:num`;`t:int32`;`mdl:num->int32`],
   mk_imp(`k < 2048 /\ n <= 16384`,
    r5b_ens (r5b_pred 2586 r5b_L1 c8a_base1 [])
     (mk_abs(`s:wasmstate`, mk_disj(
        r5b_body 146 r5b_L1 c8a_base1k1 [`k + 1 < 2048`; `n < 16384`],
        r5b_body 2612 [] (tl c8a_base1) [`k = 2047 \/ n = 16384`])))));;
let C8A_BACK1 = prove(c8a_back1,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val (word k:int32) = k /\ val (word n:int32) = n` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  R5B_INIT_TAC THEN R5B_RUN R5B_EXEC [146; 2612] THEN
  ENSURES_FINAL_STATE_TAC THEN FIRST [DISJ1_TAC THEN R5B_CLOSE1; DISJ2_TAC THEN R5B_CLOSE1;
     DISJ1_TAC THEN C8A_CLOSE1 [] ; DISJ2_TAC THEN C8A_CLOSE1 []] );;
