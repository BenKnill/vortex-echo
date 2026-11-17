(* ========================================================================= *)
(* Vortex Echo v1: lemmas and tactics for the field phase of the vortex      *)
(* export pair (ve_vk.ml): word arithmetic on i32 numerals, memory cells    *)
(* (reads over writes of other cells), the frame lemma that keeps facts on   *)
(* untouched memory through a MAYCHANGE frame, and the four segments of the  *)
(* prefix pc 21 .. 1305 of ve_vort_apply / ve_vort_unapply:                   *)
(*   seg1 21 .. 266    setup, normalisation (32-step isqrt, three div_s)     *)
(*   seg2 266 .. 480   acc := 0 (8-way unrolled loop and remainder)          *)
(*   seg3 480 .. 1038  pair loop (rows i, partners j = i+1 .. n-1)           *)
(*   seg4 1038 .. 1305 VD := rnd(acc) (4-way unrolled loop and remainder)    *)
(* Segments 2-4 are byte-identical in both bodies and are stated for a code *)
(* variable MC (vk_gencode.ml). No claim is proved here; ve_vk.ml proves the *)
(* segment lemmas and VE_VK_OK.                                              *)
(* ========================================================================= *)

needs "ve_vk_code.ml";;
needs "../../capillary/proofs/cap_helpers.ml";;
needs "ve_vk_defs.ml";;

(* ------------------------------------------------------------------------- *)
(* Linear arithmetic over the num-relational assumptions only. The states    *)
(* carry dozens of assumptions with large word terms; ASM_ARITH_TAC hands    *)
(* them all to ARITH_TAC and costs about a second even when it fails.        *)
(* ------------------------------------------------------------------------- *)
let rec vk_is_arith tm =
  if is_neg tm then vk_is_arith (rand tm)
  else if is_conj tm || is_disj tm || is_imp tm then vk_is_arith (lhand tm) && vk_is_arith (rand tm)
  else (try let op,_ = dest_const(rator(rator tm)) in
            mem op ["<";"<=";">";">=";"="] && type_of(rand tm) = `:num`
        with Failure _ -> false);;
let vk_has_read tm = can (find_term (fun t -> is_const t && fst(dest_const t) = "read")) tm;;
let VK_ARITH_TAC : tactic = fun (asl,w) ->
  let ths = filter (fun th -> let c = concl th in vk_is_arith c && not (vk_has_read c)) (map snd asl) in
  (if ths = [] then ARITH_TAC else MP_TAC (end_itlist CONJ ths) THEN ARITH_TAC) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Word arithmetic on i32 numerals (state-free rewrites for the stepper).    *)
(* ------------------------------------------------------------------------- *)
let VK_WSHL = prove
 (`!a k. word_shl (word a:N word) k = word (2 EXP k * a)`,
  REWRITE_TAC[word_shl; WORD_MUL; WORD_VAL] THEN REWRITE_TAC[WORD_MUL_SYM]);;
let VK_WMUL = prove (`!a b. word_mul (word a) (word b):N word = word (a * b)`, REWRITE_TAC[WORD_MUL]);;
let VK_WADD = prove (`!a b. word_add (word a) (word b):N word = word (a + b)`, REWRITE_TAC[WORD_ADD]);;
let VK_ARITH32_TAC =
  MP_TAC(INST_TYPE [`:32`,`:N`] VK_WSHL) THEN MP_TAC(INST_TYPE [`:32`,`:N`] VK_WMUL) THEN
  MP_TAC(INST_TYPE [`:32`,`:N`] VK_WADD) THEN REPEAT DISCH_TAC;;

(* ------------------------------------------------------------------------- *)
(* Memory cells: reads over writes of other cells (bytes32 / bytes64 /       *)
(* bytes(b,n)), and the same cell.                                          *)
(* ------------------------------------------------------------------------- *)
let VK_NONOVERLAP_TAC =
  REWRITE_TAC[ORTHOGONAL_COMPONENTS_BYTES; DIMINDEX_64] THEN
  MATCH_MP_TAC NONOVERLAPPING_MODULO_SIMPLE THEN
  SUBGOAL_THEN `val(word x:int64) = x /\ val(word a:int64) = a`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN VK_ARITH_TAC;
    CONV_TAC NUM_REDUCE_CONV THEN VK_ARITH_TAC];;
let VK_R32_W64 = prove
 (`!x a (v:int64) (m:int64->byte).
     (x + 4 <= a \/ a + 8 <= x) /\ x < 4294967296 /\ a < 4294967296
     ==> read (bytes32 (word x)) (write (bytes64 (word a)) v m) = read (bytes32 (word x)) m`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC READ_WRITE_ORTHOGONAL_COMPONENTS THEN
  REWRITE_TAC[bytes32; bytes64] THEN MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_LEFT THEN VK_NONOVERLAP_TAC);;
let VK_R64_W32 = prove
 (`!x a (v:int32) (m:int64->byte).
     (x + 8 <= a \/ a + 4 <= x) /\ x < 4294967296 /\ a < 4294967296
     ==> read (bytes64 (word x)) (write (bytes32 (word a)) v m) = read (bytes64 (word x)) m`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC READ_WRITE_ORTHOGONAL_COMPONENTS THEN
  REWRITE_TAC[bytes32; bytes64] THEN MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_LEFT THEN VK_NONOVERLAP_TAC);;
let VK_R64_W64 = prove
 (`!x a (v:int64) (m:int64->byte).
     (x + 8 <= a \/ a + 8 <= x) /\ x < 4294967296 /\ a < 4294967296
     ==> read (bytes64 (word x)) (write (bytes64 (word a)) v m) = read (bytes64 (word x)) m`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC READ_WRITE_ORTHOGONAL_COMPONENTS THEN
  REWRITE_TAC[bytes32; bytes64] THEN MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_LEFT THEN VK_NONOVERLAP_TAC);;
let VK_R32_W32 = prove
 (`!x a (v:int32) (m:int64->byte).
     (x + 4 <= a \/ a + 4 <= x) /\ x < 4294967296 /\ a < 4294967296
     ==> read (bytes32 (word x)) (write (bytes32 (word a)) v m) = read (bytes32 (word x)) m`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC READ_WRITE_ORTHOGONAL_COMPONENTS THEN
  REWRITE_TAC[bytes32; bytes64] THEN MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_LEFT THEN VK_NONOVERLAP_TAC);;
let VK_R32_WB = prove
 (`!x a n (v:num) (m:int64->byte).
     (x + 4 <= a \/ a + n <= x) /\ x < 4294967296 /\ a + n <= 4294967296
     ==> read (bytes32 (word x)) (write (bytes(word a,n)) v m) = read (bytes32 (word x)) m`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC READ_WRITE_ORTHOGONAL_COMPONENTS THEN
  REWRITE_TAC[bytes32; bytes64] THEN MATCH_MP_TAC ORTHOGONAL_COMPONENTS_SUB_LEFT THEN VK_NONOVERLAP_TAC);;
let VK_R64_WB = prove
 (`!x a n (v:num) (m:int64->byte).
     (x + 8 <= a \/ a + n <= x) /\ x < 4294967296 /\ a + n <= 4294967296
     ==> read (bytes64 (word x)) (write (bytes(word a,n)) v m) = read (bytes64 (word x)) m`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC READ_WRITE_ORTHOGONAL_COMPONENTS THEN
  REWRITE_TAC[bytes32; bytes64] THEN MATCH_MP_TAC ORTHOGONAL_COMPONENTS_SUB_LEFT THEN VK_NONOVERLAP_TAC);;
let VK_B64_SAME = prove
 (`!a (v:int64) (m:int64->byte). read (bytes64 a) (write (bytes64 a) v m) = v`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC READ_WRITE_VALID_COMPONENT THEN
  REWRITE_TAC[VALID_COMPONENT_BYTES64]);;
let VK_B64_SAME_EQ = prove
 (`!x a (v:int64) (m:int64->byte). x = a ==> read (bytes64 (word x)) (write (bytes64 (word a)) v m) = v`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[VK_B64_SAME]);;

(* peel one write off a read in the goal: the same cell, or a provably      *)
(* disjoint one (the side conditions by linear arithmetic)                  *)
let VK_PEEL_TAC : tactic =
  let pats =
   [`read (bytes32 (word (x:num))) (write (bytes32 (word (a:num))) (v:int32) (m:int64->byte))`,
      Some CAP_B32_SAME_EQ, VK_R32_W32, false;
    `read (bytes64 (word (x:num))) (write (bytes64 (word (a:num))) (v:int64) (m:int64->byte))`,
      Some VK_B64_SAME_EQ, VK_R64_W64, false;
    `read (bytes32 (word (x:num))) (write (bytes64 (word (a:num))) (v:int64) (m:int64->byte))`,
      None, VK_R32_W64, false;
    `read (bytes64 (word (x:num))) (write (bytes32 (word (a:num))) (v:int32) (m:int64->byte))`,
      None, VK_R64_W32, false;
    `read (bytes32 (word (x:num))) (write (bytes(word (a:num),n)) (v:num) (m:int64->byte))`,
      None, VK_R32_WB, true;
    `read (bytes64 (word (x:num))) (write (bytes(word (a:num),n)) (v:num) (m:int64->byte))`,
      None, VK_R64_WB, true] in
  fun (asl,w) ->
    let try1 (pat,same,other,isb) =
      let t = find_term (can (term_match [] pat)) w in
      let i = term_match [] pat t in
      let x = instantiate i `x:num` and a = instantiate i `a:num` in
      let sametac = match same with
          Some sth -> SUBGOAL_THEN (mk_eq(x,a)) ASSUME_TAC THENL
                        [VK_ARITH_TAC; FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP sth th])]
        | None -> NO_TAC in
      let vm = [instantiate i (if isb then `v:num` else if can (term_match [] `read (bytes32 x) (write (bytes32 a) (v:int32) m)`) t || can (term_match [] `read (bytes64 x) (write (bytes32 a) (v:int32) m)`) t then `v:int32` else `v:int64`); instantiate i `m:int64->byte`] in
      let args = (if isb then [x; a; instantiate i `n:num`] else [x; a]) @ vm in
      sametac ORELSE
      (MP_TAC(SPECL args other) THEN ANTS_TAC THENL
        [VK_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])]) in
    let rec go ps = match ps with
        [] -> NO_TAC
      | p::rest -> (try try1 p with Failure _ -> NO_TAC) ORELSE go rest in
    go pats (asl,w);;

let VK_WMEM_CONV tm =
  let th = WMEM_READ_OVER_WRITES_CONV tm in
  if rand(concl th) = tm then failwith "VK_WMEM_CONV" else th;;

let VK_FRAME_TAC : tactic =
  REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN REWRITE_TAC[GSYM SEQ_ASSOC] THEN
  PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[ASSIGNS_THM] THEN REWRITE_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) MP_TAC) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN STRIP_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV VK_WMEM_CONV) THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY DISCH_TAC THEN
  REPEAT VK_PEEL_TAC THEN ASM_SIMP_TAC[];;

(* stepping that also passes state-free bytes64 facts (loads of i64 cells, *)
(* orthogonality instances) as rewrites; CAP_MSTEPS_TAC passes bytes32 only *)
let vk_is_memfact tm =
  let ws = `:wasmstate` in
  not (can (find_term (fun t -> type_of t = ws)) tm) &&
  can (find_term (fun t -> is_const t && (fst(dest_const t) = "bytes32" || fst(dest_const t) = "bytes64"))) tm &&
  not (is_imp (snd(strip_forall tm)));;

let VK_MSTEPS_TAC execth snums =
  MAP_EVERY (fun s (asl,w) ->
     let mths = filter (fun th -> vk_is_memfact (concl th)) (map snd asl) in
     (CAP_STEP_TAC execth (READ_COMPONENT_COMPOSE :: mths) s THEN
      CAP_DISCARD_OLD_TAC s) (asl,w))
   (statenames "s" snums);;

(* keep a frame-stable fact R through an ensures *)
let VK_ENSURES_KEEP = prove
 (`!P Q C (R:wasmstate->bool).
     ensures wasm P Q C /\ (!s. P s ==> R s) /\ (!s s'. C s s' /\ R s ==> R s')
     ==> ensures wasm P (\s. Q s /\ R s) C`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "e") STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `s0:wasmstate` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(R:wasmstate->bool) s0` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "e" (MP_TAC o SPEC `s0:wasmstate`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_MONO) THEN
  X_GEN_TAC `s2:wasmstate` THEN REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Generic helpers for the segment proofs.                                   *)
(* ------------------------------------------------------------------------- *)
let VK_FRAME = `MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
  MAYCHANGE [wlocal 0; wlocal 1; wlocal 2; wlocal 3; wlocal 4; wlocal 5; wlocal 6; wlocal 7; wlocal 8; wlocal 9; wlocal 10; wlocal 11; wlocal 12; wlocal 13; wlocal 14; wlocal 15; wlocal 16; wlocal 17; wlocal 18; wlocal 19; wlocal 20; wlocal 21; wlocal 22; wlocal 23; wlocal 24; wlocal 25; wlocal 26; wlocal 27; wlocal 28; wlocal 29] ,,
  MAYCHANGE [wmem :> bytes(word 1966080,73728)]`;;

let VK_DEC = prove
 (`!a b. b < a ==> word (a - b + 4294967295):int32 = word (a - (b + 1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a - b + 4294967295 = (a - (b + 1)) + 4294967296` SUBST1_TAC THENL
   [VK_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
  REWRITE_TAC[WORD_ADD_0]);;

let VK_WORD_NE0 = prove
 (`!x. 0 < x /\ x < 4294967296 ==> (word x:int32 = word 0 <=> F)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN
  ASM_SIMP_TAC[CAP_VAL_WORD32; VAL_WORD_0] THEN VK_ARITH_TAC);;

let VK_WORD_NE = prove
 (`!x y. x < 4294967296 /\ y < 4294967296 /\ ~(x = y) ==> (word x:int32 = word y <=> F)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN
  ASM_SIMP_TAC[CAP_VAL_WORD32]);;

(* assume val(word t:int32) = t, t < 2^32 by arithmetic *)
let VK_VAL_TAC t =
  SUBGOAL_THEN (mk_eq(mk_comb(`val:int32->num`, mk_comb(`word:num->int32`, t)), t)) ASSUME_TAC THENL
   [MATCH_MP_TAC CAP_VAL_WORD32 THEN VK_ARITH_TAC; ALL_TAC];;

(* assume a fact, proved by arithmetic *)
let VK_ARITH_FACT_TAC t = SUBGOAL_THEN t ASSUME_TAC THENL [VK_ARITH_TAC; ALL_TAC];;

(* assume an instance of a quantified memory fact (index bound by arithmetic) *)
let VK_LOADFACT_TAC t =
  SUBGOAL_THEN t ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN VK_ARITH_TAC; ALL_TAC];;

(* congruence closure down to arithmetic leaves *)
let rec VK_CONG_TAC g =
  (REFL_TAC ORELSE
   (fun (asl,w as g) -> if is_eq w && type_of (lhs w) = `:num` then VK_ARITH_TAC g else failwith "VK_CONG_TAC") ORELSE
   (MK_COMB_TAC THEN VK_CONG_TAC)) g;;

(* close  I32 (word e1) = I32 (word e2) / word e1 = word e2 / stacks *)
let VK_WEQ_TAC : tactic = fun (asl,w as g) ->
  if not (is_eq w) then failwith "VK_WEQ_TAC" else
  (REWRITE_TAC[injectivity "wval"; CONS_11] THEN
   (REFL_TAC ORELSE (MATCH_MP_TAC VK_DEC THEN VK_ARITH_TAC) ORELSE VK_CONG_TAC)) g;;

(* assume a memory fact at a stepper address a, from the quantified fact  *)
(* at the canonical address c (a = c by arithmetic)                       *)
let VK_LOADFACT2_TAC t c =
  let a = rand(rand(rand(rator(lhs t)))) in
  SUBGOAL_THEN t ASSUME_TAC THENL
   [SUBST1_TAC(ARITH_RULE(mk_eq(a,c))) THEN FIRST_ASSUM MATCH_MP_TAC THEN VK_ARITH_TAC;
    ALL_TAC];;

(* word_and with the low mask 2^k - 1 and the high mask 2^32 - 2^k *)
let vk_mask_lemmas k =
  let p = 1 lsl k in
  let lo = mk_small_numeral (p - 1) and hi = mk_numeral (Num.num_of_string (string_of_int (4294967296 - p)))
  and pk = mk_small_numeral p and kk = mk_small_numeral k
  and qk = mk_numeral (Num.num_of_string (string_of_int (4294967296 / p))) in
  let lth = prove
   (subst [lo,`lo:num`; pk,`pk:num`] `!x. word_and (word x:int32) (word lo) = word (x MOD pk)`,
    GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
    MP_TAC(ISPECL [`word x:int32`; kk] VAL_WORD_AND_MASK_WORD) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN (subst [pk,`pk:num`] `x MOD pk MOD 4294967296 = x MOD pk`) SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN MP_TAC(SPECL [`x:num`; pk] MOD_LT_EQ) THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN (subst [pk,`pk:num`; qk,`qk:num`] `4294967296 = pk * qk`) SUBST1_TAC THENL
     [ARITH_TAC; REWRITE_TAC[MOD_MOD]]) in
  let hth = prove
   (subst [hi,`hi:num`; pk,`pk:num`] `!x. word_and (word x:int32) (word hi) = word (pk * (x DIV pk))`,
    GEN_TAC THEN
    SUBGOAL_THEN (subst [hi,`hi:num`; lo,`lo:num`]
       `!y:int32. word_and y (word hi) = word_sub y (word_and y (word lo))`)
      (fun th -> REWRITE_TAC[th]) THENL [GEN_TAC THEN BITBLAST_TAC; ALL_TAC] THEN
    REWRITE_TAC[lth] THEN
    SUBGOAL_THEN (subst [pk,`pk:num`] `word x:int32 = word_add (word (pk * (x DIV pk))) (word (x MOD pk))`)
      SUBST1_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN
      MP_TAC(SPECL [`x:num`; pk] DIVISION) THEN ARITH_TAC;
      CONV_TAC WORD_RULE]) in
  lth,hth;;
let VK_AND7,VK_ANDM8 = vk_mask_lemmas 3;;
let VK_AND31,VK_ANDM32 = vk_mask_lemmas 5;;
let VK_AND63,VK_ANDM64 = vk_mask_lemmas 6;;


(* a memory goal  !m. m < K ==> read (cell m) chain = f m : split the given *)
(* same-cell indices, peel the writes, close from the old facts             *)
let VK_MEMGOAL_TAC (cases:term list) (close:tactic) =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  (VK_ARITH_TAC ORELSE
   (MAP_EVERY (fun c -> ASM_CASES_TAC (mk_eq(`m:num`,c)) THENL
      [FIRST_X_ASSUM SUBST_ALL_TAC THEN REPEAT VK_PEEL_TAC THEN close; ALL_TAC]) cases THEN
    REPEAT VK_PEEL_TAC THEN
    (FIRST_X_ASSUM MATCH_MP_TAC THEN VK_ARITH_TAC)));;

(* weaken: goal ensures wasm P Q C from th: ensures wasm P' Q' C *)
let VK_ENS_WEAKEN_TAC (th:thm) (pretac:tactic) (posttac:tactic) =
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  EXISTS_TAC (rand(rator(rator(concl th)))) THEN CONJ_TAC THENL
   [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN pretac;
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC (rand(rator(concl th))) THEN CONJ_TAC THENL
     [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN posttac;
      ACCEPT_TAC th]];;

let VK_TRY name (tac:tactic) : tactic = fun g ->
  try tac g with Failure s -> failwith (name ^ ": " ^ s);;

let VK_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[];;

let VK_CLOSE_TAC cases close =
  REPEAT CONJ_TAC THEN TRY VK_WEQ_TAC THEN TRY(VK_MEMGOAL_TAC [] ALL_TAC) THEN
  TRY(VK_MEMGOAL_TAC cases close);;

(* an orthogonality instance  !v m. read (cell x) (write (cell a) v m) = read (cell x) m *)
let VK_RWO_TAC lem x a =
  let th = SPECL [x; a] lem in
  let vs,body = strip_forall(concl th) in
  SUBGOAL_THEN (list_mk_forall(vs, rand body)) ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC th THEN VK_ARITH_TAC; ALL_TAC];;

let VK_COND_I64 = prove
 (`!p a b. (if p then I64 a else I64 b) = I64 (if p then a else b)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;
let VK_COND_I32 = prove
 (`!p a b. (if p then I32 a else I32 b) = I32 (if p then a else b)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let VK_LEN_NZ = prove
 (`!r:int64. ((if ~(ival r > &1) then word 1 else r) = word 0 <=> F) /\
             ((if ~(ival r > &1) then word 1 else r) = word 18446744073709551615 <=> F)`,
  GEN_TAC THEN COND_CASES_TAC THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
  CONJ_TAC THEN DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  POP_ASSUM MP_TAC THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN INT_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Segment 4b: the rounding remainder loop (pc 1231 .. 1305).                *)
(* ------------------------------------------------------------------------- *)
let vk_e2_stmt mc = subst [mc,`MC:byte list`; VK_FRAME,`VKF:wasmstate->wasmstate->bool`]
 `!N (A:num->int64) b r. 1 <= r /\ r < 4 /\ b + r = 3 * N /\ N <= 640 ==>
   ensures wasm
    (\s. read wcode s = MC /\ read wpc s = word 1231 /\ read wstatus s = WRunning /\
         read wstack s = [] /\ read wlabels s = [0,1305,0] /\ read warity s = 0 /\
         read wmemsize s = 2097152 /\
         read (wlocal 6) s = I32 (word b) /\ read (wlocal 0) s = I32 (word r) /\
         (!m. m < 3 * N ==> read (wmem :> bytes64 (word (1982464 + 8 * m))) s = A m) /\
         (!m. m < b ==> read (wmem :> bytes32 (word (1974272 + 4 * m))) s = ve_vk_rnd (A m)))
    (\s. read wcode s = MC /\ read wpc s = word 1305 /\ read wstatus s = WRunning /\
         read wstack s = [] /\ read wlabels s = [] /\ read warity s = 0 /\
         read wmemsize s = 2097152 /\
         (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1974272 + 4 * m))) s = ve_vk_rnd (A m)))
    VKF`;;

let vk_e2_inv mc =
  let t = subst [mc,`MC:byte list`]
   `\t s. read wcode s = MC /\ read wstatus s = WRunning /\
          read wmemsize s = 2097152 /\ read warity s = 0 /\
          read wlabels s = [0,1257,0; 0,1305,0] /\
          read (wlocal 3) s = I32 (word (1982464 + 8 * (b + t))) /\
          read (wlocal 14) s = I32 (word (1974272 + 4 * (b + t))) /\
          read (wlocal 0) s = I32 (word (r - t)) /\
          read wstack s = (if read wpc s = word 1259 then [] else [I32 (word (r - t))]) /\
          (!m. m < 3 * N ==> read (wmem :> bytes64 (word (1982464 + 8 * m))) s = (A:num->int64) m) /\
          (!m. m < b + t ==> read (wmem :> bytes32 (word (1974272 + 4 * m))) s = ve_vk_rnd (A m))` in
  rhs(concl(TOP_DEPTH_CONV BETA_CONV t));;


let VK_E2_TAC mc exec =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_WHILE_UP_TAC `r:num` `1259` `1301` (vk_e2_inv mc) THEN REPEAT CONJ_TAC THENL
   [VK_ARITH_TAC;
    ENSURES_INIT_TAC "s0" THEN MEMNAME_TAC THEN VK_ARITH32_TAC THEN
    VK_MSTEPS_TAC exec (1--13) THEN VK_FINAL_TAC THEN
    REPEAT CONJ_TAC THEN TRY VK_WEQ_TAC THEN
    TRY(VK_MEMGOAL_TAC [] ALL_TAC);
    X_GEN_TAC `t:num` THEN STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN VK_ARITH32_TAC THEN
    VK_VAL_TAC `1982464 + 8 * (b + t)` THEN VK_VAL_TAC `1974272 + 4 * (b + t)` THEN
    VK_LOADFACT_TAC `read (bytes64 (word (1982464 + 8 * (b + t)))) mm = (A:num->int64) (b + t)` THEN
    VK_MSTEPS_TAC exec (1--20) THEN VK_FINAL_TAC THEN
    REPEAT CONJ_TAC THEN TRY VK_WEQ_TAC THEN
    TRY(VK_MEMGOAL_TAC [] ALL_TAC) THEN
    TRY(VK_MEMGOAL_TAC [`b + t:num`] (REWRITE_TAC[ve_vk_rnd]));
    X_GEN_TAC `t:num` THEN STRIP_TAC THEN
    MP_TAC(SPEC `r - t:num` VK_WORD_NE0) THEN ANTS_TAC THENL [VK_ARITH_TAC; DISCH_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
    VK_MSTEPS_TAC exec (1--2) THEN VK_FINAL_TAC;
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUB_REFL]) THEN
    VK_MSTEPS_TAC exec (1--3) THEN VK_FINAL_TAC THEN
    REPEAT CONJ_TAC THEN TRY(VK_MEMGOAL_TAC [] ALL_TAC)];;


(* ------------------------------------------------------------------------- *)
(* Segment 4: rounding VD[m] = rnd(A m), pc 1038 .. 1305.                    *)
(* ------------------------------------------------------------------------- *)
let vk_seg4_stmt mc = subst [mc,`MC:byte list`; VK_FRAME,`VKF:wasmstate->wasmstate->bool`]
 `!N (A:num->int64). 1 <= N /\ N <= 640 ==>
   ensures wasm
    (\s. read wcode s = MC /\ read wpc s = word 1038 /\ read wstatus s = WRunning /\
         read wstack s = [] /\ read wlabels s = [0,1305,0] /\ read warity s = 0 /\
         read wmemsize s = 2097152 /\
         read (wlocal 1) s = I32 (word N) /\ read (wlocal 15) s = I32 (word (3 * N)) /\
         (!m. m < 3 * N ==> read (wmem :> bytes64 (word (1982464 + 8 * m))) s = A m))
    (\s. read wcode s = MC /\ read wpc s = word 1305 /\ read wstatus s = WRunning /\
         read wstack s = [] /\ read wlabels s = [] /\ read warity s = 0 /\
         read wmemsize s = 2097152 /\
         (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1974272 + 4 * m))) s = ve_vk_rnd (A m)))
    VKF`;;

let vk_e1_inv mc =
  let t = subst [mc,`MC:byte list`]
   `\t s. read wcode s = MC /\ read wstatus s = WRunning /\
          read wmemsize s = 2097152 /\ read warity s = 0 /\
          read wlabels s = [0,1086,0; 0,1231,0; 0,1305,0] /\
          read (wlocal 1) s = I32 (word N) /\
          read (wlocal 3) s = I32 (word (32 * t)) /\
          read (wlocal 14) s = I32 (word (1974272 + 16 * t)) /\
          read (wlocal 4) s = I32 (word (32 * q)) /\
          read (wlocal 6) s = I32 (word (4 * q)) /\
          read (wlocal 0) s = I32 (word r) /\
          read wstack s = (if read wpc s = word 1088 then []
                           else [I32 (word (bitval (~(word (32 * q) = word (32 * t):int32))))]) /\
          (!m. m < 3 * N ==> read (wmem :> bytes64 (word (1982464 + 8 * m))) s = (A:num->int64) m) /\
          (!m. m < 4 * t ==> read (wmem :> bytes32 (word (1974272 + 4 * m))) s = ve_vk_rnd (A m))` in
  rhs(concl(TOP_DEPTH_CONV BETA_CONV t));;

(* the mid assertion at 1231 (E1 exit with r <> 0, or the N = 1 skip) *)
let vk_mid1231 mc b r = subst [mc,`MC:byte list`; b,`b:num`; r,`r:num`]
 `\s. read wstatus s = WRunning /\
      read wstack s = [] /\ read wlabels s = [0,1305,0] /\ read warity s = 0 /\
      read wmemsize s = 2097152 /\
      read (wlocal 6) s = I32 (word b) /\ read (wlocal 0) s = I32 (word r) /\
      (!m. m < 3 * N ==> read (wmem :> bytes64 (word (1982464 + 8 * m))) s = (A:num->int64) m) /\
      (!m. m < b ==> read (wmem :> bytes32 (word (1974272 + 4 * m))) s = ve_vk_rnd (A m))`;;

let VK_E1_BODY_TAC exec =
  X_GEN_TAC `t:num` THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN VK_ARITH32_TAC THEN
  MAP_EVERY VK_VAL_TAC [`32 * t + 1982464`; `32 * t + 1982472`; `32 * t + 1982480`; `32 * t + 1982488`;
                        `1974272 + 16 * t`; `(1974272 + 16 * t) + 4`; `(1974272 + 16 * t) + 8`; `(1974272 + 16 * t) + 12`] THEN
  VK_LOADFACT2_TAC `read (bytes64 (word (32 * t + 1982464))) mm = (A:num->int64) (4 * t)` `1982464 + 8 * (4 * t)` THEN
  VK_LOADFACT2_TAC `read (bytes64 (word (32 * t + 1982472))) mm = (A:num->int64) (4 * t + 1)` `1982464 + 8 * (4 * t + 1)` THEN
  VK_LOADFACT2_TAC `read (bytes64 (word (32 * t + 1982480))) mm = (A:num->int64) (4 * t + 2)` `1982464 + 8 * (4 * t + 2)` THEN
  VK_LOADFACT2_TAC `read (bytes64 (word (32 * t + 1982488))) mm = (A:num->int64) (4 * t + 3)` `1982464 + 8 * (4 * t + 3)` THEN
  VK_RWO_TAC VK_R64_W32 `32 * t + 1982472` `1974272 + 16 * t` THEN
  VK_RWO_TAC VK_R64_W32 `32 * t + 1982480` `1974272 + 16 * t` THEN
  VK_RWO_TAC VK_R64_W32 `32 * t + 1982480` `(1974272 + 16 * t) + 4` THEN
  VK_RWO_TAC VK_R64_W32 `32 * t + 1982488` `1974272 + 16 * t` THEN
  VK_RWO_TAC VK_R64_W32 `32 * t + 1982488` `(1974272 + 16 * t) + 4` THEN
  VK_RWO_TAC VK_R64_W32 `32 * t + 1982488` `(1974272 + 16 * t) + 8` THEN
  VK_MSTEPS_TAC exec (1--56) THEN VK_FINAL_TAC THEN
  REPEAT CONJ_TAC THEN TRY VK_WEQ_TAC THEN
  TRY(VK_MEMGOAL_TAC [] ALL_TAC) THEN
  TRY(VK_MEMGOAL_TAC [`4 * t`; `4 * t + 1`; `4 * t + 2`; `4 * t + 3`] (REWRITE_TAC[ve_vk_rnd]));;

let VK_E1_BACK_TAC exec =
  X_GEN_TAC `t:num` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`32 * q`; `32 * t`] VK_WORD_NE) THEN ANTS_TAC THENL [VK_ARITH_TAC; DISCH_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  VK_MSTEPS_TAC exec (1--2) THEN VK_FINAL_TAC;;

let VK_E1_ENTRY_TAC exec =
  ENSURES_INIT_TAC "s0" THEN MEMNAME_TAC THEN VK_ARITH32_TAC THEN
  VK_MSTEPS_TAC exec (1--26) THEN VK_FINAL_TAC THEN
  REPEAT CONJ_TAC THEN TRY VK_WEQ_TAC THEN TRY(VK_MEMGOAL_TAC [] ALL_TAC);;

(* exit to 1305 (r = 0) or to the mid assertion at 1231 (r <> 0) *)
let VK_E1_EXIT_TAC exec n =
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  VK_MSTEPS_TAC exec (1--n) THEN VK_FINAL_TAC THEN
  REPEAT CONJ_TAC THEN TRY VK_WEQ_TAC THEN TRY(VK_MEMGOAL_TAC [] ALL_TAC);;

let VK_SEG4_SETUP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `q = (3 * N) DIV 4` THEN ABBREV_TAC `r = (3 * N) MOD 4` THEN
  SUBGOAL_THEN `4 * q + r = 3 * N /\ r < 4` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q";"r"] THEN MP_TAC(SPECL [`3 * N`; `4`] DIVISION) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `word_and (word (3 * N)) (word 3):int32 = word r /\
                word_and (word (3 * N)) (word 4294967292):int32 = word (4 * q) /\
                word_and (word (8 * (3 * N))) (word 4294967264):int32 = word (32 * q)`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CAP_AND3; CAP_ANDM4; VK_ANDM32] THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "q" THEN
    SUBST1_TAC(ARITH_RULE `32 = 8 * 4`) THEN SIMP_TAC[DIV_MULT2; ARITH_EQ];
    ALL_TAC];;

let VK_SEG4_N1_TAC mc exec e2th =
FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `q = 0 /\ r = 3` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL [VK_ARITH_TAC; ALL_TAC] THEN
    ENSURES_SEQUENCE_TAC `1231` (subst [`1`,`N:num`] (vk_mid1231 mc `0` `3`)) THEN CONJ_TAC THENL
     [VK_TRY "n1steps" (ENSURES_INIT_TAC "s0" THEN MEMNAME_TAC THEN VK_ARITH32_TAC THEN
      VK_MSTEPS_TAC exec (1--11) THEN VK_FINAL_TAC THEN
      REPEAT CONJ_TAC THEN TRY VK_WEQ_TAC THEN TRY(VK_MEMGOAL_TAC [] ALL_TAC) THEN
      REWRITE_TAC[LT]);
      MP_TAC(SPECL [`1`; `A:num->int64`; `0`; `3`] e2th) THEN
      ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      VK_TRY "e2use" (DISCH_THEN(fun th -> VK_ENS_WEAKEN_TAC th (ASM_REWRITE_TAC[]) (ASM_REWRITE_TAC[])))];;

let VK_SEG4_TAC mc exec e2th =
  VK_SEG4_SETUP_TAC THEN
  ASM_CASES_TAC `N = 1` THENL
   [VK_SEG4_N1_TAC mc exec e2th;
    ALL_TAC] THEN
  SUBGOAL_THEN `(word N:int32 = word 1) <=> F` ASSUME_TAC THENL
   [VK_TRY "ne1" (MATCH_MP_TAC VK_WORD_NE THEN VK_ARITH_TAC); ALL_TAC] THEN
  SUBGOAL_THEN `1 <= q` ASSUME_TAC THENL [VK_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `r = 0` THENL
   [ENSURES_WHILE_UP_TAC `q:num` `1088` `1222` (vk_e1_inv mc) THEN REPEAT CONJ_TAC THENL
     [VK_ARITH_TAC; VK_TRY "e1entry" (VK_E1_ENTRY_TAC exec); VK_TRY "e1body" (VK_E1_BODY_TAC exec); VK_TRY "e1back" (VK_E1_BACK_TAC exec);
      FIRST_X_ASSUM SUBST_ALL_TAC THEN VK_TRY "e1exit5" (VK_E1_EXIT_TAC exec 5)];
    SUBGOAL_THEN `(word r:int32 = word 0) <=> F` ASSUME_TAC THENL
     [MATCH_MP_TAC VK_WORD_NE0 THEN VK_ARITH_TAC; ALL_TAC] THEN
    ENSURES_SEQUENCE_TAC `1231` (vk_mid1231 mc `4 * q` `r:num`) THEN CONJ_TAC THENL
     [ENSURES_WHILE_UP_TAC `q:num` `1088` `1222` (vk_e1_inv mc) THEN REPEAT CONJ_TAC THENL
       [VK_ARITH_TAC; VK_TRY "e1entry" (VK_E1_ENTRY_TAC exec); VK_TRY "e1body" (VK_E1_BODY_TAC exec); VK_TRY "e1back" (VK_E1_BACK_TAC exec);
        VK_TRY "e1exit6" (VK_E1_EXIT_TAC exec 6)];
      MP_TAC(SPECL [`N:num`; `A:num->int64`; `4 * q`; `r:num`] e2th) THEN
      ANTS_TAC THENL [VK_ARITH_TAC; ALL_TAC] THEN
      VK_TRY "e2use" (DISCH_THEN(fun th -> VK_ENS_WEAKEN_TAC th (ASM_REWRITE_TAC[]) (ASM_REWRITE_TAC[])))]];;

(* ------------------------------------------------------------------------- *)
(* Segment 2: acc[m] := 0 for m < 3N, pc 266 .. 480.                          *)
(* ------------------------------------------------------------------------- *)
let VK_XNF = `!j c. j < N /\ c < 3 ==>
   read (wmem :> bytes32 (word (1966080 + 4 * (3 * j + c)))) s = (XN:num->num->int32) j c`;;

let vk_seg2_stmt mc = subst [mc,`MC:byte list`; VK_FRAME,`VKF:wasmstate->wasmstate->bool`]
 `!N (XN:num->num->int32). 1 <= N /\ N <= 640 ==>
   ensures wasm
    (\s. read wcode s = MC /\ read wpc s = word 266 /\ read wstatus s = WRunning /\
         read wstack s = [] /\ read wlabels s = [0,1305,0] /\ read warity s = 0 /\
         read wmemsize s = 2097152 /\
         read (wlocal 1) s = I32 (word N) /\ read (wlocal 2) s = I32 (word N) /\
         (!j c. j < N /\ c < 3 ==>
            read (wmem :> bytes32 (word (1966080 + 4 * (3 * j + c)))) s = XN j c))
    (\s. read wcode s = MC /\ read wpc s = word 480 /\ read wstatus s = WRunning /\
         read wstack s = [] /\ read wlabels s = [0,1305,0] /\ read warity s = 0 /\
         read wmemsize s = 2097152 /\
         read (wlocal 1) s = I32 (word N) /\ read (wlocal 2) s = I32 (word N) /\
         read (wlocal 15) s = I32 (word (3 * N)) /\
         (!j c. j < N /\ c < 3 ==>
            read (wmem :> bytes32 (word (1966080 + 4 * (3 * j + c)))) s = XN j c) /\
         (!m. m < 3 * N ==> read (wmem :> bytes64 (word (1982464 + 8 * m))) s = word 0))
    VKF`;;

(* the remainder loop from 440 (base b, r iterations) to 480 *)
let vk_b2_stmt mc = subst [mc,`MC:byte list`; VK_FRAME,`VKF:wasmstate->wasmstate->bool`]
 `!N (XN:num->num->int32) b r. 1 <= r /\ r < 8 /\ b + r = 3 * N /\ N <= 640 ==>
   ensures wasm
    (\s. read wcode s = MC /\ read wpc s = word 440 /\ read wstatus s = WRunning /\
         read wstack s = [] /\ read wlabels s = [0,480,0; 0,1305,0] /\ read warity s = 0 /\
         read wmemsize s = 2097152 /\
         read (wlocal 1) s = I32 (word N) /\ read (wlocal 2) s = I32 (word N) /\
         read (wlocal 15) s = I32 (word (N * 3)) /\
         read (wlocal 4) s = I32 (word b) /\ read (wlocal 14) s = I32 (word r) /\
         (!j c. j < N /\ c < 3 ==>
            read (wmem :> bytes32 (word (1966080 + 4 * (3 * j + c)))) s = XN j c) /\
         (!m. m < b ==> read (wmem :> bytes64 (word (1982464 + 8 * m))) s = word 0))
    (\s. read wcode s = MC /\ read wpc s = word 480 /\ read wstatus s = WRunning /\
         read wstack s = [] /\ read wlabels s = [0,1305,0] /\ read warity s = 0 /\
         read wmemsize s = 2097152 /\
         read (wlocal 1) s = I32 (word N) /\ read (wlocal 2) s = I32 (word N) /\
         read (wlocal 15) s = I32 (word (3 * N)) /\
         (!j c. j < N /\ c < 3 ==>
            read (wmem :> bytes32 (word (1966080 + 4 * (3 * j + c)))) s = XN j c) /\
         (!m. m < 3 * N ==> read (wmem :> bytes64 (word (1982464 + 8 * m))) s = word 0))
    VKF`;;

let vk_b2_inv mc =
  let t = subst [mc,`MC:byte list`]
   `\t s. read wcode s = MC /\ read wstatus s = WRunning /\
          read wmemsize s = 2097152 /\ read warity s = 0 /\
          read wlabels s = [0,453,0; 0,480,0; 0,1305,0] /\
          read (wlocal 1) s = I32 (word N) /\ read (wlocal 2) s = I32 (word N) /\
          read (wlocal 15) s = I32 (word (N * 3)) /\
          read (wlocal 3) s = I32 (word (1982464 + 8 * (b + t))) /\
          read (wlocal 14) s = I32 (word (r - t)) /\
          read wstack s = (if read wpc s = word 455 then [] else [I32 (word (r - t))]) /\
          (!j c. j < N /\ c < 3 ==>
            read (wmem :> bytes32 (word (1966080 + 4 * (3 * j + c)))) s = (XN:num->num->int32) j c) /\
          (!m. m < b + t ==> read (wmem :> bytes64 (word (1982464 + 8 * m))) s = word 0)` in
  rhs(concl(TOP_DEPTH_CONV BETA_CONV t));;


let VK_B2_TAC mc exec =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_WHILE_UP_TAC `r:num` `455` `476` (vk_b2_inv mc) THEN REPEAT CONJ_TAC THENL
   [VK_ARITH_TAC;
    ENSURES_INIT_TAC "s0" THEN MEMNAME_TAC THEN VK_ARITH32_TAC THEN
    VK_MSTEPS_TAC exec (1--7) THEN VK_FINAL_TAC THEN VK_CLOSE_TAC [] ALL_TAC;
    X_GEN_TAC `t:num` THEN STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN VK_ARITH32_TAC THEN
    VK_VAL_TAC `1982464 + 8 * (b + t)` THEN
    VK_MSTEPS_TAC exec (1--11) THEN VK_FINAL_TAC THEN
    VK_CLOSE_TAC [`b + t:num`] ALL_TAC;
    X_GEN_TAC `t:num` THEN STRIP_TAC THEN
    MP_TAC(SPEC `r - t:num` VK_WORD_NE0) THEN ANTS_TAC THENL [VK_ARITH_TAC; DISCH_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
    VK_MSTEPS_TAC exec (1--2) THEN VK_FINAL_TAC;
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUB_REFL]) THEN
    VK_MSTEPS_TAC exec (1--3) THEN VK_FINAL_TAC THEN VK_CLOSE_TAC [] ALL_TAC];;

let vk_b1_inv mc =
  let t = subst [mc,`MC:byte list`]
   `\t s. read wcode s = MC /\ read wstatus s = WRunning /\
          read wmemsize s = 2097152 /\ read warity s = 0 /\
          read wlabels s = [0,314,0; 0,440,0; 0,480,0; 0,1305,0] /\
          read (wlocal 1) s = I32 (word N) /\ read (wlocal 2) s = I32 (word N) /\
          read (wlocal 15) s = I32 (word (N * 3)) /\
          read (wlocal 3) s = I32 (word (64 * t)) /\
          read (wlocal 0) s = I32 (word (64 * q)) /\
          read (wlocal 4) s = I32 (word (8 * q)) /\
          read (wlocal 14) s = I32 (word r) /\
          read wstack s = (if read wpc s = word 316 then []
                           else [I32 (word (bitval (~(word (64 * q) = word (64 * t):int32))))]) /\
          (!j c. j < N /\ c < 3 ==>
            read (wmem :> bytes32 (word (1966080 + 4 * (3 * j + c)))) s = (XN:num->num->int32) j c) /\
          (!m. m < 8 * t ==> read (wmem :> bytes64 (word (1982464 + 8 * m))) s = word 0)` in
  rhs(concl(TOP_DEPTH_CONV BETA_CONV t));;

let vk_mid440 mc b r = subst [mc,`MC:byte list`; b,`b:num`; r,`r:num`]
 `\s. read wstatus s = WRunning /\
      read wstack s = [] /\ read wlabels s = [0,480,0; 0,1305,0] /\ read warity s = 0 /\
      read wmemsize s = 2097152 /\
      read (wlocal 1) s = I32 (word N) /\ read (wlocal 2) s = I32 (word N) /\
      read (wlocal 15) s = I32 (word (N * 3)) /\
      read (wlocal 4) s = I32 (word b) /\ read (wlocal 14) s = I32 (word r) /\
      (!j c. j < N /\ c < 3 ==>
         read (wmem :> bytes32 (word (1966080 + 4 * (3 * j + c)))) s = (XN:num->num->int32) j c) /\
      (!m. m < b ==> read (wmem :> bytes64 (word (1982464 + 8 * m))) s = word 0)`;;

let VK_B1_BODY_TAC exec =
  X_GEN_TAC `t:num` THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN VK_ARITH32_TAC THEN
  MAP_EVERY VK_VAL_TAC [`64 * t + 1982520`; `64 * t + 1982512`; `64 * t + 1982504`; `64 * t + 1982496`;
                        `64 * t + 1982488`; `64 * t + 1982480`; `64 * t + 1982472`; `64 * t + 1982464`] THEN
  VK_MSTEPS_TAC exec (1--46) THEN VK_FINAL_TAC THEN
  VK_CLOSE_TAC [`8 * t`; `8 * t + 1`; `8 * t + 2`; `8 * t + 3`; `8 * t + 4`; `8 * t + 5`; `8 * t + 6`; `8 * t + 7`] ALL_TAC;;

let VK_B1_BACK_TAC exec =
  X_GEN_TAC `t:num` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`64 * q`; `64 * t`] VK_WORD_NE) THEN ANTS_TAC THENL [VK_ARITH_TAC; DISCH_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  VK_MSTEPS_TAC exec (1--2) THEN VK_FINAL_TAC;;

let VK_B1_ENTRY_TAC exec n =
  ENSURES_INIT_TAC "s0" THEN MEMNAME_TAC THEN VK_ARITH32_TAC THEN
  VK_MSTEPS_TAC exec (1--n) THEN VK_FINAL_TAC THEN VK_CLOSE_TAC [] ALL_TAC;;

let VK_SEG2_TAC mc exec b2th =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `q = (3 * N) DIV 8` THEN ABBREV_TAC `r = (3 * N) MOD 8` THEN
  SUBGOAL_THEN `8 * q + r = 3 * N /\ r < 8` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q";"r"] THEN MP_TAC(SPECL [`3 * N`; `8`] DIVISION) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `word_and (word (N * 3)) (word 7):int32 = word r /\
                word_and (word (N * 3)) (word 4294967288):int32 = word (8 * q) /\
                word_and (word (8 * (N * 3))) (word 4294967232):int32 = word (64 * q) /\
                val (word N:int32) = N`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VK_AND7; VK_ANDM8; VK_ANDM64] THEN
    REWRITE_TAC[ARITH_RULE `N * 3 = 3 * N`] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [AP_TERM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "q" THEN
      SUBST1_TAC(ARITH_RULE `64 = 8 * 8`) THEN SIMP_TAC[DIV_MULT2; ARITH_EQ];
      MATCH_MP_TAC CAP_VAL_WORD32 THEN VK_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `N < 3` THENL
   [SUBGOAL_THEN `q = 0 /\ r = 3 * N` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
     [MAP_EVERY EXPAND_TAC ["q";"r"] THEN CONJ_TAC THENL [MATCH_MP_TAC DIV_LT; MATCH_MP_TAC MOD_LT] THEN VK_ARITH_TAC;
      ALL_TAC] THEN
    ENSURES_SEQUENCE_TAC `440` (vk_mid440 mc `0` `3 * N`) THEN CONJ_TAC THENL
     [VK_B1_ENTRY_TAC exec 15 THEN REWRITE_TAC[LT];
      MP_TAC(SPECL [`N:num`; `XN:num->num->int32`; `0`; `3 * N`] b2th) THEN
      ANTS_TAC THENL [VK_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th -> VK_ENS_WEAKEN_TAC th (ASM_REWRITE_TAC[]) (ASM_REWRITE_TAC[]))];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= q` ASSUME_TAC THENL [VK_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `r = 0` THENL
   [ENSURES_WHILE_UP_TAC `q:num` `316` `431` (vk_b1_inv mc) THEN REPEAT CONJ_TAC THENL
     [VK_ARITH_TAC; VK_B1_ENTRY_TAC exec 28; VK_B1_BODY_TAC exec; VK_B1_BACK_TAC exec;
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
      VK_MSTEPS_TAC exec (1--5) THEN VK_FINAL_TAC THEN VK_CLOSE_TAC [] ALL_TAC];
    SUBGOAL_THEN `(word r:int32 = word 0) <=> F` ASSUME_TAC THENL
     [MATCH_MP_TAC VK_WORD_NE0 THEN VK_ARITH_TAC; ALL_TAC] THEN
    ENSURES_SEQUENCE_TAC `440` (vk_mid440 mc `8 * q` `r:num`) THEN CONJ_TAC THENL
     [ENSURES_WHILE_UP_TAC `q:num` `316` `431` (vk_b1_inv mc) THEN REPEAT CONJ_TAC THENL
       [VK_ARITH_TAC; VK_B1_ENTRY_TAC exec 28; VK_B1_BODY_TAC exec; VK_B1_BACK_TAC exec;
        ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
        VK_MSTEPS_TAC exec (1--6) THEN VK_FINAL_TAC THEN VK_CLOSE_TAC [] ALL_TAC];
      MP_TAC(SPECL [`N:num`; `XN:num->num->int32`; `8 * q`; `r:num`] b2th) THEN
      ANTS_TAC THENL [VK_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th -> VK_ENS_WEAKEN_TAC th (ASM_REWRITE_TAC[]) (ASM_REWRITE_TAC[]))]];;

(* ------------------------------------------------------------------------- *)
(* Segment 1: setup and normalisation XN[3i+c] = ve_vk_xn S i c, pc 21..266.  *)
(* SB = source base (1122304 = VB for apply, 1114112 = VA for unapply).       *)
(* ------------------------------------------------------------------------- *)
let vk_seg1_stmt mc sb = subst [mc,`MC:byte list`; sb,`SB:num`; VK_FRAME,`VKF:wasmstate->wasmstate->bool`]
 `!N (src:num->int32). 1 <= N /\ N <= 640 ==>
   ensures wasm
    (\s. read wcode s = MC /\ read wpc s = word 21 /\ read wstatus s = WRunning /\
         read wstack s = [] /\ read wlabels s = [] /\ read warity s = 0 /\
         read wmemsize s = 2097152 /\
         read (wmem :> bytes32 (word 16644)) s = word N /\
         (!m. m < 3 * N ==> read (wmem :> bytes32 (word (SB + 4 * m))) s = src m))
    (\s. read wcode s = MC /\ read wpc s = word 266 /\ read wstatus s = WRunning /\
         read wstack s = [] /\ read wlabels s = [0,1305,0] /\ read warity s = 0 /\
         read wmemsize s = 2097152 /\
         read (wlocal 1) s = I32 (word N) /\ read (wlocal 2) s = I32 (word N) /\
         (!j c. j < N /\ c < 3 ==>
            read (wmem :> bytes32 (word (1966080 + 4 * (3 * j + c)))) s = ve_vk_xn src j c))
    VKF`;;

let vk_a_inv mc sb =
  let t = subst [mc,`MC:byte list`; sb,`SB:num`]
   `\i s. read wcode s = MC /\ read wstatus s = WRunning /\
          read wmemsize s = 2097152 /\ read warity s = 0 /\
          read wlabels s = [0,53,0; 0,1305,0] /\
          read (wlocal 0) s = I32 (word i) /\
          read (wlocal 1) s = I32 (word N) /\ read (wlocal 2) s = I32 (word N) /\
          read wstack s = (if read wpc s = word 55 then []
                           else [I32 (word (bitval (~(word i = word N:int32))))]) /\
          (!m. m < 3 * N ==> read (wmem :> bytes32 (word (SB + 4 * m))) s = (src:num->int32) m) /\
          (!j c. j < i /\ c < 3 ==>
            read (wmem :> bytes32 (word (1966080 + 4 * (3 * j + c)))) s = ve_vk_xn src j c)` in
  rhs(concl(TOP_DEPTH_CONV BETA_CONV t));;

let vk_b_inv mc sb =
  let t = subst [mc,`MC:byte list`; sb,`SB:num`]
   `\k s. read wcode s = MC /\ read wstatus s = WRunning /\
          read wmemsize s = 2097152 /\ read warity s = 0 /\
          read wlabels s = [0,142,0; 0,53,0; 0,1305,0] /\
          read (wlocal 0) s = I32 (word i) /\
          read (wlocal 1) s = I32 (word N) /\ read (wlocal 2) s = I32 (word N) /\
          read (wlocal 3) s = I32 (word (32 - k)) /\
          read (wlocal 4) s = I32 (word (4 * (i * 3 + 1))) /\
          read (wlocal 6) s = I32 (word (4 * (i * 3))) /\
          read (wlocal 8) s = I32 (word (4 * (i * 3 + 2))) /\
          read (wlocal 5) s = I64 (ve_vk_sx src i 1) /\
          read (wlocal 7) s = I64 (ve_vk_sx src i 0) /\
          read (wlocal 9) s = I64 (ve_vk_sx src i 2) /\
          read (wlocal 10) s = I64 (FST (ve_isq k (ve_vk_ss src i, word 0, word 4611686018427387904))) /\
          read (wlocal 12) s = I64 (FST (SND (ve_isq k (ve_vk_ss src i, word 0, word 4611686018427387904)))) /\
          read (wlocal 11) s = I64 (SND (SND (ve_isq k (ve_vk_ss src i, word 0, word 4611686018427387904)))) /\
          read wstack s = (if read wpc s = word 144 then [] else [I32 (word (32 - k))]) /\
          (!m. m < 3 * N ==> read (wmem :> bytes32 (word (SB + 4 * m))) s = (src:num->int32) m) /\
          (!j c. j < i /\ c < 3 ==>
            read (wmem :> bytes32 (word (1966080 + 4 * (3 * j + c)))) s = ve_vk_xn src j c)` in
  rhs(concl(TOP_DEPTH_CONV BETA_CONV t));;

let VK_ISQ_ADD1 = prove
 (`!k x. ve_isq (k + 1) x = ve_isq_step (ve_isq k x)`, REWRITE_TAC[GSYM ADD1; ve_isq]);;

let VK_SX_TAC = REWRITE_TAC[ve_vk_sx; ve_vk_ss; ve_isq; ADD_CLAUSES];;

let VK_XN_GOAL_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `j:num = i` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `c = 0 \/ c = 1 \/ c = 2` MP_TAC THENL
     [VK_ARITH_TAC; DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)] THEN
    REPEAT VK_PEEL_TAC THEN
    REWRITE_TAC[ve_vk_xn; ve_vk_len; ve_vk_sx; ADD_CLAUSES] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[COND_SWAP];
    REPEAT VK_PEEL_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN VK_ARITH_TAC];;

let VK_B_BODY_TAC exec =
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN VK_ARITH32_TAC THEN
  MP_TAC VK_COND_I64 THEN MP_TAC VK_COND_I32 THEN REPEAT DISCH_TAC THEN
  VK_MSTEPS_TAC exec (1--30) THEN VK_FINAL_TAC THEN
  REPEAT CONJ_TAC THEN TRY VK_WEQ_TAC THEN TRY(VK_MEMGOAL_TAC [] ALL_TAC) THEN
  REWRITE_TAC[injectivity "wval"; VK_ISQ_ADD1; ve_isq_step; COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_SUB_0; WORD_ADD_0; FST; SND];;

let VK_B_BACK_TAC exec =
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  MP_TAC(SPEC `32 - k:num` VK_WORD_NE0) THEN ANTS_TAC THENL [VK_ARITH_TAC; DISCH_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  VK_MSTEPS_TAC exec (1--2) THEN VK_FINAL_TAC;;

let VK_A_BODY_TAC mc sb exec =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ENSURES_WHILE_UP_TAC `32` `144` `195` (vk_b_inv mc sb) THEN REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    (* 55 .. 144: loads, |x|^2, isqrt init *)
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN VK_ARITH32_TAC THEN
    MAP_EVERY VK_VAL_TAC [`4 * (i * 3 + 1)`; `4 * (i * 3)`; `4 * (i * 3 + 2)`] THEN
    VK_LOADFACT2_TAC (subst [sb,`SB:num`] `read (bytes32 (word (4 * (i * 3 + 1) + SB))) mm = (src:num->int32) (3 * i + 1)`)
      (subst [sb,`SB:num`] `SB + 4 * (3 * i + 1)`) THEN
    VK_LOADFACT2_TAC (subst [sb,`SB:num`] `read (bytes32 (word (4 * (i * 3) + SB))) mm = (src:num->int32) (3 * i)`)
      (subst [sb,`SB:num`] `SB + 4 * (3 * i)`) THEN
    VK_LOADFACT2_TAC (subst [sb,`SB:num`] `read (bytes32 (word (4 * (i * 3 + 2) + SB))) mm = (src:num->int32) (3 * i + 2)`)
      (subst [sb,`SB:num`] `SB + 4 * (3 * i + 2)`) THEN
    VK_MSTEPS_TAC exec (1--41) THEN VK_FINAL_TAC THEN
    REPEAT CONJ_TAC THEN TRY VK_WEQ_TAC THEN TRY(VK_MEMGOAL_TAC [] ALL_TAC) THEN
    TRY(REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN VK_ARITH_TAC) THEN
    REWRITE_TAC[injectivity "wval"] THEN VK_SX_TAC;
    VK_B_BODY_TAC exec;
    VK_B_BACK_TAC exec;
    (* 195 .. 263: the three divisions and stores, i := i + 1 *)
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN VK_ARITH32_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUB_REFL]) THEN
    MP_TAC VK_COND_I64 THEN MP_TAC VK_COND_I32 THEN REPEAT DISCH_TAC THEN
    MP_TAC(SPEC `FST (SND (ve_isq 32 (ve_vk_ss src i, word 0, word 4611686018427387904)))` VK_LEN_NZ) THEN
    STRIP_TAC THEN
    MAP_EVERY VK_VAL_TAC [`4 * (i * 3 + 1)`; `4 * (i * 3)`; `4 * (i * 3 + 2)`] THEN
    VK_MSTEPS_TAC exec (1--35) THEN VK_FINAL_TAC THEN
    REPEAT CONJ_TAC THEN TRY VK_WEQ_TAC THEN TRY(VK_MEMGOAL_TAC [] ALL_TAC) THEN
    VK_XN_GOAL_TAC];;

let VK_SEG1_TAC mc sb exec =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word N:int32) = N /\ (word N:int32 = word 0 <=> F) /\
                (if ~(N < 640) then I32 (word 640) else I32 (word N)) = I32 (word N)`
   STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CAP_VAL_WORD32 THEN VK_ARITH_TAC;
      MATCH_MP_TAC VK_WORD_NE0 THEN VK_ARITH_TAC;
      COND_CASES_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN VK_ARITH_TAC];
    ALL_TAC] THEN
  ENSURES_WHILE_UP_TAC `N:num` `55` `263` (vk_a_inv mc sb) THEN REPEAT CONJ_TAC THENL
   [VK_ARITH_TAC;
    ENSURES_INIT_TAC "s0" THEN MEMNAME_TAC THEN VK_ARITH32_TAC THEN
    SUBGOAL_THEN `read (bytes32 (word 16644)) mm = word N` ASSUME_TAC THENL
     [EXPAND_TAC "mm" THEN REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    VK_MSTEPS_TAC exec (1--16) THEN VK_FINAL_TAC THEN
    REPEAT CONJ_TAC THEN TRY VK_WEQ_TAC THEN TRY(VK_MEMGOAL_TAC [] ALL_TAC) THEN
    REWRITE_TAC[LT];
    VK_A_BODY_TAC mc sb exec;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`i:num`; `N:num`] VK_WORD_NE) THEN ANTS_TAC THENL [VK_ARITH_TAC; DISCH_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
    VK_MSTEPS_TAC exec (1--2) THEN VK_FINAL_TAC;
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
    VK_MSTEPS_TAC exec (1--2) THEN VK_FINAL_TAC THEN
    REPEAT CONJ_TAC THEN TRY VK_WEQ_TAC THEN TRY(VK_MEMGOAL_TAC [] ALL_TAC)];;

(* ------------------------------------------------------------------------- *)
(* Segment 3: the pair loop, acc = ve_vk_acc X C N N, pc 480 .. 1038.          *)
(* X = \i c. sx(XN i c), C = \j. sx(CW j) for generic XN, CW.                 *)
(* ------------------------------------------------------------------------- *)
let VK_DEC1 = prove
 (`!a. 1 <= a ==> word (a + 4294967295):int32 = word (a - 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a + 4294967295 = (a - 1) + 4294967296` SUBST1_TAC THENL
   [VK_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
  REWRITE_TAC[WORD_ADD_0]);;

let VK_DEN_NZ = prove
 (`!d:int64. ((if ~(ival d > &2684355) then word 2684355 else d) = word 0) <=> F`,
  GEN_TAC THEN COND_CASES_TAC THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN INT_ARITH_TAC);;

(* val(word x:int32) = y where x = y or x = y + 2^32 *)
let VK_VALW_TAC x y =
  SUBGOAL_THEN (mk_eq(mk_comb(`val:int32->num`, mk_comb(`word:num->int32`, x)), y)) ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    MATCH_MP_TAC MOD_UNIQ THEN
    (EXISTS_TAC `0` THEN VK_ARITH_TAC ORELSE EXISTS_TAC `1` THEN VK_ARITH_TAC);
    ALL_TAC];;

(* an orthogonality instance read (bytesW x) (write (bytes64 a) v m) = read (bytesW x) m *)
let VK_RW64_TAC w x a = VK_RWO_TAC (if w = 64 then VK_R64_W64 else VK_R32_W64) x a;;

let vk_X = `\i c. word_sx ((XN:num->num->int32) i c):int64`;;
let vk_C = `\j. word_sx ((CW:num->int32) j):int64`;;

let vk_seg3_stmt mc = subst [mc,`MC:byte list`; VK_FRAME,`VKF:wasmstate->wasmstate->bool`]
 `!N (XN:num->num->int32) (CW:num->int32). 1 <= N /\ N <= 640 ==>
   ensures wasm
    (\s. read wcode s = MC /\ read wpc s = word 480 /\ read wstatus s = WRunning /\
         read wstack s = [] /\ read wlabels s = [0,1305,0] /\ read warity s = 0 /\
         read wmemsize s = 2097152 /\
         read (wlocal 1) s = I32 (word N) /\ read (wlocal 2) s = I32 (word N) /\
         read (wlocal 15) s = I32 (word (3 * N)) /\
         (!j c. j < N /\ c < 3 ==>
            read (wmem :> bytes32 (word (1966080 + 4 * (3 * j + c)))) s = XN j c) /\
         (!j. j < N ==> read (wmem :> bytes32 (word (16704 + 4 * j))) s = CW j) /\
         (!m. m < 3 * N ==> read (wmem :> bytes64 (word (1982464 + 8 * m))) s = word 0))
    (\s. read wcode s = MC /\ read wpc s = word 1038 /\ read wstatus s = WRunning /\
         read wstack s = [] /\ read wlabels s = [0,1305,0] /\ read warity s = 0 /\
         read wmemsize s = 2097152 /\
         read (wlocal 1) s = I32 (word N) /\ read (wlocal 15) s = I32 (word (3 * N)) /\
         (!j c. j < N /\ c < 3 ==>
            read (wmem :> bytes64 (word (1982464 + 8 * (3 * j + c)))) s =
            ve_vk_acc (\i c. word_sx (XN i c):int64) (\j. word_sx (CW j):int64) N N j c))
    VKF`;;

let vk_c_inv mc =
  let t = subst [mc,`MC:byte list`; vk_X,`X:num->num->int64`; vk_C,`C:num->int64`]
   `\i s. read wcode s = MC /\ read wstatus s = WRunning /\
          read wmemsize s = 2097152 /\ read warity s = 0 /\
          read wlabels s = [0,511,0; 0,1305,0] /\
          read (wlocal 1) s = I32 (word N) /\ read (wlocal 2) s = I32 (word N) /\
          read (wlocal 15) s = I32 (word (3 * N)) /\
          read (wlocal 3) s = I32 (word i) /\
          (i < N ==> read (wlocal 16) s = I32 (word (N - 1 - i))) /\
          read (wlocal 17) s = I32 (word (1982464 + 24 * i)) /\
          read (wlocal 18) s = I32 (word (1966100 + 12 * i)) /\
          read (wlocal 19) s = I32 (word (16708 + 4 * i)) /\
          read wstack s = (if read wpc s = word 513 then []
                           else [I32 (word (bitval (~(word i = word N:int32))))]) /\
          (!j c. j < N /\ c < 3 ==>
            read (wmem :> bytes32 (word (1966080 + 4 * (3 * j + c)))) s = XN j c) /\
          (!j. j < N ==> read (wmem :> bytes32 (word (16704 + 4 * j))) s = CW j) /\
          (!j c. j < N /\ c < 3 ==>
            read (wmem :> bytes64 (word (1982464 + 8 * (3 * j + c)))) s = ve_vk_acc X C N i j c)` in
  rhs(concl(TOP_DEPTH_CONV BETA_CONV t));;

(* the inner loop state after k partners (j = i+1 .. i+k) of row i; pcs: *)
(* d = 1 at the loop (639 / 928), d = 0 at the mid point 932             *)
let vk_d_inv mc =
  let t = subst [mc,`MC:byte list`; vk_X,`X:num->num->int64`; vk_C,`C:num->int64`]
   `\k s. read wcode s = MC /\ read wstatus s = WRunning /\
          read wmemsize s = 2097152 /\ read warity s = 0 /\
          read wlabels s = [0,637,0; 0,932,0; 0,511,0; 0,1305,0] /\
          read (wlocal 1) s = I32 (word N) /\ read (wlocal 2) s = I32 (word N) /\
          read (wlocal 15) s = I32 (word (3 * N)) /\
          read (wlocal 16) s = I32 (word (N - 1 - i)) /\
          read (wlocal 17) s = I32 (word (1982464 + 24 * i)) /\
          read (wlocal 18) s = I32 (word (1966100 + 12 * i)) /\
          read (wlocal 19) s = I32 (word (16708 + 4 * i)) /\
          read (wlocal 20) s = I32 (word (i * 3)) /\
          read (wlocal 21) s = I32 (word (i * 3 + 2)) /\
          read (wlocal 22) s = I32 (word (i * 3 + 1)) /\
          read (wlocal 26) s = I32 (word (i + 1)) /\
          read (wlocal 3) s = I32 (word (1966100 + 12 * (i + k))) /\
          read (wlocal 0) s = I32 (word (16708 + 4 * (i + k))) /\
          read (wlocal 14) s = I32 (word (1982464 + 24 * (i + k))) /\
          read (wlocal 6) s = I32 (word (N - 1 - i - k)) /\
          read (wlocal 11) s = I64 (word_sx (XN i 0)) /\
          read (wlocal 10) s = I64 (word_sx (XN i 1)) /\
          read (wlocal 12) s = I64 (word_sx (XN i 2)) /\
          read (wlocal 27) s = I64 (word_sx (CW i)) /\
          read (wlocal 25) s = I64 (ve_vk_rs X C i k 0) /\
          read (wlocal 24) s = I64 (ve_vk_rs X C i k 1) /\
          read (wlocal 23) s = I64 (ve_vk_rs X C i k 2) /\
          read wstack s = (if read wpc s = word 639 then [] else [I32 (word (N - 1 - i - k))]) /\
          (!j c. j < N /\ c < 3 ==>
            read (wmem :> bytes32 (word (1966080 + 4 * (3 * j + c)))) s = XN j c) /\
          (!j. j < N ==> read (wmem :> bytes32 (word (16704 + 4 * j))) s = CW j) /\
          (!j c. j < N /\ c < 3 /\ ~(i < j /\ j < i + 1 + k) ==>
            read (wmem :> bytes64 (word (1982464 + 8 * (3 * j + c)))) s = ve_vk_acc X C N i j c) /\
          (!j c. i < j /\ j < i + 1 + k /\ j < N /\ c < 3 ==>
            read (wmem :> bytes64 (word (1982464 + 8 * (3 * j + c)))) s =
            ve_vk_upd X C i j c (ve_vk_acc X C N i j c))` in
  rhs(concl(TOP_DEPTH_CONV BETA_CONV t));;

(* the state at 932 after row i's partners (K = N - 1 - i of them) *)
let vk_mid932 mc =
  let t = subst [mc,`MC:byte list`; vk_X,`X:num->num->int64`; vk_C,`C:num->int64`]
   `\s. read wstatus s = WRunning /\
        read wmemsize s = 2097152 /\ read warity s = 0 /\ read wstack s = [] /\
        read wlabels s = [0,511,0; 0,1305,0] /\
        read (wlocal 1) s = I32 (word N) /\ read (wlocal 2) s = I32 (word N) /\
        read (wlocal 15) s = I32 (word (3 * N)) /\
        read (wlocal 16) s = I32 (word (N - 1 - i)) /\
        read (wlocal 17) s = I32 (word (1982464 + 24 * i)) /\
        read (wlocal 18) s = I32 (word (1966100 + 12 * i)) /\
        read (wlocal 19) s = I32 (word (16708 + 4 * i)) /\
        read (wlocal 20) s = I32 (word (i * 3)) /\
        read (wlocal 21) s = I32 (word (i * 3 + 2)) /\
        read (wlocal 22) s = I32 (word (i * 3 + 1)) /\
        read (wlocal 26) s = I32 (word (i + 1)) /\
        read (wlocal 25) s = I64 (ve_vk_rs X C i (N - 1 - i) 0) /\
        read (wlocal 24) s = I64 (ve_vk_rs X C i (N - 1 - i) 1) /\
        read (wlocal 23) s = I64 (ve_vk_rs X C i (N - 1 - i) 2) /\
        (!j c. j < N /\ c < 3 ==>
           read (wmem :> bytes32 (word (1966080 + 4 * (3 * j + c)))) s = XN j c) /\
        (!j. j < N ==> read (wmem :> bytes32 (word (16704 + 4 * j))) s = CW j) /\
        (!j c. j < N /\ c < 3 /\ ~(i < j) ==>
           read (wmem :> bytes64 (word (1982464 + 8 * (3 * j + c)))) s = ve_vk_acc X C N i j c) /\
        (!j c. i < j /\ j < N /\ c < 3 ==>
           read (wmem :> bytes64 (word (1982464 + 8 * (3 * j + c)))) s =
           ve_vk_upd X C i j c (ve_vk_acc X C N i j c))` in
  rhs(concl(TOP_DEPTH_CONV BETA_CONV t));;

let VK_ACC_ADD1 = prove
 (`!X C n i j c. ve_vk_acc X C n (i + 1) j c =
     if j = i then word_add (ve_vk_acc X C n i j c) (ve_vk_rs X C i (n - 1 - i) c)
     else if i < j then ve_vk_upd X C i j c (ve_vk_acc X C n i j c)
     else ve_vk_acc X C n i j c`,
  REWRITE_TAC[GSYM ADD1; ve_vk_acc]);;
let VK_RS_ADD1 = prove
 (`!X C i k c. ve_vk_rs X C i (k + 1) c = word_add (ve_vk_ti X C i (i + 1 + k) c) (ve_vk_rs X C i k c)`,
  REWRITE_TAC[GSYM ADD1; ve_vk_rs]);;

let VK_FIELD_TAC =
  REWRITE_TAC[injectivity "wval"; VK_RS_ADD1; ve_vk_rs; ve_vk_upd; ve_vk_tj; ve_vk_ti;
              ve_vk_w; ve_vk_v; ARITH_EQ] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[COND_SWAP; ARITH_EQ];;

let VK_D_BODY_TAC exec =
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN VK_ARITH32_TAC THEN
  MP_TAC VK_COND_I64 THEN MP_TAC VK_COND_I32 THEN MP_TAC VK_DEN_NZ THEN REPEAT DISCH_TAC THEN
  MAP_EVERY VK_VAL_TAC [`(1982464 + 24 * (i + k)) + 24`; `1966100 + 12 * (i + k)`;
     `(1982464 + 24 * (i + k)) + 32`; `(1982464 + 24 * (i + k)) + 40`; `16708 + 4 * (i + k)`] THEN
  VK_VALW_TAC `(1966100 + 12 * (i + k)) + 4294967292` `1966096 + 12 * (i + k)` THEN
  VK_VALW_TAC `(1966100 + 12 * (i + k)) + 4294967288` `1966092 + 12 * (i + k)` THEN
  VK_LOADFACT2_TAC `read (bytes32 (word (1966096 + 12 * (i + k)))) mm = (XN:num->num->int32) (i + 1 + k) 1`
    `1966080 + 4 * (3 * (i + 1 + k) + 1)` THEN
  VK_LOADFACT2_TAC `read (bytes32 (word (1966092 + 12 * (i + k)))) mm = (XN:num->num->int32) (i + 1 + k) 0`
    `1966080 + 4 * (3 * (i + 1 + k) + 0)` THEN
  VK_LOADFACT2_TAC `read (bytes32 (word (1966100 + 12 * (i + k)))) mm = (XN:num->num->int32) (i + 1 + k) 2`
    `1966080 + 4 * (3 * (i + 1 + k) + 2)` THEN
  VK_LOADFACT2_TAC `read (bytes32 (word (16708 + 4 * (i + k)))) mm = (CW:num->int32) (i + 1 + k)`
    `16704 + 4 * (i + 1 + k)` THEN
  VK_LOADFACT2_TAC (subst [vk_X,`X:num->num->int64`; vk_C,`C:num->int64`]
    `read (bytes64 (word ((1982464 + 24 * (i + k)) + 24))) mm = ve_vk_acc X C N i (i + 1 + k) 0`)
    `1982464 + 8 * (3 * (i + 1 + k) + 0)` THEN
  VK_LOADFACT2_TAC (subst [vk_X,`X:num->num->int64`; vk_C,`C:num->int64`]
    `read (bytes64 (word ((1982464 + 24 * (i + k)) + 32))) mm = ve_vk_acc X C N i (i + 1 + k) 1`)
    `1982464 + 8 * (3 * (i + 1 + k) + 1)` THEN
  VK_LOADFACT2_TAC (subst [vk_X,`X:num->num->int64`; vk_C,`C:num->int64`]
    `read (bytes64 (word ((1982464 + 24 * (i + k)) + 40))) mm = ve_vk_acc X C N i (i + 1 + k) 2`)
    `1982464 + 8 * (3 * (i + 1 + k) + 2)` THEN
  VK_RW64_TAC 64 `(1982464 + 24 * (i + k)) + 32` `(1982464 + 24 * (i + k)) + 24` THEN
  VK_RW64_TAC 64 `(1982464 + 24 * (i + k)) + 40` `(1982464 + 24 * (i + k)) + 24` THEN
  VK_RW64_TAC 64 `(1982464 + 24 * (i + k)) + 40` `(1982464 + 24 * (i + k)) + 32` THEN
  VK_RW64_TAC 32 `16708 + 4 * (i + k)` `(1982464 + 24 * (i + k)) + 24` THEN
  VK_RW64_TAC 32 `16708 + 4 * (i + k)` `(1982464 + 24 * (i + k)) + 32` THEN
  VK_RW64_TAC 32 `16708 + 4 * (i + k)` `(1982464 + 24 * (i + k)) + 40` THEN
  VK_MSTEPS_TAC exec (1--160) THEN VK_FINAL_TAC THEN
  REPEAT CONJ_TAC THEN TRY VK_WEQ_TAC THEN TRY(VK_MEMGOAL_TAC [] ALL_TAC) THEN
  TRY(VK_FIELD_TAC THEN NO_TAC) THEN
  (* acc goals *)
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `j = i + 1 + k` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `c = 0 \/ c = 1 \/ c = 2` MP_TAC THENL
     [VK_ARITH_TAC; DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)] THEN
    REPEAT VK_PEEL_TAC THEN TRY(VK_ARITH_TAC THEN NO_TAC) THEN VK_FIELD_TAC;
    REPEAT VK_PEEL_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN VK_ARITH_TAC];;

let VK_L16_TAC =
  SUBGOAL_THEN `read (wlocal 16) s0 = I32 (word (N - 1 - i))` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN VK_ARITH_TAC; ALL_TAC];;

let VK_C_PRE_FACTS_TAC =
  MAP_EVERY VK_VAL_TAC [`i + 1`; `4 * i + 16704`; `4 * (i * 3)`; `4 * (i * 3 + 2)`; `4 * (i * 3 + 1)`];;

let VK_D_ENTRY_TAC exec =
  ENSURES_INIT_TAC "s0" THEN MEMNAME_TAC THEN VK_ARITH32_TAC THEN VK_L16_TAC THEN
  SUBGOAL_THEN `(i + 1 >= N) <=> F` ASSUME_TAC THENL [VK_ARITH_TAC; ALL_TAC] THEN
  VK_C_PRE_FACTS_TAC THEN
  VK_LOADFACT2_TAC `read (bytes32 (word (4 * i + 16704))) mm = (CW:num->int32) i` `16704 + 4 * i` THEN
  VK_LOADFACT2_TAC `read (bytes32 (word (4 * (i * 3) + 1966080))) mm = (XN:num->num->int32) i 0`
    `1966080 + 4 * (3 * i + 0)` THEN
  VK_LOADFACT2_TAC `read (bytes32 (word (4 * (i * 3 + 2) + 1966080))) mm = (XN:num->num->int32) i 2`
    `1966080 + 4 * (3 * i + 2)` THEN
  VK_LOADFACT2_TAC `read (bytes32 (word (4 * (i * 3 + 1) + 1966080))) mm = (XN:num->num->int32) i 1`
    `1966080 + 4 * (3 * i + 1)` THEN
  VK_MSTEPS_TAC exec (1--62) THEN VK_FINAL_TAC THEN
  REPEAT CONJ_TAC THEN TRY VK_WEQ_TAC THEN
  TRY(REWRITE_TAC[injectivity "wval"; ve_vk_rs] THEN NO_TAC) THEN
  TRY(VK_MEMGOAL_TAC [] ALL_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN VK_ARITH_TAC;;

let VK_D_BACK_TAC exec =
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  MP_TAC(SPEC `N - 1 - i - k:num` VK_WORD_NE0) THEN ANTS_TAC THENL [VK_ARITH_TAC; DISCH_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  VK_MSTEPS_TAC exec (1--2) THEN VK_FINAL_TAC;;

let VK_D_EXIT_TAC exec =
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUB_REFL]) THEN
  VK_MSTEPS_TAC exec (1--3) THEN VK_FINAL_TAC THEN
  REPEAT CONJ_TAC THEN TRY VK_WEQ_TAC THEN TRY(VK_MEMGOAL_TAC [] ALL_TAC);;

let VK_C_SKIP_TAC exec =
  ENSURES_INIT_TAC "s0" THEN MEMNAME_TAC THEN VK_ARITH32_TAC THEN VK_L16_TAC THEN
  SUBGOAL_THEN `(i + 1 >= N) <=> T` ASSUME_TAC THENL [VK_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `N - 1 - i = 0` ASSUME_TAC THENL [VK_ARITH_TAC; ALL_TAC] THEN
  VK_C_PRE_FACTS_TAC THEN
  VK_MSTEPS_TAC exec (1--25) THEN VK_FINAL_TAC THEN
  REPEAT CONJ_TAC THEN TRY VK_WEQ_TAC THEN
  TRY(REWRITE_TAC[injectivity "wval"; ve_vk_rs] THEN NO_TAC) THEN
  TRY(VK_MEMGOAL_TAC [] ALL_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN VK_ARITH_TAC;;

let VK_C_POST_TAC exec =
  ENSURES_INIT_TAC "s0" THEN MEMNAME_TAC THEN VK_ARITH32_TAC THEN
  MAP_EVERY VK_VAL_TAC [`8 * (i * 3)`; `8 * (i * 3 + 1)`; `8 * (i * 3 + 2)`] THEN
  VK_LOADFACT2_TAC (subst [vk_X,`X:num->num->int64`; vk_C,`C:num->int64`]
    `read (bytes64 (word (8 * (i * 3) + 1982464))) mm = ve_vk_acc X C N i i 0`)
    `1982464 + 8 * (3 * i + 0)` THEN
  VK_LOADFACT2_TAC (subst [vk_X,`X:num->num->int64`; vk_C,`C:num->int64`]
    `read (bytes64 (word (8 * (i * 3 + 1) + 1982464))) mm = ve_vk_acc X C N i i 1`)
    `1982464 + 8 * (3 * i + 1)` THEN
  VK_LOADFACT2_TAC (subst [vk_X,`X:num->num->int64`; vk_C,`C:num->int64`]
    `read (bytes64 (word (8 * (i * 3 + 2) + 1982464))) mm = ve_vk_acc X C N i i 2`)
    `1982464 + 8 * (3 * i + 2)` THEN
  VK_RW64_TAC 64 `8 * (i * 3 + 1) + 1982464` `8 * (i * 3) + 1982464` THEN
  VK_RW64_TAC 64 `8 * (i * 3 + 2) + 1982464` `8 * (i * 3) + 1982464` THEN
  VK_RW64_TAC 64 `8 * (i * 3 + 2) + 1982464` `8 * (i * 3 + 1) + 1982464` THEN
  VK_MSTEPS_TAC exec (1--48) THEN VK_FINAL_TAC THEN
  REPEAT CONJ_TAC THEN TRY VK_WEQ_TAC THEN TRY(DISCH_TAC THEN VK_WEQ_TAC) THEN
  TRY(VK_MEMGOAL_TAC [] ALL_TAC) THEN
  REWRITE_TAC[VK_ACC_ADD1] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `j:num = i` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `c = 0 \/ c = 1 \/ c = 2` MP_TAC THENL
     [VK_ARITH_TAC; DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)] THEN
    REPEAT VK_PEEL_TAC;
    ASM_REWRITE_TAC[] THEN REPEAT VK_PEEL_TAC THEN
    ASM_CASES_TAC `i < j:num` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN VK_ARITH_TAC];;

let VK_C_BODY_TAC mc exec =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `932` (vk_mid932 mc) THEN CONJ_TAC THENL
   [ASM_CASES_TAC `i + 1 < N` THENL
     [ENSURES_WHILE_UP_TAC `N - 1 - i` `639` `928` (vk_d_inv mc) THEN REPEAT CONJ_TAC THENL
       [VK_ARITH_TAC; VK_TRY "dentry" (VK_D_ENTRY_TAC exec); VK_TRY "dbody" (VK_D_BODY_TAC exec);
        VK_TRY "dback" (VK_D_BACK_TAC exec); VK_TRY "dexit" (VK_D_EXIT_TAC exec)];
      VK_TRY "cskip" (VK_C_SKIP_TAC exec)];
    VK_TRY "cpost" (VK_C_POST_TAC exec)];;

let VK_SEG3_TAC mc exec =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val (word N:int32) = N /\ word (N + 4294967295):int32 = word (N - 1)`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC CAP_VAL_WORD32; MATCH_MP_TAC VK_DEC1] THEN VK_ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_WHILE_UP_TAC `N:num` `513` `1035` (vk_c_inv mc) THEN REPEAT CONJ_TAC THENL
   [VK_ARITH_TAC;
    VK_TRY "centry" (ENSURES_INIT_TAC "s0" THEN MEMNAME_TAC THEN VK_ARITH32_TAC THEN
    VK_MSTEPS_TAC exec (1--13) THEN VK_FINAL_TAC THEN
    REPEAT CONJ_TAC THEN TRY VK_WEQ_TAC THEN TRY(DISCH_TAC THEN VK_WEQ_TAC) THEN
    TRY(VK_MEMGOAL_TAC [] ALL_TAC) THEN
    TRY(REWRITE_TAC[ve_vk_acc] THEN VK_MEMGOAL_TAC [] ALL_TAC));
    VK_C_BODY_TAC mc exec;
    VK_TRY "cback" (X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`i:num`; `N:num`] VK_WORD_NE) THEN ANTS_TAC THENL [VK_ARITH_TAC; DISCH_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN VK_L16_TAC THEN
    VK_MSTEPS_TAC exec (1--2) THEN VK_FINAL_TAC);
    VK_TRY "cexit" (ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
    VK_MSTEPS_TAC exec (1--2) THEN VK_FINAL_TAC THEN
    REPEAT CONJ_TAC THEN TRY VK_WEQ_TAC THEN TRY(VK_MEMGOAL_TAC [] ALL_TAC))];;

(* ------------------------------------------------------------------------- *)
(* Composition: the four segments, the untouched model / VA / VB facts kept   *)
(* through the frame, give ve_vk_ok ve_vk.                                    *)
(* ------------------------------------------------------------------------- *)
let VK_ENSURES_SEG = prove
 (`!P Q P' Q' C (R:wasmstate->bool).
     ensures wasm P Q C /\ (!s. P' s ==> P s /\ R s) /\ (!s. Q s /\ R s ==> Q' s) /\
     (!s s'. C s s' /\ R s ==> R s')
     ==> ensures wasm P' Q' C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC `\s. (Q:wasmstate->bool) s /\ R s` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC VK_ENSURES_KEEP THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC `P:wasmstate->bool` THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[]; ASM_REWRITE_TAC[]]);;

let VK_ACC_FLAT = prove
 (`!(s:wasmstate) N (FF:num->num->int64).
     (!j c. j < N /\ c < 3 ==> read (wmem :> bytes64 (word (1982464 + 8 * (3 * j + c)))) s = FF j c)
     ==> (!m. m < 3 * N ==> read (wmem :> bytes64 (word (1982464 + 8 * m))) s = FF (m DIV 3) (m MOD 3))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`m:num`; `3`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m DIV 3`; `m MOD 3`]) THEN
  ANTS_TAC THENL [VK_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `3 * m DIV 3 + m MOD 3 = m` (fun th -> REWRITE_TAC[th]) THEN VK_ARITH_TAC);;

let VK_X_ETA = prove
 (`!S. (\i c. word_sx (ve_vk_xn S i c):int64) = ve_vk_X S`,
  REWRITE_TAC[FUN_EQ_THM; ve_vk_X]);;
let VK_C_ETA = prove
 (`!mdl. (\j. word_sx ((mdl:num->int32) (16 + j)):int64) = ve_vk_C mdl`,
  REWRITE_TAC[FUN_EQ_THM; ve_vk_C]);;

let vk_rest q = rand(rand(snd(dest_abs q)));;
let vk_mid q r =
  let s,_ = dest_abs q in
  mk_abs(s, mk_conj(vk_rest q, rhs(concl(BETA_CONV(mk_comb(r,s))))));;

let VK_USE_SEG_TAC th r pretac posttac =
  MATCH_MP_TAC VK_ENSURES_SEG THEN
  EXISTS_TAC (rand(rator(rator(concl th)))) THEN EXISTS_TAC (rand(rator(concl th))) THEN
  EXISTS_TAC r THEN REPEAT CONJ_TAC THENL
   [ACCEPT_TAC th;
    X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN pretac;
    X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN posttac;
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN VK_FRAME_TAC];;

let VK_R = `\s. (!k. k < 1024 ==> read (wmem :> bytes32 (word (16640 + 4 * k))) s = (mdl:num->int32) k) /\
                (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1114112 + 4 * m))) s = (va:num->int32) m) /\
                (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1122304 + 4 * m))) s = (vb:num->int32) m)`;;

let VK_PRE1_TAC =
  SUBGOAL_THEN `read (wmem :> bytes32 (word 16644)) s = word N` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `1` o check (fun th -> can (find_term ((=) `16640`)) (concl th))) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[];;

let VK_PRE3_TAC =
  SUBGOAL_THEN `!j. j < N ==> read (wmem :> bytes32 (word (16704 + 4 * j))) s = (mdl:num->int32) (16 + j)`
    ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `16 + j` o check (fun th -> can (find_term ((=) `16640`)) (concl th))) THEN
    REWRITE_TAC[ARITH_RULE `16640 + 4 * (16 + j) = 16704 + 4 * j`] THEN
    DISCH_THEN MATCH_MP_TAC THEN VK_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[];;

let VK_PRE4_TAC =
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC VK_ACC_FLAT THEN ASM_REWRITE_TAC[];;

let VK_POST4_TAC src =
  SUBGOAL_THEN (subst [src,`src:num->int32`]
    `!m. ve_vk mdl src m =
         ve_vk_rnd (ve_vk_acc (\i c. word_sx (ve_vk_xn src i c)) (\j. word_sx ((mdl:num->int32) (16 + j)))
                              N N (m DIV 3) (m MOD 3))`)
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[ve_vk; VK_X_ETA; VK_C_ETA; MIN] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `val (word N:int32) = N` SUBST1_TAC THENL
     [MATCH_MP_TAC CAP_VAL_WORD32 THEN VK_ARITH_TAC; ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[]];;

let vk_find_seg asl pc =
  let w = mk_comb(`word:num->int64`, mk_small_numeral pc) in
  snd(find (fun (_,th) -> let c = concl th in
     try let p = rand(rator(rator c)) in
         fst(dest_const(fst(strip_comb c))) = "ensures" && can (find_term ((=) w)) p
     with Failure _ -> false) asl);;

(* one export: the segment theorems for its code, the source src *)
let VK_EXPORT_TAC src seg1 seg2 seg3 seg4 =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; src] seg1) THEN
  MP_TAC(SPECL [`N:num`; mk_comb(`ve_vk_xn`, src)] seg2) THEN
  MP_TAC(SPECL [`N:num`; mk_comb(`ve_vk_xn`, src); `\j. (mdl:num->int32) (16 + j)`] seg3) THEN
  MP_TAC(SPECL [`N:num`; subst [src,`src:num->int32`]
     `\m. ve_vk_acc (\i c. word_sx (ve_vk_xn src i c)) (\j. word_sx ((mdl:num->int32) (16 + j)))
                    N N (m DIV 3) (m MOD 3)`] seg4) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT DISCH_TAC THEN
  W(fun (asl,w) ->
    let th1 = vk_find_seg asl 21 and th2 = vk_find_seg asl 266
    and th3 = vk_find_seg asl 480 and th4 = vk_find_seg asl 1038 in
    let q th = rand(rator(concl th)) in
    ENSURES_SEQUENCE_TAC `266` (vk_mid (q th1) VK_R) THEN CONJ_TAC THENL
     [VK_TRY "use1" (VK_USE_SEG_TAC th1 VK_R VK_PRE1_TAC (ASM_REWRITE_TAC[]));
      ENSURES_SEQUENCE_TAC `480` (vk_mid (q th2) VK_R) THEN CONJ_TAC THENL
       [VK_TRY "use2" (VK_USE_SEG_TAC th2 VK_R (ASM_REWRITE_TAC[]) (ASM_REWRITE_TAC[]));
        ENSURES_SEQUENCE_TAC `1038` (vk_mid (q th3) VK_R) THEN CONJ_TAC THENL
         [VK_TRY "use3" (VK_USE_SEG_TAC th3 VK_R VK_PRE3_TAC (ASM_REWRITE_TAC[]));
          VK_TRY "use4" (VK_USE_SEG_TAC th4 VK_R VK_PRE4_TAC (VK_POST4_TAC src))]]]);;

(* ------------------------------------------------------------------------- *)
(* Segments 2-4 (pc 266 .. 1305) are byte-identical in ve_vort_apply and     *)
(* ve_vort_unapply (the bodies differ only at offsets 73, 90 and 111, in     *)
(* segment 1). They are proved once for a code variable MC under the         *)
(* antecedent VK_DEC_H: the conjunction of the decode facts                  *)
(* wasm_decode MC pc = SOME (i,n) of the window pc 266 .. 1305 (as computed  *)
(* for ve_vort_apply_mc). The stepper uses its conjuncts. Each export's      *)
(* instance (vk_inst_code) discharges the antecedent with that export's own  *)
(* decode theorems, kernel-computed by FAST_MK_EXEC_RANGES (VE_VK_*_EXEC).   *)
(* ------------------------------------------------------------------------- *)
let vk_mcv = `MC:byte list`;;

let vk_dec_lo = 266;;

let vk_dec_pcs ((_:thm), (arr:thm option array)) =
  filter (fun pc -> pc >= vk_dec_lo && arr.(pc) <> None) (0--(Array.length arr - 1));;

let vk_dec_th (arr:thm option array) pc =
  match arr.(pc) with Some th -> th | None -> failwith "vk_dec_th";;

let VK_DEC_H =
  let (_,arr) = VE_VK_APPLY_EXEC in
  list_mk_conj (map (fun pc ->
     let th = vk_dec_th arr pc in
     let l = lhs(concl th) in
     mk_eq(mk_comb(mk_comb(rator(rator l), vk_mcv), rand l), rhs(concl th)))
   (vk_dec_pcs VE_VK_APPLY_EXEC));;

(* the stepper's decode table for MC: the conjuncts of VK_DEC_H, each with   *)
(* the hypothesis VK_DEC_H                                                    *)
let VK_GEN_EXEC =
  let (lth,arr) = VE_VK_APPLY_EXEC in
  let pcs = vk_dec_pcs VE_VK_APPLY_EXEC in
  let ths = CONJUNCTS (ASSUME VK_DEC_H) in
  let garr = Array.make (Array.length arr) None in
  List.iter2 (fun pc th -> garr.(pc) <- Some th) pcs ths;
  (lth, garr);;

(* |- VK_DEC_H ==> stmt. The antecedent is not put in the assumption list  *)
(* (as ~400 rewrites it would slow every step); DISCH_THEN's justification   *)
(* discharges the hypothesis VK_DEC_H that the decode conjuncts carry.       *)
let vk_gen_prove (stmt:term) (tac:tactic) = prove(mk_imp(VK_DEC_H, stmt), DISCH_THEN(K tac));;

(* the instance for one export: MC := its code, the antecedent discharged by *)
(* its decode theorems at the same offsets                                   *)
let vk_inst_code mc (exec:thm * thm option array) (th:thm) =
  let (_,arr) = exec in
  let dth = end_itlist CONJ (map (vk_dec_th arr) (vk_dec_pcs VE_VK_APPLY_EXEC)) in
  MP (INST [mc, vk_mcv] th) dth;;
