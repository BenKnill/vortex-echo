(* ========================================================================= *)
(* Bubble Echo v2 capillary: generic helpers for the canonical-loop proofs  *)
(* (no code constant). The 32-bit cell lemmas, MEMNAME_TAC and the stepping *)
(* that keeps facts about a named memory are copied from v1                 *)
(* tasks/bubble-echo/proofs/rot_helpers.ml (bubble/echo-20261016).          *)
(* ========================================================================= *)

needs "wasm/proofs/wasm_tactics.ml";;

let CAP_B32_OTHER = prove
 (`!a b. (a + 4 <= b \/ b + 4 <= a) /\ a < 4294967296 /\ b < 4294967296
         ==> !(v:int32) (m:int64->byte).
               read (bytes32 (word a)) (write (bytes32 (word b)) v m) =
               read (bytes32 (word a)) m`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC READ_WRITE_ORTHOGONAL_COMPONENTS THEN
  REWRITE_TAC[bytes32] THEN MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_LEFT THEN
  REWRITE_TAC[ORTHOGONAL_COMPONENTS_BYTES; DIMINDEX_64] THEN
  MATCH_MP_TAC NONOVERLAPPING_MODULO_SIMPLE THEN
  SUBGOAL_THEN `val(word a:int64) = a /\ val(word b:int64) = b`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC]);;

let CAP_B32_SAME = prove
 (`!a (v:int32) (m:int64->byte). read (bytes32 a) (write (bytes32 a) v m) = v`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC READ_WRITE_VALID_COMPONENT THEN
  REWRITE_TAC[VALID_COMPONENT_BYTES32]);;

let CAP_VAL_WORD32 = prove
 (`!x. x < 4294967296 ==> val(word x:int32) = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let RESOLVE_PC_COND_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in
     is_eq c && is_cond (rhs c))) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
  REWRITE_TAC[] THEN DISCH_TAC;;

(* Name the memory: forall facts about read (wmem :> ..) s0 become facts   *)
(* about mm = read wmem s0, which survive steps (and stores, via           *)
(* CAP_MEM_UPDATE_TAC's read wmem s' = write .. mm).                       *)
let MEMNAME_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "wmem")) (concl th)))) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ABBREV_TAC `mm = read wmem (s0:wasmstate)` THEN REPEAT DISCH_TAC;;

(* Stepping that keeps facts about a named memory mm (read (bytes32 a) mm): *)
(* only :wasmstate variables count as states when discarding old facts.     *)
let CAP_DISCARD_OLD_TAC s =
  let v = mk_var(s,`:wasmstate`) and ws = `:wasmstate` in
  let rec svars bound tm =
    match tm with
      Comb(Comb(Const("read",_),c),s') ->
        union (svars bound c)
          (if mem s' bound || not (type_of s' = ws) then svars bound s' else [s'])
    | Comb(a,b) -> union (svars bound a) (svars bound b)
    | Abs(x,t) -> svars (x::bound) t
    | _ -> [] in
  DISCARD_ASSUMPTIONS_TAC(fun th ->
    let us = svars [] (concl th) in not(us = [] || us = [v]));;

let CAP_STEPS_TAC execth snums =
  MAP_EVERY (fun s -> WASM_STEP_TAC execth [] s THEN CAP_DISCARD_OLD_TAC s)
            (statenames "s" snums);;

(* The displacement D as compiled (clang's branch-free arithmetic shift):   *)
(* m = v >>s 31; ((m xor v) >>u 16) xor m  =  v >>s 16.                     *)
let CAP_SAR16 = prove
 (`!v:int32. word_xor (word_ushr (word_xor (word_ishr v 31) v) 16) (word_ishr v 31) =
             word_ishr v 16`,
  GEN_TAC THEN BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* Several stores per step sequence. The profile's WASM_MEM_UPDATE_TAC only  *)
(* transports a memory named by a variable (read wmem s = mm), so a second  *)
(* store in one straight line loses the memory fact. CAP_MEM_UPDATE_TAC is  *)
(* the same code accepting any state-free right-hand side (a write chain    *)
(* over mm). CAP_MSTEPS_TAC also passes READ_COMPONENT_COMPOSE and every     *)
(* state-free unconditional bytes32 fact (loads in mm form, and instances   *)
(* of CAP_B32_OTHER) as extra rewrites, so loads after stores reduce.       *)
(* ------------------------------------------------------------------------- *)

let CAP_MEM_UPDATE_TAC (asl,w) =
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

let CAP_STEP_TAC (_,decode_ths) extra sname =
  WASM_BASIC_STEP_TAC decode_ths extra sname THEN
  CAP_MEM_UPDATE_TAC THEN
  ASSUMPTION_STATE_UPDATE_TAC THEN
  MAYCHANGE_STATE_UPDATE_TAC THEN
  DISCH_THEN(fun th ->
    let thl = STATE_UPDATE_NEW_RULE th in
    if thl = [] then ALL_TAC else
    MP_TAC(end_itlist CONJ thl) THEN
    CONV_TAC(LAND_CONV(DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV))) THEN
    STRIP_TAC);;

let is_memfact tm =
  let ws = `:wasmstate` in
  not (can (find_term (fun t -> type_of t = ws)) tm) &&
  can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes32")) tm &&
  not (is_imp (snd(strip_forall tm)));;

let CAP_MSTEPS_TAC execth snums =
  MAP_EVERY (fun s (asl,w) ->
     let mths = filter (fun th -> is_memfact (concl th)) (map snd asl) in
     (CAP_STEP_TAC execth (READ_COMPONENT_COMPOSE :: mths) s THEN
      CAP_DISCARD_OLD_TAC s) (asl,w))
   (statenames "s" snums);;

(* ------------------------------------------------------------------------- *)
(* Address and word arithmetic.                                              *)
(* ------------------------------------------------------------------------- *)

let CAP_VAL_WORD32_EQ = prove
 (`!x y. x = y /\ y < 4294967296 ==> val(word x:int32) = y`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CAP_VAL_WORD32 THEN
  ASM_REWRITE_TAC[]);;

(* prove val(<word_add/word chain>) = y, y < 2^32, from the assumptions *)
let VAL_TAC t = SUBGOAL_THEN t ASSUME_TAC THENL
  [REWRITE_TAC[GSYM WORD_ADD] THEN MATCH_MP_TAC CAP_VAL_WORD32_EQ THEN
   CONJ_TAC THEN ASM_ARITH_TAC; ALL_TAC];;

let CAP_B32_SAME_EQ = prove
 (`!x a (v:int32) (m:int64->byte).
     x = a ==> read (bytes32 (word x)) (write (bytes32 (word a)) v m) = v`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[CAP_B32_SAME]);;

(* an unconditional instance of CAP_B32_OTHER, as an assumption *)
let B32O_TAC a b = SUBGOAL_THEN
  (subst [a,`aa:num`; b,`bb:num`]
     `!(v:int32) (m:int64->byte).
        read (bytes32 (word aa)) (write (bytes32 (word bb)) v m) =
        read (bytes32 (word aa)) m`) ASSUME_TAC THENL
  [MATCH_MP_TAC CAP_B32_OTHER THEN ASM_ARITH_TAC; ALL_TAC];;

(* peel one write off a read: same cell or provably disjoint cell *)
let B32_PEEL_TAC : tactic = fun (asl,w) ->
  let pat = `read (bytes32 (word (x:num))) (write (bytes32 (word (a:num))) (v:int32) (m:int64->byte))` in
  let t = find_term (can (term_match [] pat)) w in
  let x = rand(rand(rand(rator t))) in
  let a = rand(rand(rand(rator(rator(rand t))))) in
  ((SUBGOAL_THEN (mk_eq(x,a)) (fun th -> REWRITE_TAC[MATCH_MP CAP_B32_SAME_EQ th]) THENL
     [ASM_ARITH_TAC; ALL_TAC]) ORELSE
   (MP_TAC(SPECL [x;a] CAP_B32_OTHER) THEN ANTS_TAC THENL
     [ASM_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])])) (asl,w);;

let CAP_AND3 = prove
 (`!x. word_and (word x:int32) (word 3) = word (x MOD 4)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  MP_TAC(ISPECL [`word x:int32`; `2`] VAL_WORD_AND_MASK_WORD) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `x MOD 4 MOD 4294967296 = x MOD 4` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN MP_TAC(SPECL [`x:num`; `4`] MOD_LT_EQ) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `4294967296 = 4 * 1073741824` SUBST1_TAC THENL
   [ARITH_TAC; REWRITE_TAC[MOD_MOD]]);;

let CAP_ANDM4 = prove
 (`!x. word_and (word x:int32) (word 4294967292) = word (4 * (x DIV 4))`,
  GEN_TAC THEN
  SUBGOAL_THEN `!y:int32. word_and y (word 4294967292) = word_sub y (word_and y (word 3))`
    (fun th -> REWRITE_TAC[th]) THENL [GEN_TAC THEN BITBLAST_TAC; ALL_TAC] THEN
  REWRITE_TAC[CAP_AND3] THEN
  SUBGOAL_THEN `word x:int32 = word_add (word (4 * (x DIV 4))) (word (x MOD 4))`
    SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN
    MP_TAC(SPECL [`x:num`; `4`] DIVISION) THEN ARITH_TAC;
    CONV_TAC WORD_RULE]);;

let CAP_DEC = prove
 (`!a b. b < a ==> word_add (word (a - b)) (word 4294967295):int32 =
                   word (a - (b + 1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN
  SUBGOAL_THEN `a - b + 4294967295 = (a - (b + 1)) + 4294967296` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
  REWRITE_TAC[WORD_ADD_0]);;

let CAP_WORD_ADD_EQ = prove
 (`!x y z. x + y = z ==> word_add (word x) (word y):int32 = word z`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD]);;

let CAP_SHL2 = prove
 (`!x. word_shl (word x:int32) 2 = word (4 * x)`,
  GEN_TAC THEN REWRITE_TAC[word_shl; VAL_WORD; DIMINDEX_32] THEN
  REWRITE_TAC[WORD_EQ; DIMINDEX_32; CONG] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MULT_LMOD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* normalize word_add/word_mul/word_shl-of-words to word (expr) and close *)
(* an equation word e1 = word e2 by arithmetic                            *)
let WORD_NUM_EQ_TAC =
  REWRITE_TAC[GSYM WORD_ADD; GSYM WORD_MUL; CAP_SHL2] THEN
  TRY(AP_TERM_TAC THEN ASM_ARITH_TAC);;

let CAP_MSTEPS_X_TAC execth extra snums =
  MAP_EVERY (fun s (asl,w) ->
     let mths = filter (fun th -> is_memfact (concl th)) (map snd asl) in
     (CAP_STEP_TAC execth (READ_COMPONENT_COMPOSE :: (extra @ mths)) s THEN
      CAP_DISCARD_OLD_TAC s) (asl,w))
   (statenames "s" snums);;
