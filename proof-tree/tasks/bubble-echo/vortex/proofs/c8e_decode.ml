(* ========================================================================= *)
(* Vortex chain rung C8e (vortex-chain-20261111-142342 c8e, C8e PROVER, Claude Opus 5.5, 2026-11-15), *)
(* row E2: decode lemmas. From the memory facts of each tick theorem (post state predicates, the byte  *)
(* frame, the va1_vabu tails) to the snapshot: va1_snap m' = va1_fwdt PT sg (kinds 0, 1, 2, 3) and the   *)
(* backward forms (no-pop, un-puncture, un-pop at a pre-image). Pure HOL over c8e_defs.ml; no stepping,   *)
(* no mk_thm / new_axiom.                                                                                *)
(* ========================================================================= *)

(* arithmetic on the numeric assumptions only (no memory reads, no big terms); first without the
   compound (disjunctive) assumptions, which make ARITH split cases *)
let c8e_numasms asl =
  let isrd t = is_const t && (let n = fst(dest_const t) in n = "read" || n = "va1_vabu" || n = "va1_snap") in
  let ok (_,th) = let c = concl th in not (can (find_term isrd) c) && type_of c = bool_ty in
  let ths = map snd (filter ok asl) in
  let compound th = let c = concl th in is_disj c || (is_neg c && is_conj (rand c)) || is_forall c || is_imp c in
  filter (fun th -> not (compound th)) ths, filter compound ths;;
let C8E_ARITH_TAC : tactic = fun (asl,w) ->
  let simple,comps = c8e_numasms asl in
  FIRST [MAP_EVERY MP_TAC simple THEN ARITH_TAC; MAP_EVERY MP_TAC (simple @ comps) THEN ARITH_TAC] (asl,w);;
(* contradiction from the numeric assumptions, one compound assumption at a time *)
let C8E_CONTRA_TAC : tactic = fun (asl,w) ->
  let simple,comps = c8e_numasms asl in
  let try1 hs = MAP_EVERY MP_TAC hs THEN ARITH_TAC in
  (MATCH_MP_TAC(TAUT `F ==> p`) THEN FIRST (try1 simple :: map (fun h -> try1 (h :: simple)) comps)) (asl,w);;

let C8E_PUT_AP = prove
 (`!b n (f:num->int32) sg w. va1_put b n f sg w = if b <= w /\ w < b + n then f (w - b) else sg w`,
  REWRITE_TAC[va1_put]);;

let C8E_SNAP_EQ = prove
 (`!(m':int64->byte) (G:num->int32).
     (!w. w < 487424 ==> read (bytes32 (word (16384 + 4 * w))) m' = G w) /\
     (!w. ~(w < 487424) ==> G w = word 0) ==> va1_snap m' = G`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[va1_snap; FUN_EQ_THM] THEN X_GEN_TAC `w:num` THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

let C8E_PEEL = prove
 (`!(m':int64->byte) (P:num->bool) b n (f:num->int32) (G:num->int32).
     (!k. k < n ==> read (bytes32 (word (16384 + 4 * (b + k)))) m' = f k) /\
     (!w. P w /\ ~(b <= w /\ w < b + n) ==> read (bytes32 (word (16384 + 4 * w))) m' = G w)
     ==> (!w. P w ==> read (bytes32 (word (16384 + 4 * w))) m' = va1_put b n f G w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[C8E_PUT_AP] THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `w - b:num` th) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    SUBGOAL_THEN `b + (w - b) = w:num` SUBST1_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let C8E_VABU_KEEP = prove
 (`!N (uw:(num->int32)#(num->int32)) (m:int64->byte) m' w.
    va1_vabu N uw m /\ va1_vabu N uw m' /\
    ((274432 + 3 * N <= w /\ w < 276480) \/ (276480 + 3 * N <= w /\ w < 278528))
    ==> read (bytes32 (word (16384 + 4 * w))) m' = read (bytes32 (word (16384 + 4 * w))) m`,
  REWRITE_TAC[va1_vabu] THEN REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN `16384 + 4 * w = 1114112 + 4 * (w - 274432)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `3 * N <= w - 274432 /\ w - 274432 < 2048` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[]];
    SUBGOAL_THEN `16384 + 4 * w = 1122304 + 4 * (w - 276480)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `3 * N <= w - 276480 /\ w - 276480 < 2048` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[]]]);;

(* region goal: !k. k < n ==> read (bytes32 (word (16384 + 4 * (b + k)))) m' = f k *)
let C8E_REG_TAC : tactic =
  REWRITE_TAC[LEFT_ADD_DISTRIB; ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  FIRST [FIRST_ASSUM MATCH_ACCEPT_TAC;
         REWRITE_TAC[ARITH_RULE `k < 1 <=> k = 0`] THEN GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
         CONV_TAC NUM_REDUCE_CONV THEN BETA_TAC THEN ASM_REWRITE_TAC[]];;

let C8E_PEELS_TAC (rt:tactic) : tactic =
  REPEAT (MATCH_MP_TAC C8E_PEEL THEN CONJ_TAC THENL [rt; BETA_TAC]);;

(* bottom: !w. conds ==> read (bytes32 (word (16384 + 4 * w))) m' = sg w, sg abbreviating va1_snap m *)

let C8E_BOT_TAC (N:term) : tactic =
  GEN_TAC THEN STRIP_TAC THEN EXPAND_TAC "sg" THEN REWRITE_TAC[va1_snap] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC (subst [N,`N:num`] `(274432 + 3 * N <= w /\ w < 276480) \/ (276480 + 3 * N <= w /\ w < 278528)`) THENL
   [MATCH_MP_TAC C8E_VABU_KEEP THEN MAP_EVERY EXISTS_TAC [N; `uw:(num->int32)#(num->int32)`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC C4_KEEP_W32 THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN C8E_ARITH_TAC];;

let C8E_OUT_TAC : tactic =
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[C8E_PUT_AP] THEN
  REPEAT(COND_CASES_TAC THENL [C8E_CONTRA_TAC; ALL_TAC]) THEN
  EXPAND_TAC "sg" THEN REWRITE_TAC[va1_snap] THEN ASM_REWRITE_TAC[];;

(* goal read (bytes32 (word A)) m' = R; use the assumption !j. j < n ==> read (bytes32 (word (b + 4 * j))) m' = f j at j *)
let C8E_USE_TAC (b:term) (j:term) : tactic = fun (asl,w) ->
  let a = rand(rand(rand(rator(lhs w)))) in
  let bj = mk_binop `(+):num->num->num` b (mk_binop `( * ):num->num->num` `4` j) in
  (SUBGOAL_THEN (mk_eq(a, bj)) SUBST1_TAC THENL [C8E_ARITH_TAC; ALL_TAC] THEN
   FIRST_ASSUM(fun th -> let th' = SPEC j th in
     let c = concl th' in
     if rand(rand(rand(rator(lhs(rand c))))) = bj then MP_TAC th' else failwith "C8E_USE_TAC") THEN
   ANTS_TAC THENL [C8E_ARITH_TAC; DISCH_THEN SUBST1_TAC]) (asl,w);;


let VA1_DEC_NP_FWD = prove
 (`!(PT:(num->int32)->num->int32) (m:int64->byte) (m':int64->byte) (uw:(num->int32)#(num->int32)).
     1 <= val (va1_snap m 65) /\ val (va1_snap m 65) <= 640 /\ va1_kind (va1_snap m) = 0 /\
     va1_tick (word_add (va1_snap m 2) (word 1)) m' /\
     va1_vab (val (va1_snap m 65)) (ve_fredkin_fwdn (\i. ve_vk (\k. va1_snap m (64 + k))) 16 (va1_sg_x (va1_snap m))) m' /\
     va1_vabu (val (va1_snap m 65)) uw m /\ va1_vabu (val (va1_snap m 65)) uw m' /\ va1_np_frame m m'
     ==> va1_snap m' = va1_fwdt PT (va1_snap m)`,
  REPEAT GEN_TAC THEN ABBREV_TAC `sg = va1_snap m` THEN
  REWRITE_TAC[va1_tick; va1_vab; va1_np_frame] THEN STRIP_TAC THEN
  REWRITE_TAC[va1_fwdt; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[va1_put_x] THEN
  MATCH_MP_TAC C8E_SNAP_EQ THEN CONJ_TAC THENL
   [C8E_PEELS_TAC C8E_REG_TAC THEN C8E_BOT_TAC `val ((sg:num->int32) 65)`;
    C8E_OUT_TAC]);;

let VA1_DEC_NP_BWD = prove
 (`!(m:int64->byte) (m':int64->byte) (uw:(num->int32)#(num->int32)).
     1 <= val (va1_snap m 65) /\ val (va1_snap m 65) <= 640 /\
     ~(va1_snap m 2 = word 0) /\ va1_snap m 3 = word 4294967295 /\
     va1_tick (word_sub (va1_snap m 2) (word 1)) m' /\
     va1_vab (val (va1_snap m 65)) (ve_fredkin_bwdn (\i. ve_vk (\k. va1_snap m (64 + k))) 16 (va1_sg_x (va1_snap m))) m' /\
     va1_vabu (val (va1_snap m 65)) uw m /\ va1_vabu (val (va1_snap m 65)) uw m' /\ va1_np_frame m m'
     ==> va1_snap m' = va1_bwd (va1_snap m)`,
  REPEAT GEN_TAC THEN ABBREV_TAC `sg = va1_snap m` THEN
  REWRITE_TAC[va1_tick; va1_vab; va1_np_frame] THEN STRIP_TAC THEN
  REWRITE_TAC[va1_bwd; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[va1_put_x] THEN
  MATCH_MP_TAC C8E_SNAP_EQ THEN CONJ_TAC THENL
   [C8E_PEELS_TAC C8E_REG_TAC THEN C8E_BOT_TAC `val ((sg:num->int32) 65)`;
    C8E_OUT_TAC]);;

(* kind 3: tick_forward returns 0 and the memory is unchanged *)
let VA1_DEC_END = prove
 (`!(PT:(num->int32)->num->int32) (m:int64->byte). va1_kind (va1_snap m) = 3 ==> va1_snap m = va1_fwdt PT (va1_snap m)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[va1_fwdt; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[ARITH_EQ]);;

(* reading the tick-theorem predicates off a snapshot *)
let C8E_SNAP_W = prove
 (`!(m:int64->byte) w. w < 487424 ==> read (bytes32 (word (16384 + 4 * w))) m = va1_snap m w`,
  SIMP_TAC[va1_snap]);;

let C8E_SNAP_W32S = prove
 (`!(m:int64->byte) b n. b + n <= 487424 ==> va1_w32s (16384 + 4 * b) n (\k. va1_snap m (b + k)) m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[va1_w32s] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `(16384 + 4 * b) + 4 * k = 16384 + 4 * (b + k)`] THEN
  MATCH_MP_TAC C8E_SNAP_W THEN ASM_ARITH_TAC);;

let C8E_SNAPRD_TAC : tactic = fun (asl,w) ->
  let l,r = dest_eq w in
  let ww = rand r and a = rand(rand(rand(rator l))) in
  (SUBGOAL_THEN (mk_eq(a, mk_binop `(+):num->num->num` `16384` (mk_binop `( * ):num->num->num` `4` ww))) SUBST1_TAC
   THENL [ARITH_TAC; MATCH_MP_TAC C8E_SNAP_W THEN ASM_ARITH_TAC]) (asl,w);;

let VA1_SNAP_ST = prove
 (`!(m:int64->byte). val (va1_snap m 65) <= 640 ==>
     va1_st (va1_snap m 2) (va1_snap m 3) (va1_snap m 32) (\k. va1_snap m (64 + k)) (val (va1_snap m 65))
            (va1_sg_x (va1_snap m)) (\k. va1_snap m (6 + k)) (\k. va1_snap m (12288 + k)) (va1_sg_ps (va1_snap m)) m /\
     va1_vabu (val (va1_snap m 65)) (va1_sg_x (va1_snap m)) m /\
     read (bytes32 (word 16404)) m = va1_snap m 5 /\
     read (bytes32 (word 16516)) m = va1_snap m 33 /\ read (bytes32 (word 16520)) m = va1_snap m 34 /\
     read (bytes32 (word 16524)) m = va1_snap m 35`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[va1_st; va1_tick; va1_pop; va1_mdl; va1_vab; va1_vabu; va1_bs; va1_w32s; va1_sg_x; va1_sg_ps; FST; SND] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN C8E_SNAPRD_TAC);;

let C8E_ST_ALT = prove
 (`!t p ap mdl N (x:(num->int32)#(num->int32)) hp tbl
    (ps:(num->int32)#(num->int32)#(num->int32)#(num->int32)#((num->int32)#(num->int32)#(num->int32)#int32)) (m:int64->byte).
     va1_st t p ap mdl N x hp tbl ps m <=>
     va1_tick t m /\ va1_pop p ap m /\ va1_mdl mdl m /\ va1_vab N x m /\
     va1_w32s 16408 26 hp m /\ va1_w32s 65536 262144 tbl m /\
     va1_w32s 1130496 2048 (FST ps) m /\ va1_w32s 1138688 2048 (FST (SND ps)) m /\
     va1_w32s 1146880 2048 (FST (SND (SND ps))) m /\ va1_w32s 1155072 2048 (FST (SND (SND (SND ps)))) m /\
     va1_bs (SND (SND (SND (SND ps)))) m`,
  REWRITE_TAC[FORALL_PAIR_THM; va1_st; FST; SND]);;

let C8E_BS_ALT = prove
 (`!(bs:(num->int32)#(num->int32)#(num->int32)#int32) (m:int64->byte).
     va1_bs bs m <=>
     va1_w32s 1179648 196608 (FST bs) m /\ va1_w32s 1163264 2048 (FST (SND bs)) m /\
     va1_w32s 1171456 2048 (FST (SND (SND bs))) m /\ read (bytes32 (word 16400)) m = SND (SND (SND bs))`,
  REWRITE_TAC[FORALL_PAIR_THM; va1_bs; FST; SND]);;

let VA1_DEC_POP_FWD = prove
 (`!(PT:(num->int32)->num->int32) (m:int64->byte) (m':int64->byte) (sg:num->int32) (ap:int32) (uw:(num->int32)#(num->int32)).
     va1_snap m = sg /\ 1 <= val (sg 65) /\ val (sg 65) <= 640 /\ va1_kind sg = 1 /\
     va1_st (word_add (sg 2) (word 1)) (sg 3) ap (\k. sg (64 + k)) (val (sg 65))
            (ve_fredkin_fwd (ve_vk (\k. sg (64 + k))) (va1_sg_x sg)) (\k. sg (6 + k)) (\k. sg (12288 + k))
            (va1_pop_fwd va1_ck va1_jigk
               (va1_pop_births (\k. sg (64 + k)) (\k. sg (6 + k)) (\k. sg (12288 + k)) (sg 2) (sg 3) (va1_sg_ps sg))
               (\k. sg (64 + k)) (\k. sg (6 + k)) (\k. sg (12288 + k)) (sg 2) (sg 3) (va1_sg_ps sg)) m' /\
     va1_vabu (val (sg 65)) uw m /\ va1_vabu (val (sg 65)) uw m' /\ va1_pop_frame m m'
     ==> va1_snap m' = va1_fwdt PT sg`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C8E_ST_ALT; va1_tick; va1_pop; va1_mdl; va1_vab; C8E_BS_ALT; va1_w32s; va1_pop_frame] THEN STRIP_TAC THEN
  REWRITE_TAC[va1_fwdt; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[va1_put_x; va1_put_ps; ARITH_EQ] THEN
  MATCH_MP_TAC C8E_SNAP_EQ THEN CONJ_TAC THENL
   [C8E_PEELS_TAC C8E_REG_TAC THEN C8E_BOT_TAC `val ((sg:num->int32) 65)`;
    C8E_OUT_TAC]);;

let C8E_ZPSEED_B = prove
 (`va1_zpseed_b = va1_zpseed`,
  REWRITE_TAC[FUN_EQ_THM; va1_zpseed_b; va1_zpseed; va1_zpx0; va1_zpx1; LET_DEF; LET_END_DEF]);;

let C8E_RBINIT_LOC = prove
 (`!(tbl:num->int32) (tb:num->int32) k.
     tbl (128 * k) = tb (128 * k) /\ tbl (128 * k + 1) = tb (128 * k + 1) ==> va1_rbinit tbl k = va1_rbinit_b tb k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[va1_rbinit_b; va1_rbinit; va1_rbv; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[WORD_ADD_SYM]);;


let C8E_RBB_LOC = prove
 (`!(tbl:num->int32) (tb:num->int32) k.
     tbl (128 * k) = tb (128 * k) /\ tbl (128 * k + 1) = tb (128 * k + 1) ==> va1_rbinit_b tbl k = va1_rbinit_b tb k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[va1_rbinit_b; LET_DEF; LET_END_DEF] THEN ASM_REWRITE_TAC[]);;

let C8E_K2_FACTS_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_tf_mid; va1_c6a_mem; va1_c6a_frame; va1_tick; va1_vab; va1_w32s] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!a. a < 4194304 /\ ~(16288 <= a /\ a < 16384) /\ ~(16396 <= a /\ a < 16404) /\
                    ~(16408 <= a /\ a < 16504) /\ ~(65536 <= a /\ a < 1114112) /\ ~(1130496 <= a /\ a < 1966080) /\
                    ~(16392 <= a /\ a < 16396) /\ ~(1114112 <= a /\ a < 1130496) /\ ~(1966080 <= a /\ a < 2039808)
                    ==> read (bytes8 (word a)) m' = read (bytes8 (word a)) m` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS `read (bytes8 (word a)) (m1:int64->byte)` THEN CONJ_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `read (bytes32 (word 16392)) m' = word_add (sg 2) (word 1)` ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS `read (bytes32 (word 16392)) (m1:int64->byte)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC C4_KEEP_W32 THEN REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN C8E_ARITH_TAC;
      ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `(!j. j < 3 * val ((sg:num->int32) 65) ==> read (bytes32 (word (1114112 + 4 * j))) m' =
                     FST (ve_fredkin_fwdn (\i. ve_vk (\k. sg (64 + k))) 16 (va1_sg_x sg)) j) /\
                (!j. j < 3 * val ((sg:num->int32) 65) ==> read (bytes32 (word (1122304 + 4 * j))) m' =
                     SND (ve_fredkin_fwdn (\i. ve_vk (\k. sg (64 + k))) 16 (va1_sg_x sg)) j)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THENL
     [TRANS_TAC EQ_TRANS `read (bytes32 (word (1114112 + 4 * j))) (m1:int64->byte)`;
      TRANS_TAC EQ_TRANS `read (bytes32 (word (1122304 + 4 * j))) (m1:int64->byte)`] THEN
    (CONJ_TAC THENL [MATCH_MP_TAC C4_KEEP_W32 THEN REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN C8E_ARITH_TAC;
                     ASM_SIMP_TAC[]]); ALL_TAC] THEN
  SUBGOAL_THEN `!j. j < 262144 ==> (tbl:num->int32) j = PT (sg:num->int32) j` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_MESON_TAC[]; ALL_TAC];;

let C8E_BIG_TAC : tactic =
  COND_CASES_TAC THENL
   [C8E_USE_TAC `1130496` `k:num` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REFL_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [C8E_USE_TAC `1138688` `k - 2048` THEN MATCH_MP_TAC C8E_RBB_LOC THEN CONJ_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN C8E_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [ASM_CASES_TAC `k < 6144` THENL
     [C8E_USE_TAC `1146880` `k - 4096`;
      ASM_CASES_TAC `k < 8192` THENL [C8E_USE_TAC `1155072` `k - 6144`; C8E_USE_TAC `1163264` `k - 8192`]] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REFL_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [C8E_USE_TAC `1171456` `k - 10240` THEN REWRITE_TAC[C8E_ZPSEED_B]; ALL_TAC] THEN
  C8E_USE_TAC `1179648` `k - 12288` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REFL_TAC;;

let C8E_HP_TAC : tactic =
  REWRITE_TAC[LEFT_ADD_DISTRIB; ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST1_TAC (DISJ_CASES_THEN2 SUBST1_TAC SUBST1_TAC) o
      MATCH_MP (ARITH_RULE `k < 3 ==> k = 0 \/ k = 1 \/ k = 2`)) THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    C8E_USE_TAC `16420` `k - 3` THEN REFL_TAC];;
let C8E_P3_TAC : tactic =
  REWRITE_TAC[LEFT_ADD_DISTRIB; ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN X_GEN_TAC `k:num` THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC SUBST1_TAC o MATCH_MP (ARITH_RULE `k < 2 ==> k = 0 \/ k = 1`)) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];;

let VA1_DEC_PUNCT_FWD = prove
 (`!(PT:(num->int32)->num->int32) (m:int64->byte) (m1:int64->byte) (m':int64->byte) (sg:num->int32) (uw:(num->int32)#(num->int32)).
     va1_snap m = sg /\ 1 <= val (sg 65) /\ val (sg 65) <= 640 /\ va1_kind sg = 2 /\
     va1_tf_mid (val (sg 65)) (\k. sg (64 + k)) (sg 2) (va1_sg_x sg) m m1 /\
     va1_c6a_mem (\k. sg (64 + k)) m1 m' /\
     read (bytes32 (word 16408)) m' = sg 33 /\ read (bytes32 (word 16412)) m' = sg 34 /\
     read (bytes32 (word 16416)) m' = sg 35 /\
     va1_w32s 65536 262144 (PT sg) m' /\ va1_w32s 16420 21 (va1_phdr (sg 33) (sg 34) (sg 35)) m' /\
     va1_vabu (val (sg 65)) uw m /\ va1_vabu (val (sg 65)) uw m'
     ==> va1_snap m' = va1_fwdt PT sg`,
  C8E_K2_FACTS_TAC THEN
  REWRITE_TAC[va1_fwdt; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[va1_put_x; ARITH_EQ] THEN MATCH_MP_TAC C8E_SNAP_EQ THEN CONJ_TAC THENL
   [MATCH_MP_TAC C8E_PEEL THEN CONJ_TAC THENL
     [REWRITE_TAC[LEFT_ADD_DISTRIB; ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN C8E_BIG_TAC;
      BETA_TAC] THEN
    MATCH_MP_TAC C8E_PEEL THEN CONJ_TAC THENL [C8E_REG_TAC; BETA_TAC] THEN
    MATCH_MP_TAC C8E_PEEL THEN CONJ_TAC THENL [C8E_HP_TAC; BETA_TAC] THEN
    MATCH_MP_TAC C8E_PEEL THEN CONJ_TAC THENL [C8E_P3_TAC; BETA_TAC] THEN
    C8E_PEELS_TAC C8E_REG_TAC THEN C8E_BOT_TAC `val ((sg:num->int32) 65)`;
    C8E_OUT_TAC]);;

let C8E_Z7_TAC : tactic =
  REWRITE_TAC[LEFT_ADD_DISTRIB; ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_CASES_TAC `k < 2048` THENL [C8E_USE_TAC `1130496` `k:num`; ALL_TAC] THEN
  TRY(ASM_CASES_TAC `k < 4096` THENL [C8E_USE_TAC `1138688` `k - 2048`; ALL_TAC]) THEN
  TRY(ASM_CASES_TAC `k < 6144` THENL [C8E_USE_TAC `1146880` `k - 4096`; ALL_TAC]) THEN
  TRY(ASM_CASES_TAC `k < 8192` THENL [C8E_USE_TAC `1155072` `k - 6144`; ALL_TAC]) THEN
  TRY(ASM_CASES_TAC `k < 10240` THENL [C8E_USE_TAC `1163264` `k - 8192`; ALL_TAC]) THEN
  TRY(ASM_CASES_TAC `k < 12288` THENL [C8E_USE_TAC `1171456` `k - 10240`; C8E_USE_TAC `1179648` `k - 12288`]) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REFL_TAC;;
let C8E_U27_TAC : tactic =
  REWRITE_TAC[LEFT_ADD_DISTRIB; ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_CASES_TAC `k = 0` THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `k = 1` THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `k = 2` THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN C8E_USE_TAC `16408` `k - 3` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  SUBGOAL_THEN `k - 3 < 24` (fun th -> REWRITE_TAC[th]) THEN C8E_ARITH_TAC;;

let VA1_DEC_UNPUNCT = prove
 (`!(m:int64->byte) (m':int64->byte) (sg:num->int32) (ap:int32) (uw:(num->int32)#(num->int32)).
     va1_snap m = sg /\ 1 <= val (sg 65) /\ val (sg 65) <= 640 /\
     ~(sg 2 = word 0) /\ ~(sg 3 = word 4294967295) /\ sg 2 = sg 3 /\
     va1_st (word_sub (sg 3) (word 1)) (word 4294967295) ap (\k. sg (64 + k)) (val (sg 65))
            (ve_fredkin_bwdn (\i. ve_vk (\k. sg (64 + k))) 16 (va1_sg_x sg))
            (\k. if k < 24 then word 0 else sg (6 + k)) (\k. word 0)
            ((\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),word 0) m' /\
     read (bytes32 (word 16404)) m' =
       word_add (sg 5) (va1_bad (\k. sg (64 + k)) (\k. sg (12288 + k))
                          ((\k. sg (278528 + k)),(\k. sg (280576 + k)),(\k. sg (282624 + k)),(\k. sg (284672 + k)),
                           (\k. sg (286720 + k)),(\k. sg (288768 + k)),sg 4)) /\
     va1_vabu (val (sg 65)) uw m /\ va1_vabu (val (sg 65)) uw m' /\ va1_unp_frame m m'
     ==> va1_snap m' = va1_bwd sg`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C8E_ST_ALT; va1_tick; va1_pop; va1_mdl; va1_vab; C8E_BS_ALT; va1_w32s; va1_unp_frame; FST; SND] THEN
  STRIP_TAC THEN
  REWRITE_TAC[va1_bwd; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[va1_put_x; va1_sg_ps; FST; SND] THEN MATCH_MP_TAC C8E_SNAP_EQ  THEN CONJ_TAC THENL
   [MATCH_MP_TAC C8E_PEEL THEN CONJ_TAC THENL [C8E_Z7_TAC; BETA_TAC] THEN
    MATCH_MP_TAC C8E_PEEL THEN CONJ_TAC THENL [C8E_REG_TAC; BETA_TAC] THEN
    MATCH_MP_TAC C8E_PEEL THEN CONJ_TAC THENL [C8E_U27_TAC; BETA_TAC] THEN
    C8E_PEELS_TAC C8E_REG_TAC THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `w = 30 \/ w = 31` THENL
   [C8E_USE_TAC `16408` `w - 6` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    SUBGOAL_THEN `~(w - 6 < 24) /\ 6 + (w - 6) = w` (fun th -> REWRITE_TAC[th]) THEN C8E_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "sg" THEN REWRITE_TAC[va1_snap] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(274432 + 3 * val ((sg:num->int32) 65) <= w /\ w < 276480) \/ (276480 + 3 * val (sg 65) <= w /\ w < 278528)` THENL
   [MATCH_MP_TAC C8E_VABU_KEEP THEN MAP_EVERY EXISTS_TAC [`val ((sg:num->int32) 65)`; `uw:(num->int32)#(num->int32)`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC C4_KEEP_W32 THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN C8E_ARITH_TAC];
    C8E_OUT_TAC]);;

let C8E_FWDT_EVAL_TAC : tactic =
  REWRITE_TAC[va1_fwdt; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[va1_put_ps; va1_put_x; C8E_PUT_AP; ARITH_EQ] THEN
  REPEAT(COND_CASES_TAC THENL [C8E_CONTRA_TAC; ALL_TAC]) THEN REFL_TAC;;

(* one region case: if cond then use the w32s fact at base, index w - c *)
let C8E_RCASE_TAC (cond:term) (base:term) (c:term) : tactic =
  ASM_CASES_TAC cond THENL
   [C8E_USE_TAC base (mk_binop `(-):num->num->num` `w:num` c) THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    TRY AP_TERM_TAC THEN C8E_ARITH_TAC; ALL_TAC];;
let C8E_WCASE_TAC (n:int) : tactic =
  ASM_CASES_TAC (mk_eq(`w:num`, mk_small_numeral n)) THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC];;


let VA1_DEC_POP_BWD = prove
 (`!(PT:(num->int32)->num->int32) (m:int64->byte) (m':int64->byte) (sg0:num->int32) (uw:(num->int32)#(num->int32)).
   va1_snap m = va1_fwdt PT sg0 /\ 1 <= val (sg0 65) /\ val (sg0 65) <= 640 /\ va1_kind sg0 = 1 /\
   va1_st (sg0 2) (sg0 3) (sg0 32) (\k. sg0 (64 + k)) (val (sg0 65)) (va1_sg_x sg0) (\k. sg0 (6 + k))
          (\k. sg0 (12288 + k)) (va1_sg_ps sg0) m' /\
   va1_vabu (val (sg0 65)) uw m /\ va1_vabu (val (sg0 65)) uw m' /\ va1_pop_frame m m'
   ==> va1_snap m' = sg0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C8E_ST_ALT; va1_tick; va1_pop; va1_mdl; va1_vab; C8E_BS_ALT; va1_w32s; va1_pop_frame; va1_sg_x; va1_sg_ps; FST; SND] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  SUBGOAL_THEN `!w. ~(278528 <= w /\ w < 487424) /\ ~(274432 <= w /\ w < 274432 + 3 * val ((sg0:num->int32) 65)) /\
                    ~(276480 <= w /\ w < 276480 + 3 * val (sg0 65)) /\ ~(w = 2) /\ ~(w = 4)
                    ==> va1_snap m w = sg0 w` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN C8E_FWDT_EVAL_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!w. w < 487424 /\ ~(278528 <= w /\ w < 487424) /\ ~(274432 <= w /\ w < 274432 + 3 * val ((sg0:num->int32) 65)) /\
                    ~(276480 <= w /\ w < 276480 + 3 * val (sg0 65)) /\ ~(w = 2) /\ ~(w = 4)
                    ==> read (bytes32 (word (16384 + 4 * w))) m = sg0 w` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[C8E_SNAP_W]; ALL_TAC] THEN
  MATCH_MP_TAC C8E_SNAP_EQ THEN CONJ_TAC THENL
   [X_GEN_TAC `w:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `w < 274432` THENL
     [C8E_WCASE_TAC 2 THEN C8E_WCASE_TAC 3 THEN C8E_WCASE_TAC 4 THEN C8E_WCASE_TAC 32 THEN
      C8E_RCASE_TAC `6 <= w /\ w < 32` `16408` `6` THEN
      C8E_RCASE_TAC `64 <= w /\ w < 1088` `16640` `64` THEN
      C8E_RCASE_TAC `12288 <= w /\ w < 274432` `65536` `12288` THEN
      (TRANS_TAC EQ_TRANS `read (bytes32 (word (16384 + 4 * w))) (m:int64->byte)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC C4_KEEP_W32 THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN C8E_ARITH_TAC;
        FIRST_ASSUM MATCH_MP_TAC THEN C8E_ARITH_TAC]);
      ALL_TAC] THEN
    ASM_CASES_TAC `w < 278528` THENL
     [ASM_CASES_TAC `w < 276480` THENL
       [ASM_CASES_TAC `w < 274432 + 3 * val ((sg0:num->int32) 65)` THENL
         [C8E_USE_TAC `1114112` `w - 274432` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN AP_TERM_TAC THEN C8E_ARITH_TAC; ALL_TAC];
        ASM_CASES_TAC `w < 276480 + 3 * val ((sg0:num->int32) 65)` THENL
         [C8E_USE_TAC `1122304` `w - 276480` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN AP_TERM_TAC THEN C8E_ARITH_TAC; ALL_TAC]] THEN
      (TRANS_TAC EQ_TRANS `read (bytes32 (word (16384 + 4 * w))) (m:int64->byte)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC C8E_VABU_KEEP THEN MAP_EVERY EXISTS_TAC [`val ((sg0:num->int32) 65)`; `uw:(num->int32)#(num->int32)`] THEN
        ASM_REWRITE_TAC[] THEN C8E_ARITH_TAC;
        FIRST_ASSUM MATCH_MP_TAC THEN C8E_ARITH_TAC]);
      ALL_TAC] THEN
    MAP_EVERY (fun (b,base) ->
      let bt = mk_small_numeral b in
      ASM_CASES_TAC (mk_binop `(<):num->num->bool` `w:num` bt) THENL
       [C8E_USE_TAC base (mk_binop `(-):num->num->num` `w:num` (mk_small_numeral (b - 2048))) THEN
        CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN AP_TERM_TAC THEN C8E_ARITH_TAC; ALL_TAC])
      [280576,`1130496`; 282624,`1138688`; 284672,`1146880`; 286720,`1155072`; 288768,`1163264`; 290816,`1171456`] THEN
    C8E_USE_TAC `1179648` `w - 290816` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN AP_TERM_TAC THEN C8E_ARITH_TAC;
    X_GEN_TAC `w:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o C AP_THM `w:num` o check (fun th -> is_eq(concl th) && lhs(concl th) = `va1_snap (m:int64->byte)`)) THEN
    REWRITE_TAC[va1_snap] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN C8E_FWDT_EVAL_TAC]);;

(* the births of the A9 post are va1_pop_births *)
let VA1_POP_BIRTHS_EQ = prove
 (`!mdl hp tbl t p (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32).
     va1_pop_births mdl hp tbl t p (ra,rb,jq,jp,di,zq,zp,nd) =
     va1_born mdl hp tbl t (FST (ve_fredkin_fwd (va1_rimd tbl) (ra,rb))) (SND (ve_fredkin_fwd (va1_rimd tbl) (ra,rb)))
       (FST (ve_kd_fwdn (\i. va1_ck mdl hp tbl t p i (SND (ve_fredkin_fwd (va1_rimd tbl) (ra,rb)))) (\i. va1_cdrift (SND (ve_fredkin_fwd (va1_rimd tbl) (ra,rb)))) 4 (zq,zp)))
       (SND (ve_kd_fwdn (\i. va1_ck mdl hp tbl t p i (SND (ve_fredkin_fwd (va1_rimd tbl) (ra,rb)))) (\i. va1_cdrift (SND (ve_fredkin_fwd (va1_rimd tbl) (ra,rb)))) 4 (zq,zp))) nd`,
  REWRITE_TAC[va1_pop_births; LET_DEF; LET_END_DEF; FST; SND]);;
