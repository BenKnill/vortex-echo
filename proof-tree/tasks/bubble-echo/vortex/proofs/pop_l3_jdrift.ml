needs "pop_design_defs.ml";;
needs "pop_design_stmts.ml";;
(* ========================================================================= *)
(* Vortex pop, segment L3 (SEG-L3 prover, Claude Opus 5.5, 2026-11-11):      *)
(* the wobble (jiggle) drift pair f23 ve_jig_drift / f24 ve_jig_undrift of  *)
(* vortex_a1.wasm on the exact bytes: VA1_JDRIFT_OK (pop_design_stmts.ml,   *)
(* frozen spec pop_design_r1_jdrift.spec).                                   *)
(*                                                                           *)
(* Body pc map (both functions, 157 B):                                      *)
(*   3 block; 5 i32.const 0; 7 i32.load8_u 16652 (FLAGS = low byte of model *)
(*   word 3); 12 i32.const 1; 14 i32.and; 15 i32.eqz; 16 br_if 0 (flag      *)
(*   clear: to 156, no store); 18 i32.const -8192; 21 local.set 0; 23 loop; *)
(*   25..151 four beads: JQ[l0+8192+4j] (op)= JP[..], j = 0..3 (op = add in *)
(*   f23, sub in f24); 152 br_if 0 on l0 += 16; 154 end; 155 end; 156 end.  *)
(* l0 = -8192 + 16 i (as the num 4294959104 + 16 i), 512 iterations; the    *)
(* i32 address l0 + 1155072 wraps to JQ 1146880 + 16 i, l0 + 1163264 to JP. *)
(* ========================================================================= *)

(* the byte at a is the low byte of the 32-bit word at a *)
let POP_L3_B8_LOW = prove
 (`!(a:int64) (m:int64->byte). read (bytes8 a) m = word_zx (read (bytes32 a) m)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; DIMINDEX_8] THEN
  REWRITE_TAC[GSYM READ_BYTES_BYTES8] THEN
  MP_TAC(ISPECL [`a:int64`; `m:int64->byte`] (INST_TYPE [`:32`,`:N`] VAL_READ_WBYTES)) THEN
  REWRITE_TAC[GSYM BYTES32_WBYTES; DIMINDEX_32] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `4`; `1`; `m:int64->byte`] READ_BYTES_MOD) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN(ACCEPT_TAC o SYM));;

(* load8_u, and 1 = bit 0 of the word *)
let POP_L3_FLAG_AND = prove
 (`!x:int32. word_and (word_zx (word_zx x:byte):int32) (word 1) =
             (if bit 0 x then word 1 else word 0)`,
  GEN_TAC THEN BITBLAST_TAC);;

(* i32 address wrap *)
let POP_L3_WRAP = prove
 (`!a b c. a + b = c + 4294967296 ==> word_add (word a) (word b):int32 = word c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
  REWRITE_TAC[WORD_ADD_0]);;

let pop_l3_inv mc op =
  let t = subst [mc,`MC:byte list`; op,`OP:int32->int32->int32`]
   `\i s. read wcode s = MC /\ read wstatus s = WRunning /\
          read wmemsize s = 4194304 /\ read warity s = 0 /\
          read wlabels s = [0,23,0; 0,156,0] /\
          read (wlocal 0) s = I32 (word (4294959104 + 16 * i)) /\
          read wstack s = (if read wpc s = word 25 then [] else [I32 (word (4294959104 + 16 * i))]) /\
          (!k. k < 2048 ==> read (wmem :> bytes32 (word (1146880 + 4 * k))) s =
                            (if k < 4 * i then OP ((jq:num->int32) k) ((jp:num->int32) k) else jq k)) /\
          (!k. k < 2048 ==> read (wmem :> bytes32 (word (1155072 + 4 * k))) s = jp k)` in
  rhs(concl(TOP_DEPTH_CONV BETA_CONV t));;

let pop_l3_num n = mk_small_numeral n;;
let pop_l3_cell b = mk_binop `(+):num->num->num` (pop_l3_num b) `16 * i`;;
let pop_l3_idx j = if j = 0 then `4 * i` else mk_binop `(+):num->num->num` `4 * i` (pop_l3_num j);;

(* unfold the contract's memory predicates, name the memory, read FLAGS *)
let POP_L3_START_TAC =
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[va1_mdl; va1_w32s]) THEN MEMNAME_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `3` o check (fun th -> can (find_term ((=) `16640`)) (concl th))) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN DISCH_TAC;;

let POP_L3_FLAG_TAC v =
  SUBGOAL_THEN (subst [v,`vv:int32`]
    `word_and (word_zx (read (bytes8 (word 16652)) mm):int32) (word 1) = vv`) ASSUME_TAC THENL
   [ASM_REWRITE_TAC[POP_L3_B8_LOW; POP_L3_FLAG_AND]; ALL_TAC];;

let POP_L3_FSTEPS_TAC exec snums (asl,w) =
  let ex = filter (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes8")) (concl th))
                  (map snd asl) in
  CAP_MSTEPS_X_TAC exec ex snums (asl,w);;

(* flag clear: 8 steps to WDone, memory unchanged *)
let POP_L3_CLEAR_TAC exec =
  POP_L3_START_TAC THEN POP_L3_FLAG_TAC `word 0:int32` THEN
  POP_L3_FSTEPS_TAC exec (1--8) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[va1_w32s; va1_jdrift; WORD_ADD_0; WORD_SUB_0];;

(* flag set, pc 3 -> loop body pc 25 with i = 0 *)
let POP_L3_ENTRY_TAC exec =
  POP_L3_START_TAC THEN POP_L3_FLAG_TAC `word 1:int32` THEN
  POP_L3_FSTEPS_TAC exec (1--10) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LT];;

let POP_L3_BODY_TAC exec =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MAP_EVERY (fun c ->
    SUBGOAL_THEN (subst [pop_l3_num c,`cc:num`; pop_l3_cell (c - 8192),`bb:num`]
       `word_add (word (4294959104 + 16 * i)) (word cc):int32 = word bb`) ASSUME_TAC THENL
     [MATCH_MP_TAC POP_L3_WRAP THEN ARITH_TAC; ALL_TAC])
   [1155072; 1163264; 1155076; 1163268; 1155080; 1163272; 1155084; 1163276] THEN
  MAP_EVERY (fun b -> VAL_TAC (subst [pop_l3_cell b,`bb:num`] `val(word bb:int32) = bb`))
   [1146880; 1155072; 1146884; 1155076; 1146888; 1155080; 1146892; 1155084] THEN
  SUBGOAL_THEN `word_add (word (4294959104 + 16 * i)) (word 16):int32 =
                word (4294959104 + 16 * (i + 1))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  (* the eight loads of iteration i, in the address forms the steps produce *)
  MAP_EVERY (fun (base,f,j) ->
    let a = pop_l3_cell (base + 4 * j) and k = pop_l3_idx j in
    SUBGOAL_THEN (subst [a,`aa:num`; f,`ff:num->int32`; k,`kk:num`]
                   `read (bytes32 (word aa)) mm = (ff:num->int32) kk`) ASSUME_TAC THENL
     [SUBGOAL_THEN (subst [a,`aa:num`; pop_l3_num base,`bb:num`; k,`kk:num`] `aa = bb + 4 * kk`)
        SUBST1_TAC THENL
       [ARITH_TAC;
        SUBGOAL_THEN (subst [k,`kk:num`] `kk < 2048 /\ ~(kk < 4 * i)`) STRIP_ASSUME_TAC THENL
         [ASM_ARITH_TAC; ASM_SIMP_TAC[]]];
      ALL_TAC])
   (allpairs (fun (b,f) j -> (b,f,j)) [1146880,`jq:num->int32`; 1155072,`jp:num->int32`] [0;1;2;3]) THEN
  (* loads after the earlier stores of the same iteration *)
  MAP_EVERY (fun (r,wj) -> B32O_TAC (pop_l3_cell r) (pop_l3_cell (1146880 + 4 * wj)))
   (List.concat (map (fun j -> List.concat (map (fun wj -> if wj < j then
       [(1146880 + 4 * j, wj); (1155072 + 4 * j, wj)] else []) [0;1;2;3])) [0;1;2;3])) THEN
  CAP_MSTEPS_TAC exec (1--52) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MAP_EVERY (fun j -> let c = pop_l3_idx j in
      ASM_CASES_TAC (subst [c,`cc:num`] `k:num = cc`) THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN REPEAT B32_PEEL_TAC THEN
        REWRITE_TAC[ARITH_RULE (subst [c,`cc:num`] `cc < 4 * (i + 1) <=> T`)];
        ALL_TAC]) [0;1;2;3] THEN
    REPEAT B32_PEEL_TAC THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(k < 4 * (i + 1) <=> k < 4 * i)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[]];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN REPEAT B32_PEEL_TAC THEN ASM_SIMP_TAC[]];;

let POP_L3_BACK_TAC exec =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(word (4294959104 + 16 * i):int32 = word 0) <=> F` ASSUME_TAC THENL
   [REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN
    SUBGOAL_THEN `val(word (4294959104 + 16 * i):int32) = 4294959104 + 16 * i` SUBST1_TAC THENL
     [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC;
      REWRITE_TAC[VAL_WORD_0] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  CAP_MSTEPS_TAC exec (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[];;

let POP_L3_EXIT_TAC exec =
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV)) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV WORD_RED_CONV)) THEN
  CAP_MSTEPS_TAC exec (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[va1_w32s; va1_jdrift] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[];;

let POP_L3_TAC mc exec op =
  REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_CASES_TAC `bit 0 ((mdl:num->int32) 3)` THENL
   [ENSURES_WHILE_UP_TAC `512` `25` `152` (pop_l3_inv mc op) THEN
    REPEAT CONJ_TAC THENL
     [ARITH_TAC; POP_L3_ENTRY_TAC exec; POP_L3_BODY_TAC exec;
      POP_L3_BACK_TAC exec; POP_L3_EXIT_TAC exec];
    POP_L3_CLEAR_TAC exec];;

let POP_L3_F23_EXEC = FAST_MK_EXEC_RULE va1_f23_mc 3;;
let POP_L3_F24_EXEC = FAST_MK_EXEC_RULE va1_f24_mc 3;;

let POP_L3_F23_OK = prove
 (lhand(rhs(concl va1_jdrift_ok)),
  POP_L3_TAC `va1_f23_mc` POP_L3_F23_EXEC `word_add:int32->int32->int32`);;

let POP_L3_F24_OK = prove
 (rand(rhs(concl va1_jdrift_ok)),
  POP_L3_TAC `va1_f24_mc` POP_L3_F24_EXEC `word_sub:int32->int32->int32`);;

let VA1_JDRIFT_OK = prove
 (parse_term pop_spec_VA1_JDRIFT_OK,
  REWRITE_TAC[va1_jdrift_ok; POP_L3_F23_OK; POP_L3_F24_OK]);;
