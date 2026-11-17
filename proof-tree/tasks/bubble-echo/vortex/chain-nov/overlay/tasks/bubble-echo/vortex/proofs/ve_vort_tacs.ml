(* ========================================================================= *)
(* Vortex Echo v1: tactics for the Fredkin loop of the vortex export pair    *)
(* ve_vort_apply / ve_vort_unapply of vortex/core/ve_core.wasm (sha256       *)
(* 72fe0ba2), from pc 1305 to the end (adapted from capillary drift_tacs.ml).*)
(* Both bodies, from 1305: block; n := N (model word 1, byte 16644), exit if *)
(* 0; 3n := 3 min(N, 640); local4 := 3n & 4094 (2q), local2 := 3n & 1 (r);  *)
(* local3 := PA, local14 := PB, local0 := VD (1974272); loop at 1370, body   *)
(* 1372 (two elements: t := A[m]; A[m] := OP; B[m] := t), br_if at 1473 on   *)
(* local4 -= 2; 1475 end; 1476..1479 exit if r = 0; 1481..1508 the odd last *)
(* element; 1511 end block; 1512 end. Apply: A = VB (PA 1122304), B = VA    *)
(* (PB 1114112), A[m] := VD[m] + VA[m]. Unapply: A = VA, B = VB,             *)
(* A[m] := VB[m] - VD[m].                                                     *)
(* ========================================================================= *)

let VE_AND1 = prove
 (`!x. word_and (word x:int32) (word 1) = word (x MOD 2)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  MP_TAC(ISPECL [`word x:int32`; `1`] VAL_WORD_AND_MASK_WORD) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `x MOD 2 MOD 4294967296 = x MOD 2` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN MP_TAC(SPECL [`x:num`; `2`] MOD_LT_EQ) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `4294967296 = 2 * 2147483648` SUBST1_TAC THENL
   [ARITH_TAC; REWRITE_TAC[MOD_MOD]]);;

let VE_AND4094_BB = prove
 (`!y:int32. word_and y (word 4094) = word_sub (word_and y (word 4095)) (word_and y (word 1))`,
  GEN_TAC THEN BITBLAST_TAC);;

let VE_AND4094 = prove
 (`!x. x < 4096 ==> word_and (word x:int32) (word 4094) = word (2 * (x DIV 2))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VE_AND4094_BB; VE_AND1] THEN
  SUBGOAL_THEN `word_and (word x:int32) (word 4095) = word x` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ] THEN MP_TAC(ISPECL [`word x:int32`; `12`] VAL_WORD_AND_MASK_WORD) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `val(word x:int32) = x` SUBST1_TAC THENL
     [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; ASM_SIMP_TAC[MOD_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `word x:int32 = word_add (word (2 * (x DIV 2))) (word (x MOD 2))` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN MP_TAC(SPECL [`x:num`; `2`] DIVISION) THEN ARITH_TAC;
    CONV_TAC WORD_RULE]);;

let VE_DEC2 = prove
 (`!q i. i < q ==> word_add (word (2 * q - 2 * i)) (word 4294967294):int32 = word (2 * q - 2 * (i + 1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN
  SUBGOAL_THEN `(2 * q - 2 * i) + 4294967294 = (2 * q - 2 * (i + 1)) + 4294967296` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
  REWRITE_TAC[WORD_ADD_0]);;

let vort_inv mc pa pb na nb ai bi =
  let t = subst [mc,`MC:byte list`; pa,`PA:num`; pb,`PB:num`; na,`NA:num->int32`; nb,`NB:num->int32`;
                 ai,`AI:num->int32`; bi,`BI:num->int32`]
   `\i s. read wcode s = MC /\ read wstatus s = WRunning /\
          read wmemsize s = 4194304 /\ read warity s = 0 /\
          read wlabels s = [0,1370,0; 0,1512,0] /\
          read (wlocal 3) s = I32 (word (PA + 8 * i)) /\
          read (wlocal 14) s = I32 (word (PB + 8 * i)) /\
          read (wlocal 0) s = I32 (word (1974272 + 8 * i)) /\
          read (wlocal 4) s = I32 (word (2 * q - 2 * i)) /\
          read (wlocal 2) s = I32 (word r) /\
          read wstack s = (if read wpc s = word 1372 then [] else [I32 (word (2 * q - 2 * i))]) /\
          (!m. m < 3 * N ==> read (wmem :> bytes32 (word (PA + 4 * m))) s =
                             (if m < 2 * i then NA m else AI m)) /\
          (!m. m < 3 * N ==> read (wmem :> bytes32 (word (PB + 4 * m))) s =
                             (if m < 2 * i then NB m else BI m)) /\
          (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1974272 + 4 * m))) s = (vd:num->int32) m)` in
  rhs(concl(TOP_DEPTH_CONV BETA_CONV t));;

let VORT_SETUP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `q = (3 * N) DIV 2` THEN ABBREV_TAC `r = (3 * N) MOD 2` THEN
  SUBGOAL_THEN `2 * q + r = 3 * N /\ r < 2 /\ 1 <= q` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q";"r"] THEN MP_TAC(SPECL [`3 * N`; `2`] DIVISION) THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word N:int32) = N` ASSUME_TAC THENL
   [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(word N:int32 = word 0)` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN
    ASM_REWRITE_TAC[VAL_WORD_0] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(if ~(N < 640) then I32 (word 640) else I32 (word N)) = I32 (word N)` ASSUME_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_mul (word N) (word 3):int32 = word (3 * N) /\
                word_and (word (3 * N)) (word 1):int32 = word r /\
                word_and (word (3 * N)) (word 4094):int32 = word (2 * q)`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WORD_MUL; VE_AND1] THEN REPEAT CONJ_TAC THENL
     [AP_TERM_TAC THEN ARITH_TAC;
      ASM_REWRITE_TAC[];
      MP_TAC(SPEC `3 * N` VE_AND4094) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]];
    ALL_TAC];;

let VORT_INIT_TAC =
  ENSURES_INIT_TAC "s0" THEN MEMNAME_TAC THEN
  SUBGOAL_THEN `read (bytes32 (word 16644)) mm = word N` ASSUME_TAC THENL
   [EXPAND_TAC "mm" THEN REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    FIRST_ASSUM ACCEPT_TAC; ALL_TAC];;

let VORT_ENTRY_TAC exec =
  VORT_INIT_TAC THEN CAP_MSTEPS_TAC exec (1--29) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LT; SUB_0; injectivity "wval"];;

let vadd a k = mk_binop `(+):num->num->num` a (mk_small_numeral k);;

(* the six loads of the two elements, in the address forms the steps produce *)
let VORT_LOADFACTS_TAC pa pb ai bi =
  let bases = [pa,ai; pb,bi; `1974272`,`vd:num->int32`] in
  MAP_EVERY (fun ((b,f),k) ->
    let a = if k = 0 then subst [b,`bb:num`] `bb + 8 * i` else vadd (subst [b,`bb:num`] `bb + 8 * i`) 4 in
    let j = if k = 0 then `2 * i` else `2 * i + 1` in
    SUBGOAL_THEN (subst [a,`aa:num`; f,`ff:num->int32`; j,`jj:num`] `read (bytes32 (word aa)) mm = (ff:num->int32) (jj:num)`)
      ASSUME_TAC THENL
     [SUBGOAL_THEN (subst [a,`aa:num`; b,`bb:num`; j,`jj:num`] `aa = bb + 4 * jj`) SUBST1_TAC THENL
       [ARITH_TAC;
        SUBGOAL_THEN (subst [j,`jj:num`] `jj < 3 * N /\ ~(jj < 2 * i)`) STRIP_ASSUME_TAC THENL
         [ASM_ARITH_TAC; ASM_SIMP_TAC[]]];
      ALL_TAC])
   (allpairs (fun x y -> (x,y)) bases [0;1]);;

let VORT_B32O_FACTS_TAC pa pb =
  let cell b k = if k = 0 then subst [b,`bb:num`] `bb + 8 * i` else vadd (subst [b,`bb:num`] `bb + 8 * i`) 4 in
  let reads = allpairs (fun b k -> cell b k) [pa; pb; `1974272`] [0;1]
  and writes = allpairs (fun b k -> cell b k) [pa; pb] [0;1] in
  MAP_EVERY (fun (x,y) -> B32O_TAC x y)
   (filter (fun (x,y) -> x <> y) (allpairs (fun x y -> (x,y)) reads writes));;

let VORT_VALS_TAC pa pb =
  MAP_EVERY (fun b ->
    VAL_TAC (subst [b,`bb:num`] `val(word (bb + 8 * i):int32) = bb + 8 * i`) THEN
    VAL_TAC (subst [b,`bb:num`] `val(word_add (word (bb + 8 * i)) (word 4):int32) = (bb + 8 * i) + 4`))
   [pa; pb; `1974272`];;

let VORT_MEM_TAC =
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  MAP_EVERY (fun c -> ASM_CASES_TAC (subst [c,`cc:num`] `m:num = cc`) THENL
    [FIRST_X_ASSUM SUBST_ALL_TAC THEN REPEAT B32_PEEL_TAC THEN ASM_SIMP_TAC[] THEN
     REWRITE_TAC[ARITH_RULE `2 * i < 2 * (i + 1) /\ 2 * i + 1 < 2 * (i + 1)`; LT_REFL;
                 ARITH_RULE `~(2 * i + 1 < 2 * i)`];
     ALL_TAC]) [`2 * i`; `2 * i + 1`] THEN
  REPEAT B32_PEEL_TAC THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `(m < 2 * (i + 1) <=> m < 2 * i)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[]];;

let VORT_BODY_TAC exec pa pb ai bi =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `2 * i + 2 <= 3 * N` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  VORT_VALS_TAC pa pb THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  VORT_LOADFACTS_TAC pa pb ai bi THEN VORT_B32O_FACTS_TAC pa pb THEN
  CAP_MSTEPS_TAC exec (1--50) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  ASM_SIMP_TAC[injectivity "wval"; CONS_11; VE_DEC2] THEN
  REPEAT CONJ_TAC THEN TRY(WORD_NUM_EQ_TAC THEN NO_TAC) THEN
  TRY(VORT_MEM_TAC THEN NO_TAC);;

let VORT_BACK_TAC exec =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(word (2 * q - 2 * i):int32 = word 0) <=> F` ASSUME_TAC THENL
   [REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN
    SUBGOAL_THEN `val(word (2 * q - 2 * i):int32) = 2 * q - 2 * i` SUBST1_TAC THENL
     [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC;
      REWRITE_TAC[VAL_WORD_0] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  CAP_MSTEPS_TAC exec (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[];;

let VORT_EXIT_EVEN_TAC exec =
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUB_REFL]) THEN
  CAP_MSTEPS_TAC exec (1--6) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  (X_GEN_TAC `m:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
   COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let VORT_EXIT_ODD_TAC exec pa pb ai bi =
  SUBGOAL_THEN `(word r:int32 = word 0) <=> F` ASSUME_TAC THENL
   [REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN
    SUBGOAL_THEN `val(word r:int32) = r` SUBST1_TAC THENL
     [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC;
      REWRITE_TAC[VAL_WORD_0] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 * q < 3 * N` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun b -> VAL_TAC (subst [b,`bb:num`] `val(word (bb + 8 * q):int32) = bb + 8 * q`))
   [pa; pb; `1974272`] THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUB_REFL]) THEN
  MAP_EVERY (fun (b,f) ->
    SUBGOAL_THEN (subst [b,`bb:num`; f,`ff:num->int32`] `read (bytes32 (word (bb + 8 * q))) mm = ff (2 * q)`)
      ASSUME_TAC THENL
     [SUBGOAL_THEN (subst [b,`bb:num`] `bb + 8 * q = bb + 4 * (2 * q)`) SUBST1_TAC THENL
       [ARITH_TAC; ASM_SIMP_TAC[LT_REFL]];
      ALL_TAC]) [pa,ai; pb,bi; `1974272`,`vd:num->int32`] THEN
  MAP_EVERY (fun (x,y) -> B32O_TAC (subst [x,`bb:num`] `bb + 8 * q`) (subst [y,`bb:num`] `bb + 8 * q`))
   [pb,pa; `1974272`,pa; pa,pb] THEN
  CAP_MSTEPS_TAC exec (1--20) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  (X_GEN_TAC `m:num` THEN DISCH_TAC THEN
   ASM_CASES_TAC `m = 2 * q` THENL
    [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[ARITH_RULE `4 * 2 * q = 8 * q`] THEN
     ASM_REWRITE_TAC[CAP_B32_SAME];
     REPEAT B32_PEEL_TAC THEN ASM_SIMP_TAC[] THEN
     COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let VORT_TAC mc exec pa pb na nb ai bi =
  VORT_SETUP_TAC THEN
  ENSURES_WHILE_UP_TAC `q:num` `1372` `1473` (vort_inv mc pa pb na nb ai bi) THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC; VORT_ENTRY_TAC exec; VORT_BODY_TAC exec pa pb ai bi; VORT_BACK_TAC exec;
    ASM_CASES_TAC `r = 0` THENL
     [VORT_EXIT_EVEN_TAC exec; VORT_EXIT_ODD_TAC exec pa pb ai bi]];;
