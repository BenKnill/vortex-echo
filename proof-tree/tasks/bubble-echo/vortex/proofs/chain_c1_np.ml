needs "ve_vort.ml";;
needs "ve_tick.ml";;
needs "ve_vk.ml";;
needs "va1_code.ml";;
needs "va1_seq_final2.ml";;
needs "chain_c1_host.ml";;
(* ========================================================================= *)
(* Vortex chain, rung C1, layer 2 of 3: the no-pop chain (PROVE-C1, Claude  *)
(* Opus 5.5, 2026-11-11). Spec chain_c1_final.spec (frozen 3b62701f...).    *)
(* Definitions va1_swf, va1_swb, va1_np_st, va1_fs_np exactly as pinned;    *)
(* tick frames keep wmemsize and wglobals (component reasoning over the     *)
(* MAYCHANGE frames of the PROVED tick theorems); one host call per tick;   *)
(* scrub in any order; the film; non-vacuity. Pure HOL over                  *)
(* VA1_TICK_FORWARD/BACKWARD_NOPOP_VK and VE_VORT_STEPS_INVERSE_VK; no       *)
(* stepping, no decode rule, no mk_thm / new_axiom / CHEAT_TAC.              *)
(* ========================================================================= *)

let va1_swf = new_definition
 `va1_swf (mdl:num->int32) = ve_fredkin_fwdn (\i. ve_vk mdl) 16`;;

let va1_swb = new_definition
 `va1_swb (mdl:num->int32) = ve_fredkin_bwdn (\i. ve_vk mdl) 16`;;

let va1_np_st = new_definition
 `va1_np_st (t:int32) (ap:int32) (mdl:num->int32) (N:num) (x:(num->int32)#(num->int32)) (m:int64->byte) <=>
    va1_tick t m /\ va1_pop (word 4294967295) ap m /\ va1_mdl mdl m /\ va1_vab N x m`;;

let va1_fs_np = new_definition
 `va1_fs_np (fs:num->byte list#num#num) <=>
    fs 9 = (va1_f9_mc,0,0) /\ fs 10 = (va1_f10_mc,0,0) /\ fs 27 = (va1_f27_mc,0,0) /\ fs 28 = (va1_f28_mc,0,0)`;;

(* ---- frames: a component d that no assigned component touches is kept ---- *)

let C1_SEQ_KEEPS = prove
 (`!(d:(A,C)component) (r1:A->A->bool) (r2:A->A->bool).
     (!s s'. r1 s s' ==> read d s' = read d s) /\
     (!s s'. r2 s s' ==> read d s' = read d s)
     ==> !s s'. (r1 ,, r2) s s' ==> read d s' = read d s`,
  REWRITE_TAC[seq] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN MESON_TAC[]);;

let C1_ASSIGNS_KEEPS = prove
 (`!(c:(A,B)component) (d:(A,C)component).
     (!y s. read d (write c y s) = read d s)
     ==> !s s'. ASSIGNS c s s' ==> read d s' = read d s`,
  REWRITE_TAC[ASSIGNS_THM] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN MESON_TAC[]);;

let C1_COMP_TAC =
  REPEAT GEN_TAC THEN REWRITE_TAC[wlocal; READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE] THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN REWRITE_TAC[];;

let C1_KEEPS_TAC (comptac:tactic) =
  REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
  REPEAT(MATCH_MP_TAC C1_SEQ_KEEPS THEN CONJ_TAC) THEN
  MATCH_MP_TAC C1_ASSIGNS_KEEPS THEN comptac;;

let c1_frame_of th = rand(snd(dest_imp(snd(strip_forall(concl th)))));;
let c1_npf_frame = c1_frame_of VA1_TICK_FORWARD_NOPOP_VK;;
let c1_npb_frame = c1_frame_of VA1_TICK_BACKWARD_NOPOP_VK;;
let c1_fr fr tm = vsubst [fr, `cf:wasmstate->wasmstate->bool`] tm;;

let C1_KEEPS_MEMSIZE = `!s s'. (cf:wasmstate->wasmstate->bool) s s' ==> read wmemsize s' = read wmemsize s`;;
let C1_KEEPS_GLOBALS = `!s s'. (cf:wasmstate->wasmstate->bool) s s' ==> read wglobals s' = read wglobals s`;;
let C1_KEEPS_BOTH = `!s s'. (cf:wasmstate->wasmstate->bool) s s'
   ==> read wmemsize s' = read wmemsize s /\ read wglobals s' = read wglobals s`;;

let VA1_NPF_MEMSIZE = prove(c1_fr c1_npf_frame C1_KEEPS_MEMSIZE, C1_KEEPS_TAC C1_COMP_TAC);;
let VA1_NPF_GLOBALS = prove(c1_fr c1_npf_frame C1_KEEPS_GLOBALS, C1_KEEPS_TAC C1_COMP_TAC);;
let VA1_NPB_MEMSIZE = prove(c1_fr c1_npb_frame C1_KEEPS_MEMSIZE, C1_KEEPS_TAC C1_COMP_TAC);;
let VA1_NPB_GLOBALS = prove(c1_fr c1_npb_frame C1_KEEPS_GLOBALS, C1_KEEPS_TAC C1_COMP_TAC);;
let VA1_NPF_KEEPS = prove(c1_fr c1_npf_frame C1_KEEPS_BOTH, MESON_TAC[VA1_NPF_MEMSIZE; VA1_NPF_GLOBALS]);;
let VA1_NPB_KEEPS = prove(c1_fr c1_npb_frame C1_KEEPS_BOTH, MESON_TAC[VA1_NPB_MEMSIZE; VA1_NPB_GLOBALS]);;

(* ---- one host call per tick ---- *)
(* lth = |- ensures (wasmc fs) P Q C (the tick theorem, antecedent discharged), *)
(* cth = callee facts, kths = frame facts `C s s' ==> ...` used on the final state *)
let C1_NP_HCALL_TAC (lth:thm) (cth:thm) (kths:thm list) : tactic =
  let _,[step;pp;qq;cc] = strip_comb(concl lth) in
  let eth,dth = CONJ_PAIR cth in
  let code = rand(lhand(concl eth)) and e = rand(rand(concl eth))
  and decls = rand(rand(concl dth)) in
  MATCH_MP_TAC (ISPECL [step; code; e; decls; `[]:wval list`; `word 1:int32`; pp; qq; cc]
                  VA1_HCALL_ENSURES) THEN
  REWRITE_TAC[eth; dth; lth] THEN CONJ_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    ASM_REWRITE_TAC[WCALL_ENTRY_READS];
    REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
    MAP_EVERY (fun kth -> FIRST_ASSUM(MP_TAC o MATCH_MP kth) THEN
                          ASM_REWRITE_TAC[WCALL_ENTRY_READS] THEN DISCH_TAC) kths THEN
    ASM_REWRITE_TAC[va1_swf; va1_swb]];;

let VA1_NP_HCALL_FWD = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (t:int32) (ap:int32) (mdl:num->int32) (N:num)
   (x:(num->int32)#(num->int32)) (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_np fs /\
     (ap = word 0 \/ ~(ap = word_add t (word 1))) /\ va1_np_st t ap mdl N x m
     ==> va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 1)
           (\gl' m'. gl' = gl /\ va1_np_st (word_add t (word 1)) ap mdl N (va1_swf mdl x) m') gl m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_fs_np; va1_np_st] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `t:int32`; `ap:int32`;
                `mdl:num->int32`; `N:num`; `x:(num->int32)#(num->int32)`]
               VA1_TICK_FORWARD_NOPOP_VK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun lth -> C1_NP_HCALL_TAC lth VA1_TICKF_CALLEE [VA1_NPF_KEEPS]));;

let VA1_NP_HCALL_BWD = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (u:int32) (ap:int32) (mdl:num->int32) (N:num)
   (y:(num->int32)#(num->int32)) (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_np fs /\ ~(u = word 0) /\ va1_np_st u ap mdl N y m
     ==> va1_hcall (wasmc fs) va1_tick_backward_mc [] (word 1)
           (\gl' m'. gl' = gl /\ va1_np_st (word_sub u (word 1)) ap mdl N (va1_swb mdl y) m') gl m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_fs_np; va1_np_st] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `u:int32`; `ap:int32`;
                `mdl:num->int32`; `N:num`; `y:(num->int32)#(num->int32)`]
               VA1_TICK_BACKWARD_NOPOP_VK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun lth -> C1_NP_HCALL_TAC lth VA1_TICKB_CALLEE [VA1_NPB_KEEPS]));;

(* ---- tick arithmetic and the inverse ---- *)

let C1_WORD_ADD1 = prove
 (`!u. word_add (word u) (word 1):int32 = word (u + 1)`,
  REWRITE_TAC[WORD_ADD]);;

let C1_WORD_SUB1 = prove
 (`!u. 0 < u ==> word_sub (word u) (word 1):int32 = word (u - 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_SUB] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < u ==> 1 <= u`]);;

let C1_WORD_NZ = prove
 (`!u kk. 0 < u /\ u <= kk /\ kk < 4294967296 ==> ~(word u:int32 = word 0)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int32->num`) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `u MOD 4294967296 = u` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let C1_AUTO_FWD = prove
 (`!(ap:int32) u kk. kk < 4294967296 /\ u < kk /\ (ap = word 0 \/ kk < val ap)
     ==> ap = word 0 \/ ~(ap = word (u + 1))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `ap:int32 = word 0` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
  SUBGOAL_THEN `(u + 1) MOD 2 EXP 32 = u + 1` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let C1_SWF_ITER = prove
 (`!mdl u x. va1_swf mdl (ITER u (va1_swf mdl) x) = ITER (u + 1) (va1_swf mdl) x`,
  REWRITE_TAC[GSYM ADD1; ITER]);;

let C1_SWB_ITER = prove
 (`!mdl u x. 0 < u ==> va1_swb mdl (ITER u (va1_swf mdl) x) = ITER (u - 1) (va1_swf mdl) x`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[LT_REFL; ITER; SUC_SUB1] THEN
  REWRITE_TAC[va1_swb; va1_swf; VE_VORT_STEPS_INVERSE_VK]);;

(* ---- scrub in any order ---- *)

let VA1_NP_SCRUB = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (ap:int32)
   (x0:(num->int32)#(num->int32)) (K:num).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_np fs /\ K < 4294967296 /\
     (ap = word 0 \/ K < val ap)
     ==> !(cs:bool list) (u:num) (m:int64->byte).
           u <= K /\ va1_cmds_ok K u cs /\
           va1_np_st (word u) ap mdl N (ITER u (va1_swf mdl) x0) m
           ==> va1_hrun (wasmc fs) cs
                 (\gl' m'. gl' = gl /\
                    va1_np_st (word (va1_cmds_end u cs)) ap mdl N
                              (ITER (va1_cmds_end u cs) (va1_swf mdl) x0) m') gl m`,
  MAP_EVERY X_GEN_TAC
   [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`;
    `ap:int32`; `x0:(num->int32)#(num->int32)`; `kk:num`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[VA1_HRUN_CLAUSES; VA1_CMDS_OK_CLAUSES; VA1_CMDS_END_CLAUSES] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[VA1_CMDS_END_CLAUSES] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:num`; `m:int64->byte`] THEN
  REWRITE_TAC[VA1_HRUN_CLAUSES; VA1_CMDS_OK_CLAUSES; VA1_CMDS_END_CLAUSES] THEN
  ASM_CASES_TAC `h:bool` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC VA1_HCALL_MONO THENL
   [EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\
       va1_np_st (word (u + 1)) ap mdl N (ITER (u + 1) (va1_swf mdl) x0) m'` THEN
    CONJ_TAC THENL
     [REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `u < kk` THEN ARITH_TAC;
      MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `word u:int32`; `ap:int32`;
        `mdl:num->int32`; `N:num`; `ITER u (va1_swf mdl) x0`; `m:int64->byte`]
        VA1_NP_HCALL_FWD) THEN
      REWRITE_TAC[C1_WORD_ADD1; C1_SWF_ITER] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC C1_AUTO_FWD THEN
      EXISTS_TAC `kk:num` THEN ASM_REWRITE_TAC[]];
    EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\
       va1_np_st (word (u - 1)) ap mdl N (ITER (u - 1) (va1_swf mdl) x0) m'` THEN
    CONJ_TAC THENL
     [REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `u <= kk` THEN ARITH_TAC;
      MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `word u:int32`; `ap:int32`;
        `mdl:num->int32`; `N:num`; `ITER u (va1_swf mdl) x0`; `m:int64->byte`]
        VA1_NP_HCALL_BWD) THEN
      SUBGOAL_THEN `word_sub (word u) (word 1):int32 = word (u - 1) /\
                    va1_swb mdl (ITER u (va1_swf mdl) x0) = ITER (u - 1) (va1_swf mdl) x0`
        (fun th -> REWRITE_TAC[th]) THENL
       [ASM_SIMP_TAC[C1_WORD_SUB1; C1_SWB_ITER]; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC C1_WORD_NZ THEN EXISTS_TAC `kk:num` THEN ASM_REWRITE_TAC[]]]);;

(* ---- the film: n forward then n backward from tick 0 ---- *)

let C1_CMDS_OK_REPT = prove
 (`!j kk u cs. u <= kk
     ==> (va1_cmds_ok kk u (APPEND (REPLICATE j T) cs) <=>
          u + j <= kk /\ va1_cmds_ok kk (u + j) cs)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[REPLICATE; APPEND; ADD_CLAUSES] THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REPLICATE; APPEND; ADD_CLAUSES; VA1_CMDS_OK_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `u < kk` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`kk:num`; `u + 1`; `cs:bool list`]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[ARITH_RULE `(u + 1) + j = SUC (u + j)`];
    REWRITE_TAC[DE_MORGAN_THM] THEN DISJ1_TAC THEN ASM_ARITH_TAC]);;

let C1_CMDS_OK_REPF = prove
 (`!j kk u. va1_cmds_ok kk u (REPLICATE j F) <=> j <= u`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; VA1_CMDS_OK_CLAUSES; LE_0] THEN ARITH_TAC);;

let C1_CMDS_END_REPT = prove
 (`!j u cs. va1_cmds_end u (APPEND (REPLICATE j T) cs) = va1_cmds_end (u + j) cs`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[REPLICATE; APPEND; VA1_CMDS_END_CLAUSES; ADD_CLAUSES;
                  ARITH_RULE `!u j. (u + 1) + j = SUC (u + j)`]);;

let C1_CMDS_END_REPF = prove
 (`!j u. va1_cmds_end u (REPLICATE j F) = u - j`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; VA1_CMDS_END_CLAUSES; SUB_0] THEN ARITH_TAC);;

let C1_FILM_SIMPS =
  [LE_0; LE_REFL; ADD_CLAUSES; SUB_REFL; ITER; C1_CMDS_OK_REPT; C1_CMDS_OK_REPF;
   C1_CMDS_END_REPT; C1_CMDS_END_REPF];;

let VA1_NP_FILM_INVERSE = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num)
   (x0:(num->int32)#(num->int32)) (n:num) (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_np fs /\ n < 4294967296 /\
     va1_np_st (word 0) (word 0) mdl N x0 m
     ==> va1_hrun (wasmc fs) (APPEND (REPLICATE n T) (REPLICATE n F))
           (\gl' m'. gl' = gl /\ va1_np_st (word 0) (word 0) mdl N x0 m') gl m`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`;
    `word 0:int32`; `x0:(num->int32)#(num->int32)`; `n:num`] VA1_NP_SCRUB) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`APPEND (REPLICATE n T) (REPLICATE n F)`; `0`; `m:int64->byte`]) THEN
  ASM_SIMP_TAC C1_FILM_SIMPS);;

(* ---- non-vacuity (pattern of pop_n1_sat.ml, SEGMENT PROVER N1) ---- *)

let C1_READ_BYTES32 = prove
 (`!(a:int64) (m:int64->byte). read (bytes32 a) m = word (read (bytes(a,4)) m)`,
  REWRITE_TAC[bytes32; READ_COMPONENT_COMPOSE; asword; through; read]);;

let C1_B32_SAT = prove
 (`!W:num->int32. ?m:int64->byte.
      !w. 4 * w + 4 <= 2 EXP 64 ==> read (bytes32 (word (4 * w))) m = W w`,
  GEN_TAC THEN
  EXISTS_TAC
   `\b:int64. write (bytes(word(4 * (val b DIV 4)):int64,4))
                    (val((W:num->int32)(val b DIV 4))) (\c:int64. word 0:byte) b` THEN
  X_GEN_TAC `w:num` THEN DISCH_TAC THEN
  REWRITE_TAC[C1_READ_BYTES32] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `word(read (bytes(word(4 * w):int64,4))
              (write (bytes(word(4 * w):int64,4)) (val((W:num->int32) w))
                     (\c:int64. word 0:byte))):int32` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[READ_BYTES_EQ] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `val(word_add (word(4 * w)) (word i):int64) DIV 4 = w`
     (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    SUBGOAL_THEN `(4 * w + i) MOD 2 EXP 64 = 4 * w + i` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `i:num` THEN ASM_ARITH_TAC;
    SIMP_TAC[READ_WRITE_BYTES; DIMINDEX_64; ARITH_RULE `4 <= 2 EXP 64`] THEN
    REWRITE_TAC[ARITH_RULE `8 * 4 = 32`] THEN
    MP_TAC(ISPEC `(W:num->int32) w` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_32] THEN SIMP_TAC[MOD_LT; WORD_VAL]]);;

let c1_addr_th a =
  let four = mk_small_numeral 4 in
  if is_numeral a then
    let n = dest_numeral a in
    let q = mk_numeral (Num.quo_num n (Num.num_of_int 4)) in
    SYM(NUM_REDUCE_CONV (mk_binop `( * ):num->num->num` four q))
  else
    let b,fk = dest_binop `(+):num->num->num` a in
    let k = rand fk in
    let q = mk_numeral (Num.quo_num (dest_numeral b) (Num.num_of_int 4)) in
    ARITH_RULE (mk_eq(a, mk_binop `( * ):num->num->num` four
                                  (mk_binop `(+):num->num->num` q k)));;

let C1_DECIDE_TAC =
  W(fun (asl,w) ->
      let l = lhs w in
      if is_cond l then
        let c = rand(rator(rator l)) in
        (SUBGOAL_THEN (mk_neg c) MP_TAC THENL
          [ASM_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[EQF_INTRO th])]) ORELSE
        (SUBGOAL_THEN c MP_TAC THENL
          [ASM_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[EQT_INTRO th])])
      else FIRST [REFL_TAC; AP_TERM_TAC THEN ASM_ARITH_TAC]);;

let C1_CONJ_TAC =
  REPEAT STRIP_TAC THEN
  W(fun (asl,w) ->
      let a = rand(rand(rand(rator(lhs w)))) in
      let th = c1_addr_th a in
      SUBST1_TAC th THEN
      REMOVE_THEN "m" (fun mth -> MP_TAC(SPEC (rand(rand(concl th))) mth))) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
                  DISCH_THEN SUBST1_TAC] THEN
  BETA_TAC THEN REPEAT C1_DECIDE_TAC;;

let VA1_NP_FILM_SAT = prove
 (`(?fs:num->byte list#num#num. va1_fs_np fs) /\
  (!(t:int32) (ap:int32) (mdl:num->int32) (N:num) (x:(num->int32)#(num->int32)).
     N <= 640 ==> ?m:int64->byte. va1_np_st t ap mdl N x m)`,
  CONJ_TAC THENL
   [EXISTS_TAC `\i. if i = 9 then (va1_f9_mc,0,0) else if i = 10 then (va1_f10_mc,0,0)
                    else if i = 27 then (va1_f27_mc,0,0) else (va1_f28_mc,0,0)` THEN
    REWRITE_TAC[va1_fs_np] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:int32`; `ap:int32`; `mdl:num->int32`; `N:num`;
                       `x:(num->int32)#(num->int32)`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC
   `\w. if w = 4098 then t:int32
        else if w = 4099 then word 4294967295
        else if w = 4128 then ap
        else if 4160 <= w /\ w < 5184 then mdl (w - 4160)
        else if 278528 <= w /\ w < 280576 then FST x (w - 278528)
        else if 280576 <= w /\ w < 282624 then SND x (w - 280576)
        else word 0` C1_B32_SAT) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:int64->byte` (LABEL_TAC "m")) THEN
  EXISTS_TAC `m:int64->byte` THEN
  REWRITE_TAC[va1_np_st; va1_tick; va1_pop; va1_mdl; va1_vab] THEN
  REPEAT CONJ_TAC THEN C1_CONJ_TAC);;
