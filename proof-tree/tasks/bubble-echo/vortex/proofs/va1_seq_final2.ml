needs "ve_vort.ml";;
needs "ve_tick.ml";;
needs "ve_vk.ml";;
needs "va1_code.ml";;
(* ========================================================================= *)
(* Vortex Echo purist a1 sequencer (lane hearth-call): the memory facts a    *)
(* call site carries, and how the callees' frames preserve them.            *)
(*   va1_tick t m   header word 2 (tick T, byte 16392) = t                  *)
(*   va1_pop pt ap m  pop tick (16396) = pt, auto-pop tick (16512) = ap      *)
(*   va1_mdl mdl m  model words 16640 + 4k = mdl k, k < 1024                 *)
(*   va1_vab N x m  VA (1114112 + 4j) = FST x j, VB (1122304 + 4j) = SND x j, *)
(*                  j < 3N                                                   *)
(* Writes: ve_tick_inc/dec write bytes 16392..16395; ve_vort_apply/unapply   *)
(* write 1114112 + 16384 (VA, VB) and 1966080 + 73728 (scratch).             *)
(* ========================================================================= *)

let va1_tick = new_definition
 `va1_tick (t:int32) (m:int64->byte) <=> read (bytes32 (word 16392)) m = t`;;

let va1_pop = new_definition
 `va1_pop (pt:int32) (ap:int32) (m:int64->byte) <=>
    read (bytes32 (word 16396)) m = pt /\ read (bytes32 (word 16512)) m = ap`;;

let va1_mdl = new_definition
 `va1_mdl (mdl:num->int32) (m:int64->byte) <=>
    !k. k < 1024 ==> read (bytes32 (word (16640 + 4 * k))) m = mdl k`;;

let va1_vab = new_definition
 `va1_vab N (x:(num->int32)#(num->int32)) (m:int64->byte) <=>
    (!j. j < 3 * N ==> read (bytes32 (word (1114112 + 4 * j))) m = FST x j) /\
    (!j. j < 3 * N ==> read (bytes32 (word (1122304 + 4 * j))) m = SND x j)`;;

let B32_BYTES_OTHER = prove
 (`!a b n (y:num) (m:int64->byte).
     (a + 4 <= b \/ b + n <= a) /\ a + 4 < 2 EXP 64 /\ b + n < 2 EXP 64
     ==> read (bytes32 (word a)) (write (bytes(word b,n)) y m) =
         read (bytes32 (word a)) m`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC READ_WRITE_ORTHOGONAL_COMPONENTS THEN
  REWRITE_TAC[bytes32] THEN MATCH_MP_TAC ORTHOGONAL_COMPONENTS_SUB_LEFT THEN
  REWRITE_TAC[ORTHOGONAL_COMPONENTS_BYTES; DIMINDEX_64] THEN
  MATCH_MP_TAC NONOVERLAPPING_MODULO_SIMPLE THEN
  SUBGOAL_THEN `val(word a:int64) = a /\ val(word b:int64) = b`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

(* a pointwise frame fact: address family a(i), index bound, region (b,n) *)
let VA1_B32_TAC =
  REPEAT STRIP_TAC THEN MATCH_MP_TAC B32_BYTES_OTHER THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;;

let VA1_TICKW_POP = prove
 (`!(y:num) m pt ap.
     va1_pop pt ap (write (bytes(word 16392,4)) y m) <=> va1_pop pt ap m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_pop] THEN
  SUBGOAL_THEN
   `read (bytes32 (word 16396)) (write (bytes(word 16392,4)) y m) =
    read (bytes32 (word 16396)) m /\
    read (bytes32 (word 16512)) (write (bytes(word 16392,4)) y m) =
    read (bytes32 (word 16512)) m`
   (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THEN VA1_B32_TAC);;

let VA1_TICKW_MDL = prove
 (`!(y:num) m mdl.
     va1_mdl mdl (write (bytes(word 16392,4)) y m) <=> va1_mdl mdl m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_mdl] THEN
  SUBGOAL_THEN
   `!k. k < 1024
        ==> read (bytes32 (word (16640 + 4 * k))) (write (bytes(word 16392,4)) y m) =
            read (bytes32 (word (16640 + 4 * k))) m`
   (fun th -> SIMP_TAC[th]) THEN
  VA1_B32_TAC);;

let VA1_TICKW_VAB = prove
 (`!(y:num) m N x. N <= 640
     ==> (va1_vab N x (write (bytes(word 16392,4)) y m) <=> va1_vab N x m)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[va1_vab] THEN
  SUBGOAL_THEN
   `(!j. j < 3 * N
         ==> read (bytes32 (word (1114112 + 4 * j))) (write (bytes(word 16392,4)) y m) =
             read (bytes32 (word (1114112 + 4 * j))) m) /\
    (!j. j < 3 * N
         ==> read (bytes32 (word (1122304 + 4 * j))) (write (bytes(word 16392,4)) y m) =
             read (bytes32 (word (1122304 + 4 * j))) m)`
   (fun th -> SIMP_TAC[th]) THEN
  CONJ_TAC THEN VA1_B32_TAC);;

(* the vortex pair writes VA/VB then scratch: tick, pop and model survive *)
let VA1_VORTW_TICK = prove
 (`!(y1:num) (y2:num) m t.
     va1_tick t (write (bytes(word 1966080,73728)) y2
                  (write (bytes(word 1114112,16384)) y1 m)) <=> va1_tick t m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_tick] THEN
  SUBGOAL_THEN
   `read (bytes32 (word 16392)) (write (bytes(word 1966080,73728)) y2
                  (write (bytes(word 1114112,16384)) y1 m)) =
    read (bytes32 (word 16392)) (write (bytes(word 1114112,16384)) y1 m) /\
    read (bytes32 (word 16392)) (write (bytes(word 1114112,16384)) y1 m) =
    read (bytes32 (word 16392)) m`
   (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THEN VA1_B32_TAC);;

let VA1_VORTW_POP = prove
 (`!(y1:num) (y2:num) m pt ap.
     va1_pop pt ap (write (bytes(word 1966080,73728)) y2
                     (write (bytes(word 1114112,16384)) y1 m)) <=> va1_pop pt ap m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_pop] THEN
  SUBGOAL_THEN
   `read (bytes32 (word 16396)) (write (bytes(word 1966080,73728)) y2
                  (write (bytes(word 1114112,16384)) y1 m)) =
    read (bytes32 (word 16396)) (write (bytes(word 1114112,16384)) y1 m) /\
    read (bytes32 (word 16396)) (write (bytes(word 1114112,16384)) y1 m) =
    read (bytes32 (word 16396)) m /\
    read (bytes32 (word 16512)) (write (bytes(word 1966080,73728)) y2
                  (write (bytes(word 1114112,16384)) y1 m)) =
    read (bytes32 (word 16512)) (write (bytes(word 1114112,16384)) y1 m) /\
    read (bytes32 (word 16512)) (write (bytes(word 1114112,16384)) y1 m) =
    read (bytes32 (word 16512)) m`
   (fun th -> REWRITE_TAC[th]) THEN
  REPEAT CONJ_TAC THEN VA1_B32_TAC);;

let VA1_VORTW_MDL = prove
 (`!(y1:num) (y2:num) m mdl.
     va1_mdl mdl (write (bytes(word 1966080,73728)) y2
                   (write (bytes(word 1114112,16384)) y1 m)) <=> va1_mdl mdl m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_mdl] THEN
  SUBGOAL_THEN
   `(!k. k < 1024
         ==> read (bytes32 (word (16640 + 4 * k)))
               (write (bytes(word 1966080,73728)) y2
                 (write (bytes(word 1114112,16384)) y1 m)) =
             read (bytes32 (word (16640 + 4 * k)))
               (write (bytes(word 1114112,16384)) y1 m)) /\
    (!k. k < 1024
         ==> read (bytes32 (word (16640 + 4 * k)))
               (write (bytes(word 1114112,16384)) y1 m) =
             read (bytes32 (word (16640 + 4 * k))) m)`
   (fun th -> SIMP_TAC[th]) THEN
  CONJ_TAC THEN VA1_B32_TAC);;

let VA1_FRAME_THS =
  [VA1_TICKW_POP; VA1_TICKW_MDL; VA1_TICKW_VAB;
   VA1_VORTW_TICK; VA1_VORTW_POP; VA1_VORTW_MDL];;
(* ========================================================================= *)
(* Vortex Echo purist a1 sequencer (lane hearth-call): call-site lemmas.     *)
(* VA1_CALL_TAC lth cth f proves a call-site lemma of the shape              *)
(*   fs f = (code,0,0) /\ p < 2 EXP 64 /\ N <= 640 /\                        *)
(*   wasm_decode mc p = SOME (Wcall f,6)                                     *)
(*   ==> ensures (wasmc fs) (caller at pc p, facts) (pc p + 6, new facts)    *)
(*               (MAYCHANGE [wpc] ,, callee memory regions)                  *)
(* from the callee leaf lth = |- ensures wasm P Q C (instantiated) and the   *)
(* callee facts cth = WASM_CALLEE_RULE code_def, through WASMC_CALL0_STEP.   *)
(* ========================================================================= *)

(* goal P(write wpc .. s): generalize the new state to s1, as after a step *)
let VA1_GEN_STATE_TAC (s1:term) : tactic = fun (asl,w) ->
  let x = find_term (fun t -> can (term_match [] `write wpc (z:int64) (s:wasmstate)`) t) w in
  let gth = mk_forall(s1, mk_imp(mk_eq(x,s1), subst [s1,x] w)) in
  (SUBGOAL_THEN gth (fun th -> MATCH_MP_TAC th THEN REFL_TAC)) (asl,w);;

let VA1_CALL_TAC (lth:thm) (cth:thm) (f:term) : tactic =
  let _,[_;pp;qq;cc] = strip_comb(concl lth) in
  let eth,dth = CONJ_PAIR cth in
  let code = rand(lhand(concl eth)) and e = rand(rand(concl eth))
  and decls = rand(rand(concl dth)) in
  let c0tm = list_mk_comb(`wcall_entry`,
     [code; `0`; `0`; `read wstack (s0:wasmstate)`; e; decls; `s0:wasmstate`]) in
  let is_rmem_c1 th = let c = concl th in
     is_eq c && lhs c = `read wmem (c1:wasmstate)` in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[va1_tick; va1_pop; va1_mdl; va1_vab]) THEN
  ABBREV_TAC `mm0 = read wmem (s0:wasmstate)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  (fun (asl,w) ->
     let fs = rand(rand(rator(rator w))) in
     MATCH_MP_TAC (ISPECL [fs; f; code; `0`; e; decls; pp; qq; cc; `6`]
                     WASMC_CALL0_STEP) (asl,w)) THEN
  CONJ_TAC THENL [ACCEPT_TAC lth; ALL_TAC] THEN
  CONJ_TAC THENL
   [CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN MESON_TAC[distinctness "wstat"];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ACCEPT_TAC eth; ALL_TAC] THEN
  CONJ_TAC THENL [ACCEPT_TAC dth; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN
  CONJ_TAC THENL
   [CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[WCALL_ENTRY_READS; READ_COMPONENT_COMPOSE] THEN
    ASM_SIMP_TAC[PAIR];
    ALL_TAC] THEN
  (* the continuation: every final callee state c1 *)
  X_GEN_TAC `c1:wasmstate` THEN
  ABBREV_TAC (mk_eq(`c0:wasmstate`, c0tm)) THEN
  SUBGOAL_THEN `read wmem (c0:wasmstate) = mm0 /\ read wmemsize c0 = 4194304 /\
                read wglobals c0 = (gl:num->wval)`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c0" THEN ASM_REWRITE_TAC[WCALL_ENTRY_READS]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (STRIP_ASSUME_TAC o CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) MP_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [MAYCHANGE; SEQ_ID] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [GSYM SEQ_ASSOC] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_SEQ] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
  CAP_MEM_UPDATE_TAC THEN ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `wcall_return (val (read wpc (s0:wasmstate)) + 6) 0 c1 s0 =
                write wpc (word (p + 6)) (write wmem (read wmem c1) s0)`
    SUBST1_TAC THENL
   [SUBGOAL_THEN `val (read wpc (s0:wasmstate)) = p` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN
    MATCH_MP_TAC WCALL_RETURN0 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  FIRST_X_ASSUM(fun th -> if is_rmem_c1 th
    then REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if concl th = `read wmem (s0:wasmstate) = mm0`
    then REWRITE_TAC[SYM th] else NO_TAC) THEN
  REWRITE_TAC[WCALL_WRITE_MEM1; WCALL_WRITE_MEM2] THEN
  VA1_GEN_STATE_TAC `s1:wasmstate` THEN
  X_GEN_TAC `s1:wasmstate` THEN
  CAP_MEM_UPDATE_TAC THEN ASSUMPTION_STATE_UPDATE_TAC THEN MAYCHANGE_STATE_UPDATE_TAC THEN
  DISCH_THEN(fun th ->
    let thl = STATE_UPDATE_NEW_RULE th in
    if thl = [] then ALL_TAC else MP_TAC(end_itlist CONJ thl) THEN STRIP_TAC) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CONJ_TAC THENL [ALL_TAC; MONOTONE_MAYCHANGE_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC VA1_FRAME_THS THEN
  REWRITE_TAC[va1_tick; va1_pop; va1_mdl; va1_vab; PAIR] THEN
  ASM_SIMP_TAC[];;

let VE_TICK_INC_CALLEE = WASM_CALLEE_RULE ve_tick_inc_mc;;
let VE_TICK_DEC_CALLEE = WASM_CALLEE_RULE ve_tick_dec_mc;;

let VA1_CALL_TI = prove
 (`!fs mc p gl t pt ap mdl N x.
     fs 27 = (ve_tick_inc_mc,0,0) /\ p < 2 EXP 64 /\ N <= 640 /\
     wasm_decode mc p = SOME (Wcall 27,6)
     ==> ensures (wasmc fs)
          (\s. read wcode s = mc /\ read wpc s = word p /\ read wstatus s = WRunning /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_tick t (read wmem s) /\ va1_pop pt ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\ va1_vab N x (read wmem s))
          (\s. read wcode s = mc /\ read wpc s = word (p + 6) /\ read wstatus s = WRunning /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_tick (word_add t (word 1)) (read wmem s) /\ va1_pop pt ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\ va1_vab N x (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wmem :> bytes(word 16392,4)])`,
  VA1_CALL_TAC (SPEC `t:int32` VE_TICK_INC_CORRECT) VE_TICK_INC_CALLEE `27`);;

let VA1_CALL_TD = prove
 (`!fs mc p gl t pt ap mdl N x.
     fs 28 = (ve_tick_dec_mc,0,0) /\ p < 2 EXP 64 /\ N <= 640 /\
     wasm_decode mc p = SOME (Wcall 28,6)
     ==> ensures (wasmc fs)
          (\s. read wcode s = mc /\ read wpc s = word p /\ read wstatus s = WRunning /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_tick t (read wmem s) /\ va1_pop pt ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\ va1_vab N x (read wmem s))
          (\s. read wcode s = mc /\ read wpc s = word (p + 6) /\ read wstatus s = WRunning /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_tick (word_sub t (word 1)) (read wmem s) /\ va1_pop pt ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\ va1_vab N x (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wmem :> bytes(word 16392,4)])`,
  VA1_CALL_TAC (SPEC `t:int32` VE_TICK_DEC_CORRECT) VE_TICK_DEC_CALLEE `28`);;
(* ========================================================================= *)
(* Call sites of the vortex Fredkin pair (premise ve_vk_ok VK, as in         *)
(* ve_vort.ml; the final leaf discharges it with VE_VK_OK).                  *)
(* ========================================================================= *)

let VE_VORT_APPLY_CALLEE = WASM_CALLEE_RULE ve_vort_apply_mc;;
let VE_VORT_UNAPPLY_CALLEE = WASM_CALLEE_RULE ve_vort_unapply_mc;;

let VA1_VORT_LEAF th =
  let vk = `VK:(num->int32)->(num->int32)->num->int32` in
  let th1 = MP (SPEC vk th) (ASSUME (mk_comb(`ve_vk_ok`,vk))) in
  let th2 = SPECL [`N:num`; `mdl:num->int32`; `FST (x:(num->int32)#(num->int32))`;
                   `SND (x:(num->int32)#(num->int32))`] th1 in
  MP th2 (end_itlist CONJ (map ASSUME
    [`(mdl:num->int32) 1 = word N`; `1 <= N`; `N <= 640`]));;

let VA1_CALL_VA = prove
 (`!VK fs mc p gl t pt ap mdl N x.
     ve_vk_ok VK /\ mdl 1 = word N /\ 1 <= N /\
     fs 9 = (ve_vort_apply_mc,0,0) /\ p < 2 EXP 64 /\ N <= 640 /\
     wasm_decode mc p = SOME (Wcall 9,6)
     ==> ensures (wasmc fs)
          (\s. read wcode s = mc /\ read wpc s = word p /\ read wstatus s = WRunning /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_tick t (read wmem s) /\ va1_pop pt ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\ va1_vab N x (read wmem s))
          (\s. read wcode s = mc /\ read wpc s = word (p + 6) /\ read wstatus s = WRunning /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_tick t (read wmem s) /\ va1_pop pt ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\
               va1_vab N (ve_fredkin_fwd (VK mdl) x) (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wmem :> bytes(word 1114112,16384)] ,,
           MAYCHANGE [wmem :> bytes(word 1966080,73728)])`,
  VA1_CALL_TAC (VA1_VORT_LEAF VE_VORT_APPLY_FREDKIN) VE_VORT_APPLY_CALLEE `9`);;

let VA1_CALL_VU = prove
 (`!VK fs mc p gl t pt ap mdl N x.
     ve_vk_ok VK /\ mdl 1 = word N /\ 1 <= N /\
     fs 10 = (ve_vort_unapply_mc,0,0) /\ p < 2 EXP 64 /\ N <= 640 /\
     wasm_decode mc p = SOME (Wcall 10,6)
     ==> ensures (wasmc fs)
          (\s. read wcode s = mc /\ read wpc s = word p /\ read wstatus s = WRunning /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_tick t (read wmem s) /\ va1_pop pt ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\ va1_vab N x (read wmem s))
          (\s. read wcode s = mc /\ read wpc s = word (p + 6) /\ read wstatus s = WRunning /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_tick t (read wmem s) /\ va1_pop pt ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\
               va1_vab N (ve_fredkin_bwd (VK mdl) x) (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wmem :> bytes(word 1114112,16384)] ,,
           MAYCHANGE [wmem :> bytes(word 1966080,73728)])`,
  VA1_CALL_TAC (VA1_VORT_LEAF VE_VORT_UNAPPLY_FREDKIN) VE_VORT_UNAPPLY_CALLEE `10`);;
(* ========================================================================= *)
(* Vortex Echo purist a1 (lane hearth-call): the sequencer exports          *)
(* tick_forward / tick_backward of vortex_a1.wasm on the no-pop path, under *)
(* the module step wasmc (frame-free direct calls), composed through the    *)
(* calls from the 72fe0ba2 leaf theorems (ve_tick.ml, ve_vort.ml; premise    *)
(* ve_vk_ok VK as in ve_vort.ml) by the call-site lemmas VA1_CALL_*.         *)
(*                                                                           *)
(* No-pop path: pop tick (16396) = -1 and the auto pop (16512) is 0 or not  *)
(* the next tick. tick_forward = 16 x ve_vort_apply then ve_tick_inc,       *)
(* returns 1; tick_backward (tick <> 0) = ve_tick_dec then 16 x             *)
(* ve_vort_unapply, returns 1. VA1_TICK_INVERSE: backward on the state      *)
(* forward leaves restores the tick, VA and VB (j < 3N).                     *)
(* ========================================================================= *)

(* gt_u against the all-ones word is false (tick_backward's pop test) *)
let VA1_GTU_MAX = prove
 (`!u:int32. val u > 4294967295 <=> F`,
  GEN_TAC THEN MP_TAC(ISPEC `u:int32` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* ---- stepping a non-call instruction under wasmc, keeping named memory *)

let CAPC_STEP_TAC (_,decode_ths) extra sname =
  WASMC_BASIC_STEP_TAC decode_ths extra sname THEN
  CAP_MEM_UPDATE_TAC THEN
  ASSUMPTION_STATE_UPDATE_TAC THEN
  MAYCHANGE_STATE_UPDATE_TAC THEN
  DISCH_THEN(fun th ->
    let thl = STATE_UPDATE_NEW_RULE th in
    if thl = [] then ALL_TAC else
    MP_TAC(end_itlist CONJ thl) THEN
    CONV_TAC(LAND_CONV(DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV))) THEN
    STRIP_TAC);;

let CAPC_MSTEP_TAC execth sname (asl,w) =
  let mths = filter (fun th -> is_memfact (concl th)) (map snd asl) in
  (CAPC_STEP_TAC execth (READ_COMPONENT_COMPOSE :: VA1_GTU_MAX :: mths) sname THEN
   CAP_DISCARD_OLD_TAC sname) (asl,w);;

(* ---- name the memory of the current state; header facts also unfolded *)

let VA1_MEMNAME_TAC (mmname:string) : tactic = fun (asl,w) ->
  let s = rand w in
  let mmv = mk_var(mmname,`:int64->byte`) in
  (ABBREV_TAC (mk_eq(mmv, mk_comb(`read wmem`, s))) THEN
   POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
   (fun (asl,w) ->
      let hs = filter (fun th -> let c = concl th in
        try let h,args = strip_comb c in
            mem (fst(dest_const h)) ["va1_tick";"va1_pop"] && last args = mmv
        with Failure _ -> false) (map snd asl) in
      MAP_EVERY (STRIP_ASSUME_TAC o REWRITE_RULE[va1_tick; va1_pop]) hs (asl,w)))
  (asl,w);;

(* ---- a call: instantiate the call-site lemma from the current facts, go *)
(* through it (WASMC_BIGSTEP_LEMMA), carry what its frame leaves alone      *)

let VA1_CALLSITE_TAC (callth:thm) (dth:thm) (pc:int) (sname:string)
                     (mmname:string) : tactic = fun (asl,w) ->
  let s = rand w in
  let ths = map snd asl in
  let fs = rand(rand(rator(rator w))) in
  let mm = rhs(concl(find_read_th "wmem" s ths)) in
  let mc = rhs(concl(find_read_th "wcode" s ths)) in
  let gl = rhs(concl(find_read_th "wglobals" s ths)) in
  let findp name = concl(find (fun th -> let c = concl th in
     try let h,args = strip_comb c in fst(dest_const h) = name && last args = mm
     with Failure _ -> false) ths) in
  let _,targs = strip_comb(findp "va1_tick") in
  let _,pargs = strip_comb(findp "va1_pop") in
  let _,vargs = strip_comb(findp "va1_vab") in
  let inst v = match fst(dest_var v) with
      "fs" -> fs | "mc" -> mc | "p" -> mk_small_numeral pc | "gl" -> gl
    | "t" -> el 0 targs | "pt" -> el 0 pargs | "ap" -> el 1 pargs
    | "x" -> el 1 vargs | _ -> v in
  let vars = fst(strip_forall(concl callth)) in
  let th = CONV_RULE(DEPTH_CONV NUM_ADD_CONV) (SPECL (map inst vars) callth) in
  let sv = mk_var(sname,`:wasmstate`) in
  (MP_TAC th THEN ANTS_TAC THENL
    [ASM_REWRITE_TAC[dth] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
   MATCH_MP_TAC WASMC_BIGSTEP_LEMMA THEN CONJ_TAC THENL
    [BETA_TAC THEN ASM_REWRITE_TAC[] THEN FAIL_TAC "call-site precondition residual";
     BETA_TAC THEN X_GEN_TAC sv THEN
     REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
     GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [MAYCHANGE; SEQ_ID] THEN
     GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [GSYM SEQ_ASSOC] THEN
     GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_SEQ] THEN
     GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_THM] THEN
     REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
     ASSUMPTION_STATE_UPDATE_TAC THEN MAYCHANGE_STATE_UPDATE_TAC THEN
     DISCH_THEN(K ALL_TAC) THEN CAP_DISCARD_OLD_TAC sname THEN
     VA1_MEMNAME_TAC mmname]) (asl,w);;

(* ---- run: ordinary steps and call sites until WDone or a stop pc *)

let rec VA1_RUN_TAC execth (calls:(int*thm)list) (stops:int list) : tactic =
  fun (asl,w) ->
  let s = rand w in
  let ths = map snd asl in
  let is_done = exists (fun th ->
    concl th = mk_eq(mk_comb(`read wstatus`,s),`WDone`)) ths in
  if is_done then ALL_TAC (asl,w) else
  let pc = dest_small_numeral(rand(rhs(concl(find_read_th "wpc" s ths)))) in
  if mem pc stops then ALL_TAC (asl,w) else
  let n = fst(dest_var s) in
  let k = int_of_string(String.sub n 1 (String.length n - 1)) + 1 in
  let sname = "s"^string_of_int k in
  let dth = match (try (snd execth).(pc) with _ -> None) with
      Some th -> th
    | None -> failwith ("VA1_RUN_TAC: no decode at pc "^string_of_int pc) in
  let i = fst(dest_pair(rand(rhs(concl dth)))) in
  let step =
    if is_comb i && is_const(rator i) && fst(dest_const(rator i)) = "Wcall" then
      VA1_CALLSITE_TAC (assoc (dest_small_numeral(rand i)) calls) dth pc sname
        ("mm"^string_of_int k)
    else CAPC_MSTEP_TAC execth sname in
  (step THEN VA1_RUN_TAC execth calls stops) (asl,w);;

(* ---- n substeps unrolled: fwdn/bwdn (\i. g) n s for a numeral n *)

let rec VA1_ITER_CONV tm =
  match tm with
    Comb(Comb(Comb(Const(c,_),f),n),x)
      when (c = "ve_fredkin_fwdn" || c = "ve_fredkin_bwdn") && is_numeral n ->
      if dest_small_numeral n = 0 then
        GEN_REWRITE_CONV I [CONJUNCT1 VE_FREDKIN_FWDN_CLAUSES;
                            CONJUNCT1 VE_FREDKIN_BWDN_CLAUSES] tm
      else
        (RATOR_CONV(RAND_CONV num_CONV) THENC
         GEN_REWRITE_CONV I [CONJUNCT2 VE_FREDKIN_FWDN_CLAUSES;
                             CONJUNCT2 VE_FREDKIN_BWDN_CLAUSES] THENC
         TOP_DEPTH_CONV BETA_CONV THENC
         ONCE_DEPTH_CONV VA1_ITER_CONV) tm
  | _ -> failwith "VA1_ITER_CONV";;

let VA1_TICK_FORWARD_NOPOP = prove
 (`!VK fs gl t ap mdl N x.
     ve_vk_ok VK /\ mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
     fs 9 = (ve_vort_apply_mc,0,0) /\ fs 27 = (ve_tick_inc_mc,0,0) /\
     (ap = word 0 \/ ~(ap = word_add t (word 1)))
     ==> ensures (wasmc fs)
          (\s. read wcode s = va1_tick_forward_mc /\ read wpc s = word 3 /\
               read wstatus s = WRunning /\ read wstack s = [] /\
               read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_tick t (read wmem s) /\
               va1_pop (word 4294967295) ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\ va1_vab N x (read wmem s))
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 1)] /\
               va1_tick (word_add t (word 1)) (read wmem s) /\
               va1_pop (word 4294967295) ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\
               va1_vab N (ve_fredkin_fwdn (\i. VK mdl) 16 x) (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
           MAYCHANGE [wstatus] ,, MAYCHANGE [wlocal 0; wlocal 1; wlocal 2] ,,
           MAYCHANGE [wmem :> bytes(word 16392,4)] ,,
           MAYCHANGE [wmem :> bytes(word 1114112,16384)] ,,
           MAYCHANGE [wmem :> bytes(word 1966080,73728)])`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN VA1_MEMNAME_TAC "mm0" THEN
  VA1_RUN_TAC VA1_TICK_FORWARD_EXEC [9,VA1_CALL_VA; 27,VA1_CALL_TI] [273] THEN
  ASM_CASES_TAC `ap:int32 = word 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC;
    SUBGOAL_THEN `~(word_add t (word 1) = ap:int32)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC]] THEN
  VA1_RUN_TAC VA1_TICK_FORWARD_EXEC [9,VA1_CALL_VA; 27,VA1_CALL_TI] [] THEN
  ENSURES_FINAL_STATE_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV VA1_ITER_CONV) THEN ASM_REWRITE_TAC[]);;

let VA1_TICK_BACKWARD_NOPOP = prove
 (`!VK fs gl u ap mdl N y.
     ve_vk_ok VK /\ mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
     fs 10 = (ve_vort_unapply_mc,0,0) /\ fs 28 = (ve_tick_dec_mc,0,0) /\
     ~(u = word 0)
     ==> ensures (wasmc fs)
          (\s. read wcode s = va1_tick_backward_mc /\ read wpc s = word 3 /\
               read wstatus s = WRunning /\ read wstack s = [] /\
               read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_tick u (read wmem s) /\
               va1_pop (word 4294967295) ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\ va1_vab N y (read wmem s))
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 1)] /\
               va1_tick (word_sub u (word 1)) (read wmem s) /\
               va1_pop (word 4294967295) ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\
               va1_vab N (ve_fredkin_bwdn (\i. VK mdl) 16 y) (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
           MAYCHANGE [wstatus] ,, MAYCHANGE [wlocal 0; wlocal 1] ,,
           MAYCHANGE [wmem :> bytes(word 16392,4)] ,,
           MAYCHANGE [wmem :> bytes(word 1114112,16384)] ,,
           MAYCHANGE [wmem :> bytes(word 1966080,73728)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN VA1_MEMNAME_TAC "mm0" THEN
  VA1_RUN_TAC VA1_TICK_BACKWARD_EXEC [10,VA1_CALL_VU; 28,VA1_CALL_TD] [] THEN
  ENSURES_FINAL_STATE_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV VA1_ITER_CONV) THEN ASM_REWRITE_TAC[]);;

(* backward on the state forward leaves: tick, VA and VB restored *)
let VA1_TICK_INVERSE = prove
 (`!VK fs gl t ap mdl N x.
     ve_vk_ok VK /\ mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
     fs 10 = (ve_vort_unapply_mc,0,0) /\ fs 28 = (ve_tick_dec_mc,0,0) /\
     ~(word_add t (word 1) = word 0)
     ==> ensures (wasmc fs)
          (\s. read wcode s = va1_tick_backward_mc /\ read wpc s = word 3 /\
               read wstatus s = WRunning /\ read wstack s = [] /\
               read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_tick (word_add t (word 1)) (read wmem s) /\
               va1_pop (word 4294967295) ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\
               va1_vab N (ve_fredkin_fwdn (\i. VK mdl) 16 x) (read wmem s))
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 1)] /\
               va1_tick t (read wmem s) /\
               va1_pop (word 4294967295) ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\ va1_vab N x (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
           MAYCHANGE [wstatus] ,, MAYCHANGE [wlocal 0; wlocal 1] ,,
           MAYCHANGE [wmem :> bytes(word 16392,4)] ,,
           MAYCHANGE [wmem :> bytes(word 1114112,16384)] ,,
           MAYCHANGE [wmem :> bytes(word 1966080,73728)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`VK:(num->int32)->(num->int32)->num->int32`;
                `fs:num->byte list#num#num`; `gl:num->wval`;
                `word_add t (word 1):int32`; `ap:int32`; `mdl:num->int32`;
                `N:num`; `ve_fredkin_fwdn (\i. (VK:(num->int32)->(num->int32)->num->int32) mdl) 16 x`]
         VA1_TICK_BACKWARD_NOPOP) THEN
  ASM_REWRITE_TAC[FREDKIN_STEPS_INVERSE;
                  WORD_RULE `word_sub (word_add (t:int32) (word 1)) (word 1) = t`]);;
(* ========================================================================= *)
(* Final statements (lane hearth-call): the vortex_a1.wasm call targets are *)
(* the 72fe0ba2 bodies, and the sequencer theorems with the field premise   *)
(* discharged by VE_VK_OK (ve_vk.ml: ve_vk_ok ve_vk). Only that premise is  *)
(* discharged: the N bounds, fs entries, no-pop state and tick conditions   *)
(* stated in each theorem remain. (Comment corrected 2026-11-07.)           *)
(* ========================================================================= *)

let VA1_F9_IS_VORT_APPLY = prove
 (`va1_f9_mc = ve_vort_apply_mc`, REWRITE_TAC[va1_f9_mc; ve_vort_apply_mc]);;
let VA1_F10_IS_VORT_UNAPPLY = prove
 (`va1_f10_mc = ve_vort_unapply_mc`, REWRITE_TAC[va1_f10_mc; ve_vort_unapply_mc]);;
let VA1_F27_IS_TICK_INC = prove
 (`va1_f27_mc = ve_tick_inc_mc`, REWRITE_TAC[va1_f27_mc; ve_tick_inc_mc]);;
let VA1_F28_IS_TICK_DEC = prove
 (`va1_f28_mc = ve_tick_dec_mc`, REWRITE_TAC[va1_f28_mc; ve_tick_dec_mc]);;

let VA1_VK_TAC th =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(SPEC `ve_vk` th) THEN ASM_REWRITE_TAC[VE_VK_OK];;

let VA1_TICK_FORWARD_NOPOP_VK = prove
 (`!fs gl t ap mdl N x.
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
     fs 9 = (va1_f9_mc,0,0) /\ fs 27 = (va1_f27_mc,0,0) /\
     (ap = word 0 \/ ~(ap = word_add t (word 1)))
     ==> ensures (wasmc fs)
          (\s. read wcode s = va1_tick_forward_mc /\ read wpc s = word 3 /\
               read wstatus s = WRunning /\ read wstack s = [] /\
               read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_tick t (read wmem s) /\
               va1_pop (word 4294967295) ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\ va1_vab N x (read wmem s))
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 1)] /\
               va1_tick (word_add t (word 1)) (read wmem s) /\
               va1_pop (word 4294967295) ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\
               va1_vab N (ve_fredkin_fwdn (\i. ve_vk mdl) 16 x) (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
           MAYCHANGE [wstatus] ,, MAYCHANGE [wlocal 0; wlocal 1; wlocal 2] ,,
           MAYCHANGE [wmem :> bytes(word 16392,4)] ,,
           MAYCHANGE [wmem :> bytes(word 1114112,16384)] ,,
           MAYCHANGE [wmem :> bytes(word 1966080,73728)])`,
  REWRITE_TAC[VA1_F9_IS_VORT_APPLY; VA1_F27_IS_TICK_INC] THEN
  VA1_VK_TAC VA1_TICK_FORWARD_NOPOP);;

let VA1_TICK_BACKWARD_NOPOP_VK = prove
 (`!fs gl u ap mdl N y.
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
     fs 10 = (va1_f10_mc,0,0) /\ fs 28 = (va1_f28_mc,0,0) /\
     ~(u = word 0)
     ==> ensures (wasmc fs)
          (\s. read wcode s = va1_tick_backward_mc /\ read wpc s = word 3 /\
               read wstatus s = WRunning /\ read wstack s = [] /\
               read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_tick u (read wmem s) /\
               va1_pop (word 4294967295) ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\ va1_vab N y (read wmem s))
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 1)] /\
               va1_tick (word_sub u (word 1)) (read wmem s) /\
               va1_pop (word 4294967295) ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\
               va1_vab N (ve_fredkin_bwdn (\i. ve_vk mdl) 16 y) (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
           MAYCHANGE [wstatus] ,, MAYCHANGE [wlocal 0; wlocal 1] ,,
           MAYCHANGE [wmem :> bytes(word 16392,4)] ,,
           MAYCHANGE [wmem :> bytes(word 1114112,16384)] ,,
           MAYCHANGE [wmem :> bytes(word 1966080,73728)])`,
  REWRITE_TAC[VA1_F10_IS_VORT_UNAPPLY; VA1_F28_IS_TICK_DEC] THEN
  VA1_VK_TAC VA1_TICK_BACKWARD_NOPOP);;

let VA1_TICK_INVERSE_VK = prove
 (`!fs gl t ap mdl N x.
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
     fs 10 = (va1_f10_mc,0,0) /\ fs 28 = (va1_f28_mc,0,0) /\
     ~(word_add t (word 1) = word 0)
     ==> ensures (wasmc fs)
          (\s. read wcode s = va1_tick_backward_mc /\ read wpc s = word 3 /\
               read wstatus s = WRunning /\ read wstack s = [] /\
               read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_tick (word_add t (word 1)) (read wmem s) /\
               va1_pop (word 4294967295) ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\
               va1_vab N (ve_fredkin_fwdn (\i. ve_vk mdl) 16 x) (read wmem s))
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 1)] /\
               va1_tick t (read wmem s) /\
               va1_pop (word 4294967295) ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\ va1_vab N x (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
           MAYCHANGE [wstatus] ,, MAYCHANGE [wlocal 0; wlocal 1] ,,
           MAYCHANGE [wmem :> bytes(word 16392,4)] ,,
           MAYCHANGE [wmem :> bytes(word 1114112,16384)] ,,
           MAYCHANGE [wmem :> bytes(word 1966080,73728)])`,
  REWRITE_TAC[VA1_F10_IS_VORT_UNAPPLY; VA1_F28_IS_TICK_DEC] THEN
  VA1_VK_TAC VA1_TICK_INVERSE);;

(* the recursive helpers the statements use, pinned for the spec *)
let VA1_FWDN_CLAUSES = prove
 (parse_term ve_spec_VE_FREDKIN_FWDN_CLAUSES, REWRITE_TAC[VE_FREDKIN_FWDN_CLAUSES]);;
let VA1_BWDN_CLAUSES = prove
 (parse_term ve_spec_VE_FREDKIN_BWDN_CLAUSES, REWRITE_TAC[VE_FREDKIN_BWDN_CLAUSES]);;
let VA1_ISQ_CLAUSES = prove
 (parse_term ve_spec_VE_ISQ_CLAUSES, REWRITE_TAC[VE_ISQ_CLAUSES]);;
let VA1_VK_RS_CLAUSES = prove
 (parse_term ve_spec_VE_VK_RS_CLAUSES, REWRITE_TAC[VE_VK_RS_CLAUSES]);;
let VA1_VK_ACC_CLAUSES = prove
 (parse_term ve_spec_VE_VK_ACC_CLAUSES, REWRITE_TAC[VE_VK_ACC_CLAUSES]);;
let VA1_WDECL_VALS_CLAUSES = prove
 (`(!code pc. wdecl_vals 0 (code:byte list) pc = SOME ([]:wval list)) /\
   (!k code pc. wdecl_vals (SUC k) code pc =
      wobind (wuleb (wdrop pc code)) (\p.
      wobind (whd (wdrop (pc + SND p) code)) (\t.
      wobind (wdecl_vals k code (pc + SND p + 1)) (\r.
        SOME (APPEND (REPLICATE (FST p) (wzero_of (val (t:byte)))) r)))))`,
  REWRITE_TAC[wdecl_vals]);;
