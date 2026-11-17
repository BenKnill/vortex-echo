needs "ve_vort.ml";;
needs "ve_tick.ml";;
needs "ve_vk.ml";;
needs "va1_code.ml";;
needs "va1_seq_final2.ml";;
needs "pop_design_defs.ml";;
needs "pop_design_stmts.ml";;
needs "pop_l2_cdrift.ml";;
needs "pop_l3_jdrift.ml";;
needs "pop_l4_drop.ml";;
needs "pop_l1_rimd.ml";;
needs "pop_l1_rim.ml";;
needs "pop_l5_unbirth.ml";;
needs "pop_h1_hol.ml";;
needs "pop_n1_sat.ml";;
needs "pop_q0_calls.ml";;
needs "pop_q1_untick.ml";;
needs "pop_q2_forward.ml";;
needs "pop_r5_jig_defs.ml";;
needs "pop_r5jig_dec.ml";;
needs "pop_r5jig_lem.ml";;
needs "pop_r5_corr_defs.ml";;
needs "pop_r5c_lem.ml";;
needs "pop_r5b_bdec.ml";;
needs "pop_r5bp_lem.ml";;
needs "pop_r5bp_lem2.ml";;
needs "pop_r5bp_lem3.ml";;
needs "pop_r5bp_lem4.ml";;
needs "pop_r5bp_lem5b.ml";;
needs "pop_r5bp_lem6.ml";;
needs "pop_s0_end.ml";;
needs "pop_r5_r4c_final.ml";;
needs "chain_c1_host.ml";;
(* ========================================================================= *)
(* Vortex chain, rung C2, layer 1 of 2: pop definitions and one host call    *)
(* per pop tick (PROVE-C2, Claude Opus 5.5, 2026-11-11). Spec                *)
(* chain_c2_final.spec (frozen sha256 c7a0c0a8...). Definitions copied       *)
(* programmatically from the frozen spec; tick frames keep wmemsize,         *)
(* wglobals (and, for R0, wmem) and every byte outside the pop regions.      *)
(* Pure HOL over VA1_TICK_FORWARD_POP_R5C, VA1_TICK_POP_INVERSE_R5 and       *)
(* VA1_TICK_FORWARD_POP_END; no stepping, no decode rule, no mk_thm /        *)
(* new_axiom / CHEAT_TAC. Helpers carry prefix C2_.                          *)
(* ========================================================================= *)

let va1_fs_pop = new_definition `va1_fs_pop (fs:num->byte list#num#num) <=>
    fs 9 = (va1_f9_mc,0,0) /\ fs 10 = (va1_f10_mc,0,0) /\ fs 11 = (va1_f11_mc,0,0) /\
    fs 12 = (va1_f12_mc,0,0) /\ fs 13 = (va1_f13_mc,0,1) /\ fs 14 = (va1_f14_mc,0,1) /\
    fs 15 = (va1_f15_mc,0,0) /\ fs 16 = (va1_f16_mc,0,0) /\ fs 17 = (va1_f17_mc,1,0) /\
    fs 18 = (va1_f18_mc,1,0) /\ fs 19 = (va1_f19_mc,0,0) /\ fs 20 = (va1_f20_mc,0,0) /\
    fs 21 = (va1_f21_mc,0,0) /\ fs 22 = (va1_f22_mc,0,0) /\ fs 23 = (va1_f23_mc,0,0) /\
    fs 24 = (va1_f24_mc,0,0) /\ fs 27 = (va1_f27_mc,0,0) /\ fs 28 = (va1_f28_mc,0,0)`;;
let va1_diof = new_definition `va1_diof (S:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32) =
    FST(SND(SND(SND(SND S))))`;;
let va1_ndof = new_definition `va1_ndof (S:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32) =
    SND(SND(SND(SND(SND(SND(SND S))))))`;;
let va1_pop_reach = define `(!(mdl:num->int32) (hp:num->int32) (tbl:num->int32) (p:int32) (t0:int32)
    (S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32) S.
     va1_pop_reach mdl hp tbl p t0 S0 0 S <=> S = S0) /\
  (!(mdl:num->int32) (hp:num->int32) (tbl:num->int32) (p:int32) (t0:int32)
    (S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32) u S.
     va1_pop_reach mdl hp tbl p t0 S0 (SUC u) S <=>
     ?S' (L:(num->int32)list).
        va1_pop_reach mdl hp tbl p t0 S0 u S' /\
        ALL (\r. r 6 = word (val t0 + u + 1) /\ r 10 = word 0 /\ r 11 = word 0) L /\
        val (va1_ndof S') + LENGTH L <= 16384 /\
        S = va1_pop_fwd va1_ck va1_jigk L mdl hp tbl (word (val t0 + u)) p S')`;;
let VA1_POP_REACH_CLAUSES = prove
 (`(!(mdl:num->int32) (hp:num->int32) (tbl:num->int32) (p:int32) (t0:int32)
    (S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32) S.
     va1_pop_reach mdl hp tbl p t0 S0 0 S <=> S = S0) /\
  (!(mdl:num->int32) (hp:num->int32) (tbl:num->int32) (p:int32) (t0:int32)
    (S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32) u S.
     va1_pop_reach mdl hp tbl p t0 S0 (SUC u) S <=>
     ?S' (L:(num->int32)list).
        va1_pop_reach mdl hp tbl p t0 S0 u S' /\
        ALL (\r. r 6 = word (val t0 + u + 1) /\ r 10 = word 0 /\ r 11 = word 0) L /\
        val (va1_ndof S') + LENGTH L <= 16384 /\
        S = va1_pop_fwd va1_ck va1_jigk L mdl hp tbl (word (val t0 + u)) p S')`,
  ACCEPT_TAC va1_pop_reach);;
let va1_pop_at = new_definition `va1_pop_at (mdl:num->int32) (N:num) (p:int32) (ap:int32) (x0:(num->int32)#(num->int32))
             (hp:num->int32) (tbl:num->int32) (t0:int32)
             (S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32)
             (u:num) (m:int64->byte) <=>
    ?S. va1_pop_reach mdl hp tbl p t0 S0 u S /\
        va1_st (word (val t0 + u)) p ap mdl N (ITER u (ve_fredkin_fwd (ve_vk mdl)) x0) hp tbl S m`;;
let va1_pop_frame = new_definition `va1_pop_frame (m0:int64->byte) (m:int64->byte) <=>
    !a. a < 4194304 /\ ~(16392 <= a /\ a < 16396) /\ ~(16400 <= a /\ a < 16404) /\
        ~(1114112 <= a /\ a < 2039808)
        ==> read (bytes8 (word a)) m = read (bytes8 (word a)) m0`;;

(* ---- frames (C1 pattern) ---- *)

let C2_SEQ_KEEPS = prove
 (`!(d:(A,C)component) (r1:A->A->bool) (r2:A->A->bool).
     (!s s'. r1 s s' ==> read d s' = read d s) /\
     (!s s'. r2 s s' ==> read d s' = read d s)
     ==> !s s'. (r1 ,, r2) s s' ==> read d s' = read d s`,
  REWRITE_TAC[seq] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN MESON_TAC[]);;

let C2_ASSIGNS_KEEPS = prove
 (`!(c:(A,B)component) (d:(A,C)component).
     (!y s. read d (write c y s) = read d s)
     ==> !s s'. ASSIGNS c s s' ==> read d s' = read d s`,
  REWRITE_TAC[ASSIGNS_THM] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN MESON_TAC[]);;

let C2_COMP_TAC =
  REPEAT GEN_TAC THEN REWRITE_TAC[wlocal; READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE] THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN REWRITE_TAC[];;

let C2_KEEPS_TAC (comptac:tactic) =
  REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
  REPEAT(MATCH_MP_TAC C2_SEQ_KEEPS THEN CONJ_TAC) THEN
  MATCH_MP_TAC C2_ASSIGNS_KEEPS THEN comptac;;

let C2_B8_BYTES_OTHER = prove
 (`!a b n (y:num) (m:int64->byte).
     (a + 1 <= b \/ b + n <= a) /\ a + 1 < 2 EXP 64 /\ b + n < 2 EXP 64
     ==> read (bytes8 (word a)) (write (bytes(word b,n)) y m) =
         read (bytes8 (word a)) m`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC READ_WRITE_ORTHOGONAL_COMPONENTS THEN
  REWRITE_TAC[bytes8] THEN MATCH_MP_TAC ORTHOGONAL_COMPONENTS_SUB_LEFT THEN
  REWRITE_TAC[ORTHOGONAL_COMPONENTS_BYTES; DIMINDEX_64] THEN
  MATCH_MP_TAC NONOVERLAPPING_MODULO_SIMPLE THEN
  SUBGOAL_THEN `val(word a:int64) = a /\ val(word b:int64) = b`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let C2_BYTE_COMP_TAC =
  C2_COMP_TAC THEN
  TRY(MATCH_MP_TAC C2_B8_BYTES_OTHER THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

let c2_frame_of th = rand(snd(dest_imp(snd(strip_forall(concl th)))));;
let c2_fwd_frame = c2_frame_of VA1_TICK_FORWARD_POP_R5C;;
let c2_bwd_frame = c2_frame_of VA1_TICK_POP_INVERSE_R5;;
let c2_end_frame = c2_frame_of VA1_TICK_FORWARD_POP_END;;
let c2_fr fr tm = vsubst [fr, `cf:wasmstate->wasmstate->bool`] tm;;

let C2_KEEPS_MEMSIZE = `!s s'. (cf:wasmstate->wasmstate->bool) s s' ==> read wmemsize s' = read wmemsize s`;;
let C2_KEEPS_GLOBALS = `!s s'. (cf:wasmstate->wasmstate->bool) s s' ==> read wglobals s' = read wglobals s`;;
let C2_KEEPS_MEM = `!s s'. (cf:wasmstate->wasmstate->bool) s s' ==> read wmem s' = read wmem s`;;
let C2_KEEPS_BOTH = `!s s'. (cf:wasmstate->wasmstate->bool) s s'
   ==> read wmemsize s' = read wmemsize s /\ read wglobals s' = read wglobals s`;;
let C2_KEEPS_ALL3 = `!s s'. (cf:wasmstate->wasmstate->bool) s s'
   ==> read wmemsize s' = read wmemsize s /\ read wglobals s' = read wglobals s /\
       read wmem s' = read wmem s`;;
let C2_KEEPS_BYTE = `!a. a < 4194304 /\ ~(16392 <= a /\ a < 16396) /\ ~(16400 <= a /\ a < 16404) /\
     ~(1114112 <= a /\ a < 2039808)
     ==> !s s'. (cf:wasmstate->wasmstate->bool) s s'
                ==> read (wmem :> bytes8 (word a)) s' = read (wmem :> bytes8 (word a)) s`;;
let C2_FRAME_BYTES = `!s s'. (cf:wasmstate->wasmstate->bool) s s'
     ==> va1_pop_frame (read wmem s) (read wmem s')`;;

let VA1_R5F_MEMSIZE = prove(c2_fr c2_fwd_frame C2_KEEPS_MEMSIZE, C2_KEEPS_TAC C2_COMP_TAC);;
let VA1_R5F_GLOBALS = prove(c2_fr c2_fwd_frame C2_KEEPS_GLOBALS, C2_KEEPS_TAC C2_COMP_TAC);;
let VA1_R5B_MEMSIZE = prove(c2_fr c2_bwd_frame C2_KEEPS_MEMSIZE, C2_KEEPS_TAC C2_COMP_TAC);;
let VA1_R5B_GLOBALS = prove(c2_fr c2_bwd_frame C2_KEEPS_GLOBALS, C2_KEEPS_TAC C2_COMP_TAC);;
let VA1_R0_MEMSIZE = prove(c2_fr c2_end_frame C2_KEEPS_MEMSIZE, C2_KEEPS_TAC C2_COMP_TAC);;
let VA1_R0_GLOBALS = prove(c2_fr c2_end_frame C2_KEEPS_GLOBALS, C2_KEEPS_TAC C2_COMP_TAC);;
let VA1_R0_MEM = prove(c2_fr c2_end_frame C2_KEEPS_MEM, C2_KEEPS_TAC C2_COMP_TAC);;
let VA1_R5F_KEEPS = prove(c2_fr c2_fwd_frame C2_KEEPS_BOTH, MESON_TAC[VA1_R5F_MEMSIZE; VA1_R5F_GLOBALS]);;
let VA1_R5B_KEEPS = prove(c2_fr c2_bwd_frame C2_KEEPS_BOTH, MESON_TAC[VA1_R5B_MEMSIZE; VA1_R5B_GLOBALS]);;
let VA1_R0_KEEPS = prove(c2_fr c2_end_frame C2_KEEPS_ALL3,
  MESON_TAC[VA1_R0_MEMSIZE; VA1_R0_GLOBALS; VA1_R0_MEM]);;

let VA1_R5F_BYTE = prove(c2_fr c2_fwd_frame C2_KEEPS_BYTE,
  GEN_TAC THEN STRIP_TAC THEN C2_KEEPS_TAC C2_BYTE_COMP_TAC);;
let VA1_R5B_BYTE = prove(c2_fr c2_bwd_frame C2_KEEPS_BYTE,
  GEN_TAC THEN STRIP_TAC THEN C2_KEEPS_TAC C2_BYTE_COMP_TAC);;

let C2_FRAME_BYTES_TAC (bth:thm) =
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[va1_pop_frame] THEN
  X_GEN_TAC `a:num` THEN DISCH_TAC THEN
  MP_TAC(SPEC `a:num` bth) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:wasmstate`; `s':wasmstate`]) THEN
  ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE];;

let VA1_R5F_FRAME_BYTES = prove(c2_fr c2_fwd_frame C2_FRAME_BYTES, C2_FRAME_BYTES_TAC VA1_R5F_BYTE);;
let VA1_R5B_FRAME_BYTES = prove(c2_fr c2_bwd_frame C2_FRAME_BYTES, C2_FRAME_BYTES_TAC VA1_R5B_BYTE);;

let VA1_POP_FRAME_REFL = prove
 (`!m. va1_pop_frame m m`,
  REWRITE_TAC[va1_pop_frame]);;

let VA1_POP_FRAME_TRANS = prove
 (`!m0 m1 m2. va1_pop_frame m0 m1 /\ va1_pop_frame m1 m2 ==> va1_pop_frame m0 m2`,
  REWRITE_TAC[va1_pop_frame] THEN MESON_TAC[]);;

(* ---- the 8-tuple ---- *)

let C2_S8 = prove
 (`!S:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32.
     ?ra rb jq jp di zq zp nd. S = (ra,rb,jq,jp,di,zq,zp,nd)`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;

let C2_SPLIT_S_TAC =
  MP_TAC(ISPEC `S:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32` C2_S8) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`ra:num->int32`; `rb:num->int32`; `jq:num->int32`; `jp:num->int32`;
                       `di:num->int32`; `zq:num->int32`; `zp:num->int32`; `nd:int32`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[va1_diof; va1_ndof; FST; SND];;

(* ---- one host call per tick ---- *)

let C2_HCALL_TAC (r:term) (lth:thm) (cth:thm) (kths:thm list) : tactic =
  let _,[step;pp;qq;cc] = strip_comb(concl lth) in
  let eth,dth = CONJ_PAIR cth in
  let code = rand(lhand(concl eth)) and e = rand(rand(concl eth))
  and decls = rand(rand(concl dth)) in
  MATCH_MP_TAC (ISPECL [step; code; e; decls; `[]:wval list`; r; pp; qq; cc]
                  VA1_HCALL_ENSURES) THEN
  REWRITE_TAC[eth; dth; lth] THEN CONJ_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    ASM_REWRITE_TAC[WCALL_ENTRY_READS];
    REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
    MAP_EVERY (fun kth -> FIRST_ASSUM(MP_TAC o MATCH_MP kth) THEN
                          ASM_REWRITE_TAC[WCALL_ENTRY_READS] THEN DISCH_TAC) kths THEN
    ASM_REWRITE_TAC[] THEN
    TRY(EXISTS_TAC `L:(num->int32)list` THEN ASM_REWRITE_TAC[])];;

let C2_FWD_TAC kths =
  REPEAT GEN_TAC THEN C2_SPLIT_S_TAC THEN REWRITE_TAC[va1_fs_pop] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `t:int32`; `p:int32`; `ap:int32`;
                `mdl:num->int32`; `N:num`; `x:(num->int32)#(num->int32)`; `hp:num->int32`;
                `tbl:num->int32`; `ra:num->int32`; `rb:num->int32`; `jq:num->int32`; `jp:num->int32`;
                `di:num->int32`; `zq:num->int32`; `zp:num->int32`; `nd:int32`]
               VA1_TICK_FORWARD_POP_R5C) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun lth -> C2_HCALL_TAC `word 1:int32` lth VA1_TICKF_CALLEE kths);;

let C2_BWD_TAC kths =
  REPEAT GEN_TAC THEN C2_SPLIT_S_TAC THEN REWRITE_TAC[va1_fs_pop] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `t:int32`; `p:int32`; `ap:int32`;
                `mdl:num->int32`; `N:num`; `x:(num->int32)#(num->int32)`; `hp:num->int32`;
                `tbl:num->int32`; `ra:num->int32`; `rb:num->int32`; `jq:num->int32`; `jp:num->int32`;
                `di:num->int32`; `zq:num->int32`; `zp:num->int32`; `nd:int32`; `L:(num->int32)list`]
               VA1_TICK_POP_INVERSE_R5) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun lth -> C2_HCALL_TAC `word 1:int32` lth VA1_TICKB_CALLEE kths);;

let VA1_POP_HCALL_FWD = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (t:int32) (p:int32) (ap:int32) (mdl:num->int32) (N:num)
   (x:(num->int32)#(num->int32)) (hp:num->int32) (tbl:num->int32)
   (S:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32)
   (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_pop fs /\
     va1_pop_window t p /\ va1_log_ok t (va1_diof S) (va1_ndof S) /\
     va1_st t p ap mdl N x hp tbl S m
     ==> va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 1)
           (\gl' m'. gl' = gl /\
              ?L. ALL (\r. r 6 = word_add t (word 1) /\ r 10 = word 0 /\ r 11 = word 0) L /\
                  val (va1_ndof S) + LENGTH L <= 16384 /\
                  va1_st (word_add t (word 1)) p ap mdl N (ve_fredkin_fwd (ve_vk mdl) x) hp tbl
                         (va1_pop_fwd va1_ck va1_jigk L mdl hp tbl t p S) m') gl m`,
  C2_FWD_TAC [VA1_R5F_KEEPS]);;

let VA1_POP_HCALL_BWD = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (t:int32) (p:int32) (ap:int32) (mdl:num->int32) (N:num)
   (x:(num->int32)#(num->int32)) (hp:num->int32) (tbl:num->int32)
   (S:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32)
   (L:(num->int32)list) (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_pop fs /\
     va1_pop_window t p /\ va1_log_ok t (va1_diof S) (va1_ndof S) /\
     ALL (\r. r 6 = word_add t (word 1)) L /\ val (va1_ndof S) + LENGTH L <= 16384 /\
     va1_st (word_add t (word 1)) p ap mdl N (ve_fredkin_fwd (ve_vk mdl) x) hp tbl
            (va1_pop_fwd va1_ck va1_jigk L mdl hp tbl t p S) m
     ==> va1_hcall (wasmc fs) va1_tick_backward_mc [] (word 1)
           (\gl' m'. gl' = gl /\ va1_st t p ap mdl N x hp tbl S m') gl m`,
  C2_BWD_TAC [VA1_R5B_KEEPS]);;

let VA1_POP_HCALL_END = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (t:int32) (p:int32) (ap:int32) (m:int64->byte).
     ~(p = word 4294967295) /\ val p <= val t /\ val (word_add p (word 520)) <= val t /\
     va1_tick t m /\ va1_pop p ap m
     ==> va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 0) (\gl' m'. gl' = gl /\ m' = m) gl m`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `t:int32`; `p:int32`; `ap:int32`]
               VA1_TICK_FORWARD_POP_END) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun lth -> C2_HCALL_TAC `word 0:int32` lth VA1_TICKF_CALLEE [VA1_R0_KEEPS]));;

(* the same two calls, carrying the byte frame (used by the chain layer) *)
let C2_POP_HCALL_FWD_FRAME = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (t:int32) (p:int32) (ap:int32) (mdl:num->int32) (N:num)
   (x:(num->int32)#(num->int32)) (hp:num->int32) (tbl:num->int32)
   (S:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32)
   (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_pop fs /\
     va1_pop_window t p /\ va1_log_ok t (va1_diof S) (va1_ndof S) /\
     va1_st t p ap mdl N x hp tbl S m
     ==> va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 1)
           (\gl' m'. gl' = gl /\
              (?L. ALL (\r. r 6 = word_add t (word 1) /\ r 10 = word 0 /\ r 11 = word 0) L /\
                  val (va1_ndof S) + LENGTH L <= 16384 /\
                  va1_st (word_add t (word 1)) p ap mdl N (ve_fredkin_fwd (ve_vk mdl) x) hp tbl
                         (va1_pop_fwd va1_ck va1_jigk L mdl hp tbl t p S) m') /\
              va1_pop_frame m m') gl m`,
  C2_FWD_TAC [VA1_R5F_KEEPS; VA1_R5F_FRAME_BYTES]);;

let C2_POP_HCALL_BWD_FRAME = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (t:int32) (p:int32) (ap:int32) (mdl:num->int32) (N:num)
   (x:(num->int32)#(num->int32)) (hp:num->int32) (tbl:num->int32)
   (S:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32)
   (L:(num->int32)list) (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_pop fs /\
     va1_pop_window t p /\ va1_log_ok t (va1_diof S) (va1_ndof S) /\
     ALL (\r. r 6 = word_add t (word 1)) L /\ val (va1_ndof S) + LENGTH L <= 16384 /\
     va1_st (word_add t (word 1)) p ap mdl N (ve_fredkin_fwd (ve_vk mdl) x) hp tbl
            (va1_pop_fwd va1_ck va1_jigk L mdl hp tbl t p S) m
     ==> va1_hcall (wasmc fs) va1_tick_backward_mc [] (word 1)
           (\gl' m'. gl' = gl /\ va1_st t p ap mdl N x hp tbl S m' /\ va1_pop_frame m m') gl m`,
  C2_BWD_TAC [VA1_R5B_KEEPS; VA1_R5B_FRAME_BYTES]);;
