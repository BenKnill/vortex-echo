needs "ve_vort.ml";;
needs "ve_tick.ml";;
needs "ve_vk.ml";;
needs "va1_code.ml";;
needs "va1_seq_final2.ml";;
needs "chain_c1_host.ml";;
needs "chain_c1_np.ml";;
(* ========================================================================= *)
(* Vortex chain, rung C1, layer 3 of 3: the byte frame C1b (PROVE-C1,       *)
(* Claude Opus 5.5, 2026-11-11). Spec chain_c1_final.spec (frozen           *)
(* 3b62701f...). Definition va1_np_frame exactly as pinned; each tick frame *)
(* keeps every byte outside the clock word, VA/VB and the scratch area      *)
(* (component reasoning over the MAYCHANGE frames, B8_BYTES_OTHER after     *)
(* B32_BYTES_OTHER of va1_seq_final2.ml); the frame carried through scrub   *)
(* and film. Pure HOL; no stepping, no decode rule, no mk_thm / new_axiom.  *)
(* ========================================================================= *)

let va1_np_frame = new_definition
 `va1_np_frame (m0:int64->byte) (m:int64->byte) <=>
    !a. a < 4194304 /\ ~(16392 <= a /\ a < 16396) /\ ~(1114112 <= a /\ a < 1130496) /\
        ~(1966080 <= a /\ a < 2039808)
        ==> read (bytes8 (word a)) m = read (bytes8 (word a)) m0`;;

let C1_B8_BYTES_OTHER = prove
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

let C1_BYTE_COMP_TAC =
  C1_COMP_TAC THEN
  TRY(MATCH_MP_TAC C1_B8_BYTES_OTHER THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

let C1_KEEPS_BYTE = `!a. a < 4194304 /\ ~(16392 <= a /\ a < 16396) /\
     ~(1114112 <= a /\ a < 1130496) /\ ~(1966080 <= a /\ a < 2039808)
     ==> !s s'. (cf:wasmstate->wasmstate->bool) s s'
                ==> read (wmem :> bytes8 (word a)) s' = read (wmem :> bytes8 (word a)) s`;;

let VA1_NPF_BYTE = prove(c1_fr c1_npf_frame C1_KEEPS_BYTE,
  GEN_TAC THEN STRIP_TAC THEN C1_KEEPS_TAC C1_BYTE_COMP_TAC);;
let VA1_NPB_BYTE = prove(c1_fr c1_npb_frame C1_KEEPS_BYTE,
  GEN_TAC THEN STRIP_TAC THEN C1_KEEPS_TAC C1_BYTE_COMP_TAC);;

let C1_FRAME_BYTES = `!s s'. (cf:wasmstate->wasmstate->bool) s s'
     ==> va1_np_frame (read wmem s) (read wmem s')`;;

let C1_FRAME_BYTES_TAC (bth:thm) =
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[va1_np_frame] THEN
  X_GEN_TAC `a:num` THEN DISCH_TAC THEN
  MP_TAC(SPEC `a:num` bth) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:wasmstate`; `s':wasmstate`]) THEN
  ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE];;

let VA1_NPF_FRAME_BYTES = prove(c1_fr c1_npf_frame C1_FRAME_BYTES, C1_FRAME_BYTES_TAC VA1_NPF_BYTE);;
let VA1_NPB_FRAME_BYTES = prove(c1_fr c1_npb_frame C1_FRAME_BYTES, C1_FRAME_BYTES_TAC VA1_NPB_BYTE);;

let VA1_NP_FRAME_REFL = prove
 (`!m. va1_np_frame m m`,
  REWRITE_TAC[va1_np_frame]);;

let VA1_NP_FRAME_TRANS = prove
 (`!m0 m1 m2. va1_np_frame m0 m1 /\ va1_np_frame m1 m2 ==> va1_np_frame m0 m2`,
  REWRITE_TAC[va1_np_frame] THEN MESON_TAC[]);;

(* ---- one host call per tick, with the byte frame ---- *)

let VA1_NP_HCALL_FWD_FRAME = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (t:int32) (ap:int32) (mdl:num->int32) (N:num)
    (x:(num->int32)#(num->int32)) (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_np fs /\
     (ap = word 0 \/ ~(ap = word_add t (word 1))) /\ va1_np_st t ap mdl N x m
     ==> va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 1)
           (\gl' m'. gl' = gl /\ va1_np_st (word_add t (word 1)) ap mdl N (va1_swf mdl x) m' /\
                     va1_np_frame m m') gl m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_fs_np; va1_np_st] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `t:int32`; `ap:int32`;
                `mdl:num->int32`; `N:num`; `x:(num->int32)#(num->int32)`]
               VA1_TICK_FORWARD_NOPOP_VK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun lth -> C1_NP_HCALL_TAC lth VA1_TICKF_CALLEE
                          [VA1_NPF_KEEPS; VA1_NPF_FRAME_BYTES]));;

let VA1_NP_HCALL_BWD_FRAME = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (u:int32) (ap:int32) (mdl:num->int32) (N:num)
    (y:(num->int32)#(num->int32)) (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_np fs /\ ~(u = word 0) /\ va1_np_st u ap mdl N y m
     ==> va1_hcall (wasmc fs) va1_tick_backward_mc [] (word 1)
           (\gl' m'. gl' = gl /\ va1_np_st (word_sub u (word 1)) ap mdl N (va1_swb mdl y) m' /\
                     va1_np_frame m m') gl m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_fs_np; va1_np_st] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `u:int32`; `ap:int32`;
                `mdl:num->int32`; `N:num`; `y:(num->int32)#(num->int32)`]
               VA1_TICK_BACKWARD_NOPOP_VK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun lth -> C1_NP_HCALL_TAC lth VA1_TICKB_CALLEE
                          [VA1_NPB_KEEPS; VA1_NPB_FRAME_BYTES]));;

(* ---- scrub with the frame, relative to any m0 framing the start memory ---- *)

let C1_NP_SCRUB_FRAME_GEN = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (ap:int32)
    (x0:(num->int32)#(num->int32)) (kk:num) (m0:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_np fs /\ kk < 4294967296 /\
     (ap = word 0 \/ kk < val ap)
     ==> !(cs:bool list) (u:num) (m:int64->byte).
           u <= kk /\ va1_cmds_ok kk u cs /\
           va1_np_st (word u) ap mdl N (ITER u (va1_swf mdl) x0) m /\ va1_np_frame m0 m
           ==> va1_hrun (wasmc fs) cs
                 (\gl' m'. gl' = gl /\
                    va1_np_st (word (va1_cmds_end u cs)) ap mdl N
                              (ITER (va1_cmds_end u cs) (va1_swf mdl) x0) m' /\
                    va1_np_frame m0 m') gl m`,
  MAP_EVERY X_GEN_TAC
   [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`;
    `ap:int32`; `x0:(num->int32)#(num->int32)`; `kk:num`; `m0:int64->byte`] THEN
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
       va1_np_st (word (u + 1)) ap mdl N (ITER (u + 1) (va1_swf mdl) x0) m' /\
       va1_np_frame m m'` THEN
    CONJ_TAC THENL
     [REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `u < kk` THEN ARITH_TAC;
        MATCH_MP_TAC VA1_NP_FRAME_TRANS THEN EXISTS_TAC `m:int64->byte` THEN
        ASM_REWRITE_TAC[]];
      MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `word u:int32`; `ap:int32`;
        `mdl:num->int32`; `N:num`; `ITER u (va1_swf mdl) x0`; `m:int64->byte`]
        VA1_NP_HCALL_FWD_FRAME) THEN
      REWRITE_TAC[C1_WORD_ADD1; C1_SWF_ITER] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC C1_AUTO_FWD THEN
      EXISTS_TAC `kk:num` THEN ASM_REWRITE_TAC[]];
    EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\
       va1_np_st (word (u - 1)) ap mdl N (ITER (u - 1) (va1_swf mdl) x0) m' /\
       va1_np_frame m m'` THEN
    CONJ_TAC THENL
     [REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `u <= kk` THEN ARITH_TAC;
        MATCH_MP_TAC VA1_NP_FRAME_TRANS THEN EXISTS_TAC `m:int64->byte` THEN
        ASM_REWRITE_TAC[]];
      MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `word u:int32`; `ap:int32`;
        `mdl:num->int32`; `N:num`; `ITER u (va1_swf mdl) x0`; `m:int64->byte`]
        VA1_NP_HCALL_BWD_FRAME) THEN
      SUBGOAL_THEN `word_sub (word u) (word 1):int32 = word (u - 1) /\
                    va1_swb mdl (ITER u (va1_swf mdl) x0) = ITER (u - 1) (va1_swf mdl) x0`
        (fun th -> REWRITE_TAC[th]) THENL
       [ASM_SIMP_TAC[C1_WORD_SUB1; C1_SWB_ITER]; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC C1_WORD_NZ THEN EXISTS_TAC `kk:num` THEN ASM_REWRITE_TAC[]]]);;

let VA1_NP_SCRUB_FRAME = prove
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
                              (ITER (va1_cmds_end u cs) (va1_swf mdl) x0) m' /\
                    va1_np_frame m m') gl m`,
  MAP_EVERY X_GEN_TAC
   [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`;
    `ap:int32`; `x0:(num->int32)#(num->int32)`; `kk:num`] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`cs:bool list`; `u:num`; `m:int64->byte`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`;
    `ap:int32`; `x0:(num->int32)#(num->int32)`; `kk:num`; `m:int64->byte`]
    C1_NP_SCRUB_FRAME_GEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`cs:bool list`; `u:num`; `m:int64->byte`]) THEN
  ASM_REWRITE_TAC[VA1_NP_FRAME_REFL]);;

let VA1_NP_FILM_BYTES = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num)
   (x0:(num->int32)#(num->int32)) (n:num) (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_np fs /\ n < 4294967296 /\
     va1_np_st (word 0) (word 0) mdl N x0 m
     ==> va1_hrun (wasmc fs) (APPEND (REPLICATE n T) (REPLICATE n F))
           (\gl' m'. gl' = gl /\ va1_np_st (word 0) (word 0) mdl N x0 m' /\ va1_np_frame m m') gl m`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`;
    `word 0:int32`; `x0:(num->int32)#(num->int32)`; `n:num`] VA1_NP_SCRUB_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`APPEND (REPLICATE n T) (REPLICATE n F)`; `0`; `m:int64->byte`]) THEN
  ASM_SIMP_TAC C1_FILM_SIMPS);;
