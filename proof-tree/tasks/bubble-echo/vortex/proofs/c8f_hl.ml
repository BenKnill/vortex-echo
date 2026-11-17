(* c8f_hl.ml (vortex-chain C8f, Claude Opus 5.5, 2026-11-15): the C8f headline theorems. *)
let C8F_POPWIN = prove
 (`!sg0:num->int32 K. va1_dom sg0 /\ va1_kind sg0 = 1 /\ val (sg0 3) + 520 < 4294967296 /\ val (sg0 2) + K <= val (sg0 3) + 520
     ==> !i. i < K ==> va1_dom (ITER i va1_fwd sg0) /\ va1_kind (ITER i va1_fwd sg0) = 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(SPEC `sg0:num->int32` C8F_POP_ITER) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;
let VA1_POP_SCRUB_N = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (sg0:num->int32) (K:num).
     va1_fs_all fs /\ va1_dom sg0 /\ va1_kind sg0 = 1 /\
     val (sg0 3) + 520 < 4294967296 /\ val (sg0 2) + K <= val (sg0 3) + 520
     ==> !(cs:bool list) (u:num) (m:int64->byte).
           u <= K /\ va1_cmds_ok K u cs /\ va1_snap m = ITER u va1_fwd sg0
           ==> va1_hrun (wasmc fs) cs
                 (\gl' m'. gl' = gl /\ va1_snap m' = ITER (va1_cmds_end u cs) va1_fwd sg0) gl m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `K:num`; `sg0:num->int32`] C8F_WALK) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC C8F_POPWIN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MATCH_MP_TAC th THEN ASM_REWRITE_TAC[]));;
let VA1_POP_CHAIN_N = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (sg0:num->int32) (k:num) (m:int64->byte).
     va1_fs_all fs /\ va1_dom sg0 /\ va1_kind sg0 = 1 /\
     val (sg0 3) + 520 < 4294967296 /\ val (sg0 2) + k <= val (sg0 3) + 520 /\ va1_snap m = sg0
     ==> va1_hrun (wasmc fs) (REPLICATE k T)
           (\gl1 m1. gl1 = gl /\ va1_snap m1 = ITER k va1_fwd sg0 /\
              va1_hrun (wasmc fs) (REPLICATE k F) (\gl2 m2. gl2 = gl /\ va1_snap m2 = sg0) gl1 m1) gl m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`sg0:num->int32`; `k:num`] C8F_POPWIN) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC VA1_HRUN_MONO THEN
  EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\ va1_snap m' = ITER k va1_fwd sg0` THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`g:num->wval`; `x:int64->byte`] THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC C8F_BWD_RUN_C THEN ASM_SIMP_TAC[ARITH_RULE `~(1 = 3)`];
    MATCH_MP_TAC C8F_FWD_RUN_C THEN ASM_SIMP_TAC[]]);;
let VA1_POP_CHAIN_TO_END_N = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (sg0:num->int32) (m:int64->byte).
     va1_fs_all fs /\ va1_dom sg0 /\ va1_kind sg0 = 1 /\ sg0 2 = sg0 3 /\
     val (sg0 3) + 520 < 4294967296 /\ va1_snap m = sg0
     ==> va1_hrun (wasmc fs) (REPLICATE 520 T)
           (\gl1 m1. gl1 = gl /\ va1_snap m1 = ITER 520 va1_fwd sg0 /\
              va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 0)
                (\gl2 m2. gl2 = gl1 /\ m2 = m1 /\
                   va1_hrun (wasmc fs) (REPLICATE 520 F) (\gl3 m3. gl3 = gl /\ va1_snap m3 = sg0) gl2 m2) gl1 m1) gl m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`sg0:num->int32`; `520`] C8F_POPWIN) THEN ASM_REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
  MP_TAC(SPEC `sg0:num->int32` C8F_POP_ITER) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `520`) THEN
  ASM_REWRITE_TAC[LE_REFL; LT_REFL] THEN STRIP_TAC THEN
  MATCH_MP_TAC VA1_HRUN_MONO THEN
  EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\ va1_snap m' = ITER 520 va1_fwd sg0` THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`g:num->wval`; `x:int64->byte`] THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC VA1_HCALL_MONO THEN EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\ m' = (x:int64->byte)` THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC C8F_BWD_RUN_C THEN ASM_SIMP_TAC[ARITH_RULE `~(1 = 3)`];
      SUBGOAL_THEN `val (va1_snap (x:int64->byte) 65) <= 640` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[va1_dom]; ALL_TAC] THEN
      MP_TAC(SPEC `x:int64->byte` C8E_SNAP_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MATCH_MP_TAC VA1_POP_HCALL_END THEN
      MAP_EVERY EXISTS_TAC [`va1_snap (x:int64->byte) 2`; `va1_snap (x:int64->byte) 3`; `va1_snap (x:int64->byte) 32`] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~((sg0:num->int32) 3 = word 4294967295)` ASSUME_TAC THENL
       [UNDISCH_TAC `va1_kind sg0 = 1` THEN REWRITE_TAC[va1_kind] THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ]; ALL_TAC] THEN
      ASM_SIMP_TAC[C8F_VAL_ADD] THEN ASM_ARITH_TAC];
    MATCH_MP_TAC C8F_FWD_RUN_C THEN ASM_SIMP_TAC[]]);;
let C8F_SG0_TAC : tactic =
  MP_TAC(SPECL [`word 0:int32`; `word K:int32`; `mdl:num->int32`; `N:num`; `x0:(num->int32)#(num->int32)`; `m0:int64->byte`] C8F_START) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `val (word N:int32) = N` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `m0:int64->byte` C8E_SNAP_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC;;
let VA1_FILM_AUTO_N = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num)
   (x0:(num->int32)#(num->int32)) (K:num) (n:num) (m0:int64->byte).
     va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\ fs 33 = (va1_puncture_mc,3,1) /\
     fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\ gl 0 = I32 (word 16384) /\
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ 1 <= K /\ K + 520 < 4294967296 /\ n <= 520 /\
     va1_np_st (word 0) (word K) mdl N x0 m0 /\ va1_clean m0 /\
     ~(read (bytes32 (word 16516)) m0 = word 0 /\ read (bytes32 (word 16520)) m0 = word 0 /\
       read (bytes32 (word 16524)) m0 = word 0)
     ==> va1_hrun (wasmn fs) (REPLICATE (K + n) T)
           (\gl1 m1. gl1 = gl /\ va1_snap m1 = ITER (K + n) va1_fwd (va1_snap m0) /\
              va1_hrun (wasmn fs) (REPLICATE (n + K) F)
                (\gl3 m3. gl3 = gl /\ va1_film_bytes_s m0 m3) gl1 m1) gl m0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C8F_SG0_TAC THEN
  SUBGOAL_THEN `va1_fs_all fs` ASSUME_TAC THENL [ASM_REWRITE_TAC[va1_fs_all]; ALL_TAC] THEN
  MP_TAC(SPECL [`va1_snap (m0:int64->byte)`; `K:num`] C8F_AUTO_ALL) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`; `x0:(num->int32)#(num->int32)`;
                `K:num`; `n:num`; `m0:int64->byte`] VA1_FILM_AUTO) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[APPEND_ASSOC] THEN REWRITE_TAC[C8F_REP_APPEND] THEN REWRITE_TAC[VA1_HRUN_APPEND] THEN DISCH_TAC THEN
  SUBGOAL_THEN `va1_hrun (wasmn fs) (REPLICATE (K + n) T)
     (\gl1 m1. gl1 = gl /\ va1_snap m1 = ITER (K + n) va1_fwd (va1_snap m0) /\
        va1_hrun (wasmn fs) (REPLICATE (n + K) F) (\gl3 m3. gl3 = gl /\ va1_snap m3 = va1_snap (m0:int64->byte)) gl1 m1) gl m0`
    ASSUME_TAC THENL
   [MATCH_MP_TAC VA1_HRUN_MONO THEN
    EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\ va1_snap m' = ITER (K + n) va1_fwd (va1_snap (m0:int64->byte))` THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`g:num->wval`; `x:int64->byte`] THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC C8F_TO_N THEN ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_MP_TAC C8F_BWD_RUN_C THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      MATCH_MP_TAC C8F_FWD_RUN_N THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]; ALL_TAC] THEN
  C8F_BOTH_TAC (c8f_has "va1_film_bytes") (c8f_has "ITER") THEN
  MAP_EVERY X_GEN_TAC [`g:num->wval`; `x:int64->byte`] THEN BETA_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try lhs(concl th) = `g:num->wval` with _ -> false)) THEN ASM_REWRITE_TAC[] THEN
  C8F_BOTH_TAC (c8f_has "va1_film_bytes") (fun t -> not (c8f_has "va1_film_bytes" t)) THEN
  MAP_EVERY X_GEN_TAC [`g3:num->wval`; `x3:int64->byte`] THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C8F_FB THEN EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[]);;
let C8F_END_N = prove
 (`!K fs gl (m:int64->byte). va1_snap m 3 = word K /\ val (va1_snap m 2) = K + 520 /\ K + 520 < 4294967296 /\
     val (va1_snap m 65) <= 640
     ==> va1_hcall (wasmn fs) va1_tick_forward_mc [] (word 0) (\gl' m'. gl' = gl /\ m' = m) gl m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC C8E_TO_WASMN THEN
  MP_TAC(SPEC `m:int64->byte` C8E_SNAP_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC VA1_POP_HCALL_END THEN
  MAP_EVERY EXISTS_TAC [`va1_snap (m:int64->byte) 2`; `va1_snap (m:int64->byte) 3`; `va1_snap (m:int64->byte) 32`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `val (word K:int32) = K` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[C8F_VAL_ADD; ARITH_RULE `K + 520 < 4294967296 ==> K + 520 < 4294967296`] THEN
  CONJ_TAC THENL [DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;
let VA1_FILM_AUTO_TO_END_N = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num)
   (x0:(num->int32)#(num->int32)) (K:num) (m0:int64->byte).
     va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\ fs 33 = (va1_puncture_mc,3,1) /\
     fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\ gl 0 = I32 (word 16384) /\
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ 1 <= K /\ K + 520 < 4294967296 /\
     va1_np_st (word 0) (word K) mdl N x0 m0 /\ va1_clean m0 /\
     ~(read (bytes32 (word 16516)) m0 = word 0 /\ read (bytes32 (word 16520)) m0 = word 0 /\
       read (bytes32 (word 16524)) m0 = word 0)
     ==> va1_hrun (wasmn fs) (REPLICATE (K + 520) T)
           (\gl3 m3. gl3 = gl /\ va1_snap m3 = ITER (K + 520) va1_fwd (va1_snap m0) /\
              va1_hcall (wasmn fs) va1_tick_forward_mc [] (word 0)
                (\gl4 m4. gl4 = gl3 /\ m4 = m3 /\
                   va1_hrun (wasmn fs) (REPLICATE (520 + K) F)
                     (\gl5 m5. gl5 = gl /\ va1_film_bytes_s m0 m5) gl4 m4) gl3 m3) gl m0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C8F_SG0_TAC THEN
  SUBGOAL_THEN `va1_fs_all fs` ASSUME_TAC THENL [ASM_REWRITE_TAC[va1_fs_all]; ALL_TAC] THEN
  MP_TAC(SPECL [`va1_snap (m0:int64->byte)`; `K:num`] C8F_AUTO_ALL) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`; `x0:(num->int32)#(num->int32)`;
                `K:num`; `m0:int64->byte`] VA1_FILM_AUTO_TO_END) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[C8F_REP_APPEND] THEN DISCH_TAC THEN
  SUBGOAL_THEN `va1_hrun (wasmn fs) (REPLICATE (K + 520) T)
     (\gl3 m3. gl3 = gl /\ va1_snap m3 = ITER (K + 520) va1_fwd (va1_snap m0) /\
        va1_hcall (wasmn fs) va1_tick_forward_mc [] (word 0)
          (\gl4 m4. gl4 = gl3 /\ m4 = m3 /\
             va1_hrun (wasmn fs) (REPLICATE (520 + K) F) (\gl5 m5. gl5 = gl /\ va1_snap m5 = va1_snap (m0:int64->byte)) gl4 m4) gl3 m3) gl m0`
    ASSUME_TAC THENL
   [MATCH_MP_TAC VA1_HRUN_MONO THEN
    EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\ va1_snap m' = ITER (K + 520) va1_fwd (va1_snap (m0:int64->byte))` THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`g:num->wval`; `x:int64->byte`] THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC VA1_HCALL_MONO THEN EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\ m' = (x:int64->byte)` THEN CONJ_TAC THENL
       [REPEAT GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC C8F_TO_N THEN ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_MP_TAC C8F_BWD_RUN_C THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC C8F_END_N THEN EXISTS_TAC `K:num` THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC C8F_FWD_RUN_N THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  C8F_BOTH_TAC (c8f_has "va1_film_bytes") (c8f_has "ITER") THEN
  MAP_EVERY X_GEN_TAC [`g:num->wval`; `x:int64->byte`] THEN BETA_TAC THEN STRIP_TAC THEN
  C8F_GSUB_TAC `g:num->wval` THEN ASM_REWRITE_TAC[] THEN
  C8F_HBOTH_TAC (c8f_has "va1_film_bytes") (fun t -> not (c8f_has "va1_film_bytes" t)) THEN
  MAP_EVERY X_GEN_TAC [`g4:num->wval`; `x4:int64->byte`] THEN BETA_TAC THEN STRIP_TAC THEN
  C8F_GSUB_TAC `g4:num->wval` THEN C8F_GSUB_TAC `x4:int64->byte` THEN ASM_REWRITE_TAC[] THEN
  C8F_BOTH_TAC (c8f_has "va1_film_bytes") (fun t -> not (c8f_has "va1_film_bytes" t)) THEN
  MAP_EVERY X_GEN_TAC [`g5:num->wval`; `x5:int64->byte`] THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C8F_FB THEN EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[]);;
let VA1_FILM_CLICK_N = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (ap:int32)
   (x0:(num->int32)#(num->int32)) (K:num) (n:num) (m0:int64->byte) (a0:int32) (a1:int32) (a2:int32).
     va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\ fs 33 = (va1_puncture_mc,3,1) /\
     fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\ gl 0 = I32 (word 16384) /\
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ 1 <= K /\ K + 520 < 4294967296 /\ n <= 520 /\
     (ap = word 0 \/ K < val ap) /\ va1_np_st (word 0) ap mdl N x0 m0 /\ va1_clean m0 /\
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0)
     ==> va1_hrun (wasmc fs) (REPLICATE K T)
           (\gl1 m1. gl1 = gl /\ va1_snap m1 = ITER K va1_fwd (va1_snap m0) /\
              va1_hcall (wasmc fs) va1_puncture_mc [I32 a2; I32 a1; I32 a0] (word 0)
                (\gl2 m2. gl2 = gl /\ va1_snap m2 = va1_clk a0 a1 a2 (ITER K va1_fwd (va1_snap m0)) /\
                   va1_hrun (wasmc fs) (REPLICATE n T)
                     (\gl3 m3. gl3 = gl /\
                        va1_snap m3 = ITER n va1_fwd (va1_clk a0 a1 a2 (ITER K va1_fwd (va1_snap m0))) /\
                        va1_hrun (wasmc fs) (REPLICATE (n + K) F)
                          (\gl4 m4. gl4 = gl /\ va1_film_bytes_s m0 m4) gl3 m3) gl2 m2) gl1 m1) gl m0`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN C8F_SG0C_TAC THEN
  SUBGOAL_THEN `va1_fs_all fs` ASSUME_TAC THENL [ASM_REWRITE_TAC[va1_fs_all]; ALL_TAC] THEN
  MP_TAC(SPECL [`va1_snap (m0:int64->byte)`; `K:num`; `a0:int32`; `a1:int32`; `a2:int32`] C8F_CLICK_POP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a0:int32`; `a1:int32`; `a2:int32`; `ITER K va1_fwd (va1_snap (m0:int64->byte))`] C8F_CLK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `val (word K:int32) = K` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`; `ap:int32`; `x0:(num->int32)#(num->int32)`;
                `K:num`; `n:num`; `m0:int64->byte`; `a0:int32`; `a1:int32`; `a2:int32`] VA1_FILM_CLICK) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VA1_HRUN_APPEND] THEN DISCH_TAC THEN
  SUBGOAL_THEN `va1_hrun (wasmc fs) (REPLICATE K T)
           (\gl1 m1. gl1 = gl /\ va1_snap m1 = ITER K va1_fwd (va1_snap m0) /\
              va1_hcall (wasmc fs) va1_puncture_mc [I32 a2; I32 a1; I32 a0] (word 0)
                (\gl2 m2. gl2 = gl /\ va1_snap m2 = va1_clk a0 a1 a2 (ITER K va1_fwd (va1_snap m0)) /\
                   va1_hrun (wasmc fs) (REPLICATE n T)
                     (\gl3 m3. gl3 = gl /\
                        va1_snap m3 = ITER n va1_fwd (va1_clk a0 a1 a2 (ITER K va1_fwd (va1_snap m0))) /\
                        va1_hrun (wasmc fs) (REPLICATE (n + K) F)
                          (\gl4 m4. gl4 = gl /\ va1_snap m4 = va1_snap (m0:int64->byte)) gl3 m3) gl2 m2) gl1 m1) gl m0`
    ASSUME_TAC THENL
   [MATCH_MP_TAC VA1_HRUN_MONO THEN
    EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\ va1_snap m' = ITER K va1_fwd (va1_snap (m0:int64->byte))` THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`g:num->wval`; `x:int64->byte`] THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC VA1_HCALL_MONO THEN
      EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\ va1_snap m' = va1_clk a0 a1 a2 (va1_snap (x:int64->byte))` THEN CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`g2:num->wval`; `y:int64->byte`] THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC VA1_HRUN_MONO THEN
        EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\
                    va1_snap m' = ITER n va1_fwd (va1_clk a0 a1 a2 (ITER K va1_fwd (va1_snap (m0:int64->byte))))` THEN
        CONJ_TAC THENL
         [MAP_EVERY X_GEN_TAC [`g3:num->wval`; `z:int64->byte`] THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC C8F_CLICK_BACK THEN MAP_EVERY EXISTS_TAC [`a0:int32`; `a1:int32`; `a2:int32`] THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
          MATCH_MP_TAC C8F_FWD_RUN_C THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) && c8f_has "va1_clk" (concl th) && c8f_has "va1_kind" (concl th))) THEN
          ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]];
        MATCH_MP_TAC C8F_CLK_HOST THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(SPECL [`K:num`; `0`] C8F_WORD_INJ) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC]];
      MATCH_MP_TAC C8F_FWD_RUN_C THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) && c8f_has "va1_kind" (concl th) &&
        not (c8f_has "va1_clk" (concl th)))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]]; ALL_TAC] THEN
  C8F_BOTH_TAC (c8f_has "va1_film_bytes") (c8f_has "ITER") THEN
  MAP_EVERY X_GEN_TAC [`g:num->wval`; `x:int64->byte`] THEN BETA_TAC THEN STRIP_TAC THEN
  C8F_GSUB_TAC `g:num->wval` THEN ASM_REWRITE_TAC[] THEN
  C8F_HBOTH_TAC (c8f_has "va1_film_bytes") (fun t -> not (c8f_has "va1_film_bytes" t)) THEN
  MAP_EVERY X_GEN_TAC [`g2:num->wval`; `y:int64->byte`] THEN BETA_TAC THEN STRIP_TAC THEN
  C8F_GSUB_TAC `g2:num->wval` THEN ASM_REWRITE_TAC[] THEN
  C8F_BOTH_TAC (c8f_has "va1_film_bytes") (fun t -> not (c8f_has "va1_film_bytes" t)) THEN
  MAP_EVERY X_GEN_TAC [`g3:num->wval`; `z:int64->byte`] THEN BETA_TAC THEN STRIP_TAC THEN
  C8F_GSUB_TAC `g3:num->wval` THEN ASM_REWRITE_TAC[] THEN
  C8F_BOTH_TAC (c8f_has "va1_film_bytes") (fun t -> not (c8f_has "va1_film_bytes" t)) THEN
  MAP_EVERY X_GEN_TAC [`g4:num->wval`; `w4:int64->byte`] THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C8F_FB THEN EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[]);;
let VA1_FILM_CLICK_TO_END_N = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (ap:int32)
   (x0:(num->int32)#(num->int32)) (K:num) (m0:int64->byte) (a0:int32) (a1:int32) (a2:int32).
     va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\ fs 33 = (va1_puncture_mc,3,1) /\
     fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\ gl 0 = I32 (word 16384) /\
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ 1 <= K /\ K + 520 < 4294967296 /\
     (ap = word 0 \/ K < val ap) /\ va1_np_st (word 0) ap mdl N x0 m0 /\ va1_clean m0 /\
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0)
     ==> va1_hrun (wasmc fs) (REPLICATE K T)
           (\gl1 m1. gl1 = gl /\ va1_snap m1 = ITER K va1_fwd (va1_snap m0) /\
              va1_hcall (wasmc fs) va1_puncture_mc [I32 a2; I32 a1; I32 a0] (word 0)
                (\gl2 m2. gl2 = gl /\ va1_snap m2 = va1_clk a0 a1 a2 (ITER K va1_fwd (va1_snap m0)) /\
                   va1_hrun (wasmc fs) (REPLICATE 520 T)
                     (\gl3 m3. gl3 = gl /\
                        va1_snap m3 = ITER 520 va1_fwd (va1_clk a0 a1 a2 (ITER K va1_fwd (va1_snap m0))) /\
                        va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 0)
                          (\gl4 m4. gl4 = gl3 /\ m4 = m3 /\
                             va1_hrun (wasmc fs) (REPLICATE (520 + K) F)
                               (\gl5 m5. gl5 = gl /\ va1_film_bytes_s m0 m5) gl4 m4) gl3 m3) gl2 m2) gl1 m1) gl m0`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN C8F_SG0C_TAC THEN
  SUBGOAL_THEN `va1_fs_all fs` ASSUME_TAC THENL [ASM_REWRITE_TAC[va1_fs_all]; ALL_TAC] THEN
  MP_TAC(SPECL [`va1_snap (m0:int64->byte)`; `K:num`; `a0:int32`; `a1:int32`; `a2:int32`] C8F_CLICK_POP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a0:int32`; `a1:int32`; `a2:int32`; `ITER K va1_fwd (va1_snap (m0:int64->byte))`] C8F_CLK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `val (word K:int32) = K` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `mdl:num->int32`; `N:num`; `ap:int32`; `x0:(num->int32)#(num->int32)`;
                `K:num`; `m0:int64->byte`; `a0:int32`; `a1:int32`; `a2:int32`] VA1_FILM_CLICK_TO_END) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VA1_HRUN_APPEND] THEN DISCH_TAC THEN
  SUBGOAL_THEN `va1_hrun (wasmc fs) (REPLICATE K T)
           (\gl1 m1. gl1 = gl /\ va1_snap m1 = ITER K va1_fwd (va1_snap m0) /\
              va1_hcall (wasmc fs) va1_puncture_mc [I32 a2; I32 a1; I32 a0] (word 0)
                (\gl2 m2. gl2 = gl /\ va1_snap m2 = va1_clk a0 a1 a2 (ITER K va1_fwd (va1_snap m0)) /\
                   va1_hrun (wasmc fs) (REPLICATE 520 T)
                     (\gl3 m3. gl3 = gl /\
                        va1_snap m3 = ITER 520 va1_fwd (va1_clk a0 a1 a2 (ITER K va1_fwd (va1_snap m0))) /\
                        va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 0)
                          (\gl4 m4. gl4 = gl3 /\ m4 = m3 /\
                             va1_hrun (wasmc fs) (REPLICATE (520 + K) F)
                               (\gl5 m5. gl5 = gl /\ va1_snap m5 = va1_snap (m0:int64->byte)) gl4 m4) gl3 m3) gl2 m2) gl1 m1) gl m0`
    ASSUME_TAC THENL
   [MATCH_MP_TAC VA1_HRUN_MONO THEN
    EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\ va1_snap m' = ITER K va1_fwd (va1_snap (m0:int64->byte))` THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`g:num->wval`; `x:int64->byte`] THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC VA1_HCALL_MONO THEN
      EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\ va1_snap m' = va1_clk a0 a1 a2 (va1_snap (x:int64->byte))` THEN CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`g2:num->wval`; `y:int64->byte`] THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC VA1_HRUN_MONO THEN
        EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\
                    va1_snap m' = ITER 520 va1_fwd (va1_clk a0 a1 a2 (ITER K va1_fwd (va1_snap (m0:int64->byte))))` THEN
        CONJ_TAC THENL
         [MAP_EVERY X_GEN_TAC [`g3:num->wval`; `z:int64->byte`] THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC VA1_HCALL_MONO THEN EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\ m' = (z:int64->byte)` THEN CONJ_TAC THENL
           [REPEAT GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
            MATCH_MP_TAC C8F_CLICK_BACK THEN MAP_EVERY EXISTS_TAC [`a0:int32`; `a1:int32`; `a2:int32`] THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
            MATCH_MP_TAC C8F_END_C THEN EXISTS_TAC `K:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
          MATCH_MP_TAC C8F_FWD_RUN_C THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) && c8f_has "va1_clk" (concl th) && c8f_has "va1_kind" (concl th))) THEN
          ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]];
        MATCH_MP_TAC C8F_CLK_HOST THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(SPECL [`K:num`; `0`] C8F_WORD_INJ) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC]];
      MATCH_MP_TAC C8F_FWD_RUN_C THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) && c8f_has "va1_kind" (concl th) &&
        not (c8f_has "va1_clk" (concl th)))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]]; ALL_TAC] THEN
  C8F_BOTH_TAC (c8f_has "va1_film_bytes") (c8f_has "ITER") THEN
  MAP_EVERY X_GEN_TAC [`g:num->wval`; `x:int64->byte`] THEN BETA_TAC THEN STRIP_TAC THEN
  C8F_GSUB_TAC `g:num->wval` THEN ASM_REWRITE_TAC[] THEN
  C8F_HBOTH_TAC (c8f_has "va1_film_bytes") (fun t -> not (c8f_has "va1_film_bytes" t)) THEN
  MAP_EVERY X_GEN_TAC [`g2:num->wval`; `y:int64->byte`] THEN BETA_TAC THEN STRIP_TAC THEN
  C8F_GSUB_TAC `g2:num->wval` THEN ASM_REWRITE_TAC[] THEN
  C8F_BOTH_TAC (c8f_has "va1_film_bytes") (fun t -> not (c8f_has "va1_film_bytes" t)) THEN
  MAP_EVERY X_GEN_TAC [`g3:num->wval`; `z:int64->byte`] THEN BETA_TAC THEN STRIP_TAC THEN
  C8F_GSUB_TAC `g3:num->wval` THEN ASM_REWRITE_TAC[] THEN
  C8F_HBOTH_TAC (c8f_has "va1_film_bytes") (fun t -> not (c8f_has "va1_film_bytes" t)) THEN
  MAP_EVERY X_GEN_TAC [`g4:num->wval`; `x4:int64->byte`] THEN BETA_TAC THEN STRIP_TAC THEN
  C8F_GSUB_TAC `g4:num->wval` THEN C8F_GSUB_TAC `x4:int64->byte` THEN ASM_REWRITE_TAC[] THEN
  C8F_BOTH_TAC (c8f_has "va1_film_bytes") (fun t -> not (c8f_has "va1_film_bytes" t)) THEN
  MAP_EVERY X_GEN_TAC [`g5:num->wval`; `w5:int64->byte`] THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C8F_FB THEN EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[]);;
let VA1_C8F_SAT = prove
 (`(!K n. 1 <= K /\ K + 520 < 4294967296 /\ n <= 520
         ==> ?(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num)
              (x0:(num->int32)#(num->int32)) (m0:int64->byte).
               va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\ fs 33 = (va1_puncture_mc,3,1) /\
               fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\ gl 0 = I32 (word 16384) /\
               mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
               va1_np_st (word 0) (word K) mdl N x0 m0 /\ va1_clean m0 /\
               ~(read (bytes32 (word 16516)) m0 = word 0 /\ read (bytes32 (word 16520)) m0 = word 0 /\
                 read (bytes32 (word 16524)) m0 = word 0)) /\
  (!K n. 1 <= K /\ K + 520 < 4294967296 /\ n <= 520
         ==> ?(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (ap:int32)
              (x0:(num->int32)#(num->int32)) (m0:int64->byte) (a0:int32) (a1:int32) (a2:int32).
               va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\ fs 33 = (va1_puncture_mc,3,1) /\
               fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\ gl 0 = I32 (word 16384) /\
               mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
               (ap = word 0 \/ K < val ap) /\ va1_np_st (word 0) ap mdl N x0 m0 /\ va1_clean m0 /\
               ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0)) /\
  (?(fs:num->byte list#num#num) (sg0:num->int32) (m:int64->byte).
     va1_fs_all fs /\ va1_dom sg0 /\ va1_kind sg0 = 1 /\ sg0 2 = sg0 3 /\
     val (sg0 3) + 520 < 4294967296 /\ va1_snap m = sg0)`,
  REPEAT CONJ_TAC THENL
   [ACCEPT_TAC VA1_C7B_SAT;
    REPEAT STRIP_TAC THEN MP_TAC(SPECL [`K:num`; `n:num`] VA1_C7B_SAT) THEN MP_TAC(SPECL [`K:num`; `n:num`] VA1_C7A_SAT) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    MP_TAC(SPECL [`1`; `0`] VA1_C7B_SAT) THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(X_CHOOSE_THEN `fs:num->byte list#num#num` (X_CHOOSE_THEN `gl:num->wval` (X_CHOOSE_THEN `mdl:num->int32`
      (X_CHOOSE_THEN `N:num` (X_CHOOSE_THEN `x0:(num->int32)#(num->int32)` (X_CHOOSE_THEN `m0:int64->byte` STRIP_ASSUME_TAC)))))) THEN
    MP_TAC(SPECL [`word 0:int32`; `word 1:int32`; `mdl:num->int32`; `N:num`; `x0:(num->int32)#(num->int32)`; `m0:int64->byte`] C8F_START) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `val (word N:int32) = N` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `m0:int64->byte` C8E_SNAP_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`va1_snap (m0:int64->byte)`; `1`] C8F_AUTO_FACTS) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
    MP_TAC(SPEC `ITER 1 va1_fwd (va1_snap (m0:int64->byte))` C8F_POPSTART) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPEC `ITER 1 va1_fwd (va1_snap (m0:int64->byte))` C8E_SNAP_SURJ) THEN ANTS_TAC THENL
     [REWRITE_TAC[num_CONV `1`; ITER] THEN REPEAT STRIP_TAC THEN
      W(fun (_,w) -> MP_TAC(SPECL [`va1_snap (m0:int64->byte)`; rand(lhs w)] C8F_FWD_HIGH)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[va1_snap] THEN ASM_SIMP_TAC[ARITH_RULE `487424 <= w ==> ~(w < 487424)`];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `m:int64->byte`) THEN
    MAP_EVERY EXISTS_TAC [`fs:num->byte list#num#num`; `ITER 1 va1_fwd (va1_snap (m0:int64->byte))`; `m:int64->byte`] THEN
    ASM_REWRITE_TAC[va1_fs_all] THEN REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV]);;
