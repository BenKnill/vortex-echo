needs "ve_vort.ml";;
needs "ve_tick.ml";;
needs "ve_vk.ml";;
needs "va1_code.ml";;
needs "va1_seq_final2.ml";;
needs "pop_design_defs.ml";;
needs "pop_design_stmts.ml";;
(* ========================================================================= *)
(* Vortex pop, segment L5 (SEG-L5 prover, Claude Opus 5.5, 2026-11-11): the  *)
(* un-birth f14 of vortex_a1.wasm (ve_birth_unapply, 271 B, entry pc 3,      *)
(* locals l0..l6) on the exact bytes: POP_L5_UNBIRTH_OK |- va1_unbirth_ok,   *)
(* and VA1_UNB_CLAUSES. Lemma file (a LEAFCHAIN layer); the spec-locked      *)
(* final leaf pop_l5_final.ml re-binds VA1_UNBIRTH_OK / VA1_UNB_CLAUSES.      *)
(*                                                                           *)
(* f14: 3..24 l0 := ND, l1 := select(16384, ND, ND <u 16384); 26..44 if ND = *)
(*   0: ND := l1 (= 0), return 0; 45..76 l2 := T + 1, l0 := 48 l1 + 1179600 *)
(*   (top record), l3 := 0, l4 := l1; 78 block, 80 loop: 82..95 exit 1 if    *)
(*   the top tag (word 6, at l5 = l0 + 24) <> l2; 97..171 if word 7 (kp) <=u *)
(*   65535: ZQ[4 (kp MOD 2048)] += word 8, ZP[..] += word 9; 172..223 six    *)
(*   i64.store 0 zero the 12 words; 226..247 l0 -= 48, l3 += 1, br_if on     *)
(*   l4 -= 1; 249..256 exit 2: l4 := 0, l3 := l1; 259..270 ND := l4,        *)
(*   return l3.                                                              *)
(* Proof: L = val ND (<= 16384, so l1 = ND). K = the number of records the   *)
(* loop pops (PL5_K_EXISTS, least index where the count runs out or the tag  *)
(* check of va1_unb fails); va1_unb b L bs = va1_unb b K bs (PL5_UNB_FINAL). *)
(* Loop invariant at i (pc 82 / 247): l0 = 1179600 + 48 (L - i), l1 = L,     *)
(* l2 = b, l3 = i, l4 = L - i, memory DI/ZQ/ZP = those of va1_unb b i bs,    *)
(* ND untouched. Pieces: PL5_ZERO (ND = 0), PL5_ENTRY (pc 3 -> 82),          *)
(* PL5_BODY (one pop, generic state X, both credit branches), PL5_BACK,      *)
(* PL5_EXIT_TAG (tag <> b at pc 82), PL5_EXIT_CNT (count out at pc 247);     *)
(* ENSURES_WHILE_UP over K iterations (K = 0 by ENSURES_TRANS).               *)
(* Memory after a pop: forward frame through the write chain (pl5_fwd:       *)
(* PL5_W32S_W32/W64 disjoint, PL5_W32S_UPD, PL5_W32S_Z64 = i64 zero store),  *)
(* then function equality (PL5_ZERO12 for the 12 zeroed words).              *)
(* ========================================================================= *)

(* ========================================================================= *)
(* vortex-pop L5 (un-birth, f14): pure lemmas. va1_unb algebra (pops as long *)
(* as the top tag is b), the depaired va1_pop1 / va1_bs, and va1_w32s frame  *)
(* lemmas over 32- and 64-bit stores. Claude Opus 5.5, 2026-11-11.           *)
(* ========================================================================= *)

let VA1_UNB_CLAUSES = prove(parse_term pop_spec_VA1_UNB_CLAUSES, REWRITE_TAC[va1_unb]);;

(* the "top tag is b" check of va1_unb, as a term builder *)
let pl5_chk b x =
  subst [b,`bb:int32`; x,`xx:(num->int32)#(num->int32)#(num->int32)#int32`]
   `0 < val (SND(SND(SND xx))) /\ FST xx (12 * (val (SND(SND(SND xx))) - 1) + 6) = bb`;;

let PL5_UNB_ADD = prove
 (`!b i c bs.
     (!j. j < i ==> 0 < val (SND(SND(SND (va1_unb b j bs)))) /\
                    FST (va1_unb b j bs) (12 * (val (SND(SND(SND (va1_unb b j bs)))) - 1) + 6) = b)
     ==> va1_unb b (i + c) bs = va1_unb b c (va1_unb b i bs)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; VA1_UNB_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[LT_0; VA1_UNB_CLAUSES] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `c:num`)) (concl th)
                          then MATCH_MP_TAC th else NO_TAC) THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC j`) THEN ASM_REWRITE_TAC[LT_SUC; VA1_UNB_CLAUSES]);;

let PL5_UNB_STEP = prove
 (`!b i bs.
     (!j. j <= i ==> 0 < val (SND(SND(SND (va1_unb b j bs)))) /\
                     FST (va1_unb b j bs) (12 * (val (SND(SND(SND (va1_unb b j bs)))) - 1) + 6) = b)
     ==> va1_unb b (i + 1) bs = va1_pop1 (va1_unb b i bs)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`b:int32`; `i:num`; `SUC 0`; `bs:(num->int32)#(num->int32)#(num->int32)#int32`] PL5_UNB_ADD) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[LT_IMP_LE]; ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES; GSYM ADD1] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VA1_UNB_CLAUSES] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN REWRITE_TAC[LE_REFL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let PL5_UNB_STOP = prove
 (`!b c bs. ~(0 < val (SND(SND(SND bs))) /\ FST bs (12 * (val (SND(SND(SND bs))) - 1) + 6) = b)
            ==> va1_unb b c bs = bs`,
  GEN_TAC THEN INDUCT_TAC THEN SIMP_TAC[VA1_UNB_CLAUSES]);;

(* va1_pop1 on projections *)
let PL5_POP1 = prove
 (`!bs:(num->int32)#(num->int32)#(num->int32)#int32.
     FST (va1_pop1 bs) =
       (\w. if 12 * (val (SND(SND(SND bs))) - 1) <= w /\ w < 12 * (val (SND(SND(SND bs))) - 1) + 12
            then word 0 else FST bs w) /\
     FST (SND (va1_pop1 bs)) =
       (\i. if val (FST bs (12 * (val (SND(SND(SND bs))) - 1) + 7)) < 65536 /\
               i = val (FST bs (12 * (val (SND(SND(SND bs))) - 1) + 7)) MOD 2048
            then word_add (FST (SND bs) i) (FST bs (12 * (val (SND(SND(SND bs))) - 1) + 8))
            else FST (SND bs) i) /\
     FST (SND (SND (va1_pop1 bs))) =
       (\i. if val (FST bs (12 * (val (SND(SND(SND bs))) - 1) + 7)) < 65536 /\
               i = val (FST bs (12 * (val (SND(SND(SND bs))) - 1) + 7)) MOD 2048
            then word_add (FST (SND (SND bs)) i) (FST bs (12 * (val (SND(SND(SND bs))) - 1) + 9))
            else FST (SND (SND bs)) i) /\
     SND (SND (SND (va1_pop1 bs))) = word (val (SND(SND(SND bs))) - 1)`,
  REWRITE_TAC[FORALL_PAIR_THM; va1_pop1] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[]);;

let PL5_BS = prove
 (`!bs:(num->int32)#(num->int32)#(num->int32)#int32. !m.
     va1_bs bs m <=>
     va1_w32s 1179648 196608 (FST bs) m /\ va1_w32s 1163264 2048 (FST (SND bs)) m /\
     va1_w32s 1171456 2048 (FST (SND (SND bs))) m /\ read (bytes32 (word 16400)) m = SND (SND (SND bs))`,
  REWRITE_TAC[FORALL_PAIR_THM; va1_bs]);;

(* ND after i successful pops *)
let PL5_UNB_ND = prove
 (`!b bs i.
     (!j. j < i ==> 0 < val (SND(SND(SND (va1_unb b j bs)))) /\
                    FST (va1_unb b j bs) (12 * (val (SND(SND(SND (va1_unb b j bs)))) - 1) + 6) = b) /\
     i <= val (SND(SND(SND bs)))
     ==> SND(SND(SND (va1_unb b i bs))) = word (val (SND(SND(SND bs))) - i)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[VA1_UNB_CLAUSES; SUB_0; WORD_VAL]; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`b:int32`; `i:num`; `bs:(num->int32)#(num->int32)#(num->int32)#int32`] PL5_UNB_STEP) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[LT_SUC_LE]; REWRITE_TAC[GSYM ADD1] THEN DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[PL5_POP1] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[LT_SUC; LT_TRANS; ARITH_RULE `j < i ==> j < SUC i`]; ASM_ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPEC `SND(SND(SND (bs:(num->int32)#(num->int32)#(num->int32)#int32)))` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_32] THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(word (val (SND(SND(SND (bs:(num->int32)#(num->int32)#(num->int32)#int32)))) - i):int32) =
                val (SND(SND(SND bs))) - i` SUBST1_TAC THENL
   [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

(* the stopping index K: the loop pops exactly K records *)
let PL5_K_EXISTS = prove
 (`!b bs L. ?K. K <= L /\
             (!j. j < K ==> 0 < val (SND(SND(SND (va1_unb b j bs)))) /\
                  FST (va1_unb b j bs) (12 * (val (SND(SND(SND (va1_unb b j bs)))) - 1) + 6) = b) /\
             (K < L ==> ~(0 < val (SND(SND(SND (va1_unb b K bs)))) /\
                  FST (va1_unb b K bs) (12 * (val (SND(SND(SND (va1_unb b K bs)))) - 1) + 6) = b))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `\k. k = L \/ k < L /\
     ~(0 < val (SND(SND(SND (va1_unb b k bs)))) /\
       FST (va1_unb b k bs) (12 * (val (SND(SND(SND (va1_unb b k bs)))) - 1) + 6) = (b:int32))` num_WOP) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN
  CONJ_TAC THENL [EXISTS_TAC `L:num` THEN REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:num` (CONJUNCTS_THEN2 (LABEL_TAC "k") (LABEL_TAC "min"))) THEN
  EXISTS_TAC `K:num` THEN
  SUBGOAL_THEN `K <= L` ASSUME_TAC THENL
   [USE_THEN "k" (DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN USE_THEN "min" (MP_TAC o SPEC `j:num`) THEN
    SUBGOAL_THEN `j < K /\ j < L /\ ~(j = L)` (fun th -> REWRITE_TAC[th] THEN TRY(CONV_TAC TAUT)) THEN
    ASM_ARITH_TAC;
    DISCH_TAC THEN USE_THEN "k" MP_TAC THEN
    SUBGOAL_THEN `K < L /\ ~(K = L)` (fun th -> REWRITE_TAC[th] THEN TRY(CONV_TAC TAUT)) THEN
    ASM_ARITH_TAC]);;

let PL5_UNB_FINAL = prove
 (`!b bs L K. K <= L /\
             (!j. j < K ==> 0 < val (SND(SND(SND (va1_unb b j bs)))) /\
                  FST (va1_unb b j bs) (12 * (val (SND(SND(SND (va1_unb b j bs)))) - 1) + 6) = b) /\
             (K < L ==> ~(0 < val (SND(SND(SND (va1_unb b K bs)))) /\
                  FST (va1_unb b K bs) (12 * (val (SND(SND(SND (va1_unb b K bs)))) - 1) + 6) = b))
             ==> va1_unb b L bs = va1_unb b K bs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`b:int32`; `K:num`; `L - K:num`; `bs:(num->int32)#(num->int32)#(num->int32)#int32`] PL5_UNB_ADD) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `K + L - K = L` SUBST1_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_CASES_TAC `K:num = L` THENL
   [ASM_REWRITE_TAC[SUB_REFL; VA1_UNB_CLAUSES];
    MATCH_MP_TAC PL5_UNB_STOP THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* ---- va1_w32s frames over single stores ---- *)

let PL5_W32S_EXT = prove
 (`!base n f g m. va1_w32s base n f m /\ (!k. k < n ==> f k = g k) ==> va1_w32s base n g m`,
  REWRITE_TAC[va1_w32s] THEN MESON_TAC[]);;

let PL5_W32S_W32 = prove
 (`!base n f e (v:int32) m.
     va1_w32s base n f m /\ (e + 4 <= base \/ base + 4 * n <= e) /\
     base + 4 * n <= 4294967296 /\ e < 4294967296
     ==> va1_w32s base n f (write (bytes32 (word e)) v m)`,
  REWRITE_TAC[va1_w32s] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`base + 4 * k`; `e:num`; `v:int32`; `m:int64->byte`] VK_R32_W32) THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[]]));;

let PL5_W32S_W64 = prove
 (`!base n f e (v:int64) m.
     va1_w32s base n f m /\ (e + 8 <= base \/ base + 4 * n <= e) /\
     base + 4 * n <= 4294967296 /\ e < 4294967296
     ==> va1_w32s base n f (write (bytes64 (word e)) v m)`,
  REWRITE_TAC[va1_w32s] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`base + 4 * k`; `e:num`; `v:int64`; `m:int64->byte`] VK_R32_W64) THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[]]));;

let PL5_W32S_UPD = prove
 (`!base n f c (v:int32) m.
     va1_w32s base n f m /\ c < n /\ base + 4 * n <= 4294967296
     ==> va1_w32s base n (\j. if j = c then v else f j) (write (bytes32 (word (base + 4 * c))) v m)`,
  REWRITE_TAC[va1_w32s] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `k:num = c` THEN ASM_REWRITE_TAC[CAP_B32_SAME] THEN
  MP_TAC(SPECL [`base + 4 * k`; `base + 4 * c`; `v:int32`; `m:int64->byte`] VK_R32_W32) THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[]]));;

let PL5_R32_W64_ZERO = prove
 (`!(x:int64) (m:int64->byte).
     read (bytes32 x) (write (bytes64 x) (word 0) m) = word 0 /\
     read (bytes32 (word_add x (word 4))) (write (bytes64 x) (word 0) m) = word 0`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!y (mm:int64->byte). read (bytes32 y) mm = word (read (bytes(y,4)) mm)`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[bytes32; READ_COMPONENT_COMPOSE; asword; through; read]; ALL_TAC] THEN
  SUBGOAL_THEN `write (bytes64 x) (word 0:int64) (m:int64->byte) = write (bytes(x,8)) 0 m`
    SUBST1_TAC THENL
   [REWRITE_TAC[bytes64; WRITE_COMPONENT_COMPOSE; asword; through; write; read; VAL_WORD_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x:int64`; `4`; `4`; `write (bytes(x:int64,8)) 0 (m:int64->byte)`] READ_BYTES_COMBINE) THEN
  REWRITE_TAC[ARITH_RULE `4 + 4 = 8`] THEN
  SIMP_TAC[READ_WRITE_BYTES; DIMINDEX_64; ARITH_RULE `8 <= 2 EXP 64`; MOD_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[ADD_EQ_0; MULT_EQ_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN SIMP_TAC[]);;

let PL5_W32S_Z64 = prove
 (`!base n f c m.
     va1_w32s base n f m /\ c + 1 < n /\ base + 4 * n <= 4294967296
     ==> va1_w32s base n (\j. if j = c \/ j = c + 1 then word 0 else f j)
                  (write (bytes64 (word (base + 4 * c))) (word 0) m)`,
  REWRITE_TAC[va1_w32s] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `k:num = c` THENL
   [ASM_REWRITE_TAC[PL5_R32_W64_ZERO]; ALL_TAC] THEN
  ASM_CASES_TAC `k:num = c + 1` THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `word (base + 4 * (c + 1)):int64 = word_add (word (base + 4 * c)) (word 4)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; REWRITE_TAC[PL5_R32_W64_ZERO]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`base + 4 * k`; `base + 4 * c`; `word 0:int64`; `m:int64->byte`] VK_R32_W64) THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[]]));;

let PL5_FRAME = `MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
            MAYCHANGE [wstatus] ,, MAYCHANGE [wlocal 0; wlocal 1; wlocal 2; wlocal 3; wlocal 4; wlocal 5; wlocal 6] ,,
            MAYCHANGE [wmem :> bytes(word 16400,4)] ,,
            MAYCHANGE [wmem :> bytes(word 1163264,16384)] ,,
            MAYCHANGE [wmem :> bytes(word 1179648,786432)]`;;
let PL5_F14_EXEC = FAST_MK_EXEC_RULE va1_f14_mc 3;;

let PL5_STEPS_TAC execth snums =
  MAP_EVERY (fun s (asl,w) ->
     let mths = filter (fun th -> vk_is_memfact (concl th)) (map snd asl) in
     (CAP_STEP_TAC execth (READ_COMPONENT_COMPOSE :: mths) s THEN
      CAP_DISCARD_OLD_TAC s THEN WASM_COMPACT_HYPS_TAC) (asl,w))
   (statenames "s" snums);;

let pl5_inv b i x = subst [b,`bb:int32`; i,`ii:num`; x,`XX:(num->int32)#(num->int32)#(num->int32)#int32`]
 `\s. read wcode s = va1_f14_mc /\ read wstatus s = WRunning /\
      read wmemsize s = 4194304 /\ read warity s = 1 /\
      read wlabels s = [0,80,0; 0,259,0] /\
      read (wlocal 0) s = I32 (word (1179600 + 48 * (L - ii))) /\
      read (wlocal 1) s = I32 (word L) /\
      read (wlocal 2) s = I32 bb /\
      read (wlocal 3) s = I32 (word ii) /\
      read (wlocal 4) s = I32 (word (L - ii)) /\
      read wstack s = (if read wpc s = word 82 then [] else [I32 (word (L - ii))]) /\
      va1_w32s 1179648 196608 (FST (XX:(num->int32)#(num->int32)#(num->int32)#int32)) (read wmem s) /\
      va1_w32s 1163264 2048 (FST (SND XX)) (read wmem s) /\
      va1_w32s 1171456 2048 (FST (SND (SND XX))) (read wmem s) /\
      read (bytes32 (word 16400)) (read wmem s) = word L`;;

let pl5_pc pc p = let s = `s:wasmstate` in
  mk_abs(s, mk_conj(`read wcode (s:wasmstate) = va1_f14_mc`,
                    mk_conj(mk_eq(`read wpc (s:wasmstate)`, mk_comb(`word:num->int64`, mk_small_numeral pc)),
                            rhs(concl(BETA_CONV(mk_comb(p,s)))))));;

let pl5_pre = `\s. read wcode s = va1_f14_mc /\ read wpc s = word 3 /\
                read wstatus s = WRunning /\ read wstack s = [] /\ read wlabels s = [] /\
                read warity s = 1 /\ read wmemsize s = 4194304 /\
                read wlocals s = wcall_locals [] decls /\
                va1_tick t (read wmem s) /\ va1_bs (di,zq,zp,word L) (read wmem s)`;;

let pl5_entry_goal =
  list_mk_forall([`L:num`; `t:int32`; `di:num->int32`; `zq:num->int32`; `zp:num->int32`; `decls:wval list`],
   mk_imp(`0 < L /\ L <= 16384 /\ wasm_decl_vals va1_f14_mc = SOME decls`,
    list_mk_comb(`ensures wasm`, [pl5_pre; pl5_pc 82 (pl5_inv `word_add (t:int32) (word 1)` `0` `(di:num->int32,zq:num->int32,zp:num->int32,word L:int32)`); PL5_FRAME])));;


let PL5_SHL_AND = prove
 (`!kp:int32. val (word_and (word_shl kp 2) (word 8188):int32) = 4 * (val kp MOD 2048)`,
  GEN_TAC THEN
  SUBGOAL_THEN `word_and (word_shl (kp:int32) 2) (word 8188) = word_shl (word_and kp (word 2047)) 2`
    SUBST1_TAC THENL [BITBLAST_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_SHL; DIMINDEX_32] THEN
  MP_TAC(ISPECL [`kp:int32`; `11`] VAL_WORD_AND_MASK_WORD) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  MATCH_MP_TAC MOD_LT THEN MP_TAC(SPECL [`val (kp:int32)`; `2048`] MOD_LT_EQ) THEN ARITH_TAC);;

let PL5_WRAP = prove
 (`!a b c. a + c = b + 4294967296 ==> word_add (word a) (word c):int32 = word b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[WORD_ADD_0]);;

let PL5_ZERO12 = prove
 (`!n k (f:num->int32).
     (if k = 12 * n + 2 \/ k = (12 * n + 2) + 1 then word 0
      else if k = 12 * n + 4 \/ k = (12 * n + 4) + 1 then word 0
      else if k = 12 * n + 6 \/ k = (12 * n + 6) + 1 then word 0
      else if k = 12 * n + 8 \/ k = (12 * n + 8) + 1 then word 0
      else if k = 12 * n + 10 \/ k = (12 * n + 10) + 1 then word 0
      else if k = 12 * n \/ k = 12 * n + 1 then word 0
      else f k) =
     (if 12 * n <= k /\ k < 12 * n + 12 then word 0 else f k)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `12 * n <= k /\ k < 12 * n + 12` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `?j. j < 12 /\ k = 12 * n + j` MP_TAC THENL
     [EXISTS_TAC `k - 12 * n` THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC)) THEN
    SPEC_TAC(`j:num`,`j:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC[GSYM ADD_ASSOC; EQ_ADD_LCANCEL; ADD_CLAUSES] THEN
    CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
    REWRITE_TAC[ARITH_RULE `!m p. m = m + p <=> p = 0`] THEN
    CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[];
    SUBGOAL_THEN `!j. j < 12 ==> ~(k = 12 * n + j)` MP_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[GSYM ADD_ASSOC; ADD_CLAUSES] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let pl5_arith asl tm = TAC_PROOF((asl,tm), VK_ARITH_TAC);;

(* forward frame: th |- va1_w32s base n f mm  ==> |- va1_w32s base n f' m (m a write chain over mm) *)
let rec pl5_fwd asl th m =
  if aconv m (rand(concl th)) then th else
  match m with
    Comb(Comb(Comb(Const("write",_),c),v),m0) ->
      let th0 = pl5_fwd asl th m0 in
      let _,args = strip_comb(concl th0) in
      let base = el 0 args and n = el 1 args and f = el 2 args in
      let cname = fst(dest_const(rator c)) and e = rand(rand c) in
      let upd = try let l,r = dest_binop `(+):num->num->num` e in
                    if l = base then Some r else if r = base then Some l else None
                with Failure _ -> None in
      (match upd with
         None ->
           let lem = if cname = "bytes32" then PL5_W32S_W32 else PL5_W32S_W64 in
           let lem' = ISPECL [base;n;f;e;v;m0] lem in
           let side = rand(lhand(concl lem')) in
           MP lem' (CONJ th0 (pl5_arith asl side))
       | Some k4 ->
           let _,cc = dest_binop `( * ):num->num->num` k4 in
           let e' = mk_binop `(+):num->num->num` base (mk_binop `( * ):num->num->num` `4` cc) in
           let lem = if cname = "bytes32" then PL5_W32S_UPD else PL5_W32S_Z64 in
           let lem' = if cname = "bytes32" then ISPECL [base;n;f;cc;v;m0] lem else ISPECL [base;n;f;cc;m0] lem in
           let side = rand(lhand(concl lem')) in
           let th1 = MP lem' (CONJ th0 (pl5_arith asl side)) in
           if e' = e then th1 else
           let eq = AP_TERM `word:num->int64` (ARITH_RULE(mk_eq(e',e))) in
           GEN_REWRITE_RULE (RAND_CONV o ONCE_DEPTH_CONV) [eq] th1)
  | _ -> failwith "pl5_fwd: not a write chain";;

(* rewrite with the state-free, read-free assumptions only *)
let pl5_pure_ths asl = filter (fun th -> let c = concl th in
   not (can (find_term (fun t -> is_const t && (let n = fst(dest_const t) in
          n = "read" || n = "write" || n = "MAYCHANGE" || n = ",,"))) c) &&
   not (can (find_term (fun t -> type_of t = `:wasmstate`)) c)) (map snd asl);;
let PL5_PURE_REWRITE_TAC ths : tactic = fun (asl,w) -> REWRITE_TAC(ths @ pl5_pure_ths asl) (asl,w);;

let PL5_FUNEQ_TAC : tactic =
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[PL5_POP1] THEN
  PL5_PURE_REWRITE_TAC[ADD_SUB] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[PL5_ZERO12] THEN
  REPEAT(COND_CASES_TAC THEN PL5_PURE_REWRITE_TAC[WORD_ADD_SYM]);;

let PL5_W32S_GOAL_TAC : tactic = fun (asl,w) ->
  let _,args = strip_comb w in
  let base = el 0 args and m = el 3 args in
  let rec inner t = match t with Comb(Comb(Comb(Const("write",_),_),_),m0) -> inner m0 | _ -> t in
  let mm = inner m in
  let th = find (fun th -> let c = concl th in
     try let h,a = strip_comb c in fst(dest_const h) = "va1_w32s" && el 0 a = base && el 3 a = mm
     with Failure _ -> false) (map snd asl) in
  let th' = pl5_fwd asl th m in
  let f' = el 2 (snd(strip_comb(concl th'))) in
  (MATCH_MP_TAC PL5_W32S_EXT THEN EXISTS_TAC f' THEN CONJ_TAC THENL [ACCEPT_TAC th'; PL5_FUNEQ_TAC]) (asl,w);;

let PL5_MEM_CLOSE_TAC : tactic =
  REPEAT CONJ_TAC THEN
  TRY(CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(PL5_W32S_GOAL_TAC THEN NO_TAC) THEN
  REPEAT VK_PEEL_TAC THEN ASM_REWRITE_TAC[];;

let PL5_DI_FACT_TAC base k v =
  let a = mk_binop `(+):num->num->num` base (mk_binop `( * ):num->num->num` `4` k) in
  let tm = subst [a,`aa:num`; v,`vv:int32`] `read (wmem :> bytes32 (word aa)) s0 = vv` in
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
    FIRST_ASSUM(fun th -> let c = concl th in
      if is_comb c && can (term_match [] (subst [base,`bb:num`] `va1_w32s bb n f m`)) c
      then MP_TAC(SPEC k (REWRITE_RULE[va1_w32s] th)) else NO_TAC) THEN
    ANTS_TAC THENL [VK_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC];;

let pl5_val_fact off c =
  let a = if off = 0 then `word (1179648 + 4 * 12 * n):int32`
          else mk_comb(mk_comb(`word_add:int32->int32->int32`, `word (1179648 + 4 * 12 * n):int32`),
                       mk_comb(`word:num->int32`, mk_small_numeral off)) in
  mk_eq(mk_comb(`val:int32->num`, a), subst [c,`cc:num`] `1179648 + 4 * cc`);;

let PL5_VALS_TAC =
  MAP_EVERY (fun (off,c) -> SUBGOAL_THEN (pl5_val_fact off c) ASSUME_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD] THEN MATCH_MP_TAC CAP_VAL_WORD32_EQ THEN CONJ_TAC THEN VK_ARITH_TAC; ALL_TAC])
   [0,`12 * n`; 8,`12 * n + 2`; 16,`12 * n + 4`; 24,`12 * n + 6`; 28,`12 * n + 7`;
    32,`12 * n + 8`; 36,`12 * n + 9`; 40,`12 * n + 10`];;


let PL5_ENTRY = prove(pl5_entry_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `decls:wval list`)) (concl th))) THEN
  REWRITE_TAC[CONJUNCT2 VA1_F14_CALLEE; option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[va1_bs; va1_tick] THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `!k. k < 7 ==> read (wlocal k) s0 = I32 (word 0)` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `wlocals`)) (concl th))) THEN
    REWRITE_TAC[wlocal; READ_COMPONENT_COMPOSE] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[wcall_locals; LENGTH; READ_ELEMENT] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[EL; HD; TL; LENGTH; ARITH] THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN STRIP_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (find_term ((=) `wlocals`)) (concl th))) THEN
  ABBREV_TAC `mm = read wmem (s0:wasmstate)` THEN
  SUBGOAL_THEN `(word L:int32 = word 0) <=> F` ASSUME_TAC THENL
   [MATCH_MP_TAC VK_WORD_NE0 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(if ~(val (word L:int32) < 16384) then I32 (word 16384) else I32 (word L)) = I32 (word L)` ASSUME_TAC THENL
   [SUBGOAL_THEN `val (word L:int32) = L` SUBST1_TAC THENL [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  PL5_STEPS_TAC PL5_F14_EXEC (1--29) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUB_0; injectivity "wval"; GSYM WORD_ADD; GSYM WORD_MUL] THEN
  AP_TERM_TAC THEN ARITH_TAC);;

let pl5_body_goal =
  list_mk_forall([`L:num`; `b:int32`; `X:(num->int32)#(num->int32)#(num->int32)#int32`; `i:num`],
   mk_imp(`i < L /\ L <= 16384 /\ val (SND(SND(SND (X:(num->int32)#(num->int32)#(num->int32)#int32)))) = L - i /\
           FST X (12 * (L - (i + 1)) + 6) = (b:int32)`,
    list_mk_comb(`ensures wasm`, [pl5_pc 82 (pl5_inv `b:int32` `i:num` `X:(num->int32)#(num->int32)#(num->int32)#int32`);
       pl5_pc 247 (pl5_inv `b:int32` `i + 1` `va1_pop1 X`); PL5_FRAME])));;

let PL5_BODY = prove(pl5_body_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `n = L - (i + 1)` THEN
  SUBGOAL_THEN `n < 16384 /\ L - i = n + 1 /\ 1179600 + 48 * (L - i) = 1179648 + 4 * 12 * n` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `kp = FST (X:(num->int32)#(num->int32)#(num->int32)#int32) (12 * n + 7)` THEN
  ABBREV_TAC `w8 = FST (X:(num->int32)#(num->int32)#(num->int32)#int32) (12 * n + 8)` THEN
  ABBREV_TAC `w9 = FST (X:(num->int32)#(num->int32)#(num->int32)#int32) (12 * n + 9)` THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN
  PL5_DI_FACT_TAC `1179648` `12 * n + 6` `b:int32` THEN
  PL5_DI_FACT_TAC `1179648` `12 * n + 7` `kp:int32` THEN
  PL5_DI_FACT_TAC `1179648` `12 * n + 8` `w8:int32` THEN
  PL5_DI_FACT_TAC `1179648` `12 * n + 9` `w9:int32` THEN
  PL5_VALS_TAC THEN
  SUBGOAL_THEN `word_add (word (1179648 + 4 * 12 * n)) (word 4294967248):int32 = word (1179600 + 48 * n) /\
                word_add (word i) (word 1):int32 = word (i + 1) /\
                word_add (word (n + 1)) (word 4294967295):int32 = word n` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PL5_WRAP THEN ARITH_TAC; REWRITE_TAC[WORD_ADD]; MATCH_MP_TAC PL5_WRAP THEN ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `val (kp:int32) < 65536` THENL
   [ABBREV_TAC `kk = val (kp:int32) MOD 2048` THEN
    SUBGOAL_THEN `kk < 2048 /\ val (word_and (word_shl (kp:int32) 2) (word 8188):int32) = 4 * kk` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "kk" THEN REWRITE_TAC[PL5_SHL_AND; MOD_LT_EQ] THEN ARITH_TAC; ALL_TAC] THEN
    PL5_DI_FACT_TAC `1163264` `kk:num` `FST (SND (X:(num->int32)#(num->int32)#(num->int32)#int32)) kk` THEN
    PL5_DI_FACT_TAC `1171456` `kk:num` `FST (SND (SND (X:(num->int32)#(num->int32)#(num->int32)#int32))) kk` THEN
    ABBREV_TAC `mm = read wmem (s0:wasmstate)` THEN
    WASM_STEPS_TAC PL5_F14_EXEC (1--79);
    ABBREV_TAC `mm = read wmem (s0:wasmstate)` THEN
    WASM_STEPS_TAC PL5_F14_EXEC (1--55)] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN PL5_MEM_CLOSE_TAC);;

let pl5_post x = subst [x,`XX:(num->int32)#(num->int32)#(num->int32)#int32`]
  `\s. read wstatus s = WDone /\ (?r. read wstack s = [I32 r]) /\ va1_bs XX (read wmem s)`;;

let pl5_bx = `X:(num->int32)#(num->int32)#(num->int32)#int32`;;

let PL5_BACK = prove
 (list_mk_forall([`L:num`; `b:int32`; pl5_bx; `i:num`],
   mk_imp(`0 < i /\ i < L /\ L <= 16384`,
    list_mk_comb(`ensures wasm`, [pl5_pc 247 (pl5_inv `b:int32` `i:num` pl5_bx);
                                  pl5_pc 82 (pl5_inv `b:int32` `i:num` pl5_bx); PL5_FRAME]))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(word (L - i):int32 = word 0) <=> F` ASSUME_TAC THENL
   [MATCH_MP_TAC VK_WORD_NE0 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN
  ABBREV_TAC `mm = read wmem (s0:wasmstate)` THEN
  PL5_STEPS_TAC PL5_F14_EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

let PL5_BS_CLOSE_TAC : tactic =
  REWRITE_TAC[PL5_BS] THEN REPEAT CONJ_TAC THEN
  TRY(PL5_W32S_GOAL_TAC THEN NO_TAC) THEN
  REWRITE_TAC[CAP_B32_SAME] THEN ASM_REWRITE_TAC[];;

let PL5_EXIT_TAG = prove
 (list_mk_forall([`L:num`; `b:int32`; pl5_bx; `i:num`],
   mk_imp(`i < L /\ L <= 16384 /\ ~(FST (X:(num->int32)#(num->int32)#(num->int32)#int32) (12 * (L - (i + 1)) + 6) = b) /\
           SND (SND (SND X)) = word (L - i)`,
    list_mk_comb(`ensures wasm`, [pl5_pc 82 (pl5_inv `b:int32` `i:num` pl5_bx); pl5_post pl5_bx; PL5_FRAME]))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `n = L - (i + 1)` THEN
  SUBGOAL_THEN `n < 16384 /\ L - i = n + 1 /\ 1179600 + 48 * (L - i) = 1179648 + 4 * 12 * n` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `tg = FST (X:(num->int32)#(num->int32)#(num->int32)#int32) (12 * n + 6)` THEN
  SUBGOAL_THEN `(tg:int32 = b) <=> F` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN
  PL5_DI_FACT_TAC `1179648` `12 * n + 6` `tg:int32` THEN
  PL5_VALS_TAC THEN
  ABBREV_TAC `mm = read wmem (s0:wasmstate)` THEN
  WASM_STEPS_TAC PL5_F14_EXEC (1--13) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MESON_TAC[]; PL5_BS_CLOSE_TAC]);;

let PL5_EXIT_CNT = prove
 (list_mk_forall([`L:num`; `b:int32`; pl5_bx],
   mk_imp(`L <= 16384 /\ SND (SND (SND (X:(num->int32)#(num->int32)#(num->int32)#int32))) = word 0`,
    list_mk_comb(`ensures wasm`, [pl5_pc 247 (pl5_inv `b:int32` `L:num` pl5_bx); pl5_post pl5_bx; PL5_FRAME]))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SUB_REFL] THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN
  ABBREV_TAC `mm = read wmem (s0:wasmstate)` THEN
  PL5_STEPS_TAC PL5_F14_EXEC (1--12) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MESON_TAC[]; PL5_BS_CLOSE_TAC]);;

let PL5_ZERO = prove
 (list_mk_forall([`t:int32`; `di:num->int32`; `zq:num->int32`; `zp:num->int32`; `decls:wval list`],
   mk_imp(`wasm_decl_vals va1_f14_mc = SOME decls`,
    list_mk_comb(`ensures wasm`, [subst [`0`,`L:num`] pl5_pre;
       pl5_post `(di:num->int32,zq:num->int32,zp:num->int32,word 0:int32)`; PL5_FRAME]))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `decls:wval list`)) (concl th))) THEN
  REWRITE_TAC[CONJUNCT2 VA1_F14_CALLEE; option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[va1_bs; va1_tick] THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `!k. k < 7 ==> read (wlocal k) s0 = I32 (word 0)` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `wlocals`)) (concl th))) THEN
    REWRITE_TAC[wlocal; READ_COMPONENT_COMPOSE] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[wcall_locals; LENGTH; READ_ELEMENT] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[EL; HD; TL; LENGTH; ARITH] THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN STRIP_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (find_term ((=) `wlocals`)) (concl th))) THEN
  ABBREV_TAC `mm = read wmem (s0:wasmstate)` THEN
  SUBGOAL_THEN `(if ~(val (word 0:int32) < 16384) then I32 (word 16384) else I32 (word 0)) = I32 (word 0)` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_0; ARITH]; ALL_TAC] THEN
  PL5_STEPS_TAC PL5_F14_EXEC (1--17) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CAP_B32_SAME] THEN REPEAT CONJ_TAC THEN
  MATCH_MP_TAC PL5_W32S_W32 THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let pl5_b = `word_add (t:int32) (word 1)`;;
let pl5_U i = subst [i,`ii:num`]
  `va1_unb (word_add (t:int32) (word 1)) ii (di:num->int32,zq:num->int32,zp:num->int32,word L:int32)`;;

let POP_L5_UNBIRTH_OK = prove(parse_term pop_spec_VA1_UNBIRTH_OK,
  REWRITE_TAC[va1_unbirth_ok] THEN
  MAP_EVERY X_GEN_TAC [`t:int32`; `di:num->int32`; `zq:num->int32`; `zp:num->int32`; `nd:int32`; `decls:wval list`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `L = val (nd:int32)` THEN
  SUBGOAL_THEN `nd:int32 = word L` SUBST_ALL_TAC THENL [EXPAND_TAC "L" THEN REWRITE_TAC[WORD_VAL]; ALL_TAC] THEN
  SUBGOAL_THEN `L <= 16384` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `L = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[VA1_UNB_CLAUSES] THEN
    MATCH_MP_TAC PL5_ZERO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `0 < L` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [pl5_b; `(di:num->int32,zq:num->int32,zp:num->int32,word L:int32)`; `L:num`] PL5_K_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `K:num` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "chk") (LABEL_TAC "stop")))) THEN
  SUBGOAL_THEN (mk_eq(pl5_U `L:num`, pl5_U `K:num`)) SUBST1_TAC THENL
   [MATCH_MP_TAC PL5_UNB_FINAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN (mk_forall(`j:num`, mk_imp(`j <= K`,
     mk_eq(subst [pl5_U `j:num`,`uu:(num->int32)#(num->int32)#(num->int32)#int32`]
             `SND (SND (SND (uu:(num->int32)#(num->int32)#(num->int32)#int32)))`, `word (L - j):int32`))))
   (LABEL_TAC "nd") THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [pl5_b; `(di:num->int32,zq:num->int32,zp:num->int32,word L:int32)`; `j:num`] PL5_UNB_ND) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [GEN_TAC THEN DISCH_TAC THEN USE_THEN "chk" MATCH_MP_TAC THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
      SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `K = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[VA1_UNB_CLAUSES] THEN
    MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
    EXISTS_TAC (pl5_pc 82 (pl5_inv pl5_b `0` `(di:num->int32,zq:num->int32,zp:num->int32,word L:int32)`)) THEN
    REPEAT CONJ_TAC THENL
     [MAYCHANGE_IDEMPOT_TAC;
      MATCH_MP_TAC PL5_ENTRY THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC PL5_EXIT_TAG THEN ASM_REWRITE_TAC[SUB_0] THEN
      REMOVE_THEN "stop" MP_TAC THEN ASM_REWRITE_TAC[VA1_UNB_CLAUSES; ADD_CLAUSES]];
    ALL_TAC] THEN
  ENSURES_WHILE_UP_TAC `K:num` `82` `247` (mk_abs(`i:num`, pl5_inv pl5_b `i:num` (pl5_U `i:num`))) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    PURE_REWRITE_TAC[CONJUNCT1 VA1_UNB_CLAUSES] THEN MATCH_MP_TAC PL5_ENTRY THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN (mk_eq(pl5_U `i + 1`, mk_comb(`va1_pop1`, pl5_U `i:num`))) SUBST1_TAC THENL
     [MATCH_MP_TAC PL5_UNB_STEP THEN GEN_TAC THEN DISCH_TAC THEN USE_THEN "chk" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC PL5_BODY THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN (mk_eq(mk_comb(`val:int32->num`, subst [pl5_U `i:num`,`uu:(num->int32)#(num->int32)#(num->int32)#int32`]
        `SND (SND (SND (uu:(num->int32)#(num->int32)#(num->int32)#int32)))`), `L - i`)) ASSUME_TAC THENL
     [USE_THEN "nd" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "chk" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[ARITH_RULE `L - i - 1 = L - (i + 1)`] THEN MESON_TAC[];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC PL5_BACK THEN ASM_ARITH_TAC;
    ASM_CASES_TAC `K:num = L` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC PL5_EXIT_CNT THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "nd" (MP_TAC o SPEC `L:num`) THEN REWRITE_TAC[LE_REFL; SUB_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
    EXISTS_TAC (pl5_pc 82 (pl5_inv pl5_b `K:num` (pl5_U `K:num`))) THEN
    REPEAT CONJ_TAC THENL
     [MAYCHANGE_IDEMPOT_TAC;
      MATCH_MP_TAC PL5_BACK THEN ASM_ARITH_TAC;
      MATCH_MP_TAC PL5_EXIT_TAG THEN
      SUBGOAL_THEN `K < L` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "nd" (MP_TAC o SPEC `K:num`) THEN REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `val (word (L - K):int32) = L - K` ASSUME_TAC THENL
       [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `0 < L - K /\ L - K - 1 = L - (K + 1)` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REMOVE_THEN "stop" MP_TAC THEN ASM_REWRITE_TAC[]]]);;
