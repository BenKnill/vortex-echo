(* vortex-chain rung C8e row E4 pure part (c8e_inv), C8e PROVER (Claude Opus 5.5), 2026-11-15; loaded after c8e_defs.ml and c8e_decode.ml on the C8p dp layer. *)
(* ========================================================================= *)
(* Vortex chain rung C8e (vortex-chain-20261111-142342 c8e, C8e PROVER, Claude Opus 5.5, 2026-11-15), *)
(* rows E4 (pure part): locality of the step functions (each reads its vectors and tables only below   *)
(* their bounds) and the inverse va1_bwd (va1_fwdt PT sg) = sg on va1_dom, kinds 0, 1, 2. Pure HOL.     *)
(* ========================================================================= *)

(* stricter numeric-assumption filter than the landed c8e_decode.ml (redefined here; arith over num only) *)
let rec c8e_arith_bool t =
  if is_conj t || is_disj t || is_imp t || is_iff t then c8e_arith_bool (lhand t) && c8e_arith_bool (rand t)
  else if is_neg t then c8e_arith_bool (rand t)
  else if t = `T` || t = `F` then true
  else (is_eq t || (is_comb t && is_comb (rator t) && is_const (rator(rator t)) &&
                    mem (fst(dest_const(rator(rator t)))) ["<"; "<="; ">"; ">="]))
       && type_of (lhand t) = `:num` &&
       not (can (find_term (fun u -> is_const u && mem (fst(dest_const u)) ["read"; "va1_snap"; "va1_vabu"])) t);;
let c8e_numasms asl =
  let ths = map snd (filter (fun (_,th) -> c8e_arith_bool (concl th)) asl) in
  let compound th = let c = concl th in is_disj c || (is_neg c && is_conj (rand c)) || is_imp c in
  filter (fun th -> not (compound th)) ths, filter compound ths;;
let C8E_ARITH_TAC : tactic = fun (asl,w) ->
  let simple,comps = c8e_numasms asl in
  FIRST [MAP_EVERY MP_TAC simple THEN ARITH_TAC; MAP_EVERY MP_TAC (simple @ comps) THEN ARITH_TAC] (asl,w);;
(* contradiction from the numeric assumptions, one compound assumption at a time *)
let C8E_CONTRA_TAC : tactic = fun (asl,w) ->
  let simple,comps = c8e_numasms asl in
  let try1 hs = MAP_EVERY MP_TAC hs THEN ARITH_TAC in
  (MATCH_MP_TAC(TAUT `F ==> p`) THEN FIRST (try1 simple :: map (fun h -> try1 (h :: simple)) comps)) (asl,w);;


(* locality of ve_vk: for m < 3 n it reads S below 3 n and mdl at 1, 16 + j (j < n) *)
let C8E_TI_LOC = prove
 (`!(X:num->num->int64) X' (C:num->int64) C' i j c.
     (!c. c < 3 ==> X i c = X' i c /\ X j c = X' j c) /\ C i = C' i /\ C j = C' j
     ==> ve_vk_ti X C i j c = ve_vk_ti X' C' i j c /\ ve_vk_tj X C i j c = ve_vk_tj X' C' i j c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> MAP_EVERY (fun n -> STRIP_ASSUME_TAC(MATCH_MP th (ARITH_RULE (mk_binop `(<):num->num->bool` (mk_small_numeral n) `3`)))) [0;1;2]) THEN
  REWRITE_TAC[ve_vk_ti; ve_vk_tj; ve_vk_w; ve_vk_v; LET_DEF; LET_END_DEF] THEN ASM_REWRITE_TAC[]);;

let C8E_RS_LOC = prove
 (`!(X:num->num->int64) X' (C:num->int64) C' n.
     (!a c. a < n /\ c < 3 ==> X a c = X' a c) /\ (!a. a < n ==> C a = C' a)
     ==> !k i c. i + k < n ==> ve_vk_rs X C i k c = ve_vk_rs X' C' i k c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN REWRITE_TAC[VA1_VK_RS_CLAUSES] THEN
  REPEAT STRIP_TAC THEN BINOP_TAC THENL
   [MP_TAC(SPECL [`X:num->num->int64`; `X':num->num->int64`; `C:num->int64`; `C':num->int64`; `i:num`; `i + 1 + k`; `c:num`] C8E_TI_LOC) THEN
    ANTS_TAC THENL [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; SIMP_TAC[]];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let C8E_ACC_LOC = prove
 (`!(X:num->num->int64) X' (C:num->int64) C' n.
     (!a c. a < n /\ c < 3 ==> X a c = X' a c) /\ (!a. a < n ==> C a = C' a)
     ==> !i j c. i <= n /\ j < n ==> ve_vk_acc X C n i j c = ve_vk_acc X' C' n i j c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN REWRITE_TAC[VA1_VK_ACC_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ve_vk_acc X C n i j c = ve_vk_acc X' C' n i j c` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `j = i:num` THEN ASM_REWRITE_TAC[] THENL
   [AP_TERM_TAC THEN MP_TAC(SPECL [`X:num->num->int64`; `X':num->num->int64`; `C:num->int64`; `C':num->int64`; `n:num`] C8E_RS_LOC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[ve_vk_upd] THEN
    MP_TAC(SPECL [`X:num->num->int64`; `X':num->num->int64`; `C:num->int64`; `C':num->int64`; `i:num`; `j:num`; `c:num`] C8E_TI_LOC) THEN
    ANTS_TAC THENL [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; SIMP_TAC[]]]);;

let C8E_VK_LOC = prove
 (`!(mdl:num->int32) mdl' (S:num->int32) S' m.
     mdl' 1 = mdl 1 /\ (!j. j < 640 ==> mdl' (16 + j) = mdl (16 + j)) /\
     (!k. k < 3 * MIN (val (mdl 1)) 640 ==> S' k = S k) /\ m < 3 * MIN (val (mdl 1)) 640
     ==> ve_vk mdl' S' m = ve_vk mdl S m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ve_vk] THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`ve_vk_X S'`; `ve_vk_X S`; `ve_vk_C mdl'`; `ve_vk_C mdl`; `MIN (val ((mdl:num->int32) 1)) 640`] C8E_ACC_LOC) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[ve_vk_X; ve_vk_C; ve_vk_xn; ve_vk_len; ve_vk_ss; ve_vk_sx] THENL
     [SUBGOAL_THEN `!c'. c' < 3 ==> (S':num->int32) (3 * a + c') = S (3 * a + c')` (fun th ->
        REWRITE_TAC[MATCH_MP th (ARITH_RULE `0 < 3`); MATCH_MP th (ARITH_RULE `1 < 3`); MATCH_MP th (ARITH_RULE `2 < 3`)] THEN
        ASM_SIMP_TAC[th]) THEN
      REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[LE_REFL] THEN SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC]);;
(* generic locality: pairs agreeing below n, and step functions that only read below n *)
let c8e_ag = new_definition
 `c8e_ag n (s:(num->int32)#(num->int32)) (s':(num->int32)#(num->int32)) <=>
    !j. j < n ==> FST s j = FST s' j /\ SND s j = SND s' j`;;
let c8e_lf = new_definition
 `c8e_lf n (f:(num->int32)->num->int32) (f':(num->int32)->num->int32) <=>
    !S S' m. (!k. k < n ==> S k = S' k) /\ m < n ==> f S m = f' S' m`;;

let C8E_FRED_LOC = prove
 (`!n f f' s s'. c8e_lf n f f' /\ c8e_ag n s s'
     ==> c8e_ag n (ve_fredkin_fwd f s) (ve_fredkin_fwd f' s') /\ c8e_ag n (ve_fredkin_bwd f s) (ve_fredkin_bwd f' s')`,
  REWRITE_TAC[c8e_lf; c8e_ag; ve_fredkin_fwd; ve_fredkin_bwd; FST; SND] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

let C8E_FREDN_LOC = prove
 (`!n f f'. (!i. c8e_lf n (f i) (f' i))
     ==> !k s s'. c8e_ag n s s' ==> c8e_ag n (ve_fredkin_fwdn f k s) (ve_fredkin_fwdn f' k s') /\
                                    c8e_ag n (ve_fredkin_bwdn f k s) (ve_fredkin_bwdn f' k s')`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[VE_FREDKIN_FWDN_CLAUSES; VE_FREDKIN_BWDN_CLAUSES] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[C8E_FRED_LOC]);;

let C8E_KD_LOC = prove
 (`!n K K' D D' s s'. c8e_lf n K K' /\ c8e_lf n D D' /\ c8e_ag n s s'
     ==> c8e_ag n (ve_kd_fwd K D s) (ve_kd_fwd K' D' s') /\ c8e_ag n (ve_kd_bwd K D s) (ve_kd_bwd K' D' s')`,
  REWRITE_TAC[c8e_lf; c8e_ag; ve_kd_fwd; ve_kd_bwd; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

let C8E_KDN_LOC = prove
 (`!n K K' D D'. (!i. c8e_lf n (K i) (K' i)) /\ (!i. c8e_lf n (D i) (D' i))
     ==> !k s s'. c8e_ag n s s' ==> c8e_ag n (ve_kd_fwdn K D k s) (ve_kd_fwdn K' D' k s') /\
                                    c8e_ag n (ve_kd_bwdn K D k s) (ve_kd_bwdn K' D' k s')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[VE_KD_FWDN_CLAUSES; VE_KD_BWDN_CLAUSES] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[C8E_KD_LOC]);;

let C8E_EVAL_TAC : tactic =
  REWRITE_TAC[va1_put_ps; va1_put_x; C8E_PUT_AP] THEN
  REPEAT(COND_CASES_TAC THEN TRY(C8E_CONTRA_TAC THEN NO_TAC));;
let C8E_MIN640 = prove(`!n. n <= 640 ==> MIN n 640 = n`, REWRITE_TAC[MIN] THEN ARITH_TAC);;
let C8E_VK_LF = prove
 (`!(mdl:num->int32) mdl' n. mdl' 1 = mdl 1 /\ (!j. j < 640 ==> mdl' (16 + j) = mdl (16 + j)) /\
     val (mdl 1) <= 640 /\ n = 3 * val (mdl 1)
     ==> c8e_lf n (ve_vk mdl') (ve_vk mdl)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[c8e_lf] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC C8E_VK_LOC THEN ASM_SIMP_TAC[C8E_MIN640] THEN ASM_MESON_TAC[]);;
let C8E_LF_TERM th = is_comb(concl th) && (try fst(dest_const(fst(strip_comb(concl th)))) = "c8e_lf" with _ -> false);;

let VA1_INV_K0 = prove
 (`!(PT:(num->int32)->num->int32) sg. va1_dom sg /\ va1_kind sg = 0 ==> va1_bwd (va1_fwdt PT sg) = sg`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_dom] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(sg:num->int32) 3 = word 4294967295` ASSUME_TAC THENL
   [ASM_CASES_TAC `(sg:num->int32) 3 = word 4294967295` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `va1_kind sg = 0` THEN ASM_REWRITE_TAC[va1_kind] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[ARITH_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `~(word_add ((sg:num->int32) 2) (word 1) = word 0)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `sg' = va1_fwdt PT sg` THEN
  SUBGOAL_THEN `!w. sg' w = va1_put_x (3 * val ((sg:num->int32) 65)) (ve_fredkin_fwdn (\i. ve_vk (\k. sg (64 + k))) 16 (va1_sg_x sg))
                         (va1_put 2 1 (\i. word_add (sg 2) (word 1)) sg) w` (LABEL_TAC "E") THENL
   [EXPAND_TAC "sg'" THEN REWRITE_TAC[va1_fwdt; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(sg':num->int32) 2 = word_add (sg 2) (word 1) /\ sg' 3 = sg 3 /\ sg' 65 = sg 65 /\
                (!k. k < 1024 ==> sg' (64 + k) = sg (64 + k)) /\
                (!w. ~(274432 <= w /\ w < 274432 + 3 * val (sg 65)) /\ ~(276480 <= w /\ w < 276480 + 3 * val (sg 65)) /\
                     ~(w = 2) ==> sg' w = sg w)` STRIP_ASSUME_TAC THENL
   [USE_THEN "E" (fun th -> REWRITE_TAC[th]) THEN REPEAT STRIP_TAC THEN C8E_EVAL_TAC THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `c8e_ag (3 * val ((sg:num->int32) 65)) (va1_sg_x sg') (ve_fredkin_fwdn (\i. ve_vk (\k. sg (64 + k))) 16 (va1_sg_x sg))`
    ASSUME_TAC THENL
   [REWRITE_TAC[c8e_ag; va1_sg_x] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT STRIP_TAC THEN
    USE_THEN "E" (fun th -> REWRITE_TAC[th]) THEN C8E_EVAL_TAC THEN REWRITE_TAC[va1_sg_x; ADD_SUB2]; ALL_TAC] THEN
  REMOVE_THEN "E" (K ALL_TAC) THEN
  SUBGOAL_THEN `c8e_lf (3 * val ((sg:num->int32) 65)) (ve_vk (\k. sg' (64 + k))) (ve_vk (\k. sg (64 + k)))` ASSUME_TAC THENL
   [MATCH_MP_TAC C8E_VK_LF THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `16 + j` o check(fun th -> is_forall(concl th) && can (find_term ((=) `1024`)) (concl th))) THEN
      REWRITE_TAC[ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN MATCH_MP_TAC THEN C8E_ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC]; ALL_TAC] THEN
  FIRST_ASSUM(fun lf -> if C8E_LF_TERM lf then
    MP_TAC(SPECL [`16`; `va1_sg_x sg'`; `ve_fredkin_fwdn (\i. ve_vk (\k. (sg:num->int32) (64 + k))) 16 (va1_sg_x sg)`]
      (MATCH_MP (BETA_RULE(ISPECL [`3 * val ((sg:num->int32) 65)`; `\i:num. ve_vk (\k. (sg':num->int32) (64 + k))`; `\i:num. ve_vk (\k. (sg:num->int32) (64 + k))`] C8E_FREDN_LOC)) (GEN `i:num` lf)))
    else failwith "") THEN
  ASM_REWRITE_TAC[FREDKIN_STEPS_INVERSE] THEN REWRITE_TAC[c8e_ag; va1_sg_x] THEN DISCH_THEN(LABEL_TAC "L" o CONJUNCT2) THEN
  REWRITE_TAC[va1_bwd; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FUN_EQ_THM; va1_put_x; va1_sg_x; C8E_PUT_AP] THEN X_GEN_TAC `w:num` THEN
  COND_CASES_TAC THENL
   [USE_THEN "L" (MP_TAC o SPEC `w - 276480`) THEN ANTS_TAC THENL [C8E_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN AP_TERM_TAC THEN C8E_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [USE_THEN "L" (MP_TAC o SPEC `w - 274432`) THEN ANTS_TAC THENL [C8E_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN AP_TERM_TAC THEN C8E_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `w = 2` SUBST1_TAC THENL [C8E_ARITH_TAC; CONV_TAC WORD_RULE];
    FIRST_ASSUM MATCH_MP_TAC THEN C8E_ARITH_TAC]);;
