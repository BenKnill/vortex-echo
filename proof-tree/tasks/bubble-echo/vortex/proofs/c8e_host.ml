(* vortex-chain rung C8e row E3 (c8e_host): the tick theorems as host calls on the snapshot, VA1_FWD_FUNCTION and VA1_BWD_FUNCTION; C8e PROVER (Claude Opus 5.5), 2026-11-15. A9 VA1_TICK_FORWARD_POP_R5C_NU re-proved by the three lines of c8a_r4n.ml (C8a final leaf). *)
let C8E_SNAP_FACTS = prove
 (`!m:int64->byte. val (va1_snap m 65) <= 640 ==>
     va1_tick (va1_snap m 2) m /\ va1_pop (va1_snap m 3) (va1_snap m 32) m /\ va1_mdl (\k. va1_snap m (64 + k)) m /\
     va1_vab (val (va1_snap m 65)) (va1_sg_x (va1_snap m)) m /\ va1_vabu (val (va1_snap m 65)) (va1_sg_x (va1_snap m)) m /\
     va1_st (va1_snap m 2) (va1_snap m 3) (va1_snap m 32) (\k. va1_snap m (64 + k)) (val (va1_snap m 65))
            (va1_sg_x (va1_snap m)) (\k. va1_snap m (6 + k)) (\k. va1_snap m (12288 + k)) (va1_sg_ps (va1_snap m)) m /\
     read (bytes32 (word 16404)) m = va1_snap m 5 /\
     read (bytes32 (word 16516)) m = va1_snap m 33 /\ read (bytes32 (word 16520)) m = va1_snap m 34 /\
     read (bytes32 (word 16524)) m = va1_snap m 35`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP VA1_SNAP_ST) THEN SIMP_TAC[C8E_ST_ALT]);;
let C8E_MDL1 = prove
 (`!m:int64->byte. (\k. va1_snap m (64 + k)) 1 = word (val (va1_snap m 65))`,
  GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_VAL]);;
let C8E_H0F_RAW = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (t:int32) (ap:int32) (mdl:num->int32) (N:num)
    (x:(num->int32)#(num->int32)) (uw:(num->int32)#(num->int32)) (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_np fs /\ (ap = word 0 \/ ~(ap = word_add t (word 1))) /\
     va1_tick t m /\ va1_pop (word 4294967295) ap m /\ va1_mdl mdl m /\ va1_vab N x m /\ va1_vabu N uw m
     ==> va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 1)
           (\gl' m'. gl' = gl /\ va1_tick (word_add t (word 1)) m' /\ va1_pop (word 4294967295) ap m' /\ va1_mdl mdl m' /\
                     va1_vab N (ve_fredkin_fwdn (\i. ve_vk mdl) 16 x) m' /\ va1_vabu N uw m' /\ va1_np_frame m m') gl m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_fs_np] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `t:int32`; `ap:int32`; `mdl:num->int32`; `N:num`;
                `x:(num->int32)#(num->int32)`; `uw:(num->int32)#(num->int32)`] VA1_TICK_FORWARD_NOPOP_VK_U) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun lth -> C1_NP_HCALL_TAC lth VA1_TICKF_CALLEE [VA1_NPF_KEEPS; VA1_NPF_FRAME_BYTES]));;
let VA1_TICK_FORWARD_POP_NU = prove(parse_term c8a_spec_VA1_TICK_FORWARD_POP_NU,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC VA1_TICK_FORWARD_POP_COND_NU THEN ASM_REWRITE_TAC POP_Q3_R1_OKS);;
let VA1_TICK_FORWARD_POP_R5_NU = prove(parse_term c8a_spec_VA1_TICK_FORWARD_POP_R5_NU,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC VA1_TICK_FORWARD_POP_NU THEN ASM_REWRITE_TAC[VA1_CORRK_OK; VA1_JIGK_OK]);;
let VA1_TICK_FORWARD_POP_R5C_NU = prove(parse_term c8a_spec_VA1_TICK_FORWARD_POP_R5C_NU,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC VA1_TICK_FORWARD_POP_R5_NU THEN ASM_REWRITE_TAC[VA1_BIRTH_EQ]);;
let C8E_H0B_RAW = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (u:int32) (ap:int32) (mdl:num->int32) (N:num)
    (y:(num->int32)#(num->int32)) (uw:(num->int32)#(num->int32)) (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_np fs /\ ~(u = word 0) /\
     va1_tick u m /\ va1_pop (word 4294967295) ap m /\ va1_mdl mdl m /\ va1_vab N y m /\ va1_vabu N uw m
     ==> va1_hcall (wasmc fs) va1_tick_backward_mc [] (word 1)
           (\gl' m'. gl' = gl /\ va1_tick (word_sub u (word 1)) m' /\ va1_pop (word 4294967295) ap m' /\ va1_mdl mdl m' /\
                     va1_vab N (ve_fredkin_bwdn (\i. ve_vk mdl) 16 y) m' /\ va1_vabu N uw m' /\ va1_np_frame m m') gl m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_fs_np] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `u:int32`; `ap:int32`; `mdl:num->int32`; `N:num`;
                `y:(num->int32)#(num->int32)`; `uw:(num->int32)#(num->int32)`] VA1_TICK_BACKWARD_NOPOP_VK_U) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun lth -> C1_NP_HCALL_TAC lth VA1_TICKB_CALLEE [VA1_NPB_KEEPS; VA1_NPB_FRAME_BYTES]));;
let C8E_H1F_RAW = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) t p ap mdl N x hp tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32)
    (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32) (uw:(num->int32)#(num->int32)) (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_pop fs /\ va1_pop_window t p /\ va1_log_ok t di nd /\
     va1_st t p ap mdl N x hp tbl (ra,rb,jq,jp,di,zq,zp,nd) m /\ va1_vabu N uw m
     ==> va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 1)
           (\gl' m'. gl' = gl /\
              va1_st (word_add t (word 1)) p ap mdl N (ve_fredkin_fwd (ve_vk mdl) x) hp tbl
                (va1_pop_fwd va1_ck va1_jigk (va1_born mdl hp tbl t (FST (ve_fredkin_fwd (va1_rimd tbl) (ra,rb))) (SND (ve_fredkin_fwd (va1_rimd tbl) (ra,rb))) (FST (ve_kd_fwdn (\i. va1_ck mdl hp tbl t p i (SND (ve_fredkin_fwd (va1_rimd tbl) (ra,rb)))) (\i. va1_cdrift (SND (ve_fredkin_fwd (va1_rimd tbl) (ra,rb)))) 4 (zq,zp))) (SND (ve_kd_fwdn (\i. va1_ck mdl hp tbl t p i (SND (ve_fredkin_fwd (va1_rimd tbl) (ra,rb)))) (\i. va1_cdrift (SND (ve_fredkin_fwd (va1_rimd tbl) (ra,rb)))) 4 (zq,zp))) nd)
                  mdl hp tbl t p (ra,rb,jq,jp,di,zq,zp,nd)) m' /\
              va1_vabu N uw m' /\ va1_pop_frame m m') gl m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_fs_pop] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `t:int32`; `p:int32`; `ap:int32`; `mdl:num->int32`; `N:num`;
                `x:(num->int32)#(num->int32)`; `hp:num->int32`; `tbl:num->int32`; `ra:num->int32`; `rb:num->int32`;
                `jq:num->int32`; `jp:num->int32`; `di:num->int32`; `zq:num->int32`; `zp:num->int32`; `nd:int32`;
                `uw:(num->int32)#(num->int32)`] VA1_TICK_FORWARD_POP_R5C_NU) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun lth -> C2_HCALL_TAC `word 1:int32` lth VA1_TICKF_CALLEE [VA1_R5F_KEEPS; VA1_R5F_FRAME_BYTES]));;
let C8E_H1B_RAW = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) t p ap mdl N x hp tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32)
    (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32) (L:(num->int32)list) (uw:(num->int32)#(num->int32)) (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_pop fs /\ va1_pop_window t p /\ va1_log_ok t di nd /\
     ALL (\r. r 6 = word_add t (word 1)) L /\ val nd + LENGTH L <= 16384 /\
     va1_st (word_add t (word 1)) p ap mdl N (ve_fredkin_fwd (ve_vk mdl) x) hp tbl
            (va1_pop_fwd va1_ck va1_jigk L mdl hp tbl t p (ra,rb,jq,jp,di,zq,zp,nd)) m /\ va1_vabu N uw m
     ==> va1_hcall (wasmc fs) va1_tick_backward_mc [] (word 1)
           (\gl' m'. gl' = gl /\ va1_st t p ap mdl N x hp tbl (ra,rb,jq,jp,di,zq,zp,nd) m' /\
                     va1_vabu N uw m' /\ va1_pop_frame m m') gl m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_fs_pop] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `t:int32`; `p:int32`; `ap:int32`; `mdl:num->int32`; `N:num`;
                `x:(num->int32)#(num->int32)`; `hp:num->int32`; `tbl:num->int32`; `ra:num->int32`; `rb:num->int32`;
                `jq:num->int32`; `jp:num->int32`; `di:num->int32`; `zq:num->int32`; `zp:num->int32`; `nd:int32`;
                `L:(num->int32)list`; `uw:(num->int32)#(num->int32)`] VA1_TICK_POP_INVERSE_R5_U) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun lth -> C2_HCALL_TAC `word 1:int32` lth VA1_TICKB_CALLEE [VA1_R5B_KEEPS; VA1_R5B_FRAME_BYTES]));;
let C8E_H3_RAW = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (t:int32) (p:int32) (ap:int32) (m:int64->byte).
     ~(p = word 4294967295) /\ val p <= val t /\ val (word_add p (word 520)) <= val t /\ va1_tick t m /\ va1_pop p ap m
     ==> va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 0) (\gl' m'. gl' = gl /\ m' = m) gl m`,
  REWRITE_TAC[VA1_POP_HCALL_END]);;
let C8E_H2B_RAW = prove
 (`!fs gl p ap mdl N y hp tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32) h uw m.
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
     fs 10 = (va1_f10_mc,0,0) /\ fs 26 = (va1_f26_mc,0,1) /\ fs 28 = (va1_f28_mc,0,0) /\
     ~(p = word 4294967295) /\ ~(p = word 0) /\
     va1_st p p ap mdl N y hp tbl (ra,rb,jq,jp,di,zq,zp,nd) m /\ read (bytes32 (word 16404)) m = h /\ va1_vabu N uw m
     ==> va1_hcall (wasmc fs) va1_tick_backward_mc [] (word 1)
           (\gl' m'. gl' = gl /\
                     va1_st (word_sub p (word 1)) (word 4294967295) ap mdl N (ve_fredkin_bwdn (\i. ve_vk mdl) 16 y)
                            (\k. if k < 24 then word 0 else hp k) (\k. word 0)
                            ((\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),word 0) m' /\
                     read (bytes32 (word 16404)) m' = word_add h (va1_bad mdl tbl (ra,rb,jq,jp,zq,zp,nd)) /\
                     va1_vabu N uw m' /\ va1_unp_frame m m') gl m`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `p:int32`; `ap:int32`; `mdl:num->int32`;
                `N:num`; `y:(num->int32)#(num->int32)`; `hp:num->int32`; `tbl:num->int32`;
                `ra:num->int32`; `rb:num->int32`; `jq:num->int32`; `jp:num->int32`; `di:num->int32`;
                `zq:num->int32`; `zp:num->int32`; `nd:int32`; `h:int32`; `uw:(num->int32)#(num->int32)`] VA1_TICK_UNPUNCT_U) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun lth ->
    let _,[step;pp;qq;cc] = strip_comb(concl lth) in
    let eth,dth = CONJ_PAIR VA1_TICKB_CALLEE in
    let code = rand(lhand(concl eth)) and e = rand(rand(concl eth))
    and decls = rand(rand(concl dth)) in
    MATCH_MP_TAC (ISPECL [step; code; e; decls; `[]:wval list`; `word 1:int32`; pp; qq; cc]
                    VA1_HCALL_ENSURES) THEN
    REWRITE_TAC[eth; dth; lth] THEN CONJ_TAC THENL
     [GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      ASM_REWRITE_TAC[WCALL_ENTRY_READS; LENGTH];
      REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
      MAP_EVERY (fun kth -> FIRST_ASSUM(MP_TAC o MATCH_MP kth) THEN
                            ASM_REWRITE_TAC[WCALL_ENTRY_READS; LENGTH] THEN DISCH_TAC)
        [C3_T_KEEPS; C3_T_FRAME_BYTES] THEN
      ASM_REWRITE_TAC[]]));;
let C8E_KIND_FACTS = prove
 (`!sg:num->int32.
     (va1_kind sg = 0 ==> sg 3 = word 4294967295 /\ (sg 32 = word 0 \/ ~(sg 32 = word_add (sg 2) (word 1)))) /\
     (va1_kind sg = 1 ==> va1_pop_window (sg 2) (sg 3)) /\
     (va1_kind sg = 2 ==> sg 3 = word 4294967295 /\ ~(sg 32 = word 0) /\ word_add (sg 2) (word 1) = sg 32) /\
     (va1_kind sg = 3 ==> ~(sg 3 = word 4294967295) /\ val (sg 3) <= val (sg 2) /\ val (word_add (sg 3) (word 520)) <= val (sg 2))`,
  GEN_TAC THEN REWRITE_TAC[va1_kind; va1_pop_window] THEN REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN FIRST [ASM_ARITH_TAC; ASM_MESON_TAC[]]);;
let C8E_DOM_N = prove
 (`!sg:num->int32. va1_dom sg ==> 1 <= val (sg 65) /\ val (sg 65) <= 640`, SIMP_TAC[va1_dom]);;
let C8E_SNAP_PRE_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_fs_all] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C8E_DOM_N) THEN
  MP_TAC(SPEC `m:int64->byte` C8E_SNAP_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `va1_snap (m:int64->byte)` C8E_KIND_FACTS) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;
let C8E_S0F = prove
 (`!(PT:(num->int32)->num->int32) (fs:num->byte list#num#num) (gl:num->wval) (m:int64->byte).
     va1_fs_all fs /\ va1_dom (va1_snap m) /\ va1_kind (va1_snap m) = 0
     ==> va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 1)
           (\gl' m'. gl' = gl /\ va1_snap m' = va1_fwdt PT (va1_snap m)) gl m`,
  C8E_SNAP_PRE_TAC THEN MATCH_MP_TAC VA1_HCALL_MONO THEN
  EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\ va1_tick (word_add (va1_snap m 2) (word 1)) m' /\
                va1_pop (word 4294967295) (va1_snap m 32) m' /\ va1_mdl (\k. va1_snap m (64 + k)) m' /\
                va1_vab (val (va1_snap m 65)) (ve_fredkin_fwdn (\i. ve_vk (\k. va1_snap m (64 + k))) 16 (va1_sg_x (va1_snap m))) m' /\
                va1_vabu (val (va1_snap m 65)) (va1_sg_x (va1_snap m)) m' /\ va1_np_frame m m'` THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC VA1_DEC_NP_FWD THEN EXISTS_TAC `va1_sg_x (va1_snap (m:int64->byte))` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC C8E_H0F_RAW THEN ASM_REWRITE_TAC[C8E_MDL1; va1_fs_np] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `va1_snap (m:int64->byte) 3 = word 4294967295`)) THEN
    ASM_REWRITE_TAC[]]);;
let C8E_S3F = prove
 (`!(PT:(num->int32)->num->int32) (fs:num->byte list#num#num) (gl:num->wval) (m:int64->byte).
     va1_fs_all fs /\ va1_dom (va1_snap m) /\ va1_kind (va1_snap m) = 3
     ==> va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 0)
           (\gl' m'. gl' = gl /\ va1_snap m' = va1_fwdt PT (va1_snap m)) gl m`,
  C8E_SNAP_PRE_TAC THEN MATCH_MP_TAC VA1_HCALL_MONO THEN
  EXISTS_TAC `\gl' m'. gl' = (gl:num->wval) /\ m' = (m:int64->byte)` THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC VA1_DEC_END THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC C8E_H3_RAW THEN MAP_EVERY EXISTS_TAC [`va1_snap (m:int64->byte) 2`; `va1_snap (m:int64->byte) 3`; `va1_snap (m:int64->byte) 32`] THEN
    ASM_REWRITE_TAC[]]);;
let C8E_MONO_TAC (post:tactic) (th:thm) : tactic =
  let q = el 4 (snd(strip_comb(concl th))) in
  MATCH_MP_TAC VA1_HCALL_MONO THEN EXISTS_TAC q THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN post;
    ACCEPT_TAC th];;
let c8e_sgl = [`\k. va1_snap (m:int64->byte) (278528 + k)`; `\k. va1_snap (m:int64->byte) (280576 + k)`;
               `\k. va1_snap (m:int64->byte) (282624 + k)`; `\k. va1_snap (m:int64->byte) (284672 + k)`;
               `\w. va1_snap (m:int64->byte) (290816 + w)`; `\k. va1_snap (m:int64->byte) (286720 + k)`;
               `\k. va1_snap (m:int64->byte) (288768 + k)`; `va1_snap (m:int64->byte) 4`];;
let c8e_sgh = [`va1_snap (m:int64->byte) 2`; `va1_snap (m:int64->byte) 3`; `va1_snap (m:int64->byte) 32`;
               `\k. va1_snap (m:int64->byte) (64 + k)`; `val (va1_snap (m:int64->byte) 65)`; `va1_sg_x (va1_snap (m:int64->byte))`;
               `\k. va1_snap (m:int64->byte) (6 + k)`; `\k. va1_snap (m:int64->byte) (12288 + k)`];;
let C8E_S1F = prove
 (`!(PT:(num->int32)->num->int32) (fs:num->byte list#num#num) (gl:num->wval) (m:int64->byte).
     va1_fs_all fs /\ va1_dom (va1_snap m) /\ va1_kind (va1_snap m) = 1
     ==> va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 1)
           (\gl' m'. gl' = gl /\ va1_snap m' = va1_fwdt PT (va1_snap m)) gl m`,
  C8E_SNAP_PRE_TAC THEN
  SUBGOAL_THEN `va1_log_ok (va1_snap m 2) (\w. va1_snap (m:int64->byte) (290816 + w)) (va1_snap m 4)` ASSUME_TAC THENL
   [UNDISCH_TAC `va1_dom (va1_snap (m:int64->byte))` THEN ASM_REWRITE_TAC[va1_dom; ARITH_EQ] THEN SIMP_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[va1_sg_ps]) THEN
  MP_TAC(ISPECL ([`fs:num->byte list#num#num`; `gl:num->wval`] @ c8e_sgh @ c8e_sgl @ [`va1_sg_x (va1_snap (m:int64->byte))`; `m:int64->byte`]) C8E_H1F_RAW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[C8E_MDL1]; ALL_TAC] THEN
  DISCH_THEN(C8E_MONO_TAC
    (MATCH_MP_TAC VA1_DEC_POP_FWD THEN MAP_EVERY EXISTS_TAC [`m:int64->byte`; `va1_snap (m:int64->byte) 32`; `va1_sg_x (va1_snap (m:int64->byte))`] THEN
     ASM_REWRITE_TAC[va1_sg_ps; VA1_POP_BIRTHS_EQ])));;
let C8E_FWDT_K02 = prove
 (`!(PT:(num->int32)->num->int32) sg.
     (va1_kind sg = 0 ==> va1_fwdt PT sg 2 = word_add (sg 2) (word 1) /\ va1_fwdt PT sg 3 = sg 3 /\ va1_fwdt PT sg 65 = sg 65) /\
     (va1_kind sg = 2 ==> va1_fwdt PT sg 2 = word_add (sg 2) (word 1) /\ va1_fwdt PT sg 3 = word_add (sg 2) (word 1) /\
                          va1_fwdt PT sg 65 = sg 65)`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[va1_fwdt; LET_DEF; LET_END_DEF; ARITH_EQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[va1_put_x; C8E_PUT_AP] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;
let C8E_S0B = prove
 (`!(PT:(num->int32)->num->int32) (fs:num->byte list#num#num) (gl:num->wval) (m:int64->byte) sg0.
     va1_fs_all fs /\ va1_dom sg0 /\ va1_kind sg0 = 0 /\ va1_snap m = va1_fwdt PT sg0
     ==> va1_hcall (wasmc fs) va1_tick_backward_mc [] (word 1)
           (\gl' m'. gl' = gl /\ va1_snap m' = va1_bwd (va1_snap m)) gl m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_fs_all] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C8E_DOM_N) THEN
  MP_TAC(SPECL [`PT:(num->int32)->num->int32`; `sg0:num->int32`] C8E_FWDT_K02) THEN REWRITE_TAC[ASSUME `va1_kind (sg0:num->int32) = 0`; ARITH_EQ] THEN STRIP_TAC THEN
  MP_TAC(SPEC `sg0:num->int32` C8E_KIND_FACTS) THEN REWRITE_TAC[ASSUME `va1_kind (sg0:num->int32) = 0`; ARITH_EQ] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `~(word_add ((sg0:num->int32) 2) (word 1) = word 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `va1_dom sg0` THEN ASM_REWRITE_TAC[va1_dom] THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `val (va1_snap (m:int64->byte) 65) <= 640 /\ 1 <= val (va1_snap m 65) /\
                ~(va1_snap m 2 = word 0) /\ va1_snap m 3 = word 4294967295` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `va1_snap (m:int64->byte) = va1_fwdt PT sg0`)) THEN
  MP_TAC(SPEC `m:int64->byte` C8E_SNAP_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `va1_snap (m:int64->byte) 2`; `va1_snap (m:int64->byte) 32`;
                 `\k. va1_snap (m:int64->byte) (64 + k)`; `val (va1_snap (m:int64->byte) 65)`; `va1_sg_x (va1_snap (m:int64->byte))`;
                 `va1_sg_x (va1_snap (m:int64->byte))`; `m:int64->byte`] C8E_H0B_RAW) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[C8E_MDL1; va1_fs_np] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `va1_snap (m:int64->byte) 3 = word 4294967295`)) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(C8E_MONO_TAC
    (MATCH_MP_TAC VA1_DEC_NP_BWD THEN EXISTS_TAC `va1_sg_x (va1_snap (m:int64->byte))` THEN ASM_REWRITE_TAC[])));;
let C8E_S2B = prove
 (`!(PT:(num->int32)->num->int32) (fs:num->byte list#num#num) (gl:num->wval) (m:int64->byte) sg0.
     va1_fs_all fs /\ va1_dom sg0 /\ va1_kind sg0 = 2 /\ va1_snap m = va1_fwdt PT sg0
     ==> va1_hcall (wasmc fs) va1_tick_backward_mc [] (word 1)
           (\gl' m'. gl' = gl /\ va1_snap m' = va1_bwd (va1_snap m)) gl m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_fs_all] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C8E_DOM_N) THEN
  MP_TAC(SPECL [`PT:(num->int32)->num->int32`; `sg0:num->int32`] C8E_FWDT_K02) THEN
  REWRITE_TAC[ASSUME `va1_kind (sg0:num->int32) = 2`; ARITH_EQ] THEN STRIP_TAC THEN
  MP_TAC(SPEC `sg0:num->int32` C8E_KIND_FACTS) THEN REWRITE_TAC[ASSUME `va1_kind (sg0:num->int32) = 2`; ARITH_EQ] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `~(word_add ((sg0:num->int32) 2) (word 1) = word 4294967295)` ASSUME_TAC THENL
   [UNDISCH_TAC `va1_dom sg0` THEN REWRITE_TAC[va1_dom; ASSUME `va1_kind (sg0:num->int32) = 2`; ARITH_EQ] THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `val (va1_snap (m:int64->byte) 65) <= 640 /\ 1 <= val (va1_snap m 65) /\
                ~(va1_snap m 2 = word 0) /\ ~(va1_snap m 2 = word 4294967295) /\ va1_snap m 3 = va1_snap m 2` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `va1_snap (m:int64->byte) = va1_fwdt PT sg0`)) THEN
  MP_TAC(SPEC `m:int64->byte` C8E_SNAP_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[va1_sg_ps]) THEN
  MP_TAC(ISPECL ([`fs:num->byte list#num#num`; `gl:num->wval`; `va1_snap (m:int64->byte) 2`; `va1_snap (m:int64->byte) 32`;
                 `\k. va1_snap (m:int64->byte) (64 + k)`; `val (va1_snap (m:int64->byte) 65)`; `va1_sg_x (va1_snap (m:int64->byte))`;
                 `\k. va1_snap (m:int64->byte) (6 + k)`; `\k. va1_snap (m:int64->byte) (12288 + k)`] @ c8e_sgl @
                 [`va1_snap (m:int64->byte) 5`; `va1_sg_x (va1_snap (m:int64->byte))`; `m:int64->byte`]) C8E_H2B_RAW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[C8E_MDL1] THEN UNDISCH_TAC `va1_fs_np fs` THEN SIMP_TAC[va1_fs_np]; ALL_TAC] THEN
  DISCH_THEN(C8E_MONO_TAC
    (MATCH_MP_TAC VA1_DEC_UNPUNCT THEN MAP_EVERY EXISTS_TAC [`m:int64->byte`; `va1_snap (m:int64->byte) 32`; `va1_sg_x (va1_snap (m:int64->byte))`] THEN
     ASM_REWRITE_TAC[])));;
let C8E_K1_IMG = prove
 (`!(PT:(num->int32)->num->int32) sg. va1_dom sg /\ va1_kind sg = 1 ==>
     va1_fwdt PT sg 2 = word_add (sg 2) (word 1) /\ va1_fwdt PT sg 3 = sg 3 /\ va1_fwdt PT sg 32 = sg 32 /\
     va1_fwdt PT sg 65 = sg 65 /\
     (!k. k < 1024 ==> va1_fwdt PT sg (64 + k) = sg (64 + k)) /\ (!k. k < 26 ==> va1_fwdt PT sg (6 + k) = sg (6 + k)) /\
     (!k. k < 262144 ==> va1_fwdt PT sg (12288 + k) = sg (12288 + k)) /\
     c8e_agps (va1_pop_fwd va1_ck va1_jigk
         (va1_pop_births (\k. sg (64 + k)) (\k. sg (6 + k)) (\k. sg (12288 + k)) (sg 2) (sg 3) (va1_sg_ps sg))
         (\k. sg (64 + k)) (\k. sg (6 + k)) (\k. sg (12288 + k)) (sg 2) (sg 3) (va1_sg_ps sg)) (va1_sg_ps (va1_fwdt PT sg)) /\
     c8e_ag (3 * val (sg 65)) (ve_fredkin_fwd (ve_vk (\k. sg (64 + k))) (va1_sg_x sg)) (va1_sg_x (va1_fwdt PT sg))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_dom] THEN STRIP_TAC THEN
  ABBREV_TAC `sg' = va1_fwdt PT sg` THEN
  SUBGOAL_THEN c8e_k1_E (LABEL_TAC "E") THENL
   [EXPAND_TAC "sg'" THEN REWRITE_TAC[va1_fwdt; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    ASM_REWRITE_TAC[ARITH_EQ]; ALL_TAC] THEN
  ABBREV_TAC `PF = va1_pop_fwd va1_ck va1_jigk
         (va1_pop_births (\k. (sg:num->int32) (64 + k)) (\k. sg (6 + k)) (\k. sg (12288 + k)) (sg 2) (sg 3) (va1_sg_ps sg))
         (\k. sg (64 + k)) (\k. sg (6 + k)) (\k. sg (12288 + k)) (sg 2) (sg 3) (va1_sg_ps sg)` THEN
  ABBREV_TAC `FX = ve_fredkin_fwd (ve_vk (\k. (sg:num->int32) (64 + k))) (va1_sg_x sg)` THEN
  REWRITE_TAC[c8e_agps; c8e_ag; va1_sg_ps; va1_sg_x; FST; SND] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT STRIP_TAC THEN USE_THEN "E" (fun th -> REWRITE_TAC[th]) THEN C8E_EVAL_TAC THEN
  REWRITE_TAC[va1_sg_x; FST; SND; ADD_SUB2] THEN CONV_TAC NUM_REDUCE_CONV);;
let C8E_AG_SYM = prove
 (`!n (s:(num->int32)#(num->int32)) s'. c8e_ag n s s' ==> c8e_ag n s' s`, SIMP_TAC[c8e_ag]);;
let C8E_AGPS_SYM = prove
 (`!(ps:(num->int32)#(num->int32)#(num->int32)#(num->int32)#((num->int32)#(num->int32)#(num->int32)#int32)) ps'.
     c8e_agps ps ps' ==> c8e_agps ps' ps`, SIMP_TAC[c8e_agps]);;
let C8E_ST_CONG = prove
 (`!t p ap mdl mdl' N (x:(num->int32)#(num->int32)) x' hp hp' tbl tbl'
    (ps:(num->int32)#(num->int32)#(num->int32)#(num->int32)#((num->int32)#(num->int32)#(num->int32)#int32)) ps' (m:int64->byte).
     (!k. k < 1024 ==> mdl k = mdl' k) /\ c8e_ag (3 * N) x x' /\ (!k. k < 26 ==> hp k = hp' k) /\
     (!k. k < 262144 ==> tbl k = tbl' k) /\ c8e_agps ps ps'
     ==> (va1_st t p ap mdl N x hp tbl ps m <=> va1_st t p ap mdl' N x' hp' tbl' ps' m)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C8E_ST_ALT; C8E_BS_ALT; va1_mdl; va1_vab; va1_w32s; c8e_agps; c8e_ag] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[]);;
let c8e_sgl0 = [`\k. (sg0:num->int32) (278528 + k)`; `\k. (sg0:num->int32) (280576 + k)`;
               `\k. (sg0:num->int32) (282624 + k)`; `\k. (sg0:num->int32) (284672 + k)`;
               `\w. (sg0:num->int32) (290816 + w)`; `\k. (sg0:num->int32) (286720 + k)`;
               `\k. (sg0:num->int32) (288768 + k)`; `(sg0:num->int32) 4`];;
let c8e_ps0 = end_itlist (fun a b -> mk_pair(a,b)) c8e_sgl0 and c8e_psm = end_itlist (fun a b -> mk_pair(a,b)) c8e_sgl;;
let c8e_mdl0 = `\k. (sg0:num->int32) (64 + k)` and c8e_hp0 = `\k. (sg0:num->int32) (6 + k)` and c8e_tbl0 = `\k. (sg0:num->int32) (12288 + k)`;;
let c8e_L0 = list_mk_comb(`va1_pop_births`, [c8e_mdl0; c8e_hp0; c8e_tbl0; `(sg0:num->int32) 2`; `(sg0:num->int32) 3`; c8e_ps0]);;
let c8e_PF0 = list_mk_comb(`va1_pop_fwd va1_ck va1_jigk`, [c8e_L0; c8e_mdl0; c8e_hp0; c8e_tbl0; `(sg0:num->int32) 2`; `(sg0:num->int32) 3`; c8e_ps0]);;
let c8e_FX0 = `ve_fredkin_fwd (ve_vk (\k. (sg0:num->int32) (64 + k))) (va1_sg_x sg0)`;;
let C8E_S1B = prove
 (`!(PT:(num->int32)->num->int32) (fs:num->byte list#num#num) (gl:num->wval) (m:int64->byte) sg0.
     va1_fs_all fs /\ va1_dom sg0 /\ va1_kind sg0 = 1 /\ va1_snap m = va1_fwdt PT sg0
     ==> va1_hcall (wasmc fs) va1_tick_backward_mc [] (word 1)
           (\gl' m'. gl' = gl /\ va1_snap m' = va1_bwd (va1_snap m)) gl m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_fs_all] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> concl th = `va1_snap (m:int64->byte) = va1_fwdt PT sg0`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C8E_DOM_N) THEN
  SUBGOAL_THEN `va1_bwd (va1_snap (m:int64->byte)) = sg0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `va1_fwdt PT sg0 = va1_snap (m:int64->byte)`)) THEN
    MATCH_MP_TAC VA1_INV_K1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`PT:(num->int32)->num->int32`; `sg0:num->int32`] C8E_K1_IMG) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `sg0:num->int32` C8E_KIND_FACTS) THEN REWRITE_TAC[ASSUME `va1_kind (sg0:num->int32) = 1`; ARITH_EQ] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `va1_log_ok ((sg0:num->int32) 2) (\w. sg0 (290816 + w)) (sg0 4)` ASSUME_TAC THENL
   [UNDISCH_TAC `va1_dom sg0` THEN REWRITE_TAC[va1_dom; ASSUME `va1_kind (sg0:num->int32) = 1`; ARITH_EQ] THEN SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(SPEC `m:int64->byte` C8E_SNAP_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[va1_sg_ps]) THEN
  MP_TAC(ISPECL [`word_add ((sg0:num->int32) 2) (word 1)`; `(sg0:num->int32) 3`; `(sg0:num->int32) 32`;
                 `\k. va1_snap (m:int64->byte) (64 + k)`; c8e_mdl0; `val ((sg0:num->int32) 65)`;
                 `va1_sg_x (va1_snap (m:int64->byte))`; c8e_FX0; `\k. va1_snap (m:int64->byte) (6 + k)`; c8e_hp0;
                 `\k. va1_snap (m:int64->byte) (12288 + k)`; c8e_tbl0; c8e_psm; c8e_PF0; `m:int64->byte`] C8E_ST_CONG) THEN
  ANTS_TAC THENL
   [CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC C8E_AG_SYM THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC C8E_AGPS_SYM THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  SUBGOAL_THEN (mk_conj(mk_comb(`ALL (\r:num->int32. r 6 = word_add ((sg0:num->int32) 2) (word 1))`, c8e_L0),
                         mk_binop `(<=):num->num->bool` (mk_binop `(+):num->num->num` `val ((sg0:num->int32) 4)` (mk_comb(`LENGTH:(num->int32)list->num`, c8e_L0))) `16384`))
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VA1_POP_BIRTHS_EQ] THEN MATCH_MP_TAC C8E_BORN_TAG THEN ASM_MESON_TAC[va1_log_ok]; ALL_TAC] THEN
  MP_TAC(ISPECL ([`fs:num->byte list#num#num`; `gl:num->wval`; `(sg0:num->int32) 2`; `(sg0:num->int32) 3`; `(sg0:num->int32) 32`;
                  c8e_mdl0; `val ((sg0:num->int32) 65)`; `va1_sg_x (sg0:num->int32)`; c8e_hp0; c8e_tbl0] @ c8e_sgl0 @
                 [c8e_L0; `va1_sg_x (va1_snap (m:int64->byte))`; `m:int64->byte`]) C8E_H1B_RAW) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_VAL]; ALL_TAC] THEN
  DISCH_THEN(C8E_MONO_TAC
    (MATCH_MP_TAC VA1_DEC_POP_BWD THEN
     MAP_EVERY EXISTS_TAC [`PT:(num->int32)->num->int32`; `m:int64->byte`; `va1_sg_x (va1_snap (m:int64->byte))`] THEN
     ASM_REWRITE_TAC[va1_sg_ps])));;
let C8E_TO_WASMN = prove
 (`!fs code args r (Q:(num->wval)->(int64->byte)->bool) gl m.
     va1_hcall (wasmc fs) code args r Q gl m ==> va1_hcall (wasmn fs) code args r Q gl m`,
  REWRITE_TAC[va1_hcall] THEN MESON_TAC[VA1_C5P_EVENTUALLY_WASMN]);;
let VA1_BWD_FUNCTION = prove
 (`!(PT:(num->int32)->num->int32) (fs:num->byte list#num#num) (gl:num->wval) (m:int64->byte).
     va1_fs_all fs /\ gl 0 = I32 (word 16384) /\ va1_imgt PT (va1_snap m)
     ==> va1_hcall (wasmn fs) va1_tick_backward_mc [] (word 1)
           (\gl' m'. gl' = gl /\ va1_snap m' = va1_bwd (va1_snap m)) gl m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_imgt] THEN STRIP_TAC THEN MATCH_MP_TAC C8E_TO_WASMN THEN
  SUBGOAL_THEN `~(va1_kind (va1_bwd (va1_snap (m:int64->byte))) = 4)` ASSUME_TAC THENL [ASM_MESON_TAC[va1_dom]; ALL_TAC] THEN
  MP_TAC(SPEC `va1_bwd (va1_snap (m:int64->byte))` C8E_KIND_RANGE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [MATCH_MP_TAC C8E_S0B; MATCH_MP_TAC C8E_S1B; MATCH_MP_TAC C8E_S2B] THEN
  MAP_EVERY EXISTS_TAC [`PT:(num->int32)->num->int32`; `va1_bwd (va1_snap (m:int64->byte))`] THEN ASM_REWRITE_TAC[]);;
let C8E_S2F = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (m:int64->byte).
     va1_fs_all fs /\ gl 0 = I32 (word 16384) /\ va1_dom (va1_snap m) /\ va1_kind (va1_snap m) = 2
     ==> va1_hcall (wasmn fs) va1_tick_forward_mc [] (word 1)
           (\gl' m'. gl' = gl /\ va1_snap m' = va1_fwdt va1_ptbl_sg (va1_snap m)) gl m`,
  C8E_SNAP_PRE_TAC THEN
  SUBGOAL_THEN `~(va1_snap (m:int64->byte) 33 = word 0 /\ va1_snap m 34 = word 0 /\ va1_snap m 35 = word 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `va1_dom (va1_snap (m:int64->byte))` THEN ASM_REWRITE_TAC[va1_dom; ARITH_EQ] THEN SIMP_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[va1_fs_np]) THEN
  MP_TAC(ISPECL [`fs:num->byte list#num#num`; `gl:num->wval`; `va1_snap (m:int64->byte) 2`; `\k. va1_snap (m:int64->byte) (64 + k)`;
                 `val (va1_snap (m:int64->byte) 65)`; `va1_sg_x (va1_snap (m:int64->byte))`;
                 `va1_snap (m:int64->byte) 33`; `va1_snap (m:int64->byte) 34`; `va1_snap (m:int64->byte) 35`; `m:int64->byte`;
                 `va1_sg_x (va1_snap (m:int64->byte))`] VA1_TICK_FORWARD_PUNCT_NU) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[C8E_MDL1] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> concl th = `word_add (va1_snap (m:int64->byte) 2) (word 1) = va1_snap m 32`)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `va1_snap (m:int64->byte) 3 = word 4294967295`)) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun lth ->
    let _,[step;pp;qq;cc] = strip_comb(concl lth) in
    let eth,dth = CONJ_PAIR VA1_TICKF_CALLEE in
    let code = rand(lhand(concl eth)) and e = rand(rand(concl eth)) and decls = rand(rand(concl dth)) in
    MATCH_MP_TAC (ISPECL [step; code; e; decls; `[]:wval list`; `word 1:int32`; pp; qq; cc] VA1_HCALL_ENSURES) THEN
    REWRITE_TAC[eth; dth; lth]) THEN
  CONJ_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[WCALL_ENTRY_READS];
    REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC VA1_DEC_PUNCT_FWD THEN
    MAP_EVERY EXISTS_TAC [`m:int64->byte`; `m1:int64->byte`; `va1_sg_x (va1_snap (m:int64->byte))`] THEN
    ASM_REWRITE_TAC[va1_ptbl_sg] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV THENC NUM_REDUCE_CONV)) THEN ASM_REWRITE_TAC[]]);;
let VA1_FWD_FUNCTION = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (m:int64->byte).
     va1_fs_all fs /\ gl 0 = I32 (word 16384) /\ va1_dom (va1_snap m)
     ==> va1_hcall (wasmn fs) va1_tick_forward_mc []
           (if va1_kind (va1_snap m) = 3 then word 0 else word 1)
           (\gl' m'. gl' = gl /\ va1_snap m' = va1_fwd (va1_snap m)) gl m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[va1_fwd] THEN
  SUBGOAL_THEN `~(va1_kind (va1_snap (m:int64->byte)) = 4)` ASSUME_TAC THENL [ASM_MESON_TAC[va1_dom]; ALL_TAC] THEN
  MP_TAC(SPEC `va1_snap (m:int64->byte)` C8E_KIND_RANGE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[ARITH_EQ] THENL
   [MATCH_MP_TAC C8E_TO_WASMN THEN MATCH_MP_TAC C8E_S0F;
    MATCH_MP_TAC C8E_TO_WASMN THEN MATCH_MP_TAC C8E_S1F;
    MATCH_MP_TAC C8E_S2F;
    MATCH_MP_TAC C8E_TO_WASMN THEN MATCH_MP_TAC C8E_S3F] THEN
  ASM_REWRITE_TAC[]);;
