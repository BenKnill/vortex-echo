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
needs "chain_c3a_defs.ml";;
needs "chain_c3a_f26a.ml";;
needs "chain_c3a_f26b.ml";;
needs "chain_c3a_f26c.ml";;
needs "chain_c3a_seq.ml";;
needs "chain_c3a_fin.ml";;
needs "chain_c2_host_pop.ml";;
needs "chain_c2_chain.ml";;
needs "chain_c1_np.ml";;
needs "chain_c1_frame.ml";;
needs "chain_c4_lem.ml";;
needs "chain_c4_film.ml";;
needs "chain_c3b_dec.ml";;
needs "chain_c7_c3b_defs.ml";;
needs "chain_c7_c3b_l1.ml";;
needs "chain_c7_c3b_pure.ml";;
needs "chain_c5_dec.ml";;
needs "chain_c5_tacs.ml";;
needs "chain_c5_leaves.ml";;
needs "chain_c5_punct_a.ml";;
needs "chain_c5_punct_b.ml";;
needs "chain_c5_punct_c.ml";;
needs "chain_c7_c6a_host.ml";;
needs "chain_c5p_frames.ml";;
needs "chain_c5p_rules.ml";;
needs "chain_c7_c6b_host.ml";;
needs "c8b_stmts.ml";;
needs "c8b_vort_u.ml";;
needs "c8b_nopop_u.ml";;
needs "c8b_pop_u.ml";;
needs "c8b_c6_u.ml";;
needs "c8a_born_defs.ml";;
needs "c8a_shape_lem.ml";;
needs "c8a_isqv.ml";;
needs "c8a_seg1v.ml";;
needs "c8a_fold_lem.ml";;
needs "c8a_iter1.ml";;
needs "c8a_loop2v.ml";;
needs "c8a_loop3v.ml";;
needs "c8a_final_lem.ml";;
needs "c8a_birtheq.ml";;
needs "c8a_r4n_stmts.ml";;
needs "c8a_r4n_lem.ml";;
(* vortex-chain C8a final leaf rows A8/A9 (Claude Opus 5.5, 2026-11-15). Spec c8a_r4n.spec (frozen sha256 in FROZEN-C8A.txt).
   A8 VA1_TICK_FORWARD_POP_COND_NU is re-bound from the s5 layer (c8a_r4n_lem.ml); A9 R4/R4b/R4c _NU by the MATCH_MP_TAC
   chain of C8b B6 (c8b_pop_u.ml), with VA1_BIRTH_EQ (s4 layer, c8a_birtheq.ml) for the births contract; pins re-bound. *)
let VA1_TICK_FORWARD_POP_COND_NU = prove(parse_term c8a_spec_VA1_TICK_FORWARD_POP_COND_NU, ACCEPT_TAC VA1_TICK_FORWARD_POP_COND_NU);;
let VA1_TICK_FORWARD_POP_NU = prove(parse_term c8a_spec_VA1_TICK_FORWARD_POP_NU,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC VA1_TICK_FORWARD_POP_COND_NU THEN ASM_REWRITE_TAC POP_Q3_R1_OKS);;
let VA1_TICK_FORWARD_POP_R5_NU = prove(parse_term c8a_spec_VA1_TICK_FORWARD_POP_R5_NU,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC VA1_TICK_FORWARD_POP_NU THEN ASM_REWRITE_TAC[VA1_CORRK_OK; VA1_JIGK_OK]);;
let VA1_TICK_FORWARD_POP_R5C_NU = prove(parse_term c8a_spec_VA1_TICK_FORWARD_POP_R5C_NU,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC VA1_TICK_FORWARD_POP_R5_NU THEN ASM_REWRITE_TAC[VA1_BIRTH_EQ]);;
let VA1P_KD_FWDN_CLAUSES = prove(`(!K D s. ve_kd_fwdn K D 0 s = s) /\
   (!K D n s. ve_kd_fwdn K D (SUC n) s = ve_kd_fwd (K n) (D n) (ve_kd_fwdn K D n s))`, ACCEPT_TAC VA1P_KD_FWDN_CLAUSES);;
let VA1_FOLD1_CLAUSES = prove(`(!mdl hp tbl t rb nd0 st. va1_fold1 mdl hp tbl t rb nd0 0 st = st) /\
  (!mdl hp tbl t rb nd0 k st. va1_fold1 mdl hp tbl t rb nd0 (SUC k) st =
       va1_step1 mdl hp tbl t rb nd0 k (va1_fold1 mdl hp tbl t rb nd0 k st))`, REWRITE_TAC[va1_fold1]);;
let VA1_FOLD2_CLAUSES = prove(`(!mdl hp tbl t rb nd0 L. va1_fold2 mdl hp tbl t rb nd0 0 L = L) /\
  (!mdl hp tbl t rb nd0 k L. va1_fold2 mdl hp tbl t rb nd0 (SUC k) L =
       va1_step2 mdl hp tbl t rb nd0 k (va1_fold2 mdl hp tbl t rb nd0 k L))`, REWRITE_TAC[va1_fold2]);;
let VA1_FOLD3_CLAUSES = prove(`(!mdl hp tbl t ra rb nd0 L. va1_fold3 mdl hp tbl t ra rb nd0 0 L = L) /\
  (!mdl hp tbl t ra rb nd0 k L. va1_fold3 mdl hp tbl t ra rb nd0 (SUC k) L =
       va1_step3 mdl hp tbl t ra rb nd0 k (va1_fold3 mdl hp tbl t ra rb nd0 k L))`, REWRITE_TAC[va1_fold3]);;
let VA1_ISQ_CLAUSES = prove(`(!x. ve_isq 0 x = x) /\ (!k x. ve_isq (SUC k) x = ve_isq_step (ve_isq k x))`, ACCEPT_TAC VA1_ISQ_CLAUSES);;
let VA1_PUSH_CLAUSES = prove(`(!bs. va1_push ([]:(num->int32)list) (bs:(num->int32)#(num->int32)#(num->int32)#int32) = bs) /\
   (!r rs bs. va1_push (CONS r rs) bs = va1_push rs (va1_push1 r bs))`, ACCEPT_TAC VA1_PUSH_CLAUSES);;
let VA1_VK_ACC_CLAUSES = prove(`(!X C n j c. ve_vk_acc X C n 0 j c = word 0) /\
   (!X C n i j c. ve_vk_acc X C n (SUC i) j c =
      if j = i then word_add (ve_vk_acc X C n i j c) (ve_vk_rs X C i (n - 1 - i) c)
      else if i < j then ve_vk_upd X C i j c (ve_vk_acc X C n i j c)
      else ve_vk_acc X C n i j c)`, ACCEPT_TAC VA1_VK_ACC_CLAUSES);;
let VA1_VK_RS_CLAUSES = prove(`(!X C i c. ve_vk_rs X C i 0 c = word 0) /\
   (!X C i k c. ve_vk_rs X C i (SUC k) c = word_add (ve_vk_ti X C i (i + 1 + k) c) (ve_vk_rs X C i k c))`, ACCEPT_TAC VA1_VK_RS_CLAUSES);;
let VA1_WDECL_VALS_CLAUSES = prove(`(!code pc. wdecl_vals 0 (code:byte list) pc = SOME ([]:wval list)) /\
  (!k code pc. wdecl_vals (SUC k) code pc =
     wobind (wuleb (wdrop pc code)) (\p.
     wobind (whd (wdrop (pc + SND p) code)) (\t.
     wobind (wdecl_vals k code (pc + SND p + 1)) (\r.
       SOME (APPEND (REPLICATE (FST p) (wzero_of (val (t:byte)))) r)))))`, ACCEPT_TAC VA1_WDECL_VALS_CLAUSES);;
let C8A_R4N_CHECK = if forall (fun th -> hyp th = []) [VA1_TICK_FORWARD_POP_COND_NU; VA1_TICK_FORWARD_POP_NU; VA1_TICK_FORWARD_POP_R5_NU; VA1_TICK_FORWARD_POP_R5C_NU; VA1P_KD_FWDN_CLAUSES; VA1_FOLD1_CLAUSES; VA1_FOLD2_CLAUSES; VA1_FOLD3_CLAUSES; VA1_ISQ_CLAUSES; VA1_PUSH_CLAUSES; VA1_VK_ACC_CLAUSES; VA1_VK_RS_CLAUSES; VA1_WDECL_VALS_CLAUSES] then TRUTH else failwith "C8A_R4N_CHECK";;
