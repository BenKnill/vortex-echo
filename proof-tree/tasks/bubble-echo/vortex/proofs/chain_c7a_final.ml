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
needs "chain_c7_film.ml";;
needs "chain_c7_host.ml";;
(* C7a spec-locked final leaf for chain_c7a_final.spec (C7, Claude Opus 5.5, 2026-11-13): re-binds each spec theorem
   against its frozen literal statement (ACCEPT_TAC of the layer theorem). Defines nothing. *)
let VA1_FILM_CLICK = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (ap:int32)
   (x0:(num->int32)#(num->int32)) (K:num) (n:num) (m0:int64->byte) (a0:int32) (a1:int32) (a2:int32).
     va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\
     fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\ gl 0 = I32 (word 16384) /\
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ 1 <= K /\ K + 520 < 4294967296 /\ n <= 520 /\
     (ap = word 0 \/ K < val ap) /\ va1_np_st (word 0) ap mdl N x0 m0 /\ va1_clean m0 /\
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0)
     ==> va1_hrun (wasmc fs) (REPLICATE K T)
           (\gl1 m1. va1_hcall (wasmc fs) va1_puncture_mc [I32 a2; I32 a1; I32 a0] (word 0)
              (va1_hrun (wasmc fs) (APPEND (REPLICATE n T) (REPLICATE (n + K) F))
                 (\gl3 m3. gl3 = gl /\ va1_np_st (word 0) ap mdl N x0 m3 /\ va1_clean m3 /\
                           read (bytes32 (word 16404)) m3 = read (bytes32 (word 16404)) m0 /\
                           va1_film_bytes N m0 m3)) gl1 m1) gl m0`,
  ACCEPT_TAC VA1_FILM_CLICK);;

let VA1_FILM_CLICK_TO_END = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (ap:int32)
   (x0:(num->int32)#(num->int32)) (K:num) (m0:int64->byte) (a0:int32) (a1:int32) (a2:int32).
     va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\
     fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\ gl 0 = I32 (word 16384) /\
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ 1 <= K /\ K + 520 < 4294967296 /\
     (ap = word 0 \/ K < val ap) /\ va1_np_st (word 0) ap mdl N x0 m0 /\ va1_clean m0 /\
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0)
     ==> va1_hrun (wasmc fs) (REPLICATE K T)
           (\gl1 m1. va1_hcall (wasmc fs) va1_puncture_mc [I32 a2; I32 a1; I32 a0] (word 0)
              (va1_hrun (wasmc fs) (REPLICATE 520 T)
                 (\gl3 m3. gl3 = gl /\
                    va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 0)
                      (\gl4 m4. gl4 = gl3 /\ m4 = m3 /\
                         va1_hrun (wasmc fs) (REPLICATE (520 + K) F)
                           (\gl5 m5. gl5 = gl /\ va1_np_st (word 0) ap mdl N x0 m5 /\ va1_clean m5 /\
                              read (bytes32 (word 16404)) m5 = read (bytes32 (word 16404)) m0 /\
                              va1_film_bytes N m0 m5) gl4 m4) gl3 m3)) gl1 m1) gl m0`,
  ACCEPT_TAC VA1_FILM_CLICK_TO_END);;

let VA1_C7A_SAT = prove
 (`!K n. 1 <= K /\ K + 520 < 4294967296 /\ n <= 520
        ==> ?(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (ap:int32)
             (x0:(num->int32)#(num->int32)) (m0:int64->byte) (a0:int32) (a1:int32) (a2:int32).
              va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\
              fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\ gl 0 = I32 (word 16384) /\
              mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
              (ap = word 0 \/ K < val ap) /\ va1_np_st (word 0) ap mdl N x0 m0 /\ va1_clean m0 /\
              ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0)`,
  ACCEPT_TAC VA1_C7A_SAT);;

let VA1_WDECL_VALS_CLAUSES = prove
 (`(!code pc. wdecl_vals 0 (code:byte list) pc = SOME ([]:wval list)) /\
  (!k code pc. wdecl_vals (SUC k) code pc =
     wobind (wuleb (wdrop pc code)) (\p.
     wobind (whd (wdrop (pc + SND p) code)) (\t.
     wobind (wdecl_vals k code (pc + SND p + 1)) (\r.
       SOME (APPEND (REPLICATE (FST p) (wzero_of (val (t:byte)))) r)))))`,
  ACCEPT_TAC VA1_WDECL_VALS_CLAUSES);;

