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
(* ========================================================================= *)
(* Vortex chain, rung C4: spec-locked final leaf for chain_c4_final.spec     *)
(* (C4 agent, Claude Opus 5.5, 2026-11-13). Re-binds each of the 23 spec    *)
(* theorems against its frozen literal statement (ACCEPT_TAC of the layer   *)
(* or basis theorem). Defines nothing; no parser change.                    *)
(* ========================================================================= *)

let VA1_FILM_INVERSE_CLICK = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (ap:int32)
   (x0:(num->int32)#(num->int32)) (K:num) (n:num) (m0:int64->byte).
     va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ 1 <= K /\ K + 520 < 4294967296 /\ n <= 520 /\
     (ap = word 0 \/ K < val ap) /\ va1_np_st (word 0) ap mdl N x0 m0 /\ va1_clean m0
     ==> va1_hrun (wasmc fs) (REPLICATE K T)
           (\gl1 m1. gl1 = gl /\ va1_np_st (word K) ap mdl N (ITER K (va1_swf mdl) x0) m1 /\ va1_clean m1 /\
              !gl2 m2. va1_punct_rel mdl gl1 m1 gl2 m2
                ==> va1_hrun (wasmc fs) (APPEND (REPLICATE n T) (REPLICATE (n + K) F))
                      (\gl3 m3. gl3 = gl /\ va1_np_st (word 0) ap mdl N x0 m3 /\ va1_clean m3 /\
                         read (bytes32 (word 16404)) m3 = read (bytes32 (word 16404)) m0 /\
                         va1_film_bytes N m0 m3) gl2 m2) gl m0`,
  ACCEPT_TAC VA1_FILM_INVERSE_CLICK);;

let VA1_FILM_INVERSE_AUTO = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num)
   (x0:(num->int32)#(num->int32)) (K:num) (n:num) (m0:int64->byte).
     va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ 1 <= K /\ K + 520 < 4294967296 /\ n <= 520 /\
     va1_np_st (word 0) (word K) mdl N x0 m0 /\ va1_clean m0
     ==> va1_hrun (wasmc fs) (REPLICATE (K - 1) T)
           (\gl1 m1. gl1 = gl /\ va1_np_st (word (K - 1)) (word K) mdl N (ITER (K - 1) (va1_swf mdl) x0) m1 /\
              va1_clean m1 /\
              !gl2 m2. va1_autopunct_rel mdl N (ITER (K - 1) (va1_swf mdl) x0) gl1 m1 gl2 m2
                ==> va1_hrun (wasmc fs) (APPEND (REPLICATE n T) (REPLICATE (n + K) F))
                      (\gl3 m3. gl3 = gl /\ va1_np_st (word 0) (word K) mdl N x0 m3 /\ va1_clean m3 /\
                         read (bytes32 (word 16404)) m3 = read (bytes32 (word 16404)) m0 /\
                         va1_film_bytes N m0 m3) gl2 m2) gl m0`,
  ACCEPT_TAC VA1_FILM_INVERSE_AUTO);;

let VA1_FILM_TO_END_CLICK = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (ap:int32)
   (x0:(num->int32)#(num->int32)) (K:num) (m0:int64->byte).
     va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ 1 <= K /\ K + 520 < 4294967296 /\
     (ap = word 0 \/ K < val ap) /\ va1_np_st (word 0) ap mdl N x0 m0 /\ va1_clean m0
     ==> va1_hrun (wasmc fs) (REPLICATE K T)
           (\gl1 m1. gl1 = gl /\ va1_np_st (word K) ap mdl N (ITER K (va1_swf mdl) x0) m1 /\ va1_clean m1 /\
              !gl2 m2. va1_punct_rel mdl gl1 m1 gl2 m2
                ==> va1_hrun (wasmc fs) (REPLICATE 520 T)
                      (\gl3 m3. gl3 = gl /\
                         va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 0)
                           (\gl4 m4. gl4 = gl3 /\ m4 = m3 /\
                              va1_hrun (wasmc fs) (REPLICATE (520 + K) F)
                                (\gl5 m5. gl5 = gl /\ va1_np_st (word 0) ap mdl N x0 m5 /\ va1_clean m5 /\
                                   read (bytes32 (word 16404)) m5 = read (bytes32 (word 16404)) m0 /\
                                   va1_film_bytes N m0 m5) gl4 m4) gl3 m3) gl2 m2) gl m0`,
  ACCEPT_TAC VA1_FILM_TO_END_CLICK);;

let VA1_FILM_TO_END_AUTO = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num)
   (x0:(num->int32)#(num->int32)) (K:num) (m0:int64->byte).
     va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ 1 <= K /\ K + 520 < 4294967296 /\
     va1_np_st (word 0) (word K) mdl N x0 m0 /\ va1_clean m0
     ==> va1_hrun (wasmc fs) (REPLICATE (K - 1) T)
           (\gl1 m1. gl1 = gl /\ va1_np_st (word (K - 1)) (word K) mdl N (ITER (K - 1) (va1_swf mdl) x0) m1 /\
              va1_clean m1 /\
              !gl2 m2. va1_autopunct_rel mdl N (ITER (K - 1) (va1_swf mdl) x0) gl1 m1 gl2 m2
                ==> va1_hrun (wasmc fs) (REPLICATE 520 T)
                      (\gl3 m3. gl3 = gl /\
                         va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 0)
                           (\gl4 m4. gl4 = gl3 /\ m4 = m3 /\
                              va1_hrun (wasmc fs) (REPLICATE (520 + K) F)
                                (\gl5 m5. gl5 = gl /\ va1_np_st (word 0) (word K) mdl N x0 m5 /\ va1_clean m5 /\
                                   read (bytes32 (word 16404)) m5 = read (bytes32 (word 16404)) m0 /\
                                   va1_film_bytes N m0 m5) gl4 m4) gl3 m3) gl2 m2) gl m0`,
  ACCEPT_TAC VA1_FILM_TO_END_AUTO);;

let VA1_PUNCT_REL_SAT = prove
 (`!(mdl:num->int32) (gl:num->wval) (m:int64->byte). ?gl' m'. va1_punct_rel mdl gl m gl' m'`,
  ACCEPT_TAC VA1_PUNCT_REL_SAT);;

let VA1_AUTOPUNCT_REL_SAT = prove
 (`!(mdl:num->int32) (N:num) (x:(num->int32)#(num->int32)) (gl:num->wval) (m:int64->byte).
     N <= 640 ==> ?gl' m'. va1_autopunct_rel mdl N x gl m gl' m'`,
  ACCEPT_TAC VA1_AUTOPUNCT_REL_SAT);;

let VA1_FILM_SAT = prove
 (`(?fs:num->byte list#num#num. va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1)) /\
  (!(ap:int32) (mdl:num->int32) (N:num) (x0:(num->int32)#(num->int32)).
     N <= 640 ==> ?m0:int64->byte. va1_np_st (word 0) ap mdl N x0 m0 /\ va1_clean m0) /\
  (?(fs:num->byte list#num#num) (mdl:num->int32) (N:num) (x0:(num->int32)#(num->int32)) (m0:int64->byte).
     va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\ mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
     va1_np_st (word 0) (word 0) mdl N x0 m0 /\ va1_clean m0) /\
  (!K. ?(fs:num->byte list#num#num) (mdl:num->int32) (N:num) (x0:(num->int32)#(num->int32)) (m0:int64->byte).
     va1_fs_np fs /\ va1_fs_pop fs /\ fs 26 = (va1_f26_mc,0,1) /\ mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
     va1_np_st (word 0) (word K) mdl N x0 m0 /\ va1_clean m0)`,
  ACCEPT_TAC VA1_FILM_SAT);;

let VA1_HCALL_UNPUNCT = prove
 (`!fs gl p ap mdl N y hp tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32) h m.
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
     fs 10 = (va1_f10_mc,0,0) /\ fs 26 = (va1_f26_mc,0,1) /\ fs 28 = (va1_f28_mc,0,0) /\
     ~(p = word 4294967295) /\ ~(p = word 0) /\
     va1_st p p ap mdl N y hp tbl (ra,rb,jq,jp,di,zq,zp,nd) m /\ read (bytes32 (word 16404)) m = h
     ==> va1_hcall (wasmc fs) va1_tick_backward_mc [] (word 1)
           (\gl' m'. gl' = gl /\
                     va1_st (word_sub p (word 1)) (word 4294967295) ap mdl N (ve_fredkin_bwdn (\i. ve_vk mdl) 16 y)
                            (\k. if k < 24 then word 0 else hp k) (\k. word 0)
                            ((\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),word 0) m' /\
                     read (bytes32 (word 16404)) m' = word_add h (va1_bad mdl tbl (ra,rb,jq,jp,zq,zp,nd)) /\
                     va1_unp_frame m m') gl m`,
  ACCEPT_TAC VA1_HCALL_UNPUNCT);;

let VA1_BAD_PUNCT = prove
 (`!mdl tbl. va1_bad mdl tbl ((\k. word 251658), va1_rbinit tbl, (\k. word 0), (\k. word 0), (\k. word 0),
                            va1_zpseed mdl, word 0) = word 0`,
  ACCEPT_TAC VA1_BAD_PUNCT);;

let VA1_POP_CHAIN_BYTES = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (p:int32) (ap:int32)
   (x0:(num->int32)#(num->int32)) (hp:num->int32) (tbl:num->int32) (t0:int32)
   (S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32)
   (k:num) (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_pop fs /\
     ~(p = word 4294967295) /\ val p <= val t0 /\ val t0 + k <= val p + 520 /\ val p + 520 < 4294967296 /\
     va1_log_ok t0 (va1_diof S0) (va1_ndof S0) /\ va1_st t0 p ap mdl N x0 hp tbl S0 m
     ==> va1_hrun (wasmc fs) (APPEND (REPLICATE k T) (REPLICATE k F))
           (\gl' m'. gl' = gl /\ va1_st t0 p ap mdl N x0 hp tbl S0 m' /\ va1_pop_frame m m') gl m`,
  ACCEPT_TAC VA1_POP_CHAIN_BYTES);;

let VA1_POP_HCALL_END = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (t:int32) (p:int32) (ap:int32) (m:int64->byte).
     ~(p = word 4294967295) /\ val p <= val t /\ val (word_add p (word 520)) <= val t /\
     va1_tick t m /\ va1_pop p ap m
     ==> va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 0) (\gl' m'. gl' = gl /\ m' = m) gl m`,
  ACCEPT_TAC VA1_POP_HCALL_END);;

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
  ACCEPT_TAC VA1_NP_SCRUB_FRAME);;

let VE_VORT_STEPS_INVERSE_VK = prove
 (`!(mdl:num->int32) n s.
     ve_fredkin_bwdn (\i. ve_vk mdl) n (ve_fredkin_fwdn (\i. ve_vk mdl) n s) = s`,
  ACCEPT_TAC VE_VORT_STEPS_INVERSE_VK);;

let VA1_HRUN_CLAUSES = prove
 (`(!(step:wasmstate->wasmstate->bool) (Q:(num->wval)->(int64->byte)->bool) gl m.
     va1_hrun step [] Q gl m <=> Q gl m) /\
  (!(step:wasmstate->wasmstate->bool) c cs (Q:(num->wval)->(int64->byte)->bool) gl m.
     va1_hrun step (CONS c cs) Q gl m <=>
     va1_hcall step (if c then va1_tick_forward_mc else va1_tick_backward_mc) [] (word 1)
               (va1_hrun step cs Q) gl m)`,
  ACCEPT_TAC VA1_HRUN_CLAUSES);;

let VA1_HRUN_APPEND = prove
 (`!(step:wasmstate->wasmstate->bool) (cs1:bool list) (cs2:bool list) (Q:(num->wval)->(int64->byte)->bool).
     va1_hrun step (APPEND cs1 cs2) Q = va1_hrun step cs1 (va1_hrun step cs2 Q)`,
  ACCEPT_TAC VA1_HRUN_APPEND);;

let VA1_CMDS_OK_CLAUSES = prove
 (`(!K u. va1_cmds_ok K u [] <=> T) /\
  (!K u c cs. va1_cmds_ok K u (CONS c cs) <=>
     if c then u < K /\ va1_cmds_ok K (u + 1) cs else 0 < u /\ va1_cmds_ok K (u - 1) cs)`,
  ACCEPT_TAC VA1_CMDS_OK_CLAUSES);;

let VA1_CMDS_END_CLAUSES = prove
 (`(!u. va1_cmds_end u [] = u) /\
  (!u c cs. va1_cmds_end u (CONS c cs) = va1_cmds_end (if c then u + 1 else u - 1) cs)`,
  ACCEPT_TAC VA1_CMDS_END_CLAUSES);;

let VA1_FWDN_CLAUSES = prove
 (`(!f s. ve_fredkin_fwdn f 0 s = s) /\
   (!f n s. ve_fredkin_fwdn f (SUC n) s = ve_fredkin_fwd (f n) (ve_fredkin_fwdn f n s))`,
  ACCEPT_TAC VA1_FWDN_CLAUSES);;

let VA1_BWDN_CLAUSES = prove
 (`(!f s. ve_fredkin_bwdn f 0 s = s) /\
   (!f n s. ve_fredkin_bwdn f (SUC n) s = ve_fredkin_bwdn f n (ve_fredkin_bwd (f n) s))`,
  ACCEPT_TAC VA1_BWDN_CLAUSES);;

let VA1_ISQ_CLAUSES = prove
 (`(!x. ve_isq 0 x = x) /\ (!k x. ve_isq (SUC k) x = ve_isq_step (ve_isq k x))`,
  ACCEPT_TAC VA1_ISQ_CLAUSES);;

let VA1_VK_RS_CLAUSES = prove
 (`(!X C i c. ve_vk_rs X C i 0 c = word 0) /\
   (!X C i k c. ve_vk_rs X C i (SUC k) c = word_add (ve_vk_ti X C i (i + 1 + k) c) (ve_vk_rs X C i k c))`,
  ACCEPT_TAC VA1_VK_RS_CLAUSES);;

let VA1_VK_ACC_CLAUSES = prove
 (`(!X C n j c. ve_vk_acc X C n 0 j c = word 0) /\
   (!X C n i j c. ve_vk_acc X C n (SUC i) j c =
      if j = i then word_add (ve_vk_acc X C n i j c) (ve_vk_rs X C i (n - 1 - i) c)
      else if i < j then ve_vk_upd X C i j c (ve_vk_acc X C n i j c)
      else ve_vk_acc X C n i j c)`,
  ACCEPT_TAC VA1_VK_ACC_CLAUSES);;

let VA1_WDECL_VALS_CLAUSES = prove
 (`(!code pc. wdecl_vals 0 (code:byte list) pc = SOME ([]:wval list)) /\
  (!k code pc. wdecl_vals (SUC k) code pc =
     wobind (wuleb (wdrop pc code)) (\p.
     wobind (whd (wdrop (pc + SND p) code)) (\t.
     wobind (wdecl_vals k code (pc + SND p + 1)) (\r.
       SOME (APPEND (REPLICATE (FST p) (wzero_of (val (t:byte)))) r)))))`,
  ACCEPT_TAC VA1_WDECL_VALS_CLAUSES);;

