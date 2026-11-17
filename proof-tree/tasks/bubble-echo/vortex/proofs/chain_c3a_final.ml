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
(* ========================================================================= *)
(* Vortex chain, rung C3a: spec-locked final leaf for chain_c3a_final2.spec  *)
(* (frozen sha256 bdd326f9...; C3A, Claude Opus 5.5, 2026-11-13). Every one  *)
(* of the 15 spec theorems is re-bound here against its frozen literal      *)
(* statement (ACCEPT_TAC of the layer or basis theorem), including the 6     *)
(* copied ones. Layers: chain_c3a_defs/f26a/f26b/f26c/seq/fin.ml. This leaf  *)
(* defines nothing and changes no parser state.                              *)
(* ========================================================================= *)

let VA1_F26_CALLEE = prove
 (`wasm_entry va1_f26_mc = SOME 5 /\
  wasm_decl_vals va1_f26_mc = SOME [I32 (word 0); I32 (word 0); I32 (word 0); I32 (word 0); I32 (word 0); I64 (word 0)]`,
  ACCEPT_TAC VA1_F26_CALLEE);;

let VA1_F26_OK = prove
 (`!p ap mdl hp tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32) h decls.
     ~(p = word 4294967295) /\ wasm_decl_vals va1_f26_mc = SOME decls
     ==> ensures wasm
          (\s. read wcode s = va1_f26_mc /\ read wpc s = word 5 /\ read wstatus s = WRunning /\
               read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\ read wlocals s = wcall_locals [] decls /\
               va1_pop p ap (read wmem s) /\ va1_mdl mdl (read wmem s) /\
               read (bytes32 (word 16404)) (read wmem s) = h /\
               va1_w32s 16408 26 hp (read wmem s) /\ va1_w32s 65536 262144 tbl (read wmem s) /\
               va1_w32s 1130496 2048 ra (read wmem s) /\ va1_w32s 1138688 2048 rb (read wmem s) /\
               va1_w32s 1146880 2048 jq (read wmem s) /\ va1_w32s 1155072 2048 jp (read wmem s) /\
               va1_bs (di,zq,zp,nd) (read wmem s))
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (va1_bad mdl tbl (ra,rb,jq,jp,zq,zp,nd))] /\
               va1_pop (word 4294967295) ap (read wmem s) /\
               read (bytes32 (word 16404)) (read wmem s) = word_add h (va1_bad mdl tbl (ra,rb,jq,jp,zq,zp,nd)) /\
               va1_w32s 16408 26 (\k. if k < 24 then word 0 else hp k) (read wmem s) /\
               va1_w32s 1130496 2048 (\k. word 0) (read wmem s) /\ va1_w32s 1138688 2048 (\k. word 0) (read wmem s) /\
               va1_w32s 1146880 2048 (\k. word 0) (read wmem s) /\ va1_w32s 1155072 2048 (\k. word 0) (read wmem s) /\
               va1_bs ((\k. word 0),(\k. word 0),(\k. word 0),word 0) (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocal 0; wlocal 1; wlocal 2; wlocal 3; wlocal 4; wlocal 5] ,,
           MAYCHANGE [wmem :> bytes(word 16396,116)] ,, MAYCHANGE [wmem :> bytes(word 1130496,835584)])`,
  ACCEPT_TAC VA1_F26_OK);;

let VA1_TICK_UNPUNCT = prove
 (`!fs gl p ap mdl N y hp tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32) h.
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
     fs 10 = (va1_f10_mc,0,0) /\ fs 26 = (va1_f26_mc,0,1) /\ fs 28 = (va1_f28_mc,0,0) /\
     ~(p = word 4294967295) /\ ~(p = word 0)
     ==> ensures (wasmc fs)
          (\s. read wcode s = va1_tick_backward_mc /\ read wpc s = word 3 /\ read wstatus s = WRunning /\
               read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_st p p ap mdl N y hp tbl (ra,rb,jq,jp,di,zq,zp,nd) (read wmem s) /\
               read (bytes32 (word 16404)) (read wmem s) = h)
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 1)] /\
               va1_st (word_sub p (word 1)) (word 4294967295) ap mdl N (ve_fredkin_bwdn (\i. ve_vk mdl) 16 y)
                      (\k. if k < 24 then word 0 else hp k) (\k. word 0)
                      ((\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),word 0) (read wmem s) /\
               read (bytes32 (word 16404)) (read wmem s) = word_add h (va1_bad mdl tbl (ra,rb,jq,jp,zq,zp,nd)))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocal 0; wlocal 1] ,,
           MAYCHANGE [wmem :> bytes(word 16392,120)] ,, MAYCHANGE [wmem :> bytes(word 65536,1048576)] ,,
           MAYCHANGE [wmem :> bytes(word 1114112,851968)] ,, MAYCHANGE [wmem :> bytes(word 1966080,73728)])`,
  ACCEPT_TAC VA1_TICK_UNPUNCT);;

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

let VA1_BAD_COUNT = prove
 (`!mdl tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32).
     val nd <= 16384
     ==> val (va1_bad mdl tbl (ra,rb,jq,jp,zq,zp,nd)) = val nd + nsum (0..2047) (\k. va1_mis mdl tbl (ra,rb,jq,jp,zq,zp) k)`,
  ACCEPT_TAC VA1_BAD_COUNT);;

let VA1_BAD_ZERO_IFF = prove
 (`!mdl tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32).
     val nd <= 16384
     ==> (va1_bad mdl tbl (ra,rb,jq,jp,zq,zp,nd) = word 0 <=>
          nd = word 0 /\
          !k. k < 2048 ==> ra k = word 251658 /\ rb k = va1_rbinit tbl k /\ jq k = word 0 /\
                           jp k = word 0 /\ zq k = word 0 /\ zp k = va1_zpseed mdl k)`,
  ACCEPT_TAC VA1_BAD_ZERO_IFF);;

let VA1_UNPUNCT_SAT = prove
 (`(?fs:num->byte list#num#num. fs 10 = (va1_f10_mc,0,0) /\ fs 26 = (va1_f26_mc,0,1) /\ fs 28 = (va1_f28_mc,0,0)) /\
  (!gl p ap mdl N y hp tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32) h.
     N <= 640
     ==> ?s. read wcode s = va1_tick_backward_mc /\ read wpc s = word 3 /\ read wstatus s = WRunning /\
             read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
             read wmemsize s = 4194304 /\ read wglobals s = gl /\
             va1_st p p ap mdl N y hp tbl (ra,rb,jq,jp,di,zq,zp,nd) (read wmem s) /\
             read (bytes32 (word 16404)) (read wmem s) = h)`,
  ACCEPT_TAC VA1_UNPUNCT_SAT);;

let VA1_F26_SAT = prove
 (`!p ap mdl hp tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32) h.
     ?s. read wcode s = va1_f26_mc /\ read wpc s = word 5 /\ read wstatus s = WRunning /\
         read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
         read wmemsize s = 4194304 /\
         read wlocals s = wcall_locals [] [I32 (word 0); I32 (word 0); I32 (word 0); I32 (word 0); I32 (word 0); I64 (word 0)] /\
         va1_pop p ap (read wmem s) /\ va1_mdl mdl (read wmem s) /\
         read (bytes32 (word 16404)) (read wmem s) = h /\
         va1_w32s 16408 26 hp (read wmem s) /\ va1_w32s 65536 262144 tbl (read wmem s) /\
         va1_w32s 1130496 2048 ra (read wmem s) /\ va1_w32s 1138688 2048 rb (read wmem s) /\
         va1_w32s 1146880 2048 jq (read wmem s) /\ va1_w32s 1155072 2048 jp (read wmem s) /\
         va1_bs (di,zq,zp,nd) (read wmem s)`,
  ACCEPT_TAC VA1_F26_SAT);;

let VA1_TICKB_CALLEE = prove
 (`wasm_entry va1_tick_backward_mc = SOME 3 /\
  wasm_decl_vals va1_tick_backward_mc = SOME [I32 (word 0); I32 (word 0)]`,
  ACCEPT_TAC VA1_TICKB_CALLEE);;

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

