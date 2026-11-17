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
needs "chain_c2_host_pop.ml";;
needs "chain_c2_chain.ml";;
(* ========================================================================= *)
(* Vortex chain, rung C2: spec-locked final leaf for chain_c2_final.spec     *)
(* (frozen sha256 c7a0c0a8...; PROVE-C2, Claude Opus 5.5, 2026-11-11).       *)
(* Every one of the 33 spec theorems is re-bound here against its frozen     *)
(* literal statement (ACCEPT_TAC of the layer or basis theorem), including   *)
(* the 22 copied ones, so that the receipt's inspect checks each one in this *)
(* leaf. Layers: chain_c2_host_pop.ml, chain_c2_chain.ml. This leaf defines  *)
(* nothing and changes no parser state.                                      *)
(* ========================================================================= *)

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
  ACCEPT_TAC VA1_POP_REACH_CLAUSES);;

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
  ACCEPT_TAC VA1_POP_HCALL_FWD);;

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
  ACCEPT_TAC VA1_POP_HCALL_BWD);;

let VA1_POP_HCALL_END = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (t:int32) (p:int32) (ap:int32) (m:int64->byte).
     ~(p = word 4294967295) /\ val p <= val t /\ val (word_add p (word 520)) <= val t /\
     va1_tick t m /\ va1_pop p ap m
     ==> va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 0) (\gl' m'. gl' = gl /\ m' = m) gl m`,
  ACCEPT_TAC VA1_POP_HCALL_END);;

let VA1_POP_REACH_LOG_OK = prove
 (`!(mdl:num->int32) (hp:num->int32) (tbl:num->int32) (p:int32) (t0:int32)
   (S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32)
   (u:num)
   (S:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32).
     va1_log_ok t0 (va1_diof S0) (va1_ndof S0) /\ val t0 + u < 4294967296 /\
     va1_pop_reach mdl hp tbl p t0 S0 u S
     ==> va1_log_ok (word (val t0 + u)) (va1_diof S) (va1_ndof S)`,
  ACCEPT_TAC VA1_POP_REACH_LOG_OK);;

let VA1_POP_SCRUB = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (p:int32) (ap:int32)
   (x0:(num->int32)#(num->int32)) (hp:num->int32) (tbl:num->int32) (t0:int32)
   (S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32)
   (K:num).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_pop fs /\
     ~(p = word 4294967295) /\ val p <= val t0 /\ val t0 + K <= val p + 520 /\ val p + 520 < 4294967296 /\
     va1_log_ok t0 (va1_diof S0) (va1_ndof S0)
     ==> !(cs:bool list) (u:num) (m:int64->byte).
           u <= K /\ va1_cmds_ok K u cs /\ va1_pop_at mdl N p ap x0 hp tbl t0 S0 u m
           ==> va1_hrun (wasmc fs) cs
                 (\gl' m'. gl' = gl /\
                    va1_pop_at mdl N p ap x0 hp tbl t0 S0 (va1_cmds_end u cs) m') gl m`,
  ACCEPT_TAC VA1_POP_SCRUB);;

let VA1_POP_CHAIN_INVERSE = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (p:int32) (ap:int32)
   (x0:(num->int32)#(num->int32)) (hp:num->int32) (tbl:num->int32) (t0:int32)
   (S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32)
   (k:num) (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_pop fs /\
     ~(p = word 4294967295) /\ val p <= val t0 /\ val t0 + k <= val p + 520 /\ val p + 520 < 4294967296 /\
     va1_log_ok t0 (va1_diof S0) (va1_ndof S0) /\ va1_st t0 p ap mdl N x0 hp tbl S0 m
     ==> va1_hrun (wasmc fs) (APPEND (REPLICATE k T) (REPLICATE k F))
           (\gl' m'. gl' = gl /\ va1_st t0 p ap mdl N x0 hp tbl S0 m') gl m`,
  ACCEPT_TAC VA1_POP_CHAIN_INVERSE);;

let VA1_POP_CHAIN_TO_END = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (p:int32) (ap:int32)
   (x0:(num->int32)#(num->int32)) (hp:num->int32) (tbl:num->int32)
   (S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32)
   (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_pop fs /\
     ~(p = word 4294967295) /\ val p + 520 < 4294967296 /\
     va1_log_ok p (va1_diof S0) (va1_ndof S0) /\ va1_st p p ap mdl N x0 hp tbl S0 m
     ==> va1_hrun (wasmc fs) (REPLICATE 520 T)
           (\gl1 m1. gl1 = gl /\ va1_pop_at mdl N p ap x0 hp tbl p S0 520 m1 /\
              va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 0)
                (\gl2 m2. gl2 = gl1 /\ m2 = m1 /\
                   va1_hrun (wasmc fs) (REPLICATE 520 F)
                     (\gl3 m3. gl3 = gl /\ va1_st p p ap mdl N x0 hp tbl S0 m3) gl2 m2) gl1 m1) gl m`,
  ACCEPT_TAC VA1_POP_CHAIN_TO_END);;

let VA1_POP_CHAIN_SAT = prove
 (`(!(t:int32) (p:int32) (ap:int32) (mdl:num->int32) (N:num) (x:(num->int32)#(num->int32))
    (hp:num->int32) (tbl:num->int32)
    (S:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32).
     N <= 640 ==> ?m:int64->byte. va1_st t p ap mdl N x hp tbl S m) /\
  (?(fs:num->byte list#num#num) (mdl:num->int32) (N:num) (p:int32) (ap:int32)
    (x0:(num->int32)#(num->int32)) (hp:num->int32) (tbl:num->int32)
    (S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32)
    (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_pop fs /\
     ~(p = word 4294967295) /\ val p + 520 < 4294967296 /\
     va1_log_ok p (va1_diof S0) (va1_ndof S0) /\ va1_st p p ap mdl N x0 hp tbl S0 m)`,
  ACCEPT_TAC VA1_POP_CHAIN_SAT);;

let VA1_POP_SCRUB_FRAME = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num) (p:int32) (ap:int32)
   (x0:(num->int32)#(num->int32)) (hp:num->int32) (tbl:num->int32) (t0:int32)
   (S0:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32)
   (K:num).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_pop fs /\
     ~(p = word 4294967295) /\ val p <= val t0 /\ val t0 + K <= val p + 520 /\ val p + 520 < 4294967296 /\
     va1_log_ok t0 (va1_diof S0) (va1_ndof S0)
     ==> !(cs:bool list) (u:num) (m:int64->byte).
           u <= K /\ va1_cmds_ok K u cs /\ va1_pop_at mdl N p ap x0 hp tbl t0 S0 u m
           ==> va1_hrun (wasmc fs) cs
                 (\gl' m'. gl' = gl /\
                    va1_pop_at mdl N p ap x0 hp tbl t0 S0 (va1_cmds_end u cs) m' /\
                    va1_pop_frame m m') gl m`,
  ACCEPT_TAC VA1_POP_SCRUB_FRAME);;

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

let VA1_HRUN_CLAUSES = prove
 (`(!(step:wasmstate->wasmstate->bool) (Q:(num->wval)->(int64->byte)->bool) gl m.
     va1_hrun step [] Q gl m <=> Q gl m) /\
  (!(step:wasmstate->wasmstate->bool) c cs (Q:(num->wval)->(int64->byte)->bool) gl m.
     va1_hrun step (CONS c cs) Q gl m <=>
     va1_hcall step (if c then va1_tick_forward_mc else va1_tick_backward_mc) [] (word 1)
               (va1_hrun step cs Q) gl m)`,
  ACCEPT_TAC VA1_HRUN_CLAUSES);;

let VA1_CMDS_OK_CLAUSES = prove
 (`(!K u. va1_cmds_ok K u [] <=> T) /\
  (!K u c cs. va1_cmds_ok K u (CONS c cs) <=>
     if c then u < K /\ va1_cmds_ok K (u + 1) cs else 0 < u /\ va1_cmds_ok K (u - 1) cs)`,
  ACCEPT_TAC VA1_CMDS_OK_CLAUSES);;

let VA1_CMDS_END_CLAUSES = prove
 (`(!u. va1_cmds_end u [] = u) /\
  (!u c cs. va1_cmds_end u (CONS c cs) = va1_cmds_end (if c then u + 1 else u - 1) cs)`,
  ACCEPT_TAC VA1_CMDS_END_CLAUSES);;

let VA1_HCALL_ENSURES = prove
 (`!(step:wasmstate->wasmstate->bool) (code:byte list) (e:num) (decls:wval list) (args:wval list) (r:int32)
   (P:wasmstate->bool) (Q:wasmstate->bool) (C:wasmstate->wasmstate->bool)
   (R:(num->wval)->(int64->byte)->bool) (gl:num->wval) (m:int64->byte).
     wasm_entry code = SOME e /\ wasm_decl_vals code = SOME decls /\ ensures step P Q C /\
     (!s0. read wmemsize s0 = 4194304 /\ read wglobals s0 = gl /\ read wmem s0 = m
           ==> P (wcall_entry code (LENGTH args) 1 args e decls s0)) /\
     (!s0 s. read wmemsize s0 = 4194304 /\ read wglobals s0 = gl /\ read wmem s0 = m /\
             Q s /\ C (wcall_entry code (LENGTH args) 1 args e decls s0) s
             ==> read wstatus s = WDone /\ read wstack s = [I32 r] /\
                 read wmemsize s = 4194304 /\ R (read wglobals s) (read wmem s))
     ==> va1_hcall step code args r R gl m`,
  ACCEPT_TAC VA1_HCALL_ENSURES);;

let VA1_HCALL_MONO = prove
 (`!(step:wasmstate->wasmstate->bool) (code:byte list) (args:wval list) (r:int32)
   (Q:(num->wval)->(int64->byte)->bool) (Q':(num->wval)->(int64->byte)->bool) (gl:num->wval) (m:int64->byte).
     (!g x. Q g x ==> Q' g x) /\ va1_hcall step code args r Q gl m
     ==> va1_hcall step code args r Q' gl m`,
  ACCEPT_TAC VA1_HCALL_MONO);;

let VA1_HRUN_MONO = prove
 (`!(step:wasmstate->wasmstate->bool) (cs:bool list)
   (Q:(num->wval)->(int64->byte)->bool) (Q':(num->wval)->(int64->byte)->bool) (gl:num->wval) (m:int64->byte).
     (!g x. Q g x ==> Q' g x) /\ va1_hrun step cs Q gl m
     ==> va1_hrun step cs Q' gl m`,
  ACCEPT_TAC VA1_HRUN_MONO);;

let VA1_HRUN_APPEND = prove
 (`!(step:wasmstate->wasmstate->bool) (cs1:bool list) (cs2:bool list) (Q:(num->wval)->(int64->byte)->bool).
     va1_hrun step (APPEND cs1 cs2) Q = va1_hrun step cs1 (va1_hrun step cs2 Q)`,
  ACCEPT_TAC VA1_HRUN_APPEND);;

let VA1_HCALL_START_SAT = prove
 (`!(gl:num->wval) (m:int64->byte).
     ?s0. read wmemsize s0 = 4194304 /\ read wglobals s0 = gl /\ read wmem s0 = m`,
  ACCEPT_TAC VA1_HCALL_START_SAT);;

let VA1_HCALL_RUNS = prove
 (`!(fs:num->byte list#num#num) (code:byte list) (args:wval list) (r:int32)
   (Q:(num->wval)->(int64->byte)->bool) (gl:num->wval) (m:int64->byte).
     va1_hcall (wasmc fs) code args r Q gl m
     ==> ?e decls.
           wasm_entry code = SOME e /\ wasm_decl_vals code = SOME decls /\
           !s0. read wmemsize s0 = 4194304 /\ read wglobals s0 = gl /\ read wmem s0 = m
                ==> (?s. RTC (wasmc fs) (wcall_entry code (LENGTH args) 1 args e decls s0) s /\
                         read wstatus s = WDone /\ read wstack s = [I32 r] /\
                         read wmemsize s = 4194304 /\ Q (read wglobals s) (read wmem s)) /\
                    (!s. RTC (wasmc fs) (wcall_entry code (LENGTH args) 1 args e decls s0) s /\
                         ~(read wstatus s = WRunning)
                         ==> read wstatus s = WDone /\ read wstack s = [I32 r] /\
                             read wmemsize s = 4194304 /\ Q (read wglobals s) (read wmem s))`,
  ACCEPT_TAC VA1_HCALL_RUNS);;

let VA1_TICKF_CALLEE = prove
 (`wasm_entry va1_tick_forward_mc = SOME 3 /\
  wasm_decl_vals va1_tick_forward_mc = SOME [I32 (word 0); I32 (word 0); I32 (word 0)]`,
  ACCEPT_TAC VA1_TICKF_CALLEE);;

let VA1_TICKB_CALLEE = prove
 (`wasm_entry va1_tick_backward_mc = SOME 3 /\
  wasm_decl_vals va1_tick_backward_mc = SOME [I32 (word 0); I32 (word 0)]`,
  ACCEPT_TAC VA1_TICKB_CALLEE);;

let VA1_TICK_FORWARD_POP_R5C = prove
 (`!fs gl t p ap mdl N x hp tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
     fs 9 = (va1_f9_mc,0,0) /\ fs 11 = (va1_f11_mc,0,0) /\ fs 13 = (va1_f13_mc,0,1) /\
     fs 15 = (va1_f15_mc,0,0) /\ fs 17 = (va1_f17_mc,1,0) /\ fs 19 = (va1_f19_mc,0,0) /\
     fs 21 = (va1_f21_mc,0,0) /\ fs 23 = (va1_f23_mc,0,0) /\ fs 27 = (va1_f27_mc,0,0) /\
     va1_pop_window t p /\ va1_log_ok t di nd
     ==> ensures (wasmc fs)
          (\s. read wcode s = va1_tick_forward_mc /\ read wpc s = word 3 /\
             read wstatus s = WRunning /\ read wstack s = [] /\
             read wlabels s = [] /\ read warity s = 1 /\
             read wmemsize s = 4194304 /\ read wglobals s = gl /\
             va1_st t p ap mdl N x hp tbl (ra,rb,jq,jp,di,zq,zp,nd) (read wmem s))
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 1)] /\
             ?L. ALL (\r. r 6 = word_add t (word 1) /\ r 10 = word 0 /\ r 11 = word 0) L /\
                 val nd + LENGTH L <= 16384 /\
                 va1_st (word_add t (word 1)) p ap mdl N (ve_fredkin_fwd (ve_vk mdl) x) hp tbl
                        (va1_pop_fwd va1_ck va1_jigk L mdl hp tbl t p (ra,rb,jq,jp,di,zq,zp,nd)) (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
           MAYCHANGE [wstatus] ,, MAYCHANGE [wlocal 0; wlocal 1; wlocal 2] ,,
           MAYCHANGE [wmem :> bytes(word 16392,4)] ,, MAYCHANGE [wmem :> bytes(word 16400,4)] ,,
           MAYCHANGE [wmem :> bytes(word 1114112,851968)] ,,
           MAYCHANGE [wmem :> bytes(word 1966080,73728)])`,
  ACCEPT_TAC VA1_TICK_FORWARD_POP_R5C);;

let VA1_TICK_POP_INVERSE_R5 = prove
 (`!fs gl t p ap mdl N x hp tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32) L.
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
     fs 10 = (va1_f10_mc,0,0) /\ fs 12 = (va1_f12_mc,0,0) /\ fs 14 = (va1_f14_mc,0,1) /\
     fs 16 = (va1_f16_mc,0,0) /\ fs 18 = (va1_f18_mc,1,0) /\ fs 20 = (va1_f20_mc,0,0) /\
     fs 22 = (va1_f22_mc,0,0) /\ fs 24 = (va1_f24_mc,0,0) /\ fs 28 = (va1_f28_mc,0,0) /\
     va1_pop_window t p /\ va1_log_ok t di nd /\
     ALL (\r. r 6 = word_add t (word 1)) L /\ val nd + LENGTH L <= 16384
     ==> ensures (wasmc fs)
          (\s. read wcode s = va1_tick_backward_mc /\ read wpc s = word 3 /\
             read wstatus s = WRunning /\ read wstack s = [] /\
             read wlabels s = [] /\ read warity s = 1 /\
             read wmemsize s = 4194304 /\ read wglobals s = gl /\
             va1_st (word_add t (word 1)) p ap mdl N (ve_fredkin_fwd (ve_vk mdl) x) hp tbl
                    (va1_pop_fwd va1_ck va1_jigk L mdl hp tbl t p (ra,rb,jq,jp,di,zq,zp,nd)) (read wmem s))
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 1)] /\
             va1_st t p ap mdl N x hp tbl (ra,rb,jq,jp,di,zq,zp,nd) (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
           MAYCHANGE [wstatus] ,, MAYCHANGE [wlocal 0; wlocal 1] ,,
           MAYCHANGE [wmem :> bytes(word 16392,4)] ,, MAYCHANGE [wmem :> bytes(word 16400,4)] ,,
           MAYCHANGE [wmem :> bytes(word 1114112,851968)] ,,
           MAYCHANGE [wmem :> bytes(word 1966080,73728)])`,
  ACCEPT_TAC VA1_TICK_POP_INVERSE_R5);;

let VA1_LOG_OK_POP_FWD = prove
 (`!(CK:(num->int32)->(num->int32)->(num->int32)->int32->int32->num->(num->int32)->(num->int32)->num->int32)
  (JK:(num->int32)->(num->int32)->(num->int32)->int32->int32->(num->int32)->(num->int32)->num->int32)
  L mdl hp tbl t p (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32).
     va1_log_ok t di nd /\ ~(word_add t (word 1) = word 0) /\
     ALL (\r. r 6 = word_add t (word 1)) L /\ val nd + LENGTH L <= 16384
     ==> va1_log_ok (word_add t (word 1))
           (FST(SND(SND(SND(SND(va1_pop_fwd CK JK L mdl hp tbl t p (ra,rb,jq,jp,di,zq,zp,nd)))))))
           (SND(SND(SND(SND(SND(SND(SND(va1_pop_fwd CK JK L mdl hp tbl t p (ra,rb,jq,jp,di,zq,zp,nd)))))))))`,
  ACCEPT_TAC VA1_LOG_OK_POP_FWD);;

let VA1_ST_SAT = prove
 (`!t p ap mdl N x hp tbl ps. N <= 640 ==> ?m. va1_st t p ap mdl N x hp tbl ps m`,
  ACCEPT_TAC VA1_ST_SAT);;

let VA1_TICK_FORWARD_POP_END = prove
 (`!fs gl t p ap.
     ~(p = word 4294967295) /\ val p <= val t /\ val (word_add p (word 520)) <= val t
     ==> ensures (wasmc fs)
          (\s. read wcode s = va1_tick_forward_mc /\ read wpc s = word 3 /\
             read wstatus s = WRunning /\ read wstack s = [] /\
             read wlabels s = [] /\ read warity s = 1 /\
             read wmemsize s = 4194304 /\ read wglobals s = gl /\
             va1_tick t (read wmem s) /\ va1_pop p ap (read wmem s))
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 0)])
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
           MAYCHANGE [wstatus] ,, MAYCHANGE [wlocal 0; wlocal 1; wlocal 2])`,
  ACCEPT_TAC VA1_TICK_FORWARD_POP_END);;

let VA1_PUSH_CLAUSES = prove
 (`(!bs. va1_push ([]:(num->int32)list) (bs:(num->int32)#(num->int32)#(num->int32)#int32) = bs) /\
   (!r rs bs. va1_push (CONS r rs) bs = va1_push rs (va1_push1 r bs))`,
  ACCEPT_TAC VA1_PUSH_CLAUSES);;

let VA1P_KD_FWDN_CLAUSES = prove
 (`(!K D s. ve_kd_fwdn K D 0 s = s) /\
   (!K D n s. ve_kd_fwdn K D (SUC n) s = ve_kd_fwd (K n) (D n) (ve_kd_fwdn K D n s))`,
  ACCEPT_TAC VA1P_KD_FWDN_CLAUSES);;

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

