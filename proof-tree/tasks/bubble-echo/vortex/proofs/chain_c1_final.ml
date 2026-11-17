needs "ve_vort.ml";;
needs "ve_tick.ml";;
needs "ve_vk.ml";;
needs "va1_code.ml";;
needs "va1_seq_final2.ml";;
needs "chain_c1_host.ml";;
needs "chain_c1_np.ml";;
needs "chain_c1_frame.ml";;
(* ========================================================================= *)
(* Vortex chain, rung C1: spec-locked final leaf for chain_c1_final.spec     *)
(* (frozen sha256 3b62701f...; PROVE-C1, Claude Opus 5.5, 2026-11-11).       *)
(* Every spec theorem is re-bound here against its frozen literal statement  *)
(* (ACCEPT_TAC of the layer or basis theorem), including the two CALLEE      *)
(* facts and the nine re-stated PROVED / CLAUSES theorems, so that the       *)
(* receipt's inspect checks each one in this leaf. Layers: chain_c1_host.ml  *)
(* (generic host-call layer), chain_c1_np.ml (no-pop chain),                 *)
(* chain_c1_frame.ml (byte frame C1b). This leaf defines nothing and changes *)
(* no parser state.                                                          *)
(* ========================================================================= *)

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

let VA1_NP_HCALL_FWD = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (t:int32) (ap:int32) (mdl:num->int32) (N:num)
   (x:(num->int32)#(num->int32)) (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_np fs /\
     (ap = word 0 \/ ~(ap = word_add t (word 1))) /\ va1_np_st t ap mdl N x m
     ==> va1_hcall (wasmc fs) va1_tick_forward_mc [] (word 1)
           (\gl' m'. gl' = gl /\ va1_np_st (word_add t (word 1)) ap mdl N (va1_swf mdl x) m') gl m`,
  ACCEPT_TAC VA1_NP_HCALL_FWD);;

let VA1_NP_HCALL_BWD = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (u:int32) (ap:int32) (mdl:num->int32) (N:num)
   (y:(num->int32)#(num->int32)) (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_np fs /\ ~(u = word 0) /\ va1_np_st u ap mdl N y m
     ==> va1_hcall (wasmc fs) va1_tick_backward_mc [] (word 1)
           (\gl' m'. gl' = gl /\ va1_np_st (word_sub u (word 1)) ap mdl N (va1_swb mdl y) m') gl m`,
  ACCEPT_TAC VA1_NP_HCALL_BWD);;

let VA1_NP_SCRUB = prove
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
                              (ITER (va1_cmds_end u cs) (va1_swf mdl) x0) m') gl m`,
  ACCEPT_TAC VA1_NP_SCRUB);;

let VA1_NP_FILM_INVERSE = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num)
   (x0:(num->int32)#(num->int32)) (n:num) (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_np fs /\ n < 4294967296 /\
     va1_np_st (word 0) (word 0) mdl N x0 m
     ==> va1_hrun (wasmc fs) (APPEND (REPLICATE n T) (REPLICATE n F))
           (\gl' m'. gl' = gl /\ va1_np_st (word 0) (word 0) mdl N x0 m') gl m`,
  ACCEPT_TAC VA1_NP_FILM_INVERSE);;

let VA1_NP_FILM_SAT = prove
 (`(?fs:num->byte list#num#num. va1_fs_np fs) /\
  (!(t:int32) (ap:int32) (mdl:num->int32) (N:num) (x:(num->int32)#(num->int32)).
     N <= 640 ==> ?m:int64->byte. va1_np_st t ap mdl N x m)`,
  ACCEPT_TAC VA1_NP_FILM_SAT);;

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

let VA1_NP_FILM_BYTES = prove
 (`!(fs:num->byte list#num#num) (gl:num->wval) (mdl:num->int32) (N:num)
   (x0:(num->int32)#(num->int32)) (n:num) (m:int64->byte).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ va1_fs_np fs /\ n < 4294967296 /\
     va1_np_st (word 0) (word 0) mdl N x0 m
     ==> va1_hrun (wasmc fs) (APPEND (REPLICATE n T) (REPLICATE n F))
           (\gl' m'. gl' = gl /\ va1_np_st (word 0) (word 0) mdl N x0 m' /\ va1_np_frame m m') gl m`,
  ACCEPT_TAC VA1_NP_FILM_BYTES);;

let VE_VORT_STEPS_INVERSE_VK = prove
 (`!(mdl:num->int32) n s.
     ve_fredkin_bwdn (\i. ve_vk mdl) n (ve_fredkin_fwdn (\i. ve_vk mdl) n s) = s`,
  ACCEPT_TAC VE_VORT_STEPS_INVERSE_VK);;

let VA1_TICK_FORWARD_NOPOP_VK = prove
 (`!fs gl t ap mdl N x.
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
     fs 9 = (va1_f9_mc,0,0) /\ fs 27 = (va1_f27_mc,0,0) /\
     (ap = word 0 \/ ~(ap = word_add t (word 1)))
     ==> ensures (wasmc fs)
          (\s. read wcode s = va1_tick_forward_mc /\ read wpc s = word 3 /\
               read wstatus s = WRunning /\ read wstack s = [] /\
               read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_tick t (read wmem s) /\
               va1_pop (word 4294967295) ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\ va1_vab N x (read wmem s))
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 1)] /\
               va1_tick (word_add t (word 1)) (read wmem s) /\
               va1_pop (word 4294967295) ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\
               va1_vab N (ve_fredkin_fwdn (\i. ve_vk mdl) 16 x) (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
           MAYCHANGE [wstatus] ,, MAYCHANGE [wlocal 0; wlocal 1; wlocal 2] ,,
           MAYCHANGE [wmem :> bytes(word 16392,4)] ,,
           MAYCHANGE [wmem :> bytes(word 1114112,16384)] ,,
           MAYCHANGE [wmem :> bytes(word 1966080,73728)])`,
  ACCEPT_TAC VA1_TICK_FORWARD_NOPOP_VK);;

let VA1_TICK_BACKWARD_NOPOP_VK = prove
 (`!fs gl u ap mdl N y.
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
     fs 10 = (va1_f10_mc,0,0) /\ fs 28 = (va1_f28_mc,0,0) /\
     ~(u = word 0)
     ==> ensures (wasmc fs)
          (\s. read wcode s = va1_tick_backward_mc /\ read wpc s = word 3 /\
               read wstatus s = WRunning /\ read wstack s = [] /\
               read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_tick u (read wmem s) /\
               va1_pop (word 4294967295) ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\ va1_vab N y (read wmem s))
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 1)] /\
               va1_tick (word_sub u (word 1)) (read wmem s) /\
               va1_pop (word 4294967295) ap (read wmem s) /\
               va1_mdl mdl (read wmem s) /\
               va1_vab N (ve_fredkin_bwdn (\i. ve_vk mdl) 16 y) (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
           MAYCHANGE [wstatus] ,, MAYCHANGE [wlocal 0; wlocal 1] ,,
           MAYCHANGE [wmem :> bytes(word 16392,4)] ,,
           MAYCHANGE [wmem :> bytes(word 1114112,16384)] ,,
           MAYCHANGE [wmem :> bytes(word 1966080,73728)])`,
  ACCEPT_TAC VA1_TICK_BACKWARD_NOPOP_VK);;

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
