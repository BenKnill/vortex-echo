needs "chain_c6b_host.ml";;
(* vortex-chain c6b (Claude Opus 5.5, 2026-11-13): spec-locked final leaf for chain_c6b_final.spec (sha256 667b4b91e6e07060ae79bd6864c09cbfc241e8a7dd5dd2bef5cccf9f4ee5d4b5);
   re-binds its 3 theorems from the host layer. *)
let VA1_TICK_FORWARD_PUNCT = prove(`!(fs:num->byte list#num#num) (gl:num->wval) (t:int32) (mdl:num->int32) (N:num) (x:(num->int32)#(num->int32)) (a0:int32) (a1:int32) (a2:int32) (m0:int64->byte).
     fs 9 = (va1_f9_mc,0,0) /\ fs 27 = (va1_f27_mc,0,0) /\ fs 33 = (va1_puncture_mc,3,1) /\
     fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ gl 0 = I32 (word 16384) /\ ~(word_add t (word 1) = word 0) /\
     va1_tick t m0 /\ va1_pop (word 4294967295) (word_add t (word 1)) m0 /\ va1_mdl mdl m0 /\ va1_vab N x m0 /\
     read (bytes32 (word 16516)) m0 = a0 /\ read (bytes32 (word 16520)) m0 = a1 /\ read (bytes32 (word 16524)) m0 = a2 /\
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0)
     ==> ensures (wasmn fs)
          (\s. read wcode s = va1_tick_forward_mc /\ read wpc s = word 3 /\ read wstatus s = WRunning /\
               read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\ read wmem s = m0)
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 1)] /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               ?m1. va1_tf_mid N mdl t x m0 m1 /\ va1_c6a_mem mdl m1 (read wmem s) /\
                    read (bytes32 (word 16408)) (read wmem s) = a0 /\ read (bytes32 (word 16412)) (read wmem s) = a1 /\
                    read (bytes32 (word 16416)) (read wmem s) = a2)
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocal 0; wlocal 1; wlocal 2] ,, MAYCHANGE [wmem])`,
  MATCH_ACCEPT_TAC VA1_TICK_FORWARD_PUNCT);;
let VA1_C6B_SAT = prove(`!(t:int32) (mdl:num->int32) (N:num) (x:(num->int32)#(num->int32)) (a0:int32) (a1:int32) (a2:int32).
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\ ~(word_add t (word 1) = word 0) /\
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0)
     ==> ?(fs:num->byte list#num#num) (gl:num->wval) (m0:int64->byte) (s:wasmstate).
           fs 9 = (va1_f9_mc,0,0) /\ fs 27 = (va1_f27_mc,0,0) /\ fs 33 = (va1_puncture_mc,3,1) /\
     fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\
           gl 0 = I32 (word 16384) /\
           va1_tick t m0 /\ va1_pop (word 4294967295) (word_add t (word 1)) m0 /\ va1_mdl mdl m0 /\ va1_vab N x m0 /\
     read (bytes32 (word 16516)) m0 = a0 /\ read (bytes32 (word 16520)) m0 = a1 /\ read (bytes32 (word 16524)) m0 = a2 /\
           read wcode s = va1_tick_forward_mc /\ read wpc s = word 3 /\ read wstatus s = WRunning /\
           read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
           read wmemsize s = 4194304 /\ read wglobals s = gl /\ read wmem s = m0`,
  MATCH_ACCEPT_TAC VA1_C6B_SAT);;
let VA1_FWDN_CLAUSES = prove(`(!f s. ve_fredkin_fwdn f 0 s = s) /\
   (!f n s. ve_fredkin_fwdn f (SUC n) s = ve_fredkin_fwd (f n) (ve_fredkin_fwdn f n s))`,
  MATCH_ACCEPT_TAC VA1_FWDN_CLAUSES);;
