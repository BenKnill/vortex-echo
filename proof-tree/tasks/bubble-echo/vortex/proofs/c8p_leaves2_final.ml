(* c8p_leaves2_final.ml (vortex-chain c8p, Claude Opus 5.5, 2026-11-14): spec-locked final leaf for c8p_leaves2.spec;
   re-binds its 3 theorems from c8p_leaves2_pf.ml. Basis parent: the C6b host layer in vortex-pop/assembly/proj. *)
needs "chain_c6b_host.ml";;
needs "c8p_leaves2_defs.ml";;
needs "c8p_leaves2_pf.ml";;
let VA1_F32_VALUE = prove
 (`!x k. ensures wasm
 (\s. read wcode s = va1_f32_mc /\ read wpc s = word 5 /\ read wstatus s = WRunning /\
      read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
      read (wlocal 0) s = F64 x /\ read (wlocal 1) s = I32 k)
 (\s. read wstatus s = WDone /\ read wstack s = [F64 (va1_f32v x k)])
 (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
  MAYCHANGE [wlocal 0; wlocal 2; wlocal 3])`,
  ACCEPT_TAC VA1_F32_VALUE);;
let VA1_F34_VALUE = prove
 (`!a0 a1 a2. ensures wasm
 (\s. read wcode s = va1_f34_mc /\ read wpc s = word 7 /\ read wstatus s = WRunning /\
      read wstack s = [] /\ read wlabels s = [] /\ read warity s = 0 /\ read wmemsize s = 4194304 /\
      read (wlocal 0) s = I32 (word 16352) /\ read (wlocal 1) s = I32 (word 16320) /\
      read (wlocal 2) s = I32 (word 16288) /\
      read (bytes64 (word 16352)) (read wmem s) = a0 /\ read (bytes64 (word 16360)) (read wmem s) = a1 /\
      read (bytes64 (word 16368)) (read wmem s) = a2)
 (\s. read wstatus s = WDone /\ read wstack s = [] /\
      read (bytes64 (word 16320)) (read wmem s) = va1_f34e1x a0 a1 a2 /\
      read (bytes64 (word 16328)) (read wmem s) = va1_f34e1y a0 a1 a2 /\
      read (bytes64 (word 16336)) (read wmem s) = va1_f34e1z a0 a1 a2 /\
      read (bytes64 (word 16288)) (read wmem s) = va1_f34e2x a0 a1 a2 /\
      read (bytes64 (word 16296)) (read wmem s) = va1_f34e2y a0 a1 a2 /\
      read (bytes64 (word 16304)) (read wmem s) = va1_f34e2z a0 a1 a2)
 (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
  MAYCHANGE [wlocal 3; wlocal 4; wlocal 5; wlocal 6; wlocal 7; wlocal 8; wlocal 9] ,,
  MAYCHANGE [wmem :> bytes64 (word 16320)] ,, MAYCHANGE [wmem :> bytes64 (word 16328)] ,,
  MAYCHANGE [wmem :> bytes64 (word 16336)] ,, MAYCHANGE [wmem :> bytes64 (word 16288)] ,,
  MAYCHANGE [wmem :> bytes64 (word 16296)] ,, MAYCHANGE [wmem :> bytes64 (word 16304)])`,
  ACCEPT_TAC VA1_F34_VALUE);;
let VA1_F34V_PRE_SAT = prove
 (`!a0 a1 a2. ?s:wasmstate. (\s. read wcode s = va1_f34_mc /\ read wpc s = word 7 /\ read wstatus s = WRunning /\
      read wstack s = [] /\ read wlabels s = [] /\ read warity s = 0 /\ read wmemsize s = 4194304 /\
      read (wlocal 0) s = I32 (word 16352) /\ read (wlocal 1) s = I32 (word 16320) /\
      read (wlocal 2) s = I32 (word 16288) /\
      read (bytes64 (word 16352)) (read wmem s) = a0 /\ read (bytes64 (word 16360)) (read wmem s) = a1 /\
      read (bytes64 (word 16368)) (read wmem s) = a2) s`,
  ACCEPT_TAC VA1_F34V_PRE_SAT);;
