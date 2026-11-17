(* c8p_f33_final.ml (vortex-chain c8p, Claude Opus 5.5, 2026-11-15): spec-locked final leaf for c8p_f33.spec (rows P3/P4);
   re-binds VA1_F33_TO_F25_V from layer c8p_f33_p.ml (C8P_F33_TO_F25_V). Definitions: c8p_f33_defs.ml (placed by C8e). *)
needs "chain_c6b_host.ml";;
needs "c8p_leaves2_pf.ml";;
needs "c8p_f33_defs.ml";;
needs "c8p_f33_p.ml";;
let VA1_F33_TO_F25_V = prove
 (`!fs a0 a1 a2 m.
     fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\
     read (bytes32 (word 16396)) m = word 4294967295 /\ ~(read (bytes32 (word 16392)) m = word 0) /\
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0)
     ==> ensures (wasmc fs) (va1_f33_pre a0 a1 a2 m)
          (\s. read wcode s = va1_puncture_mc /\ read wpc s = word 1232 /\ read wstatus s = WRunning /\
               read wstack s = [I32 a2; I32 a1; I32 a0] /\ read wlabels s = [0,1241,0] /\
               read warity s = 1 /\ read wmemsize s = 4194304 /\
               read (wglobal 0) s = I32 (word 16288) /\ read (wlocal 3) s = I32 (word 16288) /\
               va1_f33_frame m (read wmem s) /\
               va1_w32s 65536 262144 (va1_ptbl a0 a1 a2 (read (bytes32 (word 16648)) m)) (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocals] ,, MAYCHANGE [wglobal 0] ,, MAYCHANGE [wmem])`,
  ACCEPT_TAC C8P_F33_TO_F25_V);;
