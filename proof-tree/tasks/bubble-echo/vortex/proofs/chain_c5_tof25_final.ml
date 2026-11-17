(* Vortex chain rung C5 part 2c, final leaf (spec-locked to chain_c5_tof25.spec): re-binds VA1_F33_TO_F25. *)
needs "chain_c5_punct_c.ml";;
let VA1_F33_TO_F25 = prove
 (`!fs a0 a1 a2 m.
     fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\
     read (bytes32 (word 16396)) m = word 4294967295 /\ ~(read (bytes32 (word 16392)) m = word 0) /\
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0)
     ==> ensures (wasmc fs) (va1_f33_pre a0 a1 a2 m)
          (\s. read wcode s = va1_puncture_mc /\ read wpc s = word 1232 /\ read wstatus s = WRunning /\
               read wstack s = [I32 a2; I32 a1; I32 a0] /\ read wlabels s = [0,1241,0] /\
               read warity s = 1 /\ read wmemsize s = 4194304 /\
               read (wglobal 0) s = I32 (word 16288) /\ read (wlocal 3) s = I32 (word 16288) /\
               va1_f33_frame m (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocals] ,, MAYCHANGE [wglobal 0] ,, MAYCHANGE [wmem])`,
  ACCEPT_TAC VA1_F33_TO_F25);;
