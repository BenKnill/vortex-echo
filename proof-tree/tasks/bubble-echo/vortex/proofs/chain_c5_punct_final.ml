(* Vortex chain rung C5 part 2, final leaf (spec-locked to chain_c5_punct.spec): re-binds every spec theorem. *)
needs "chain_c5_punct_a.ml";;
let VA1_F33_ENTRY = prove
 (`!a0 a1 a2 s.
     read wmemsize s = 4194304 /\ read (wglobal 0) s = I32 (word 16384)
     ==> va1_f33_pre a0 a1 a2 (read wmem s)
          (wcall_entry va1_puncture_mc 3 1 [I32 a2; I32 a1; I32 a0] 17
            [I32 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); I64 (word 0)] s)`,
  ACCEPT_TAC VA1_F33_ENTRY);;
let VA1_F33_GUARD_P = prove
 (`!fs a0 a1 a2 m.
     ~(read (bytes32 (word 16396)) m = word 4294967295)
     ==> ensures (wasmc fs) (va1_f33_pre a0 a1 a2 m)
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 1)] /\
               read (wglobal 0) s = I32 (word 16384) /\ read wmem s = m)
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocal 3; wlocal 4] ,, MAYCHANGE [wglobal 0])`,
  ACCEPT_TAC VA1_F33_GUARD_P);;
let VA1_F33_GUARD_T = prove
 (`!fs a0 a1 a2 m.
     read (bytes32 (word 16396)) m = word 4294967295 /\ read (bytes32 (word 16392)) m = word 0
     ==> ensures (wasmc fs) (va1_f33_pre a0 a1 a2 m)
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 3)] /\
               read (wglobal 0) s = I32 (word 16384) /\ read wmem s = m)
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocal 3; wlocal 4] ,, MAYCHANGE [wglobal 0])`,
  ACCEPT_TAC VA1_F33_GUARD_T);;
let VA1_F33_GUARD_ARGS = prove
 (`!fs a0 a1 a2 m.
     read (bytes32 (word 16396)) m = word 4294967295 /\ ~(read (bytes32 (word 16392)) m = word 0) /\
     a0 = word 0 /\ a1 = word 0 /\ a2 = word 0
     ==> ensures (wasmc fs) (va1_f33_pre a0 a1 a2 m)
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 2)] /\
               read (wglobal 0) s = I32 (word 16384) /\ read wmem s = m)
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocal 3; wlocal 4] ,, MAYCHANGE [wglobal 0])`,
  ACCEPT_TAC VA1_F33_GUARD_ARGS);;
let VA1_F33_EPILOGUE = prove
 (`!fs r. ensures (wasmc fs) (va1_f33_epi_pre r)
          (\s. read wstatus s = WDone /\ read wstack s = [I32 r] /\ read (wglobal 0) s = I32 (word 16384))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocal 4] ,, MAYCHANGE [wglobal 0])`,
  ACCEPT_TAC VA1_F33_EPILOGUE);;
let VA1_F33_SAT = prove
 (`!a0 a1 a2. ?fs m1 m2 m3 s1 s2 s3.
     fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\
     ~(read (bytes32 (word 16396)) m1 = word 4294967295) /\
     read (bytes32 (word 16396)) m2 = word 4294967295 /\ read (bytes32 (word 16392)) m2 = word 0 /\
     read (bytes32 (word 16396)) m3 = word 4294967295 /\ ~(read (bytes32 (word 16392)) m3 = word 0) /\
     va1_f33_pre a0 a1 a2 m1 s1 /\ va1_f33_pre a0 a1 a2 m2 s2 /\ va1_f33_pre a0 a1 a2 m3 s3`,
  ACCEPT_TAC VA1_F33_SAT);;
let VA1_F33_EPI_SAT = prove
 (`!r. ?s. va1_f33_epi_pre r s`,
  ACCEPT_TAC VA1_F33_EPI_SAT);;
