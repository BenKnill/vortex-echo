needs "chain_c6a_host.ml";;
(* vortex-chain c6a (Claude Opus 5.5, 2026-11-13): spec-locked final leaf for chain_c6a_final.spec (sha256 4082be069ba5ff58cbabca7c740dcb9e8009d408c43896b2e45aef148b1eeba7);
   re-binds its 4 theorems from the host layer. *)
let VA1_PUNCTURE_OK = prove(`!(fs:num->byte list#num#num) (t:int32) (mdl:num->int32) (a0:int32) (a1:int32) (a2:int32) (m:int64->byte).
     fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\
     read (bytes32 (word 16396)) m = word 4294967295 /\ va1_tick t m /\ ~(t = word 0) /\ va1_mdl mdl m /\
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0)
     ==> ensures (wasmc fs) (va1_f33_pre a0 a1 a2 m)
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 0)] /\
               read (wglobal 0) s = I32 (word 16384) /\ read wmemsize s = 4194304 /\
               va1_c6a_mem mdl m (read wmem s) /\
               read (bytes32 (word 16408)) (read wmem s) = a0 /\ read (bytes32 (word 16412)) (read wmem s) = a1 /\
               read (bytes32 (word 16416)) (read wmem s) = a2)
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocals] ,, MAYCHANGE [wglobal 0] ,, MAYCHANGE [wmem])`,
  MATCH_ACCEPT_TAC VA1_PUNCTURE_OK);;
let VA1_HCALL_PUNCTURE = prove(`!(fs:num->byte list#num#num) (gl:num->wval) (t:int32) (mdl:num->int32) (a0:int32) (a1:int32) (a2:int32) (m:int64->byte).
     fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\
     read (bytes32 (word 16396)) m = word 4294967295 /\ va1_tick t m /\ ~(t = word 0) /\ va1_mdl mdl m /\
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0) /\
     gl 0 = I32 (word 16384)
     ==> ?e decls.
           wasm_entry va1_puncture_mc = SOME e /\ wasm_decl_vals va1_puncture_mc = SOME decls /\
           !s0. read wmemsize s0 = 4194304 /\ read wglobals s0 = gl /\ read wmem s0 = m
                ==> eventually (wasmc fs)
                      (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 0)] /\
                           read wmemsize s = 4194304 /\
                           va1_c6a_rel mdl gl m (read wglobals s) (read wmem s) /\
                           read (bytes32 (word 16408)) (read wmem s) = a0 /\ read (bytes32 (word 16412)) (read wmem s) = a1 /\
                           read (bytes32 (word 16416)) (read wmem s) = a2)
                      (wcall_entry va1_puncture_mc (LENGTH [I32 a2; I32 a1; I32 a0]) 1 [I32 a2; I32 a1; I32 a0] e decls s0)`,
  MATCH_ACCEPT_TAC VA1_HCALL_PUNCTURE);;
let VA1_PUNCTURE_RUNS = prove(`!(fs:num->byte list#num#num) (gl:num->wval) (t:int32) (mdl:num->int32) (a0:int32) (a1:int32) (a2:int32) (m:int64->byte) (s0:wasmstate).
     fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\
     read (bytes32 (word 16396)) m = word 4294967295 /\ va1_tick t m /\ ~(t = word 0) /\ va1_mdl mdl m /\
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0) /\
     gl 0 = I32 (word 16384) /\
     read wmemsize s0 = 4194304 /\ read wglobals s0 = gl /\ read wmem s0 = m
     ==> (?s. RTC (wasmc fs) (wcall_entry va1_puncture_mc 3 1 [I32 a2; I32 a1; I32 a0] 17
                [I32 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); I64 (word 0)] s0) s /\
              read wstatus s = WDone) /\
         (!s. RTC (wasmc fs) (wcall_entry va1_puncture_mc 3 1 [I32 a2; I32 a1; I32 a0] 17
                [I32 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); I64 (word 0)] s0) s /\
              ~(read wstatus s = WRunning)
              ==> read wstatus s = WDone /\ read wstack s = [I32 (word 0)] /\ read wmemsize s = 4194304 /\
                  va1_c6a_rel mdl gl m (read wglobals s) (read wmem s) /\
                  read (bytes32 (word 16408)) (read wmem s) = a0 /\ read (bytes32 (word 16412)) (read wmem s) = a1 /\
                  read (bytes32 (word 16416)) (read wmem s) = a2)`,
  MATCH_ACCEPT_TAC VA1_PUNCTURE_RUNS);;
let VA1_C6A_SAT = prove(`!(t:int32) (mdl:num->int32) (a0:int32) (a1:int32) (a2:int32).
     ~(t = word 0) /\ ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0)
     ==> ?(fs:num->byte list#num#num) (gl:num->wval) (m:int64->byte) (s0:wasmstate).
           fs 25 = (va1_f25_mc,3,1) /\ fs 32 = (va1_f32_mc,2,1) /\ fs 34 = (va1_f34_mc,3,0) /\
           read (bytes32 (word 16396)) m = word 4294967295 /\ va1_tick t m /\ va1_mdl mdl m /\
           gl 0 = I32 (word 16384) /\
           read wmemsize s0 = 4194304 /\ read wglobals s0 = gl /\ read wmem s0 = m`,
  MATCH_ACCEPT_TAC VA1_C6A_SAT);;
