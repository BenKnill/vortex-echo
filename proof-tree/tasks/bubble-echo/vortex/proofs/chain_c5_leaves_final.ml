(* Vortex chain rung C5 part 1, final leaf (spec-locked to chain_c5_leaves.spec): re-binds every spec theorem. *)
needs "chain_c5_leaves.ml";;
let VA1_C5_WDECL_VALS_CLAUSES = prove
 (`(!code pc. wdecl_vals 0 (code:byte list) pc = SOME ([]:wval list)) /\
  (!k code pc. wdecl_vals (SUC k) code pc =
     wobind (wuleb (wdrop pc code)) (\p.
     wobind (whd (wdrop (pc + SND p) code)) (\t.
     wobind (wdecl_vals k code (pc + SND p + 1)) (\r.
       SOME (APPEND (REPLICATE (FST p) (wzero_of (val (t:byte)))) r)))))`,
  ACCEPT_TAC VA1_C5_WDECL_VALS_CLAUSES);;
let VA1_F64G_MAG_LT = prove
 (`!E Fr. E <= 1085 /\ Fr < 4503599627370496
         ==> (if 1075 <= (if E = 0 then 1 else E)
              then (if E = 0 then Fr else Fr + 4503599627370496) *
                   2 EXP ((if E = 0 then 1 else E) - 1075)
              else (if E = 0 then Fr else Fr + 4503599627370496) DIV
                   2 EXP (1075 - (if E = 0 then 1 else E))) < 9223372036854775808`,
  ACCEPT_TAC VA1_F64G_MAG_LT);;
let VA1_F64G_SPLIT = prove
 (`!x. x MOD 9223372036854775808 =
       ((x DIV 4503599627370496) MOD 2048) * 4503599627370496 + x MOD 4503599627370496`,
  ACCEPT_TAC VA1_F64G_SPLIT);;
let VA1_F64_TRUNC_GUARD = prove
 (`!v:int64. wfrel 99 (word_and v (word 9223372036854775807)) (word 4890909195324358656)
             ==> ~wftrap 176 v`,
  ACCEPT_TAC VA1_F64_TRUNC_GUARD);;
let VA1_TRUNC_GUARD_OK = prove
 (`va1_trunc_guard_ok`,
  ACCEPT_TAC VA1_TRUNC_GUARD_OK);;
let VA1_F32_CALLEE = prove
 (`wasm_entry va1_f32_mc = SOME 5 /\
  wasm_decl_vals va1_f32_mc = SOME [F64 (word 0); I64 (word 0)]`,
  ACCEPT_TAC VA1_F32_CALLEE);;
let VA1_F34_CALLEE = prove
 (`wasm_entry va1_f34_mc = SOME 7 /\
  wasm_decl_vals va1_f34_mc = SOME
  [F64 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0)]`,
  ACCEPT_TAC VA1_F34_CALLEE);;
let VA1_PUNCTURE_CALLEE = prove
 (`wasm_entry va1_puncture_mc = SOME 17 /\
  wasm_decl_vals va1_puncture_mc = SOME
  [I32 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); I32 (word 0); I64 (word 0)]`,
  ACCEPT_TAC VA1_PUNCTURE_CALLEE);;
let VA1_F32_CORRECT = prove
 (`!x k. ensures wasm
 (\s. read wcode s = va1_f32_mc /\ read wpc s = word 5 /\ read wstatus s = WRunning /\
      read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
      read (wlocal 0) s = F64 x /\ read (wlocal 1) s = I32 k)
 (\s. read wstatus s = WDone /\ ?r. read wstack s = [F64 r])
 (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
  MAYCHANGE [wlocal 0; wlocal 2; wlocal 3])`,
  ACCEPT_TAC VA1_F32_CORRECT);;
let VA1_F32_ENTRY = prove
 (`!x k rest s.
     (\s. read wcode s = va1_f32_mc /\ read wpc s = word 5 /\ read wstatus s = WRunning /\
      read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
      read (wlocal 0) s = F64 x /\ read (wlocal 1) s = I32 k)
     (wcall_entry va1_f32_mc 2 1 (CONS (I32 k) (CONS (F64 x) rest)) 5 [F64 (word 0); I64 (word 0)] s)`,
  ACCEPT_TAC VA1_F32_ENTRY);;
let VA1_F32_PRE_SAT = prove
 (`!x k. ?s:wasmstate. (\s. read wcode s = va1_f32_mc /\ read wpc s = word 5 /\ read wstatus s = WRunning /\
      read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
      read (wlocal 0) s = F64 x /\ read (wlocal 1) s = I32 k) s`,
  ACCEPT_TAC VA1_F32_PRE_SAT);;
let VA1_F34_CORRECT = prove
 (`ensures wasm
 (\s. read wcode s = va1_f34_mc /\ read wpc s = word 7 /\ read wstatus s = WRunning /\
      read wstack s = [] /\ read wlabels s = [] /\ read warity s = 0 /\ read wmemsize s = 4194304 /\
      read (wlocal 0) s = I32 (word 16352) /\ read (wlocal 1) s = I32 (word 16320) /\
      read (wlocal 2) s = I32 (word 16288))
 (\s. read wstatus s = WDone /\ read wstack s = [])
 (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
  MAYCHANGE [wlocal 3; wlocal 4; wlocal 5; wlocal 6; wlocal 7; wlocal 8; wlocal 9] ,,
  MAYCHANGE [wmem :> bytes64 (word 16320)] ,, MAYCHANGE [wmem :> bytes64 (word 16328)] ,,
  MAYCHANGE [wmem :> bytes64 (word 16336)] ,, MAYCHANGE [wmem :> bytes64 (word 16288)] ,,
  MAYCHANGE [wmem :> bytes64 (word 16296)] ,, MAYCHANGE [wmem :> bytes64 (word 16304)])`,
  ACCEPT_TAC VA1_F34_CORRECT);;
let VA1_F34_ENTRY = prove
 (`!rest s. read wmemsize s = 4194304 ==>
     (\s. read wcode s = va1_f34_mc /\ read wpc s = word 7 /\ read wstatus s = WRunning /\
      read wstack s = [] /\ read wlabels s = [] /\ read warity s = 0 /\ read wmemsize s = 4194304 /\
      read (wlocal 0) s = I32 (word 16352) /\ read (wlocal 1) s = I32 (word 16320) /\
      read (wlocal 2) s = I32 (word 16288))
     (wcall_entry va1_f34_mc 3 0
        (CONS (I32 (word 16288)) (CONS (I32 (word 16320)) (CONS (I32 (word 16352)) rest))) 7
        [F64 (word 0); I32 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0); F64 (word 0)] s)`,
  ACCEPT_TAC VA1_F34_ENTRY);;
let VA1_F34_PRE_SAT = prove
 (`?s:wasmstate. (\s. read wcode s = va1_f34_mc /\ read wpc s = word 7 /\ read wstatus s = WRunning /\
      read wstack s = [] /\ read wlabels s = [] /\ read warity s = 0 /\ read wmemsize s = 4194304 /\
      read (wlocal 0) s = I32 (word 16352) /\ read (wlocal 1) s = I32 (word 16320) /\
      read (wlocal 2) s = I32 (word 16288)) s`,
  ACCEPT_TAC VA1_F34_PRE_SAT);;
