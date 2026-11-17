(* Vortex chain rung C5', final leaf (spec-locked to chain_c5p.spec): re-binds every spec theorem: the 7 C5' rules of
   chain_c5p_rules.ml and the 24 public theorems of main's wasm_frames.ml as delivered by the shim chain_c5p_frames.ml. *)
needs "chain_c5p_rules.ml";;
let VA1_C5P_ENSURES_WASMN = prove
 (`!fs (P:wasmstate->bool) Q C. ensures (wasmc fs) P Q C ==> ensures (wasmn fs) P Q C`,
  ACCEPT_TAC VA1_C5P_ENSURES_WASMN);;
let VA1_C5P_EVENTUALLY_WASMN = prove
 (`!fs P s. eventually (wasmc fs) P s ==> eventually (wasmn fs) P s`,
  ACCEPT_TAC VA1_C5P_EVENTUALLY_WASMN);;
let VA1_F33_WFSUM = prove
 (`!fs a0 a1 a2 m (Q:wasmstate->bool).
     (!s. Q s ==> read (wglobal 0) s = I32 (word 16384)) /\
     ensures (wasmc fs) (va1_f33_pre a0 a1 a2 m) Q
       (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
        MAYCHANGE [wlocals] ,, MAYCHANGE [wglobal 0] ,, MAYCHANGE [wmem])
     ==> wfsum fs (va1_f33_pre a0 a1 a2 m) Q
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
        MAYCHANGE [wlocals] ,, MAYCHANGE [wmem])`,
  ACCEPT_TAC VA1_F33_WFSUM);;
let VA1_CALL33_WASMN = prove
 (`!fs mc pc a0 a1 a2 (rest:wval list) m r (R:(int64->byte)->bool) (Q:wasmstate->bool).
     fs 33 = (va1_puncture_mc,3,1) /\ pc < 2 EXP 64 /\ wasm_decode mc pc = SOME (Wcall 33,6) /\
     wfsum fs (va1_f33_pre a0 a1 a2 m) Q
       (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
        MAYCHANGE [wlocals] ,, MAYCHANGE [wmem]) /\
     (!c. Q c ==> read wstatus c = WDone /\ read wstack c = [I32 r] /\ R (read wmem c))
     ==> ensures (wasmn fs)
          (\s. read wcode s = mc /\ read wpc s = word pc /\ read wstatus s = WRunning /\
               read wstack s = CONS (I32 a2) (CONS (I32 a1) (CONS (I32 a0) rest)) /\
               read wmemsize s = 4194304 /\ read (wglobal 0) s = I32 (word 16384) /\ read wmem s = m)
          (\s. read wcode s = mc /\ read wpc s = word (pc + 6) /\ read wstatus s = WRunning /\
               read wstack s = CONS (I32 r) rest /\
               read wmemsize s = 4194304 /\ read (wglobal 0) s = I32 (word 16384) /\ R (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wmem])`,
  ACCEPT_TAC VA1_CALL33_WASMN);;
let VA1_CALL33_FROM_WASMC = prove
 (`!fs mc pc a0 a1 a2 (rest:wval list) m r (R:(int64->byte)->bool) (Q:wasmstate->bool).
     fs 33 = (va1_puncture_mc,3,1) /\ pc < 2 EXP 64 /\ wasm_decode mc pc = SOME (Wcall 33,6) /\
     ensures (wasmc fs) (va1_f33_pre a0 a1 a2 m) Q
       (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
        MAYCHANGE [wlocals] ,, MAYCHANGE [wglobal 0] ,, MAYCHANGE [wmem]) /\
     (!c. Q c ==> read wstatus c = WDone /\ read wstack c = [I32 r] /\
              read (wglobal 0) c = I32 (word 16384) /\ R (read wmem c))
     ==> ensures (wasmn fs)
          (\s. read wcode s = mc /\ read wpc s = word pc /\ read wstatus s = WRunning /\
               read wstack s = CONS (I32 a2) (CONS (I32 a1) (CONS (I32 a0) rest)) /\
               read wmemsize s = 4194304 /\ read (wglobal 0) s = I32 (word 16384) /\ read wmem s = m)
          (\s. read wcode s = mc /\ read wpc s = word (pc + 6) /\ read wstatus s = WRunning /\
               read wstack s = CONS (I32 r) rest /\
               read wmemsize s = 4194304 /\ read (wglobal 0) s = I32 (word 16384) /\ R (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wmem])`,
  ACCEPT_TAC VA1_CALL33_FROM_WASMC);;
let VA1_TF_CALL33_SITE = prove
 (`!fs a0 a1 a2 (rest:wval list) m r (R:(int64->byte)->bool) (Q:wasmstate->bool).
     fs 33 = (va1_puncture_mc,3,1) /\
     ensures (wasmc fs) (va1_f33_pre a0 a1 a2 m) Q
       (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
        MAYCHANGE [wlocals] ,, MAYCHANGE [wglobal 0] ,, MAYCHANGE [wmem]) /\
     (!c. Q c ==> read wstatus c = WDone /\ read wstack c = [I32 r] /\
              read (wglobal 0) c = I32 (word 16384) /\ R (read wmem c))
     ==> ensures (wasmn fs)
          (\s. read wcode s = va1_tick_forward_mc /\ read wpc s = word 309 /\ read wstatus s = WRunning /\
               read wstack s = CONS (I32 a2) (CONS (I32 a1) (CONS (I32 a0) rest)) /\
               read wmemsize s = 4194304 /\ read (wglobal 0) s = I32 (word 16384) /\ read wmem s = m)
          (\s. read wcode s = va1_tick_forward_mc /\ read wpc s = word 315 /\ read wstatus s = WRunning /\
               read wstack s = CONS (I32 r) rest /\
               read wmemsize s = 4194304 /\ read (wglobal 0) s = I32 (word 16384) /\ R (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wmem])`,
  ACCEPT_TAC VA1_TF_CALL33_SITE);;
let VA1_C5P_SITE_SAT = prove
 (`!a0 a1 a2 (rest:wval list) m. ?s.
     read wcode s = va1_tick_forward_mc /\ read wpc s = word 309 /\ read wstatus s = WRunning /\
     read wstack s = CONS (I32 a2) (CONS (I32 a1) (CONS (I32 a0) rest)) /\
     read wmemsize s = 4194304 /\ read (wglobal 0) s = I32 (word 16384) /\ read wmem s = m`,
  ACCEPT_TAC VA1_C5P_SITE_SAT);;
let WASMF_DET = prove
 (`!fs x y z. wasmf fs x y /\ wasmf fs x z ==> y = z`,
  ACCEPT_TAC WASMF_DET);;
let WASMF_LIFT = prove
 (`!fs (P:wasmstate->bool) Q C.
     ensures wasm P Q C
     ==> !k. ensures (wasmf fs) (\x. P (FST x) /\ SND x = k)
                                (\x. Q (FST x) /\ SND x = k)
                                (\x y. C (FST x) (FST y))`,
  ACCEPT_TAC WASMF_LIFT);;
let WASMN_TO_WASMF = prove
 (`!fs (P:wasmstate->bool) Q C.
     ensures (wasmn fs) P Q C
     ==> !k. ensures (wasmf fs) (\x. P (FST x) /\ SND x = k)
                                (\x. Q (FST x) /\ SND x = k)
                                (\x y. C (FST x) (FST y))`,
  ACCEPT_TAC WASMN_TO_WASMF);;
let WASMN_TO_WFSUM = prove
 (`!fs (P:wasmstate->bool) Q C. ensures (wasmn fs) P Q C ==> wfsum fs P Q C`,
  ACCEPT_TAC WASMN_TO_WFSUM);;
let WASM_TO_WFSUM = prove
 (`!fs (P:wasmstate->bool) Q C. ensures wasm P Q C ==> wfsum fs P Q C`,
  ACCEPT_TAC WASM_TO_WFSUM);;
let WASMN_CALL_ENSURES = prove
 (`!fs f code np nr e decls (P:wasmstate->bool) Q C Pre Post D n.
     wfsum fs P Q C /\
     (!c. Q c ==> ~(read wstatus c = WRunning)) /\
     fs f = (code,np,nr) /\ wasm_entry code = SOME e /\
     wasm_decl_vals code = SOME decls /\
     (!s. Pre s ==> read wstatus s = WRunning /\
                    wasm_decode (read wcode s) (val (read wpc s)) = SOME (Wcall f,n) /\
                    np <= LENGTH (read wstack s) /\
                    P (wcall_entry code np nr (read wstack s) e decls s)) /\
     (!s c1. Pre s /\ Q c1 /\ C (wcall_entry code np nr (read wstack s) e decls s) c1
             ==> Post (wcall_return (val (read wpc s) + n) np c1 s) /\
                 D s (wcall_return (val (read wpc s) + n) np c1 s))
     ==> ensures (wasmn fs) Pre Post D`,
  ACCEPT_TAC WASMN_CALL_ENSURES);;
let WASMN_CALL_STEP = prove
 (`!fs f code np nr e decls (P:wasmstate->bool) Q C n s R.
     wfsum fs P Q C /\
     (!c. Q c ==> ~(read wstatus c = WRunning)) /\
     fs f = (code,np,nr) /\ wasm_entry code = SOME e /\
     wasm_decl_vals code = SOME decls /\
     read wstatus s = WRunning /\
     wasm_decode (read wcode s) (val (read wpc s)) = SOME (Wcall f,n) /\
     np <= LENGTH (read wstack s) /\
     P (wcall_entry code np nr (read wstack s) e decls s) /\
     (!c1. Q c1 /\ C (wcall_entry code np nr (read wstack s) e decls s) c1
           ==> eventually (wasmn fs) R (wcall_return (val (read wpc s) + n) np c1 s))
     ==> eventually (wasmn fs) R s`,
  ACCEPT_TAC WASMN_CALL_STEP);;
let WCALL_RETURN_TRAP_OBS = prove
 (`!npc np c1 s. read wstatus c1 = WTrapped
     ==> wtrap_obs (wcall_return npc np c1 s) = wtrap_obs c1`,
  ACCEPT_TAC WCALL_RETURN_TRAP_OBS);;
let WASMF_TRAPPED_STEP = prove
 (`!fs x y. wasmf fs x y /\ read wstatus (FST x) = WTrapped
            ==> read wstatus (FST y) = WTrapped /\ wtrap_obs (FST y) = wtrap_obs (FST x)`,
  ACCEPT_TAC WASMF_TRAPPED_STEP);;
let WASMF_TRAPPED_RTC = prove
 (`!fs x y. RTC (wasmf fs) x y
            ==> read wstatus (FST x) = WTrapped
                ==> read wstatus (FST y) = WTrapped /\
                    wtrap_obs (FST y) = wtrap_obs (FST x)`,
  ACCEPT_TAC WASMF_TRAPPED_RTC);;
let EVENTUALLY_RTC_DET = prove
 (`!(R:A->A->bool) P.
     (!x y z. R x y /\ R x z ==> y = z)
     ==> !x y. RTC R x y ==> eventually R P y ==> eventually R P x`,
  ACCEPT_TAC EVENTUALLY_RTC_DET);;
let DIV3_BIG_HIDES_LOOP = prove
 (`eventually div3_big (\x. x = 1) 0`,
  ACCEPT_TAC DIV3_BIG_HIDES_LOOP);;
let DIV3_NONDETERMINISTIC = prove
 (`~(!x y z. div3 x y /\ div3 x z ==> y = z)`,
  ACCEPT_TAC DIV3_NONDETERMINISTIC);;
let RTC_WASM_WASMF = prove
 (`!fs a b. RTC wasm a b ==> RTC (wasmf fs) (a,[]) (b,[])`,
  ACCEPT_TAC RTC_WASM_WASMF);;
let WASMC_WASMN = prove
 (`!fs s s'. wasmc fs s s' ==> wasmn fs s s'`,
  ACCEPT_TAC WASMC_WASMN);;
let RTC_DET_FINAL = prove
 (`!(R:A->A->bool).
     (!x y z. R x y /\ R x z ==> y = z)
     ==> !x y. RTC R x y
               ==> !z. RTC R x z /\ (!u. ~R y u) /\ (!u. ~R z u) ==> y = z`,
  ACCEPT_TAC RTC_DET_FINAL);;
let WASM_CALLN_DET = prove
 (`!fs f npc s a b.
     wasm_calln fs f npc s a /\ wasm_calln fs f npc s b ==> a = b`,
  ACCEPT_TAC WASM_CALLN_DET);;
let WASMN_DET = prove
 (`!fs s a b. wasmn fs s a /\ wasmn fs s b ==> a = b`,
  ACCEPT_TAC WASMN_DET);;
let EVENTUALLY_SUBREL_DET = prove
 (`!(r1:A->A->bool) r2 P.
     (!x y. r1 x y ==> r2 x y) /\ (!x y z. r2 x y /\ r2 x z ==> y = z)
     ==> !s. eventually r1 P s ==> eventually r2 P s`,
  ACCEPT_TAC EVENTUALLY_SUBREL_DET);;
let EVENTUALLY_WASMC_WASMN = prove
 (`!fs P s. eventually (wasmc fs) P s ==> eventually (wasmn fs) P s`,
  ACCEPT_TAC EVENTUALLY_WASMC_WASMN);;
let ENSURES_WASMC_WASMN = prove
 (`!fs (P:wasmstate->bool) Q C. ensures (wasmc fs) P Q C ==> ensures (wasmn fs) P Q C`,
  ACCEPT_TAC ENSURES_WASMC_WASMN);;
let MAYCHANGE_RESTORED = prove
 (`!(c:(A,B)component) (C:A->A->bool).
     strongly_valid_component c /\ (!s s'. C s s' ==> read c s' = read c s)
     ==> !s s'. (C ,, MAYCHANGE [c]) s s' /\ read c s' = read c s ==> C s s'`,
  ACCEPT_TAC MAYCHANGE_RESTORED);;
let ENSURES_MAYCHANGE_RESTORED = prove
 (`!(step:A->A->bool) P Q C (c:(A,B)component).
     strongly_valid_component c /\ (!s s'. C s s' ==> read c s' = read c s) /\
     (!s s'. P s /\ Q s' /\ (C ,, MAYCHANGE [c]) s s' ==> read c s' = read c s) /\
     ensures step P Q (C ,, MAYCHANGE [c])
     ==> ensures step P Q C`,
  ACCEPT_TAC ENSURES_MAYCHANGE_RESTORED);;
let WASM_ENSURES_GLOBAL_RESTORED = prove
 (`!(step:wasmstate->wasmstate->bool) P Q C k.
     (!s s'. C s s' ==> read (wglobal k) s' = read (wglobal k) s) /\
     (!s s'. P s /\ Q s' /\ (C ,, MAYCHANGE [wglobal k]) s s'
             ==> read (wglobal k) s' = read (wglobal k) s) /\
     ensures step P Q (C ,, MAYCHANGE [wglobal k])
     ==> ensures step P Q C`,
  ACCEPT_TAC WASM_ENSURES_GLOBAL_RESTORED);;
