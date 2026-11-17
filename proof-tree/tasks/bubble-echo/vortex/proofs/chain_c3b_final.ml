needs "ve_vort.ml";;
needs "ve_tick.ml";;
needs "ve_vk.ml";;
needs "va1_code.ml";;
needs "va1_seq_final2.ml";;
needs "pop_design_defs.ml";;
needs "pop_design_stmts.ml";;
needs "chain_c3b_dec.ml";;
needs "chain_c3b_defs.ml";;
needs "chain_c3b_l1.ml";;
needs "chain_c3b_pure.ml";;
(* vortex-chain c3b (Claude Opus 5.5, 2026-11-13): spec-locked final leaf for chain_c3b_final.spec
   (frozen sha256 296578ea2110e60d0c5a28a5ee7a9c10ab42f1a1e0f49dbe8ce30813208c2a18): re-binds its 9 theorems. *)
let VA1_F25_ENTRY = prove(`wasm_entry va1_f25_mc = SOME 13`,
  MATCH_ACCEPT_TAC VA1_F25_ENTRY);;
let VA1_F25_OK = prove(`!(a0:int32) (a1:int32) (a2:int32) (t:int32) (mdl:num->int32) (tbl:num->int32) (decls:wval list).
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0) /\ wasm_decl_vals va1_f25_mc = SOME decls
     ==> ensures wasm
          (\s. read wcode s = va1_f25_mc /\ read wpc s = word 13 /\ read wstatus s = WRunning /\
               read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\
               read wlocals s = wcall_locals [I32 a2; I32 a1; I32 a0] decls /\
               va1_tick t (read wmem s) /\ read (bytes32 (word 16396)) (read wmem s) = word 4294967295 /\
               va1_mdl mdl (read wmem s) /\ va1_w32s 65536 262144 tbl (read wmem s))
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 0)] /\
               va1_f25_post t mdl tbl a0 a1 a2 (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocal 0; wlocal 1; wlocal 2; wlocal 3; wlocal 4; wlocal 5; wlocal 6; wlocal 7;
                      wlocal 8; wlocal 9; wlocal 10; wlocal 11; wlocal 12; wlocal 13; wlocal 14; wlocal 15] ,,
           MAYCHANGE [wmem :> bytes(word 16396,8)] ,, MAYCHANGE [wmem :> bytes(word 16408,96)] ,,
           MAYCHANGE [wmem :> bytes(word 1130496,835584)])`,
  MATCH_ACCEPT_TAC VA1_F25_OK);;
let VA1_F25_GUARD_P = prove(`!(a0:int32) (a1:int32) (a2:int32) (decls:wval list).
     wasm_decl_vals va1_f25_mc = SOME decls
     ==> ensures wasm
          (\s. read wcode s = va1_f25_mc /\ read wpc s = word 13 /\ read wstatus s = WRunning /\
               read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\
               read wlocals s = wcall_locals [I32 a2; I32 a1; I32 a0] decls /\
               ~(read (bytes32 (word 16396)) (read wmem s) = word 4294967295))
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 1)])
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus])`,
  MATCH_ACCEPT_TAC VA1_F25_GUARD_P);;
let VA1_F25_GUARD_ARGS = prove(`!(decls:wval list).
     wasm_decl_vals va1_f25_mc = SOME decls
     ==> ensures wasm
          (\s. read wcode s = va1_f25_mc /\ read wpc s = word 13 /\ read wstatus s = WRunning /\
               read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\
               read wlocals s = wcall_locals [I32 (word 0); I32 (word 0); I32 (word 0)] decls /\
               read (bytes32 (word 16396)) (read wmem s) = word 4294967295)
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 2)])
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus])`,
  MATCH_ACCEPT_TAC VA1_F25_GUARD_ARGS);;
let VA1_F25_FRAME_BYTES = prove(`!(s:wasmstate) (s':wasmstate).
     (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
      MAYCHANGE [wlocal 0; wlocal 1; wlocal 2; wlocal 3; wlocal 4; wlocal 5; wlocal 6; wlocal 7;
                 wlocal 8; wlocal 9; wlocal 10; wlocal 11; wlocal 12; wlocal 13; wlocal 14; wlocal 15] ,,
      MAYCHANGE [wmem :> bytes(word 16396,8)] ,, MAYCHANGE [wmem :> bytes(word 16408,96)] ,,
      MAYCHANGE [wmem :> bytes(word 1130496,835584)]) s s'
     ==> va1_f25_frame (read wmem s) (read wmem s')`,
  MATCH_ACCEPT_TAC VA1_F25_FRAME_BYTES);;
let VA1_F25_SAT = prove(`!(a0:int32) (a1:int32) (a2:int32) (t:int32) (mdl:num->int32) (tbl:num->int32).
     ?(decls:wval list) (s:wasmstate).
       wasm_decl_vals va1_f25_mc = SOME decls /\
       read wcode s = va1_f25_mc /\ read wpc s = word 13 /\ read wstatus s = WRunning /\
       read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
       read wmemsize s = 4194304 /\
       read wlocals s = wcall_locals [I32 a2; I32 a1; I32 a0] decls /\
       va1_tick t (read wmem s) /\ read (bytes32 (word 16396)) (read wmem s) = word 4294967295 /\
       va1_mdl mdl (read wmem s) /\ va1_w32s 65536 262144 tbl (read wmem s)`,
  MATCH_ACCEPT_TAC VA1_F25_SAT);;
let VA1_BAD_PUNCT = prove(`!(mdl:num->int32) (tbl:num->int32).
     va1_bad mdl tbl ((\k. word 251658), va1_rbinit tbl, (\k. word 0), (\k. word 0), (\k. word 0),
                      va1_zpseed mdl, word 0) = word 0`,
  MATCH_ACCEPT_TAC VA1_BAD_PUNCT);;
let VA1_PUNCT_UNPUNCT_INVERSE = prove(`!(t:int32) (mdl:num->int32) (tbl:num->int32) (a0:int32) (a1:int32) (a2:int32)
   (m0:int64->byte) (m1:int64->byte) (m2:int64->byte).
     ~(t = word 4294967295) /\
     va1_punct_clean m0 /\ va1_mdl mdl m0 /\ va1_w32s 65536 262144 tbl m0 /\
     va1_f25_post t mdl tbl a0 a1 a2 m1 /\ va1_f25_frame m0 m1 /\
     va1_unpunct_post m1 m2 /\ va1_unpunct_frame m1 m2
     ==> !a. a < 4194304 ==> read (bytes8 (word a)) m2 = read (bytes8 (word a)) m0`,
  MATCH_ACCEPT_TAC VA1_PUNCT_UNPUNCT_INVERSE);;
let VA1_PUNCT_UNPUNCT_SAT = prove(`!(t:int32) (mdl:num->int32) (tbl:num->int32) (a0:int32) (a1:int32) (a2:int32).
     ~(t = word 4294967295)
     ==> ?(m0:int64->byte) (m1:int64->byte) (m2:int64->byte).
           va1_punct_clean m0 /\ va1_mdl mdl m0 /\ va1_w32s 65536 262144 tbl m0 /\
           va1_f25_post t mdl tbl a0 a1 a2 m1 /\ va1_f25_frame m0 m1 /\
           va1_unpunct_post m1 m2 /\ va1_unpunct_frame m1 m2`,
  MATCH_ACCEPT_TAC VA1_PUNCT_UNPUNCT_SAT);;
