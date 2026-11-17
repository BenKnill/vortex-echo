(* c8p_f25h2_final.ml (vortex-chain c8p, Claude Opus 5.5, 2026-11-14): spec-locked final leaf for c8p_f25h2.spec (row P5, v2);
   re-binds VA1_F25_HDR from c8p_f25h2_pf.ml. Basis parent: the C6b host layer in vortex-pop/assembly/proj. *)
needs "chain_c6b_host.ml";;
needs "c8p_f25h2_defs.ml";;
needs "c8p_f25h2_pf.ml";;
let VA1_F25_HDR = prove
 (`!(a0:int32) (a1:int32) (a2:int32) (t:int32) (mdl:num->int32) (tbl:num->int32) (decls:wval list).
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0) /\ wasm_decl_vals va1_f25_mc = SOME decls
     ==> ensures wasm
          (\s. read wcode s = va1_f25_mc /\ read wpc s = word 13 /\ read wstatus s = WRunning /\
               read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\
               read wlocals s = wcall_locals [I32 a2; I32 a1; I32 a0] decls /\
               va1_tick t (read wmem s) /\ read (bytes32 (word 16396)) (read wmem s) = word 4294967295 /\
               va1_mdl mdl (read wmem s) /\ va1_w32s 65536 262144 tbl (read wmem s))
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 0)] /\
               va1_f25_post t mdl tbl a0 a1 a2 (read wmem s) /\
               va1_w32s 16420 21 (va1_phdr a0 a1 a2) (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocal 0; wlocal 1; wlocal 2; wlocal 3; wlocal 4; wlocal 5; wlocal 6; wlocal 7;
                      wlocal 8; wlocal 9; wlocal 10; wlocal 11; wlocal 12; wlocal 13; wlocal 14; wlocal 15] ,,
           MAYCHANGE [wmem :> bytes(word 16396,8)] ,, MAYCHANGE [wmem :> bytes(word 16408,96)] ,,
           MAYCHANGE [wmem :> bytes(word 1130496,835584)])`,
  ACCEPT_TAC VA1_F25_HDR);;
