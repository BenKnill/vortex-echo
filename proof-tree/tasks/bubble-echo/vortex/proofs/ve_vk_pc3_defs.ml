(* ========================================================================= *)
(* Vortex Echo v1 control: the named premise ve_vk_ok exactly as merged in   *)
(* PR #72 (vortex/proofs/ve_vort_defs.ml at ff414f05), renamed ve_vk_ok_pc3.  *)
(* It runs both prefixes of ve_vort_apply / ve_vort_unapply from pc 3, but   *)
(* the bodies start with 10 local-declaration groups and the first           *)
(* instruction is at pc 21 (wasm_entry). ve_vk_pc3.ml proves that no VK      *)
(* satisfies it (VE_VK_OK_PC3_UNSAT).                                        *)
(* ========================================================================= *)

let ve_vk_ok_pc3 = new_definition
 `ve_vk_ok_pc3 (VK:(num->int32)->(num->int32)->num->int32) <=>
    (!N (mdl:num->int32) (va:num->int32) (vb:num->int32).
        mdl 1 = word N /\ 1 <= N /\ N <= 640
        ==> ensures wasm
             (\s. read wcode s = ve_vort_apply_mc /\ read wpc s = word 3 /\
               read wstatus s = WRunning /\ read wstack s = [] /\ read wlabels s = [] /\
               read warity s = 0 /\ read wmemsize s = 2097152 /\
               (!k. k < 1024 ==> read (wmem :> bytes32 (word (16640 + 4 * k))) s = mdl k) /\
               (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1114112 + 4 * m))) s = va m) /\
               (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1122304 + 4 * m))) s = vb m))
             (\s. read wcode s = ve_vort_apply_mc /\ read wpc s = word 1305 /\
               read wstatus s = WRunning /\ read wstack s = [] /\ read wlabels s = [] /\
               read warity s = 0 /\ read wmemsize s = 2097152 /\
               (!k. k < 1024 ==> read (wmem :> bytes32 (word (16640 + 4 * k))) s = mdl k) /\
               (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1114112 + 4 * m))) s = va m) /\
               (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1122304 + 4 * m))) s = vb m) /\
               (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1974272 + 4 * m))) s = VK mdl vb m))
            (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
            MAYCHANGE [wlocal 0; wlocal 1; wlocal 2; wlocal 3; wlocal 4; wlocal 5; wlocal 6; wlocal 7; wlocal 8; wlocal 9; wlocal 10; wlocal 11; wlocal 12; wlocal 13; wlocal 14; wlocal 15; wlocal 16; wlocal 17; wlocal 18; wlocal 19; wlocal 20; wlocal 21; wlocal 22; wlocal 23; wlocal 24; wlocal 25; wlocal 26; wlocal 27; wlocal 28; wlocal 29] ,,
            MAYCHANGE [wmem :> bytes(word 1966080,73728)])) /\
    (!N (mdl:num->int32) (va:num->int32) (vb:num->int32).
        mdl 1 = word N /\ 1 <= N /\ N <= 640
        ==> ensures wasm
             (\s. read wcode s = ve_vort_unapply_mc /\ read wpc s = word 3 /\
               read wstatus s = WRunning /\ read wstack s = [] /\ read wlabels s = [] /\
               read warity s = 0 /\ read wmemsize s = 2097152 /\
               (!k. k < 1024 ==> read (wmem :> bytes32 (word (16640 + 4 * k))) s = mdl k) /\
               (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1114112 + 4 * m))) s = va m) /\
               (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1122304 + 4 * m))) s = vb m))
             (\s. read wcode s = ve_vort_unapply_mc /\ read wpc s = word 1305 /\
               read wstatus s = WRunning /\ read wstack s = [] /\ read wlabels s = [] /\
               read warity s = 0 /\ read wmemsize s = 2097152 /\
               (!k. k < 1024 ==> read (wmem :> bytes32 (word (16640 + 4 * k))) s = mdl k) /\
               (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1114112 + 4 * m))) s = va m) /\
               (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1122304 + 4 * m))) s = vb m) /\
               (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1974272 + 4 * m))) s = VK mdl va m))
            (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
            MAYCHANGE [wlocal 0; wlocal 1; wlocal 2; wlocal 3; wlocal 4; wlocal 5; wlocal 6; wlocal 7; wlocal 8; wlocal 9; wlocal 10; wlocal 11; wlocal 12; wlocal 13; wlocal 14; wlocal 15; wlocal 16; wlocal 17; wlocal 18; wlocal 19; wlocal 20; wlocal 21; wlocal 22; wlocal 23; wlocal 24; wlocal 25; wlocal 26; wlocal 27; wlocal 28; wlocal 29] ,,
            MAYCHANGE [wmem :> bytes(word 1966080,73728)]))`;;
