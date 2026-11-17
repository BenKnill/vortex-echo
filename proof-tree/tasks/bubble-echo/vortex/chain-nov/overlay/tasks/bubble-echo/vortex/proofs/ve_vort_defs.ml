(* ========================================================================= *)
(* Vortex Echo v1: the vortex Fredkin export pair of vortex/core/ve_core.wasm *)
(* (sha256 72fe0ba2), ve_vort_apply / ve_vort_unapply. Each body is a prefix *)
(* (pc 21 .. 1305: normalisation of the source into XN, the regularised       *)
(* Biot-Savart field into VACC (i64) and its rounding into VD; SPEC.md 5.1)  *)
(* and the Fredkin loop (pc 1305 .. end), proved on the bytes in ve_vort.ml.  *)
(*                                                                           *)
(* ve_vk_ok VK is the NAMED premise for the prefixes: run from the entry with *)
(* a model with N = 1 .. 640 (model word 1), each prefix reaches pc 1305      *)
(* (stack and labels empty, no trap) with VD[m] = VK mdl S m for m < 3N, the  *)
(* same function VK for both exports, S = VB for apply and S = VA for unapply,*)
(* the model, VA and VB unchanged, writing only the locals and the scratch    *)
(* region 0x1E0000 .. 0x1F2000. Entry pc 21 is wasm_entry, the first        *)
(* instruction after the 10 local-declaration groups (PR #72 stated pc 3,    *)
(* inside the declarations, which made the premise unsatisfiable: control    *)
(* leaf ve_vk_pc3). ve_vk.ml proves ve_vk_ok ve_vk (VE_VK_OK).                *)
(* ========================================================================= *)

let ve_vk_ok = new_definition
 `ve_vk_ok (VK:(num->int32)->(num->int32)->num->int32) <=>
    (!N (mdl:num->int32) (va:num->int32) (vb:num->int32).
        mdl 1 = word N /\ 1 <= N /\ N <= 640
        ==> ensures wasm
             (\s. read wcode s = ve_vort_apply_mc /\ read wpc s = word 21 /\
               read wstatus s = WRunning /\ read wstack s = [] /\ read wlabels s = [] /\
               read warity s = 0 /\ read wmemsize s = 4194304 /\
               (!k. k < 1024 ==> read (wmem :> bytes32 (word (16640 + 4 * k))) s = mdl k) /\
               (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1114112 + 4 * m))) s = va m) /\
               (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1122304 + 4 * m))) s = vb m))
             (\s. read wcode s = ve_vort_apply_mc /\ read wpc s = word 1305 /\
               read wstatus s = WRunning /\ read wstack s = [] /\ read wlabels s = [] /\
               read warity s = 0 /\ read wmemsize s = 4194304 /\
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
             (\s. read wcode s = ve_vort_unapply_mc /\ read wpc s = word 21 /\
               read wstatus s = WRunning /\ read wstack s = [] /\ read wlabels s = [] /\
               read warity s = 0 /\ read wmemsize s = 4194304 /\
               (!k. k < 1024 ==> read (wmem :> bytes32 (word (16640 + 4 * k))) s = mdl k) /\
               (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1114112 + 4 * m))) s = va m) /\
               (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1122304 + 4 * m))) s = vb m))
             (\s. read wcode s = ve_vort_unapply_mc /\ read wpc s = word 1305 /\
               read wstatus s = WRunning /\ read wstack s = [] /\ read wlabels s = [] /\
               read warity s = 0 /\ read wmemsize s = 4194304 /\
               (!k. k < 1024 ==> read (wmem :> bytes32 (word (16640 + 4 * k))) s = mdl k) /\
               (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1114112 + 4 * m))) s = va m) /\
               (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1122304 + 4 * m))) s = vb m) /\
               (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1974272 + 4 * m))) s = VK mdl va m))
            (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
            MAYCHANGE [wlocal 0; wlocal 1; wlocal 2; wlocal 3; wlocal 4; wlocal 5; wlocal 6; wlocal 7; wlocal 8; wlocal 9; wlocal 10; wlocal 11; wlocal 12; wlocal 13; wlocal 14; wlocal 15; wlocal 16; wlocal 17; wlocal 18; wlocal 19; wlocal 20; wlocal 21; wlocal 22; wlocal 23; wlocal 24; wlocal 25; wlocal 26; wlocal 27; wlocal 28; wlocal 29] ,,
            MAYCHANGE [wmem :> bytes(word 1966080,73728)]))`;;
