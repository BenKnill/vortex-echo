(* Spec: Vortex Echo v1, the header tick pair ve_tick_inc / ve_tick_dec on the exact bytes of vortex/core/ve_core.wasm (sha256 72fe0ba2): header word 2 (byte 16392) := T + 1 resp. T - 1 (mod 2^32), no other memory written; dec on the word inc leaves restores T. *)
theorem VE_TICK_INC_CORRECT
 `!(t:int32). ensures wasm
      (\s. read wcode s = ve_tick_inc_mc /\ read wpc s = word 1 /\
           read wstatus s = WRunning /\ read wstack s = [] /\
           read wlabels s = [] /\ read warity s = 0 /\ read wmemsize s = 2097152 /\
           read (wmem :> bytes32 (word 16392)) s = t)
      (\s. read wstatus s = WDone /\ read wstack s = [] /\
           read (wmem :> bytes32 (word 16392)) s = word_add t (word 1))
      (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
       MAYCHANGE [wstatus] ,, MAYCHANGE [wmem :> bytes(word 16392,4)])`;;
theorem VE_TICK_DEC_CORRECT
 `!(t:int32). ensures wasm
      (\s. read wcode s = ve_tick_dec_mc /\ read wpc s = word 1 /\
           read wstatus s = WRunning /\ read wstack s = [] /\
           read wlabels s = [] /\ read warity s = 0 /\ read wmemsize s = 2097152 /\
           read (wmem :> bytes32 (word 16392)) s = t)
      (\s. read wstatus s = WDone /\ read wstack s = [] /\
           read (wmem :> bytes32 (word 16392)) s = word_sub t (word 1))
      (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
       MAYCHANGE [wstatus] ,, MAYCHANGE [wmem :> bytes(word 16392,4)])`;;
theorem VE_TICK_INVERSE
 `!(t:int32). ensures wasm
      (\s. read wcode s = ve_tick_dec_mc /\ read wpc s = word 1 /\
           read wstatus s = WRunning /\ read wstack s = [] /\
           read wlabels s = [] /\ read warity s = 0 /\ read wmemsize s = 2097152 /\
           read (wmem :> bytes32 (word 16392)) s = word_add t (word 1))
      (\s. read wstatus s = WDone /\ read wstack s = [] /\
           read (wmem :> bytes32 (word 16392)) s = t)
      (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
       MAYCHANGE [wstatus] ,, MAYCHANGE [wmem :> bytes(word 16392,4)])`;;
definition ve_tick_inc_mc
 `ve_tick_inc_mc:byte list = [word 0x00; word 0x41; word 0x00; word 0x41; word 0x00; word 0x28; word 0x02; word 0x88; word 0x80; word 0x01; word 0x41; word 0x01; word 0x6a; word 0x36; word 0x02; word 0x88; word 0x80; word 0x01; word 0x0b]`;;
definition ve_tick_dec_mc
 `ve_tick_dec_mc:byte list = [word 0x00; word 0x41; word 0x00; word 0x41; word 0x00; word 0x28; word 0x02; word 0x88; word 0x80; word 0x01; word 0x41; word 0x7f; word 0x6a; word 0x36; word 0x02; word 0x88; word 0x80; word 0x01; word 0x0b]`;;
(* define'd recursive helpers: their meaning is pinned by the CLAUSES theorems above *)
