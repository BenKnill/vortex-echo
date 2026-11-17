(* Spec: lane vortex-chain-20261111-142342, rung C3a (C3A agent, Claude Opus 5.5, 2026-11-13; file chain_c3a_final2.spec; times in c3a/STATUS.md, from date). Vortex Echo purist module tasks/bubble-echo/vortex/purist/vortex_a1.wasm (sha256 a3cf8c82) on its exact bytes: the UN-PUNCTURE tick, i.e. tick_backward (f36) when the clock word T equals the pop word P (P <> -1, P <> 0), under wasmc (wasm plus frame-free direct calls; every callee here, f26 ve_unpuncture, f28 tick_dec and f10 vort_unapply, makes no call itself). This is new stepping of the bytes, integer only; f26 is stepped here (its 2048-bead check loop, 26 header stores, the 1024 x 6 and 24576 x 4 zeroing loops), and so is tick_backward's inline 32768 x 4 speed-table clear. No leaf-contract premise: f10 and f28 come from PROVED call-site lemmas (VA1P_CALL_F10 / VA1P_CALL_F28, pop_q0_calls.ml), f26 from VA1_F26_OK, which this spec states and the prover must prove on the bytes.
   Definitions (new). va1_f26_mc is function #26's body bytes. va1_rbv / va1_rbinit transcribe f26's rb_init for bead k from the two speed-table words tbl (128 k) and tbl (128 k + 1) (i64 arithmetic on their sign extensions, exactly as the bytes at f26 pc 135-199; the same instruction sequence f25 uses to seed RB). va1_zpx0 / va1_zpx1 / va1_zpseed transcribe zp_seed for bead k from model word 2 (ZSEED, byte 16648) (f26 pc 23-44 and 202-274). va1_mis mdl tbl (ra,rb,jq,jp,zq,zp) k counts, as a number 0..6, the six per-bead checks f26 makes: RA <> 251658, JQ <> 0, JP <> 0, ZQ <> 0, RB <> va1_rbinit, ZP <> va1_zpseed. va1_bad mdl tbl (ra,rb,jq,jp,zq,zp,nd) = nd + the sum over beads 0..2047, as an i32 word (mod 2^32), which is what f26 computes and adds to header word 5 (healErr, byte 16404). It is the true count only when it cannot wrap: VA1_BAD_COUNT / VA1_BAD_ZERO_IFF need val nd <= 16384 (the module's droplet capacity); with an unrestricted nd the word can wrap (for example nd = 0xFFFFFFFF plus one mismatch gives 0). va1_unp_frame m0 m says every byte of the 4 MiB memory outside [16392,16512) and [65536,2039808) is unchanged.
   Headlines. VA1_TICK_UNPUNCT: from tick_backward's entry with va1_st p p ap mdl N y hp tbl (ra,rb,jq,jp,di,zq,zp,nd) (clock = pop word = p) and healErr = h, the run reaches WDone with result 1, the clock p - 1, the pop word -1, the auto-pop word and model unchanged, the 3N vortex words in use = 16 backward swirl steps of y (ve_fredkin_bwdn (\i. ve_vk mdl) 16 y, the same image as the PROVED no-pop backward tick), header words 6..29 zero and words 30, 31 unchanged, the speed table zero, RA, RB, JQ, JP, ZQ, ZP, every droplet word and the droplet count zero, and healErr = h + va1_bad mdl tbl (ra,rb,jq,jp,zq,zp,nd); memory writes stay inside the named MAYCHANGE regions. VA1_HCALL_UNPUNCT: the same as one host call (C1's va1_hcall), globals unchanged, plus va1_unp_frame. VA1_BAD_PUNCT: on the state the puncture is built to leave (RA = 251658, RB = va1_rbinit tbl, JQ = JP = ZQ = 0, ZP = va1_zpseed mdl, nd = 0) the count is 0 for EVERY speed table. That f25 (ve_puncture) leaves exactly that state is NOT proved here (rung C3b); it is TESTED (c3a/tools/c3a_unpunct.mjs: 300 real punctures on the bytes, va1_bad = 0 and healErr unchanged on all). VA1_F26_OK: f26's own contract from its entry (stated here, to be proved). VA1_UNPUNCT_SAT / VA1_F26_SAT: the preconditions are satisfiable for every choice of the data (so neither ensures is vacuous), and a function table with the three callees exists.
   Wording rule (LADDER 1.2): the frames are memory regions, not "every byte". The un-puncture tick may change [16392,16512) (clock, pop word, droplet count, healErr, header words 6..31), the speed table [65536,1114112), [1114112,1966080) (vortex arrays VA/VB including the unused words VA/VB[3N..2048), rings, droplet words) and the scratch area [1966080,2039808); the scratch area and the unused vortex words are pinned by no post. Not covered: the forward puncture (f25, f33/f34/f32 and the auto-puncture path; LADDER 1.3: no theorem here says anything about tick_forward through a puncture, total or partial), that the state before the puncture had pop data zero (a chain invariant, rung C4), and the 96-byte stack frame [16288,16384) the forward puncture leaves (outside this tick). STATUS AT FREEZE: no theorem of this spec is proved yet; this is the target statement for proofs in Hearth's model of WebAssembly (the PROVED inputs it builds on are VA1P_CALL_F10 / VA1P_CALL_F28 of pop_q0_calls.ml and the copied entries named below). Prove with plain --spec, not --benchmark. Recursive constants reached through the copied entries (ve_fredkin_bwdn, ve_isq, ve_vk_rs, ve_vk_acc, wdecl_vals) are pinned by their CLAUSES theorems; every other constant the statements reach is pinned by a definition entry copied byte for byte from the frozen chain_c2_final.spec (c7a0c0a8) or chain_c1_final.spec (3b62701f), except the new entries in the C3a block.
   Version note: this is chain_c3a_final2.spec. It differs from the frozen chain_c3a_final.spec (sha256 2dc9792e) ONLY in the pin text of va1_mis and va1_bad: there they were written with tuple-pattern arguments ((ra,rb,jq,jp,zq,zp) and (ra,..,nd)), which Hearth's spec lock cannot read as NAME x1 .. xn = t (the one receipted run with that spec, runs/20261113T070220Z-1261254-chain_c3a_final-0deb21, was REFUSED at spec lock and proved nothing). Here the same constants are pinned in the variable form of the kernel's stored definition (q a tuple, its components by FST/SND); for an explicit tuple q = (ra,rb,jq,jp,zq,zp[,nd]) the projections reduce to exactly the old text, so the meaning is unchanged; every other entry and every theorem is byte-identical. *)

(* ---- C3a definitions (new) ---- *)
definition va1_f26_mc
 `va1_f26_mc:byte list = [word 0x02; word 0x05; word 0x7f; word 0x01; word 0x7e; word 0x41; word 0x00; word 0x21; word 0x00; word 0x02; word 0x40; word 0x41; word 0x00; word 0x28; word 0x02; word 0x8c; word 0x80; word 0x01; word 0x41; word 0x7f; word 0x46; word 0x0d; word 0x00; word 0x41; word 0x00; word 0x28; word 0x02; word 0x88; word 0x82; word 0x01; word 0x41; word 0xb5; word 0xdc; word 0xca; word 0x95; word 0x7c; word 0x6c; word 0x41; word 0xe7; word 0x8c; word 0xdb; word 0xa8; word 0x7a; word 0x6a; word 0x21; word 0x01; word 0x41; word 0x00; word 0x28; word 0x02; word 0x90; word 0x80; word 0x01; word 0x21; word 0x00; word 0x41; word 0x80; word 0x80; word 0x04; word 0x21; word 0x02; word 0x41; word 0x00; word 0x21; word 0x03; word 0x41; word 0x00; word 0x21; word 0x04; word 0x03; word 0x40; word 0x20; word 0x00; word 0x20; word 0x03; word 0x41; word 0x80; word 0x80; word 0xc5; word 0x00; word 0x6a; word 0x28; word 0x02; word 0x00; word 0x41; word 0x8a; word 0xae; word 0x0f; word 0x47; word 0x6a; word 0x20; word 0x03; word 0x41; word 0x80; word 0x80; word 0xc6; word 0x00; word 0x6a; word 0x28; word 0x02; word 0x00; word 0x41; word 0x00; word 0x47; word 0x6a; word 0x20; word 0x03; word 0x41; word 0x80; word 0xc0; word 0xc6; word 0x00; word 0x6a; word 0x28; word 0x02; word 0x00; word 0x41; word 0x00; word 0x47; word 0x6a; word 0x20; word 0x03; word 0x41; word 0x80; word 0x80; word 0xc7; word 0x00; word 0x6a; word 0x28; word 0x02; word 0x00; word 0x41; word 0x00; word 0x47; word 0x6a; word 0x20; word 0x03; word 0x41; word 0x80; word 0xc0; word 0xc5; word 0x00; word 0x6a; word 0x28; word 0x02; word 0x00; word 0x20; word 0x02; word 0x41; word 0x04; word 0x6a; word 0x34; word 0x02; word 0x00; word 0x20; word 0x02; word 0x34; word 0x02; word 0x00; word 0x22; word 0x05; word 0x7d; word 0x42; word 0x8a; word 0xae; word 0x0f; word 0x7e; word 0x42; word 0x80; word 0x80; word 0x10; word 0x7c; word 0x42; word 0x13; word 0x87; word 0x20; word 0x05; word 0x7c; word 0x22; word 0x05; word 0x42; word 0x01; word 0x20; word 0x05; word 0x42; word 0x01; word 0x55; word 0x1b; word 0x42; word 0x01; word 0x7c; word 0x42; word 0x01; word 0x88; word 0xa7; word 0x41; word 0x8a; word 0xae; word 0x0f; word 0x6a; word 0x47; word 0x6a; word 0x20; word 0x03; word 0x41; word 0x80; word 0xc0; word 0xc7; word 0x00; word 0x6a; word 0x28; word 0x02; word 0x00; word 0x20; word 0x01; word 0x20; word 0x04; word 0x41; word 0xb9; word 0xf3; word 0xdd; word 0xf1; word 0x79; word 0x73; word 0x41; word 0xeb; word 0x94; word 0xaf; word 0xaf; word 0x78; word 0x6c; word 0x73; word 0x22; word 0x00; word 0x41; word 0x0f; word 0x76; word 0x20; word 0x00; word 0x73; word 0x41; word 0xed; word 0xf8; word 0xec; word 0xe0; word 0x02; word 0x6c; word 0x22; word 0x00; word 0x41; word 0x0c; word 0x76; word 0x20; word 0x00; word 0x73; word 0xad; word 0x42; word 0xfd; word 0x90; word 0x14; word 0x7e; word 0x42; word 0x80; word 0x80; word 0x80; word 0x80; word 0x98; word 0xf8; word 0xfe; word 0x7e; word 0x7c; word 0x42; word 0x30; word 0x87; word 0xa7; word 0x47; word 0x6a; word 0x21; word 0x00; word 0x20; word 0x02; word 0x41; word 0x80; word 0x04; word 0x6a; word 0x21; word 0x02; word 0x20; word 0x04; word 0x41; word 0x01; word 0x6a; word 0x21; word 0x04; word 0x20; word 0x03; word 0x41; word 0x04; word 0x6a; word 0x22; word 0x03; word 0x41; word 0x80; word 0xc0; word 0x00; word 0x47; word 0x0d; word 0x00; word 0x0b; word 0x41; word 0x00; word 0x41; word 0x00; word 0x28; word 0x02; word 0x94; word 0x80; word 0x01; word 0x20; word 0x00; word 0x6a; word 0x36; word 0x02; word 0x94; word 0x80; word 0x01; word 0x41; word 0x00; word 0x41; word 0x7f; word 0x36; word 0x02; word 0x8c; word 0x80; word 0x01; word 0x41; word 0x00; word 0x41; word 0x00; word 0x36; word 0x02; word 0x98; word 0x80; word 0x01; word 0x41; word 0x00; word 0x41; word 0x00; word 0x36; word 0x02; word 0x9c; word 0x80; word 0x01; word 0x41; word 0x00; word 0x41; word 0x00; word 0x36; word 0x02; word 0xa0; word 0x80; word 0x01; word 0x41; word 0x00; word 0x41; word 0x00; word 0x36; word 0x02; word 0xa4; word 0x80; word 0x01; word 0x41; word 0x00; word 0x41; word 0x00; word 0x36; word 0x02; word 0xa8; word 0x80; word 0x01; word 0x41; word 0x00; word 0x41; word 0x00; word 0x36; word 0x02; word 0xac; word 0x80; word 0x01; word 0x41; word 0x00; word 0x41; word 0x00; word 0x36; word 0x02; word 0xb0; word 0x80; word 0x01; word 0x41; word 0x00; word 0x41; word 0x00; word 0x36; word 0x02; word 0xb4; word 0x80; word 0x01; word 0x41; word 0x00; word 0x41; word 0x00; word 0x36; word 0x02; word 0xb8; word 0x80; word 0x01; word 0x41; word 0x00; word 0x41; word 0x00; word 0x36; word 0x02; word 0xbc; word 0x80; word 0x01; word 0x41; word 0x00; word 0x41; word 0x00; word 0x36; word 0x02; word 0xc0; word 0x80; word 0x01; word 0x41; word 0x00; word 0x41; word 0x00; word 0x36; word 0x02; word 0xc4; word 0x80; word 0x01; word 0x41; word 0x00; word 0x41; word 0x00; word 0x36; word 0x02; word 0xc8; word 0x80; word 0x01; word 0x41; word 0x00; word 0x41; word 0x00; word 0x36; word 0x02; word 0xcc; word 0x80; word 0x01; word 0x41; word 0x00; word 0x41; word 0x00; word 0x36; word 0x02; word 0xd0; word 0x80; word 0x01; word 0x41; word 0x00; word 0x41; word 0x00; word 0x36; word 0x02; word 0xd4; word 0x80; word 0x01; word 0x41; word 0x00; word 0x41; word 0x00; word 0x36; word 0x02; word 0xd8; word 0x80; word 0x01; word 0x41; word 0x00; word 0x41; word 0x00; word 0x36; word 0x02; word 0xdc; word 0x80; word 0x01; word 0x41; word 0x00; word 0x41; word 0x00; word 0x36; word 0x02; word 0xe0; word 0x80; word 0x01; word 0x41; word 0x00; word 0x41; word 0x00; word 0x36; word 0x02; word 0xe4; word 0x80; word 0x01; word 0x41; word 0x00; word 0x41; word 0x00; word 0x36; word 0x02; word 0xe8; word 0x80; word 0x01; word 0x41; word 0x00; word 0x41; word 0x00; word 0x36; word 0x02; word 0xec; word 0x80; word 0x01; word 0x41; word 0x00; word 0x41; word 0x00; word 0x36; word 0x02; word 0xf0; word 0x80; word 0x01; word 0x41; word 0x00; word 0x41; word 0x00; word 0x36; word 0x02; word 0xf4; word 0x80; word 0x01; word 0x41; word 0x80; word 0x40; word 0x21; word 0x03; word 0x03; word 0x40; word 0x20; word 0x03; word 0x41; word 0x80; word 0xc0; word 0xc5; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0x80; word 0x80; word 0xc8; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0x80; word 0xc0; word 0xc7; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0x80; word 0x80; word 0xc7; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0x80; word 0xc0; word 0xc6; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0x80; word 0x80; word 0xc6; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0x08; word 0x6a; word 0x22; word 0x03; word 0x0d; word 0x00; word 0x0b; word 0x41; word 0x80; word 0x80; word 0x50; word 0x21; word 0x03; word 0x03; word 0x40; word 0x20; word 0x03; word 0x41; word 0x98; word 0x80; word 0xf8; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0x90; word 0x80; word 0xf8; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0x88; word 0x80; word 0xf8; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0x80; word 0x80; word 0xf8; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0x20; word 0x6a; word 0x22; word 0x03; word 0x0d; word 0x00; word 0x0b; word 0x41; word 0x00; word 0x41; word 0x00; word 0x36; word 0x02; word 0x90; word 0x80; word 0x01; word 0x0b; word 0x20; word 0x00; word 0x0b]`;;
definition va1_rbv
 `va1_rbv (tbl:num->int32) (k:num) =
    word_add (word_ishr (word_add (word_mul (word_sub (word_sx (tbl (128 * k + 1)):int64) (word_sx (tbl (128 * k)))) (word 251658)) (word 262144)) 19)
             (word_sx (tbl (128 * k)):int64)`;;
definition va1_rbinit
 `va1_rbinit (tbl:num->int32) (k:num) =
    word_add (word_zx (word_ushr (word_add (if ival (va1_rbv tbl k) > &1 then va1_rbv tbl k else word 1) (word 1)) 1):int32) (word 251658)`;;
definition va1_zpx0
 `va1_zpx0 (mdl:num->int32) (k:num) =
    word_xor (word_add (word_mul (mdl 2) (word 3266489909)) (word 2769733223))
             (word_mul (word_xor (word k) (word 2654435769)) (word 2246822507)):int32`;;
definition va1_zpx1
 `va1_zpx1 (mdl:num->int32) (k:num) =
    word_mul (word_xor (word_ushr (va1_zpx0 mdl k) 15) (va1_zpx0 mdl k)) (word 739982445):int32`;;
definition va1_zpseed
 `va1_zpseed (mdl:num->int32) (k:num) =
    word_zx (word_ishr (word_add (word_mul (word_zx (word_xor (word_ushr (va1_zpx1 mdl k) 12) (va1_zpx1 mdl k)):int64) (word 329853))
                                 (word 18446176457274163200)) 48):int32`;;
definition va1_mis
 `va1_mis (mdl:num->int32) (tbl:num->int32) (q:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)) (k:num) =
    bitval (~(FST q k = word 251658)) + bitval (~(FST (SND (SND q)) k = word 0)) +
    bitval (~(FST (SND (SND (SND q))) k = word 0)) + bitval (~(FST (SND (SND (SND (SND q)))) k = word 0)) +
    bitval (~(FST (SND q) k = va1_rbinit tbl k)) + bitval (~(SND (SND (SND (SND (SND q)))) k = va1_zpseed mdl k))`;;
definition va1_bad
 `va1_bad (mdl:num->int32) (tbl:num->int32) (q:(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#int32) =
    word_add (SND (SND (SND (SND (SND (SND q))))))
             (word (nsum (0..2047) (\k. va1_mis mdl tbl (FST q,FST (SND q),FST (SND (SND q)),FST (SND (SND (SND q))),
                                                         FST (SND (SND (SND (SND q)))),FST (SND (SND (SND (SND (SND q)))))) k)))`;;
definition va1_unp_frame
 `va1_unp_frame (m0:int64->byte) (m:int64->byte) <=>
    !a. a < 4194304 /\ ~(16392 <= a /\ a < 16512) /\ ~(65536 <= a /\ a < 2039808)
        ==> read (bytes8 (word a)) m = read (bytes8 (word a)) m0`;;

(* ---- C3a theorems (new) ---- *)
theorem VA1_F26_CALLEE
 `wasm_entry va1_f26_mc = SOME 5 /\
  wasm_decl_vals va1_f26_mc = SOME [I32 (word 0); I32 (word 0); I32 (word 0); I32 (word 0); I32 (word 0); I64 (word 0)]`;;
theorem VA1_F26_OK
 `!p ap mdl hp tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32) h decls.
     ~(p = word 4294967295) /\ wasm_decl_vals va1_f26_mc = SOME decls
     ==> ensures wasm
          (\s. read wcode s = va1_f26_mc /\ read wpc s = word 5 /\ read wstatus s = WRunning /\
               read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\ read wlocals s = wcall_locals [] decls /\
               va1_pop p ap (read wmem s) /\ va1_mdl mdl (read wmem s) /\
               read (bytes32 (word 16404)) (read wmem s) = h /\
               va1_w32s 16408 26 hp (read wmem s) /\ va1_w32s 65536 262144 tbl (read wmem s) /\
               va1_w32s 1130496 2048 ra (read wmem s) /\ va1_w32s 1138688 2048 rb (read wmem s) /\
               va1_w32s 1146880 2048 jq (read wmem s) /\ va1_w32s 1155072 2048 jp (read wmem s) /\
               va1_bs (di,zq,zp,nd) (read wmem s))
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (va1_bad mdl tbl (ra,rb,jq,jp,zq,zp,nd))] /\
               va1_pop (word 4294967295) ap (read wmem s) /\
               read (bytes32 (word 16404)) (read wmem s) = word_add h (va1_bad mdl tbl (ra,rb,jq,jp,zq,zp,nd)) /\
               va1_w32s 16408 26 (\k. if k < 24 then word 0 else hp k) (read wmem s) /\
               va1_w32s 1130496 2048 (\k. word 0) (read wmem s) /\ va1_w32s 1138688 2048 (\k. word 0) (read wmem s) /\
               va1_w32s 1146880 2048 (\k. word 0) (read wmem s) /\ va1_w32s 1155072 2048 (\k. word 0) (read wmem s) /\
               va1_bs ((\k. word 0),(\k. word 0),(\k. word 0),word 0) (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocal 0; wlocal 1; wlocal 2; wlocal 3; wlocal 4; wlocal 5] ,,
           MAYCHANGE [wmem :> bytes(word 16396,116)] ,, MAYCHANGE [wmem :> bytes(word 1130496,835584)])`;;
theorem VA1_TICK_UNPUNCT
 `!fs gl p ap mdl N y hp tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32) h.
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
     fs 10 = (va1_f10_mc,0,0) /\ fs 26 = (va1_f26_mc,0,1) /\ fs 28 = (va1_f28_mc,0,0) /\
     ~(p = word 4294967295) /\ ~(p = word 0)
     ==> ensures (wasmc fs)
          (\s. read wcode s = va1_tick_backward_mc /\ read wpc s = word 3 /\ read wstatus s = WRunning /\
               read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\ read wglobals s = gl /\
               va1_st p p ap mdl N y hp tbl (ra,rb,jq,jp,di,zq,zp,nd) (read wmem s) /\
               read (bytes32 (word 16404)) (read wmem s) = h)
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 1)] /\
               va1_st (word_sub p (word 1)) (word 4294967295) ap mdl N (ve_fredkin_bwdn (\i. ve_vk mdl) 16 y)
                      (\k. if k < 24 then word 0 else hp k) (\k. word 0)
                      ((\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),word 0) (read wmem s) /\
               read (bytes32 (word 16404)) (read wmem s) = word_add h (va1_bad mdl tbl (ra,rb,jq,jp,zq,zp,nd)))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocal 0; wlocal 1] ,,
           MAYCHANGE [wmem :> bytes(word 16392,120)] ,, MAYCHANGE [wmem :> bytes(word 65536,1048576)] ,,
           MAYCHANGE [wmem :> bytes(word 1114112,851968)] ,, MAYCHANGE [wmem :> bytes(word 1966080,73728)])`;;
theorem VA1_HCALL_UNPUNCT
 `!fs gl p ap mdl N y hp tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32) h m.
     mdl 1 = word N /\ 1 <= N /\ N <= 640 /\
     fs 10 = (va1_f10_mc,0,0) /\ fs 26 = (va1_f26_mc,0,1) /\ fs 28 = (va1_f28_mc,0,0) /\
     ~(p = word 4294967295) /\ ~(p = word 0) /\
     va1_st p p ap mdl N y hp tbl (ra,rb,jq,jp,di,zq,zp,nd) m /\ read (bytes32 (word 16404)) m = h
     ==> va1_hcall (wasmc fs) va1_tick_backward_mc [] (word 1)
           (\gl' m'. gl' = gl /\
                     va1_st (word_sub p (word 1)) (word 4294967295) ap mdl N (ve_fredkin_bwdn (\i. ve_vk mdl) 16 y)
                            (\k. if k < 24 then word 0 else hp k) (\k. word 0)
                            ((\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),(\k. word 0),word 0) m' /\
                     read (bytes32 (word 16404)) m' = word_add h (va1_bad mdl tbl (ra,rb,jq,jp,zq,zp,nd)) /\
                     va1_unp_frame m m') gl m`;;
theorem VA1_BAD_PUNCT
 `!mdl tbl. va1_bad mdl tbl ((\k. word 251658), va1_rbinit tbl, (\k. word 0), (\k. word 0), (\k. word 0),
                            va1_zpseed mdl, word 0) = word 0`;;
theorem VA1_BAD_COUNT
 `!mdl tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32).
     val nd <= 16384
     ==> val (va1_bad mdl tbl (ra,rb,jq,jp,zq,zp,nd)) = val nd + nsum (0..2047) (\k. va1_mis mdl tbl (ra,rb,jq,jp,zq,zp) k)`;;
theorem VA1_BAD_ZERO_IFF
 `!mdl tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32).
     val nd <= 16384
     ==> (va1_bad mdl tbl (ra,rb,jq,jp,zq,zp,nd) = word 0 <=>
          nd = word 0 /\
          !k. k < 2048 ==> ra k = word 251658 /\ rb k = va1_rbinit tbl k /\ jq k = word 0 /\
                           jp k = word 0 /\ zq k = word 0 /\ zp k = va1_zpseed mdl k)`;;
theorem VA1_UNPUNCT_SAT
 `(?fs:num->byte list#num#num. fs 10 = (va1_f10_mc,0,0) /\ fs 26 = (va1_f26_mc,0,1) /\ fs 28 = (va1_f28_mc,0,0)) /\
  (!gl p ap mdl N y hp tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32) h.
     N <= 640
     ==> ?s. read wcode s = va1_tick_backward_mc /\ read wpc s = word 3 /\ read wstatus s = WRunning /\
             read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
             read wmemsize s = 4194304 /\ read wglobals s = gl /\
             va1_st p p ap mdl N y hp tbl (ra,rb,jq,jp,di,zq,zp,nd) (read wmem s) /\
             read (bytes32 (word 16404)) (read wmem s) = h)`;;
theorem VA1_F26_SAT
 `!p ap mdl hp tbl (ra:num->int32) (rb:num->int32) (jq:num->int32) (jp:num->int32) (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32) h.
     ?s. read wcode s = va1_f26_mc /\ read wpc s = word 5 /\ read wstatus s = WRunning /\
         read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
         read wmemsize s = 4194304 /\
         read wlocals s = wcall_locals [] [I32 (word 0); I32 (word 0); I32 (word 0); I32 (word 0); I32 (word 0); I64 (word 0)] /\
         va1_pop p ap (read wmem s) /\ va1_mdl mdl (read wmem s) /\
         read (bytes32 (word 16404)) (read wmem s) = h /\
         va1_w32s 16408 26 hp (read wmem s) /\ va1_w32s 65536 262144 tbl (read wmem s) /\
         va1_w32s 1130496 2048 ra (read wmem s) /\ va1_w32s 1138688 2048 rb (read wmem s) /\
         va1_w32s 1146880 2048 jq (read wmem s) /\ va1_w32s 1155072 2048 jp (read wmem s) /\
         va1_bs (di,zq,zp,nd) (read wmem s)`;;

(* ---- copied verbatim from chain_c1_final.spec (sha256 3b62701f) ---- *)
theorem VA1_TICKB_CALLEE
 `wasm_entry va1_tick_backward_mc = SOME 3 /\
  wasm_decl_vals va1_tick_backward_mc = SOME [I32 (word 0); I32 (word 0)]`;;
theorem VA1_BWDN_CLAUSES
 `(!f s. ve_fredkin_bwdn f 0 s = s) /\
   (!f n s. ve_fredkin_bwdn f (SUC n) s = ve_fredkin_bwdn f n (ve_fredkin_bwd (f n) s))`;;
theorem VA1_ISQ_CLAUSES
 `(!x. ve_isq 0 x = x) /\ (!k x. ve_isq (SUC k) x = ve_isq_step (ve_isq k x))`;;
theorem VA1_VK_RS_CLAUSES
 `(!X C i c. ve_vk_rs X C i 0 c = word 0) /\
   (!X C i k c. ve_vk_rs X C i (SUC k) c = word_add (ve_vk_ti X C i (i + 1 + k) c) (ve_vk_rs X C i k c))`;;
theorem VA1_VK_ACC_CLAUSES
 `(!X C n j c. ve_vk_acc X C n 0 j c = word 0) /\
   (!X C n i j c. ve_vk_acc X C n (SUC i) j c =
      if j = i then word_add (ve_vk_acc X C n i j c) (ve_vk_rs X C i (n - 1 - i) c)
      else if i < j then ve_vk_upd X C i j c (ve_vk_acc X C n i j c)
      else ve_vk_acc X C n i j c)`;;
theorem VA1_WDECL_VALS_CLAUSES
 `(!code pc. wdecl_vals 0 (code:byte list) pc = SOME ([]:wval list)) /\
  (!k code pc. wdecl_vals (SUC k) code pc =
     wobind (wuleb (wdrop pc code)) (\p.
     wobind (whd (wdrop (pc + SND p) code)) (\t.
     wobind (wdecl_vals k code (pc + SND p + 1)) (\r.
       SOME (APPEND (REPLICATE (FST p) (wzero_of (val (t:byte)))) r)))))`;;
definition va1_hcall
 `va1_hcall (step:wasmstate->wasmstate->bool) (code:byte list) (args:wval list) (r:int32)
            (Q:(num->wval)->(int64->byte)->bool) (gl:num->wval) (m:int64->byte) <=>
    ?e decls.
      wasm_entry code = SOME e /\ wasm_decl_vals code = SOME decls /\
      !s0. read wmemsize s0 = 4194304 /\ read wglobals s0 = gl /\ read wmem s0 = m
           ==> eventually step
                 (\s. read wstatus s = WDone /\ read wstack s = [I32 r] /\
                      read wmemsize s = 4194304 /\ Q (read wglobals s) (read wmem s))
                 (wcall_entry code (LENGTH args) 1 args e decls s0)`;;
definition ve_fredkin_bwd
 `ve_fredkin_bwd (f:(num->int32)->num->int32) (s:(num->int32)#(num->int32)) =
    ((\m. word_sub (SND s m) (f (FST s) m)),FST s)`;;
definition ve_vk_sx `ve_vk_sx (S:num->int32) i c = (word_sx (S (3 * i + c)):int64)`;;
definition ve_vk_ss
 `ve_vk_ss (S:num->int32) i =
    word_add (word_add (word_mul (ve_vk_sx S i 1) (ve_vk_sx S i 1))
                       (word_mul (ve_vk_sx S i 0) (ve_vk_sx S i 0)))
             (word_mul (ve_vk_sx S i 2) (ve_vk_sx S i 2))`;;
definition ve_vk_len
 `ve_vk_len (S:num->int32) i =
    let r = FST (SND (ve_isq 32 (ve_vk_ss S i, word 0, word 4611686018427387904))) in
    if ival r > &1 then r else (word 1:int64)`;;
definition ve_vk_xn
 `ve_vk_xn (S:num->int32) i c =
    (word_zx (iword (wtdiv (ival (word_shl (ve_vk_sx S i c) 30)) (ival (ve_vk_len S i))):int64)
     :int32)`;;
definition ve_vk_X `ve_vk_X (S:num->int32) i c = (word_sx (ve_vk_xn S i c):int64)`;;
definition ve_vk_C `ve_vk_C (mdl:num->int32) j = (word_sx (mdl (16 + j)):int64)`;;
definition ve_vk_rnd
 `ve_vk_rnd (a:int64) = (word_zx (word_ishr (word_add a (word 34359738368)) 36):int32)`;;
definition ve_vk
 `ve_vk (mdl:num->int32) (S:num->int32) m =
    ve_vk_rnd (ve_vk_acc (ve_vk_X S) (ve_vk_C mdl) (MIN (val (mdl 1)) 640)
                         (MIN (val (mdl 1)) 640) (m DIV 3) (m MOD 3))`;;
definition wasm_decl_vals
 `wasm_decl_vals (code:byte list) =
    wobind (wuleb code) (\p. wdecl_vals (FST p) code (SND p))`;;
definition wcall_locals
 `wcall_locals (args:wval list) (decls:wval list) (k:num) =
    if k < LENGTH args then EL (LENGTH args - 1 - k) args
    else if k - LENGTH args < LENGTH decls then EL (k - LENGTH args) decls
    else I32 (word 0)`;;
definition wcall_entry
 `wcall_entry (code:byte list) np nr (stk:wval list) e (decls:wval list)
              (s:wasmstate) =
    write wcode code
     (write wpc (word e)
       (write wstack []
         (write wlocals (wcall_locals (wtake np stk) decls)
           (write wlabels []
             (write warity nr
               (write wstatus WRunning s))))))`;;
definition wcall_return
 `wcall_return npc np (c1:wasmstate) (s:wasmstate) =
    if read wstatus c1 = WDone
    then write wpc (word npc)
          (write wstack (APPEND (read wstack c1) (wdrop np (read wstack s)))
            (write wmem (read wmem c1)
              (write wmemsize (read wmemsize c1)
                (write wglobals (read wglobals c1) s))))
    else write wstatus WTrapped
          (write wmem (read wmem c1)
            (write wmemsize (read wmemsize c1)
              (write wglobals (read wglobals c1) s)))`;;
definition wasm_call
 `wasm_call (fs:num->byte list#num#num) f npc (s:wasmstate) (s':wasmstate) <=>
    ?code np nr e decls c1.
      fs f = (code,np,nr) /\ np <= LENGTH (read wstack s) /\
      wasm_entry code = SOME e /\ wasm_decl_vals code = SOME decls /\
      RTC wasm (wcall_entry code np nr (read wstack s) e decls s) c1 /\
      ~(read wstatus c1 = WRunning) /\
      s' = wcall_return npc np c1 s`;;
definition wasmc
 `wasmc (fs:num->byte list#num#num) s s' <=>
    wasm s s' \/
    read wstatus s = WRunning /\
    ?f n. wasm_decode (read wcode s) (val (read wpc s)) = SOME (Wcall f,n) /\
          wasm_call fs f (val (read wpc s) + n) s s'`;;
definition va1_tick
 `va1_tick (t:int32) (m:int64->byte) <=> read (bytes32 (word 16392)) m = t`;;
definition va1_pop
 `va1_pop (pt:int32) (ap:int32) (m:int64->byte) <=>
    read (bytes32 (word 16396)) m = pt /\ read (bytes32 (word 16512)) m = ap`;;
definition va1_mdl
 `va1_mdl (mdl:num->int32) (m:int64->byte) <=>
    !k. k < 1024 ==> read (bytes32 (word (16640 + 4 * k))) m = mdl k`;;
definition va1_vab
 `va1_vab N (x:(num->int32)#(num->int32)) (m:int64->byte) <=>
    (!j. j < 3 * N ==> read (bytes32 (word (1114112 + 4 * j))) m = FST x j) /\
    (!j. j < 3 * N ==> read (bytes32 (word (1122304 + 4 * j))) m = SND x j)`;;
definition ve_isq_step
 `ve_isq_step (x:int64#int64#int64) =
    if val (FST x) < val (word_add (SND (SND x)) (FST (SND x)))
    then (FST x, word_ushr (FST (SND x)) 1, word_ushr (SND (SND x)) 2)
    else (word_sub (FST x) (word_add (SND (SND x)) (FST (SND x))),
          word_add (SND (SND x)) (word_ushr (FST (SND x)) 1),
          word_ushr (SND (SND x)) 2)`;;
definition ve_vk_w
 `ve_vk_w (X:num->num->int64) i j =
    let den = word_sub (word 1076426179)
                (word_ishr (word_add (word_add (word_mul (X j 1) (X i 1))
                                               (word_mul (X j 0) (X i 0)))
                                     (word_mul (X j 2) (X i 2))) 30) in
    word_udiv (word 18014398509481984) (if ival den > &2684355 then den else word 2684355)`;;
definition ve_vk_v
 `ve_vk_v (X:num->num->int64) i j c =
    if c = 0 then word_sub (word_mul (X j 1) (X i 2)) (word_mul (X j 2) (X i 1))
    else if c = 1 then word_sub (word_mul (X j 2) (X i 0)) (word_mul (X j 0) (X i 2))
    else word_sub (word_mul (X j 0) (X i 1)) (word_mul (X j 1) (X i 0))`;;
definition ve_vk_tj
 `ve_vk_tj (X:num->num->int64) (C:num->int64) i j c =
    word_ishr (word_mul (word_ishr (word_mul (ve_vk_w X i j) (C i)) 20)
                        (word_ishr (word_sub (word 0) (ve_vk_v X i j c)) 36)) 12`;;
definition ve_vk_ti
 `ve_vk_ti (X:num->num->int64) (C:num->int64) i j c =
    word_ishr (word_mul (word_ishr (word_mul (ve_vk_w X i j) (C j)) 20)
                        (word_ishr (ve_vk_v X i j c) 36)) 12`;;
definition ve_vk_upd
 `ve_vk_upd (X:num->num->int64) (C:num->int64) i j c (a:int64) =
    if c = 2 then word_add a (ve_vk_tj X C i j c) else word_add (ve_vk_tj X C i j c) a`;;
definition wzero_of
 `wzero_of (t:num) =
    if t = 0x7E then I64 (word 0) else if t = 0x7D then F32 (word 0)
    else if t = 0x7C then F64 (word 0) else I32 (word 0)`;;
definition va1_tick_backward_mc
 `va1_tick_backward_mc:byte list = [word 0x01; word 0x02; word 0x7f; word 0x41; word 0x00; word 0x21; word 0x00; word 0x02; word 0x40; word 0x41; word 0x00; word 0x28; word 0x02; word 0x88; word 0x80; word 0x01; word 0x22; word 0x01; word 0x45; word 0x0d; word 0x00; word 0x02; word 0x40; word 0x41; word 0x00; word 0x28; word 0x02; word 0x8c; word 0x80; word 0x01; word 0x22; word 0x00; word 0x41; word 0x7f; word 0x46; word 0x0d; word 0x00; word 0x20; word 0x01; word 0x20; word 0x00; word 0x47; word 0x0d; word 0x00; word 0x10; word 0x9a; word 0x80; word 0x80; word 0x80; word 0x00; word 0x1a; word 0x41; word 0x80; word 0x80; word 0x40; word 0x21; word 0x00; word 0x03; word 0x40; word 0x20; word 0x00; word 0x41; word 0x98; word 0x80; word 0xc4; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x00; word 0x41; word 0x90; word 0x80; word 0xc4; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x00; word 0x41; word 0x88; word 0x80; word 0xc4; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x00; word 0x41; word 0x80; word 0x80; word 0xc4; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x00; word 0x41; word 0x20; word 0x6a; word 0x22; word 0x00; word 0x0d; word 0x00; word 0x0b; word 0x41; word 0x00; word 0x28; word 0x02; word 0x8c; word 0x80; word 0x01; word 0x21; word 0x00; word 0x0b; word 0x10; word 0x9c; word 0x80; word 0x80; word 0x80; word 0x00; word 0x10; word 0x8a; word 0x80; word 0x80; word 0x80; word 0x00; word 0x02; word 0x40; word 0x20; word 0x01; word 0x20; word 0x00; word 0x4b; word 0x0d; word 0x00; word 0x10; word 0x8a; word 0x80; word 0x80; word 0x80; word 0x00; word 0x10; word 0x8a; word 0x80; word 0x80; word 0x80; word 0x00; word 0x10; word 0x8a; word 0x80; word 0x80; word 0x80; word 0x00; word 0x10; word 0x8a; word 0x80; word 0x80; word 0x80; word 0x00; word 0x10; word 0x8a; word 0x80; word 0x80; word 0x80; word 0x00; word 0x10; word 0x8a; word 0x80; word 0x80; word 0x80; word 0x00; word 0x10; word 0x8a; word 0x80; word 0x80; word 0x80; word 0x00; word 0x10; word 0x8a; word 0x80; word 0x80; word 0x80; word 0x00; word 0x10; word 0x8a; word 0x80; word 0x80; word 0x80; word 0x00; word 0x10; word 0x8a; word 0x80; word 0x80; word 0x80; word 0x00; word 0x10; word 0x8a; word 0x80; word 0x80; word 0x80; word 0x00; word 0x10; word 0x8a; word 0x80; word 0x80; word 0x80; word 0x00; word 0x10; word 0x8a; word 0x80; word 0x80; word 0x80; word 0x00; word 0x10; word 0x8a; word 0x80; word 0x80; word 0x80; word 0x00; word 0x10; word 0x8a; word 0x80; word 0x80; word 0x80; word 0x00; word 0x41; word 0x01; word 0x0f; word 0x0b; word 0x10; word 0x8e; word 0x80; word 0x80; word 0x80; word 0x00; word 0x1a; word 0x10; word 0x8c; word 0x80; word 0x80; word 0x80; word 0x00; word 0x10; word 0x94; word 0x80; word 0x80; word 0x80; word 0x00; word 0x41; word 0x03; word 0x10; word 0x92; word 0x80; word 0x80; word 0x80; word 0x00; word 0x10; word 0x94; word 0x80; word 0x80; word 0x80; word 0x00; word 0x41; word 0x02; word 0x10; word 0x92; word 0x80; word 0x80; word 0x80; word 0x00; word 0x10; word 0x94; word 0x80; word 0x80; word 0x80; word 0x00; word 0x41; word 0x01; word 0x21; word 0x00; word 0x41; word 0x01; word 0x10; word 0x92; word 0x80; word 0x80; word 0x80; word 0x00; word 0x10; word 0x94; word 0x80; word 0x80; word 0x80; word 0x00; word 0x41; word 0x00; word 0x10; word 0x92; word 0x80; word 0x80; word 0x80; word 0x00; word 0x10; word 0x98; word 0x80; word 0x80; word 0x80; word 0x00; word 0x10; word 0x96; word 0x80; word 0x80; word 0x80; word 0x00; word 0x10; word 0x90; word 0x80; word 0x80; word 0x80; word 0x00; word 0x0b; word 0x20; word 0x00; word 0x0b]`;;
definition va1_f10_mc
 `va1_f10_mc:byte list = [word 0x0a; word 0x05; word 0x7f; word 0x01; word 0x7e; word 0x01; word 0x7f; word 0x01; word 0x7e; word 0x01; word 0x7f; word 0x05; word 0x7e; word 0x09; word 0x7f; word 0x03; word 0x7e; word 0x01; word 0x7f; word 0x03; word 0x7e; word 0x41; word 0x00; word 0x21; word 0x00; word 0x02; word 0x40; word 0x41; word 0x00; word 0x28; word 0x02; word 0x84; word 0x82; word 0x01; word 0x22; word 0x01; word 0x45; word 0x0d; word 0x00; word 0x20; word 0x01; word 0x41; word 0x80; word 0x05; word 0x20; word 0x01; word 0x41; word 0x80; word 0x05; word 0x49; word 0x1b; word 0x21; word 0x02; word 0x03; word 0x40; word 0x20; word 0x00; word 0x41; word 0x03; word 0x6c; word 0x22; word 0x03; word 0x41; word 0x01; word 0x6a; word 0x41; word 0x02; word 0x74; word 0x22; word 0x04; word 0x34; word 0x02; word 0x80; word 0x80; word 0x44; word 0x22; word 0x05; word 0x20; word 0x05; word 0x7e; word 0x20; word 0x03; word 0x41; word 0x02; word 0x74; word 0x22; word 0x06; word 0x34; word 0x02; word 0x80; word 0x80; word 0x44; word 0x22; word 0x07; word 0x20; word 0x07; word 0x7e; word 0x7c; word 0x20; word 0x03; word 0x41; word 0x02; word 0x6a; word 0x41; word 0x02; word 0x74; word 0x22; word 0x08; word 0x34; word 0x02; word 0x80; word 0x80; word 0x44; word 0x22; word 0x09; word 0x20; word 0x09; word 0x7e; word 0x7c; word 0x21; word 0x0a; word 0x42; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0xc0; word 0x00; word 0x21; word 0x0b; word 0x41; word 0x20; word 0x21; word 0x03; word 0x42; word 0x00; word 0x21; word 0x0c; word 0x03; word 0x40; word 0x42; word 0x00; word 0x20; word 0x0b; word 0x20; word 0x0a; word 0x20; word 0x0b; word 0x20; word 0x0c; word 0x7c; word 0x22; word 0x0d; word 0x54; word 0x22; word 0x0e; word 0x1b; word 0x20; word 0x0c; word 0x42; word 0x01; word 0x88; word 0x7c; word 0x21; word 0x0c; word 0x20; word 0x0a; word 0x42; word 0x00; word 0x20; word 0x0d; word 0x20; word 0x0e; word 0x1b; word 0x7d; word 0x21; word 0x0a; word 0x20; word 0x0b; word 0x42; word 0x02; word 0x88; word 0x21; word 0x0b; word 0x20; word 0x03; word 0x41; word 0x7f; word 0x6a; word 0x22; word 0x03; word 0x0d; word 0x00; word 0x0b; word 0x20; word 0x04; word 0x20; word 0x05; word 0x42; word 0x1e; word 0x86; word 0x20; word 0x0c; word 0x42; word 0x01; word 0x20; word 0x0c; word 0x42; word 0x01; word 0x55; word 0x1b; word 0x22; word 0x0b; word 0x7f; word 0x3e; word 0x02; word 0x80; word 0x80; word 0x78; word 0x20; word 0x06; word 0x20; word 0x07; word 0x42; word 0x1e; word 0x86; word 0x20; word 0x0b; word 0x7f; word 0x3e; word 0x02; word 0x80; word 0x80; word 0x78; word 0x20; word 0x08; word 0x20; word 0x09; word 0x42; word 0x1e; word 0x86; word 0x20; word 0x0b; word 0x7f; word 0x3e; word 0x02; word 0x80; word 0x80; word 0x78; word 0x20; word 0x00; word 0x41; word 0x01; word 0x6a; word 0x22; word 0x00; word 0x20; word 0x02; word 0x47; word 0x0d; word 0x00; word 0x0b; word 0x20; word 0x02; word 0x41; word 0x03; word 0x6c; word 0x22; word 0x0f; word 0x41; word 0x07; word 0x71; word 0x21; word 0x0e; word 0x41; word 0x00; word 0x21; word 0x04; word 0x02; word 0x40; word 0x02; word 0x40; word 0x20; word 0x01; word 0x41; word 0x03; word 0x49; word 0x0d; word 0x00; word 0x20; word 0x0f; word 0x41; word 0x78; word 0x71; word 0x21; word 0x04; word 0x20; word 0x0f; word 0x41; word 0x03; word 0x74; word 0x41; word 0x40; word 0x71; word 0x21; word 0x00; word 0x41; word 0x00; word 0x21; word 0x03; word 0x03; word 0x40; word 0x20; word 0x03; word 0x41; word 0xb8; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0xb0; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0xa8; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0xa0; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0x98; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0x90; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0x88; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0x80; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x00; word 0x20; word 0x03; word 0x41; word 0xc0; word 0x00; word 0x6a; word 0x22; word 0x03; word 0x47; word 0x0d; word 0x00; word 0x0b; word 0x20; word 0x0e; word 0x45; word 0x0d; word 0x01; word 0x0b; word 0x20; word 0x04; word 0x41; word 0x03; word 0x74; word 0x41; word 0x80; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x21; word 0x03; word 0x03; word 0x40; word 0x20; word 0x03; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0x08; word 0x6a; word 0x21; word 0x03; word 0x20; word 0x0e; word 0x41; word 0x7f; word 0x6a; word 0x22; word 0x0e; word 0x0d; word 0x00; word 0x0b; word 0x0b; word 0x20; word 0x02; word 0x41; word 0x7f; word 0x6a; word 0x21; word 0x10; word 0x41; word 0x00; word 0x21; word 0x03; word 0x41; word 0x80; word 0x80; word 0xf9; word 0x00; word 0x21; word 0x11; word 0x41; word 0x94; word 0x80; word 0xf8; word 0x00; word 0x21; word 0x12; word 0x41; word 0xc4; word 0x82; word 0x01; word 0x21; word 0x13; word 0x03; word 0x40; word 0x20; word 0x03; word 0x41; word 0x03; word 0x6c; word 0x22; word 0x14; word 0x41; word 0x02; word 0x6a; word 0x21; word 0x15; word 0x20; word 0x14; word 0x41; word 0x01; word 0x6a; word 0x21; word 0x16; word 0x42; word 0x00; word 0x21; word 0x17; word 0x42; word 0x00; word 0x21; word 0x18; word 0x42; word 0x00; word 0x21; word 0x19; word 0x02; word 0x40; word 0x20; word 0x03; word 0x41; word 0x01; word 0x6a; word 0x22; word 0x1a; word 0x20; word 0x02; word 0x4f; word 0x0d; word 0x00; word 0x20; word 0x03; word 0x41; word 0x02; word 0x74; word 0x41; word 0xc0; word 0x82; word 0x01; word 0x6a; word 0x34; word 0x02; word 0x00; word 0x21; word 0x1b; word 0x20; word 0x14; word 0x41; word 0x02; word 0x74; word 0x34; word 0x02; word 0x80; word 0x80; word 0x78; word 0x21; word 0x0b; word 0x20; word 0x15; word 0x41; word 0x02; word 0x74; word 0x34; word 0x02; word 0x80; word 0x80; word 0x78; word 0x21; word 0x0c; word 0x20; word 0x16; word 0x41; word 0x02; word 0x74; word 0x34; word 0x02; word 0x80; word 0x80; word 0x78; word 0x21; word 0x0a; word 0x42; word 0x00; word 0x21; word 0x19; word 0x20; word 0x10; word 0x21; word 0x06; word 0x20; word 0x13; word 0x21; word 0x00; word 0x20; word 0x12; word 0x21; word 0x03; word 0x20; word 0x11; word 0x21; word 0x0e; word 0x42; word 0x00; word 0x21; word 0x18; word 0x42; word 0x00; word 0x21; word 0x17; word 0x03; word 0x40; word 0x20; word 0x0e; word 0x41; word 0x18; word 0x6a; word 0x22; word 0x04; word 0x42; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x20; word 0x42; word 0xc3; word 0xeb; word 0xa3; word 0x81; word 0x04; word 0x20; word 0x03; word 0x41; word 0x7c; word 0x6a; word 0x34; word 0x02; word 0x00; word 0x22; word 0x0d; word 0x20; word 0x0a; word 0x7e; word 0x20; word 0x03; word 0x41; word 0x78; word 0x6a; word 0x34; word 0x02; word 0x00; word 0x22; word 0x05; word 0x20; word 0x0b; word 0x7e; word 0x7c; word 0x20; word 0x03; word 0x34; word 0x02; word 0x00; word 0x22; word 0x07; word 0x20; word 0x0c; word 0x7e; word 0x7c; word 0x42; word 0x1e; word 0x87; word 0x7d; word 0x22; word 0x09; word 0x42; word 0xc3; word 0xeb; word 0xa3; word 0x01; word 0x20; word 0x09; word 0x42; word 0xc3; word 0xeb; word 0xa3; word 0x01; word 0x55; word 0x1b; word 0x80; word 0x22; word 0x1c; word 0x20; word 0x1b; word 0x7e; word 0x42; word 0x14; word 0x87; word 0x22; word 0x09; word 0x42; word 0x00; word 0x20; word 0x0d; word 0x20; word 0x0c; word 0x7e; word 0x20; word 0x07; word 0x20; word 0x0a; word 0x7e; word 0x7d; word 0x22; word 0x1d; word 0x7d; word 0x42; word 0x24; word 0x87; word 0x7e; word 0x42; word 0x0c; word 0x87; word 0x20; word 0x04; word 0x29; word 0x03; word 0x00; word 0x7c; word 0x37; word 0x03; word 0x00; word 0x20; word 0x0e; word 0x41; word 0x20; word 0x6a; word 0x22; word 0x08; word 0x20; word 0x09; word 0x42; word 0x00; word 0x20; word 0x07; word 0x20; word 0x0b; word 0x7e; word 0x20; word 0x05; word 0x20; word 0x0c; word 0x7e; word 0x7d; word 0x22; word 0x07; word 0x7d; word 0x42; word 0x24; word 0x87; word 0x7e; word 0x42; word 0x0c; word 0x87; word 0x20; word 0x08; word 0x29; word 0x03; word 0x00; word 0x7c; word 0x37; word 0x03; word 0x00; word 0x20; word 0x0e; word 0x41; word 0x28; word 0x6a; word 0x22; word 0x0e; word 0x20; word 0x0e; word 0x29; word 0x03; word 0x00; word 0x20; word 0x09; word 0x42; word 0x00; word 0x20; word 0x05; word 0x20; word 0x0a; word 0x7e; word 0x20; word 0x0d; word 0x20; word 0x0b; word 0x7e; word 0x7d; word 0x22; word 0x05; word 0x7d; word 0x42; word 0x24; word 0x87; word 0x7e; word 0x42; word 0x0c; word 0x87; word 0x7c; word 0x37; word 0x03; word 0x00; word 0x20; word 0x1c; word 0x20; word 0x00; word 0x34; word 0x02; word 0x00; word 0x7e; word 0x42; word 0x14; word 0x87; word 0x22; word 0x0d; word 0x20; word 0x05; word 0x42; word 0x24; word 0x87; word 0x7e; word 0x42; word 0x0c; word 0x87; word 0x20; word 0x17; word 0x7c; word 0x21; word 0x17; word 0x20; word 0x0d; word 0x20; word 0x07; word 0x42; word 0x24; word 0x87; word 0x7e; word 0x42; word 0x0c; word 0x87; word 0x20; word 0x18; word 0x7c; word 0x21; word 0x18; word 0x20; word 0x0d; word 0x20; word 0x1d; word 0x42; word 0x24; word 0x87; word 0x7e; word 0x42; word 0x0c; word 0x87; word 0x20; word 0x19; word 0x7c; word 0x21; word 0x19; word 0x20; word 0x00; word 0x41; word 0x04; word 0x6a; word 0x21; word 0x00; word 0x20; word 0x03; word 0x41; word 0x0c; word 0x6a; word 0x21; word 0x03; word 0x20; word 0x04; word 0x21; word 0x0e; word 0x20; word 0x06; word 0x41; word 0x7f; word 0x6a; word 0x22; word 0x06; word 0x0d; word 0x00; word 0x0b; word 0x0b; word 0x20; word 0x14; word 0x41; word 0x03; word 0x74; word 0x22; word 0x03; word 0x20; word 0x03; word 0x29; word 0x03; word 0x80; word 0x80; word 0x79; word 0x20; word 0x19; word 0x7c; word 0x37; word 0x03; word 0x80; word 0x80; word 0x79; word 0x20; word 0x16; word 0x41; word 0x03; word 0x74; word 0x22; word 0x03; word 0x20; word 0x03; word 0x29; word 0x03; word 0x80; word 0x80; word 0x79; word 0x20; word 0x18; word 0x7c; word 0x37; word 0x03; word 0x80; word 0x80; word 0x79; word 0x20; word 0x15; word 0x41; word 0x03; word 0x74; word 0x22; word 0x03; word 0x20; word 0x03; word 0x29; word 0x03; word 0x80; word 0x80; word 0x79; word 0x20; word 0x17; word 0x7c; word 0x37; word 0x03; word 0x80; word 0x80; word 0x79; word 0x20; word 0x10; word 0x41; word 0x7f; word 0x6a; word 0x21; word 0x10; word 0x20; word 0x13; word 0x41; word 0x04; word 0x6a; word 0x21; word 0x13; word 0x20; word 0x12; word 0x41; word 0x0c; word 0x6a; word 0x21; word 0x12; word 0x20; word 0x11; word 0x41; word 0x18; word 0x6a; word 0x21; word 0x11; word 0x20; word 0x1a; word 0x21; word 0x03; word 0x20; word 0x1a; word 0x20; word 0x02; word 0x47; word 0x0d; word 0x00; word 0x0b; word 0x20; word 0x0f; word 0x41; word 0x03; word 0x71; word 0x21; word 0x00; word 0x41; word 0x00; word 0x21; word 0x06; word 0x02; word 0x40; word 0x20; word 0x01; word 0x41; word 0x01; word 0x46; word 0x0d; word 0x00; word 0x20; word 0x0f; word 0x41; word 0x7c; word 0x71; word 0x21; word 0x06; word 0x20; word 0x0f; word 0x41; word 0x03; word 0x74; word 0x41; word 0x60; word 0x71; word 0x21; word 0x04; word 0x41; word 0x00; word 0x21; word 0x03; word 0x41; word 0x80; word 0xc0; word 0xf8; word 0x00; word 0x21; word 0x0e; word 0x03; word 0x40; word 0x20; word 0x0e; word 0x20; word 0x03; word 0x41; word 0x80; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x29; word 0x03; word 0x00; word 0x42; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x01; word 0x7c; word 0x42; word 0x24; word 0x87; word 0x3e; word 0x02; word 0x00; word 0x20; word 0x0e; word 0x41; word 0x04; word 0x6a; word 0x20; word 0x03; word 0x41; word 0x88; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x29; word 0x03; word 0x00; word 0x42; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x01; word 0x7c; word 0x42; word 0x24; word 0x87; word 0x3e; word 0x02; word 0x00; word 0x20; word 0x0e; word 0x41; word 0x08; word 0x6a; word 0x20; word 0x03; word 0x41; word 0x90; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x29; word 0x03; word 0x00; word 0x42; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x01; word 0x7c; word 0x42; word 0x24; word 0x87; word 0x3e; word 0x02; word 0x00; word 0x20; word 0x0e; word 0x41; word 0x0c; word 0x6a; word 0x20; word 0x03; word 0x41; word 0x98; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x29; word 0x03; word 0x00; word 0x42; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x01; word 0x7c; word 0x42; word 0x24; word 0x87; word 0x3e; word 0x02; word 0x00; word 0x20; word 0x0e; word 0x41; word 0x10; word 0x6a; word 0x21; word 0x0e; word 0x20; word 0x04; word 0x20; word 0x03; word 0x41; word 0x20; word 0x6a; word 0x22; word 0x03; word 0x47; word 0x0d; word 0x00; word 0x0b; word 0x20; word 0x00; word 0x45; word 0x0d; word 0x01; word 0x0b; word 0x20; word 0x06; word 0x41; word 0x03; word 0x74; word 0x41; word 0x80; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x21; word 0x03; word 0x20; word 0x06; word 0x41; word 0x02; word 0x74; word 0x41; word 0x80; word 0xc0; word 0xf8; word 0x00; word 0x6a; word 0x21; word 0x0e; word 0x03; word 0x40; word 0x20; word 0x0e; word 0x20; word 0x03; word 0x29; word 0x03; word 0x00; word 0x42; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x01; word 0x7c; word 0x42; word 0x24; word 0x87; word 0x3e; word 0x02; word 0x00; word 0x20; word 0x03; word 0x41; word 0x08; word 0x6a; word 0x21; word 0x03; word 0x20; word 0x0e; word 0x41; word 0x04; word 0x6a; word 0x21; word 0x0e; word 0x20; word 0x00; word 0x41; word 0x7f; word 0x6a; word 0x22; word 0x00; word 0x0d; word 0x00; word 0x0b; word 0x0b; word 0x02; word 0x40; word 0x41; word 0x00; word 0x28; word 0x02; word 0x84; word 0x82; word 0x01; word 0x22; word 0x03; word 0x45; word 0x0d; word 0x00; word 0x20; word 0x03; word 0x41; word 0x80; word 0x05; word 0x20; word 0x03; word 0x41; word 0x80; word 0x05; word 0x49; word 0x1b; word 0x41; word 0x03; word 0x6c; word 0x22; word 0x03; word 0x41; word 0xfe; word 0x1f; word 0x71; word 0x21; word 0x04; word 0x20; word 0x03; word 0x41; word 0x01; word 0x71; word 0x21; word 0x02; word 0x41; word 0x80; word 0x80; word 0xc4; word 0x00; word 0x21; word 0x03; word 0x41; word 0x80; word 0xc0; word 0xc4; word 0x00; word 0x21; word 0x0e; word 0x41; word 0x80; word 0xc0; word 0xf8; word 0x00; word 0x21; word 0x00; word 0x03; word 0x40; word 0x20; word 0x03; word 0x28; word 0x02; word 0x00; word 0x21; word 0x06; word 0x20; word 0x03; word 0x20; word 0x0e; word 0x28; word 0x02; word 0x00; word 0x20; word 0x00; word 0x28; word 0x02; word 0x00; word 0x6b; word 0x36; word 0x02; word 0x00; word 0x20; word 0x0e; word 0x20; word 0x06; word 0x36; word 0x02; word 0x00; word 0x20; word 0x03; word 0x41; word 0x04; word 0x6a; word 0x22; word 0x06; word 0x28; word 0x02; word 0x00; word 0x21; word 0x08; word 0x20; word 0x06; word 0x20; word 0x0e; word 0x41; word 0x04; word 0x6a; word 0x22; word 0x14; word 0x28; word 0x02; word 0x00; word 0x20; word 0x00; word 0x41; word 0x04; word 0x6a; word 0x28; word 0x02; word 0x00; word 0x6b; word 0x36; word 0x02; word 0x00; word 0x20; word 0x14; word 0x20; word 0x08; word 0x36; word 0x02; word 0x00; word 0x20; word 0x00; word 0x41; word 0x08; word 0x6a; word 0x21; word 0x00; word 0x20; word 0x0e; word 0x41; word 0x08; word 0x6a; word 0x21; word 0x0e; word 0x20; word 0x03; word 0x41; word 0x08; word 0x6a; word 0x21; word 0x03; word 0x20; word 0x04; word 0x41; word 0x7e; word 0x6a; word 0x22; word 0x04; word 0x0d; word 0x00; word 0x0b; word 0x20; word 0x02; word 0x45; word 0x0d; word 0x00; word 0x20; word 0x03; word 0x28; word 0x02; word 0x00; word 0x21; word 0x04; word 0x20; word 0x03; word 0x20; word 0x0e; word 0x28; word 0x02; word 0x00; word 0x20; word 0x00; word 0x28; word 0x02; word 0x00; word 0x6b; word 0x36; word 0x02; word 0x00; word 0x20; word 0x0e; word 0x20; word 0x04; word 0x36; word 0x02; word 0x00; word 0x0b; word 0x0b]`;;
definition va1_f28_mc
 `va1_f28_mc:byte list = [word 0x00; word 0x41; word 0x00; word 0x41; word 0x00; word 0x28; word 0x02; word 0x88; word 0x80; word 0x01; word 0x41; word 0x7f; word 0x6a; word 0x36; word 0x02; word 0x88; word 0x80; word 0x01; word 0x0b]`;;
(* ---- copied verbatim from chain_c2_final.spec (sha256 c7a0c0a8) ---- *)
definition va1_w32s
 `va1_w32s (base:num) (n:num) (f:num->int32) (m:int64->byte) <=>
    !k. k < n ==> read (bytes32 (word (base + 4 * k))) m = f k`;;
definition va1_bs
 `va1_bs (bs:(num->int32)#(num->int32)#(num->int32)#(int32)) (m:int64->byte) <=>
    va1_w32s 1179648 196608 (FST bs) m /\ va1_w32s 1163264 2048 (FST (SND bs)) m /\
    va1_w32s 1171456 2048 (FST (SND (SND bs))) m /\ read (bytes32 (word 16400)) m = (SND (SND (SND bs)))`;;
definition va1_st
 `va1_st (t:int32) (p:int32) (ap:int32) (mdl:num->int32) (N:num)
        (x:(num->int32)#(num->int32)) (hp:num->int32) (tbl:num->int32)
        (ps:(num->int32)#(num->int32)#(num->int32)#(num->int32)#((num->int32)#(num->int32)#(num->int32)#int32)) (m:int64->byte) <=>
    va1_tick t m /\ va1_pop p ap m /\ va1_mdl mdl m /\ va1_vab N x m /\
    va1_w32s 16408 26 hp m /\ va1_w32s 65536 262144 tbl m /\
    va1_w32s 1130496 2048 (FST ps) m /\ va1_w32s 1138688 2048 (FST (SND ps)) m /\
    va1_w32s 1146880 2048 (FST (SND (SND ps))) m /\ va1_w32s 1155072 2048 (FST (SND (SND (SND ps)))) m /\ va1_bs (SND (SND (SND (SND ps)))) m`;;
