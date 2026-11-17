(* Spec: Vortex Echo v1, the vortex Fredkin export pair ve_vort_apply / ve_vort_unapply on the exact bytes of vortex/core/ve_core.wasm (sha256 72fe0ba2). (1) The Fredkin loop of each body, from pc 1305 to the end, unconditionally: apply VA' = VB, VB' = VD + VA; unapply VA' = VB - VD, VB' = VA, for m < 3N (N = 1..640 from model word 1), writing only those two regions and its locals. (2) The whole exports under the NAMED premise ve_vk_ok VK (the field phase, pc 21..1305 of both bodies (pc 21 = wasm_entry, the first instruction after the local declarations; corrected from pc 3 as merged in PR #72), leaves VD = VK(model, source) with the same VK for both, source VB resp. VA, writing only locals and scratch; discharged in ve_vk.spec by VE_VK_OK): apply is the Fredkin step (VA, VB) -> (VB, VA + VK(mdl, VB)) of ve_fredkin_fwd, unapply is ve_fredkin_bwd, and unapply on the state apply leaves restores VA and VB (VE_VORT_INVERSE, an instance of FREDKIN_STEP_INVERSE); VE_VORT_STEPS_INVERSE: n substeps with this VK (FREDKIN_STEPS_INVERSE). *)
theorem VE_VORT_APPLY_LOOP_CORRECT
 `!N (va:num->int32) (vb:num->int32) (vd:num->int32).
     1 <= N /\ N <= 640
     ==> ensures wasm
          (\s. read wcode s = ve_vort_apply_mc /\ read wpc s = word 1305 /\
               read wstatus s = WRunning /\ read wstack s = [] /\
               read wlabels s = [] /\ read warity s = 0 /\
               read wmemsize s = 2097152 /\
               read (wmem :> bytes32 (word 16644)) s = word N /\
               (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1114112 + 4 * m))) s = va m) /\
               (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1122304 + 4 * m))) s = vb m) /\
               (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1974272 + 4 * m))) s = vd m))
          (\s. read wstatus s = WDone /\ read wstack s = [] /\
               (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1114112 + 4 * m))) s = vb m) /\
               (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1122304 + 4 * m))) s = word_add (vd m) (va m)))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
           MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocal 0; wlocal 2; wlocal 3; wlocal 4; wlocal 6; wlocal 8; wlocal 14; wlocal 20] ,,
           MAYCHANGE [wmem :> bytes(word 1114112,16384)])`;;
theorem VE_VORT_UNAPPLY_LOOP_CORRECT
 `!N (va:num->int32) (vb:num->int32) (vd:num->int32).
     1 <= N /\ N <= 640
     ==> ensures wasm
          (\s. read wcode s = ve_vort_unapply_mc /\ read wpc s = word 1305 /\
               read wstatus s = WRunning /\ read wstack s = [] /\
               read wlabels s = [] /\ read warity s = 0 /\
               read wmemsize s = 2097152 /\
               read (wmem :> bytes32 (word 16644)) s = word N /\
               (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1114112 + 4 * m))) s = va m) /\
               (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1122304 + 4 * m))) s = vb m) /\
               (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1974272 + 4 * m))) s = vd m))
          (\s. read wstatus s = WDone /\ read wstack s = [] /\
               (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1114112 + 4 * m))) s = word_sub (vb m) (vd m)) /\
               (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1122304 + 4 * m))) s = va m))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
           MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocal 0; wlocal 2; wlocal 3; wlocal 4; wlocal 6; wlocal 8; wlocal 14; wlocal 20] ,,
           MAYCHANGE [wmem :> bytes(word 1114112,16384)])`;;
theorem VE_VORT_APPLY_CORRECT
 `!VK. ve_vk_ok VK
     ==> !N (mdl:num->int32) (va:num->int32) (vb:num->int32).
          mdl 1 = word N /\ 1 <= N /\ N <= 640
          ==> ensures wasm
               (\s. read wcode s = ve_vort_apply_mc /\ read wpc s = word 21 /\
                    read wstatus s = WRunning /\ read wstack s = [] /\
                    read wlabels s = [] /\ read warity s = 0 /\
                    read wmemsize s = 2097152 /\
                    (!k. k < 1024 ==> read (wmem :> bytes32 (word (16640 + 4 * k))) s = mdl k) /\
                    (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1114112 + 4 * m))) s = va m) /\
                    (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1122304 + 4 * m))) s = vb m))
               (\s. read wstatus s = WDone /\ read wstack s = [] /\
                    (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1114112 + 4 * m))) s = vb m) /\
                    (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1122304 + 4 * m))) s = word_add (va m) (VK mdl vb m)))
               (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
                MAYCHANGE [wstatus] ,,
                MAYCHANGE [wlocal 0; wlocal 1; wlocal 2; wlocal 3; wlocal 4; wlocal 5; wlocal 6; wlocal 7; wlocal 8; wlocal 9; wlocal 10; wlocal 11; wlocal 12; wlocal 13; wlocal 14; wlocal 15; wlocal 16; wlocal 17; wlocal 18; wlocal 19; wlocal 20; wlocal 21; wlocal 22; wlocal 23; wlocal 24; wlocal 25; wlocal 26; wlocal 27; wlocal 28; wlocal 29] ,,
                MAYCHANGE [wmem :> bytes(word 1114112,16384)] ,,
                MAYCHANGE [wmem :> bytes(word 1966080,73728)])`;;
theorem VE_VORT_UNAPPLY_CORRECT
 `!VK. ve_vk_ok VK
     ==> !N (mdl:num->int32) (va:num->int32) (vb:num->int32).
          mdl 1 = word N /\ 1 <= N /\ N <= 640
          ==> ensures wasm
               (\s. read wcode s = ve_vort_unapply_mc /\ read wpc s = word 21 /\
                    read wstatus s = WRunning /\ read wstack s = [] /\
                    read wlabels s = [] /\ read warity s = 0 /\
                    read wmemsize s = 2097152 /\
                    (!k. k < 1024 ==> read (wmem :> bytes32 (word (16640 + 4 * k))) s = mdl k) /\
                    (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1114112 + 4 * m))) s = va m) /\
                    (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1122304 + 4 * m))) s = vb m))
               (\s. read wstatus s = WDone /\ read wstack s = [] /\
                    (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1114112 + 4 * m))) s = word_sub (vb m) (VK mdl va m)) /\
                    (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1122304 + 4 * m))) s = va m))
               (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
                MAYCHANGE [wstatus] ,,
                MAYCHANGE [wlocal 0; wlocal 1; wlocal 2; wlocal 3; wlocal 4; wlocal 5; wlocal 6; wlocal 7; wlocal 8; wlocal 9; wlocal 10; wlocal 11; wlocal 12; wlocal 13; wlocal 14; wlocal 15; wlocal 16; wlocal 17; wlocal 18; wlocal 19; wlocal 20; wlocal 21; wlocal 22; wlocal 23; wlocal 24; wlocal 25; wlocal 26; wlocal 27; wlocal 28; wlocal 29] ,,
                MAYCHANGE [wmem :> bytes(word 1114112,16384)] ,,
                MAYCHANGE [wmem :> bytes(word 1966080,73728)])`;;
theorem VE_VORT_APPLY_FREDKIN
 `!VK. ve_vk_ok VK
     ==> !N (mdl:num->int32) (va:num->int32) (vb:num->int32).
          mdl 1 = word N /\ 1 <= N /\ N <= 640
          ==> ensures wasm
               (\s. read wcode s = ve_vort_apply_mc /\ read wpc s = word 21 /\
                    read wstatus s = WRunning /\ read wstack s = [] /\
                    read wlabels s = [] /\ read warity s = 0 /\
                    read wmemsize s = 2097152 /\
                    (!k. k < 1024 ==> read (wmem :> bytes32 (word (16640 + 4 * k))) s = mdl k) /\
                    (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1114112 + 4 * m))) s = va m) /\
                    (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1122304 + 4 * m))) s = vb m))
               (\s. read wstatus s = WDone /\ read wstack s = [] /\
                    (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1114112 + 4 * m))) s = FST (ve_fredkin_fwd (VK mdl) (va,vb)) m) /\
                    (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1122304 + 4 * m))) s = SND (ve_fredkin_fwd (VK mdl) (va,vb)) m))
               (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
                MAYCHANGE [wstatus] ,,
                MAYCHANGE [wlocal 0; wlocal 1; wlocal 2; wlocal 3; wlocal 4; wlocal 5; wlocal 6; wlocal 7; wlocal 8; wlocal 9; wlocal 10; wlocal 11; wlocal 12; wlocal 13; wlocal 14; wlocal 15; wlocal 16; wlocal 17; wlocal 18; wlocal 19; wlocal 20; wlocal 21; wlocal 22; wlocal 23; wlocal 24; wlocal 25; wlocal 26; wlocal 27; wlocal 28; wlocal 29] ,,
                MAYCHANGE [wmem :> bytes(word 1114112,16384)] ,,
                MAYCHANGE [wmem :> bytes(word 1966080,73728)])`;;
theorem VE_VORT_UNAPPLY_FREDKIN
 `!VK. ve_vk_ok VK
     ==> !N (mdl:num->int32) (va:num->int32) (vb:num->int32).
          mdl 1 = word N /\ 1 <= N /\ N <= 640
          ==> ensures wasm
               (\s. read wcode s = ve_vort_unapply_mc /\ read wpc s = word 21 /\
                    read wstatus s = WRunning /\ read wstack s = [] /\
                    read wlabels s = [] /\ read warity s = 0 /\
                    read wmemsize s = 2097152 /\
                    (!k. k < 1024 ==> read (wmem :> bytes32 (word (16640 + 4 * k))) s = mdl k) /\
                    (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1114112 + 4 * m))) s = va m) /\
                    (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1122304 + 4 * m))) s = vb m))
               (\s. read wstatus s = WDone /\ read wstack s = [] /\
                    (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1114112 + 4 * m))) s = FST (ve_fredkin_bwd (VK mdl) (va,vb)) m) /\
                    (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1122304 + 4 * m))) s = SND (ve_fredkin_bwd (VK mdl) (va,vb)) m))
               (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
                MAYCHANGE [wstatus] ,,
                MAYCHANGE [wlocal 0; wlocal 1; wlocal 2; wlocal 3; wlocal 4; wlocal 5; wlocal 6; wlocal 7; wlocal 8; wlocal 9; wlocal 10; wlocal 11; wlocal 12; wlocal 13; wlocal 14; wlocal 15; wlocal 16; wlocal 17; wlocal 18; wlocal 19; wlocal 20; wlocal 21; wlocal 22; wlocal 23; wlocal 24; wlocal 25; wlocal 26; wlocal 27; wlocal 28; wlocal 29] ,,
                MAYCHANGE [wmem :> bytes(word 1114112,16384)] ,,
                MAYCHANGE [wmem :> bytes(word 1966080,73728)])`;;
theorem VE_VORT_INVERSE
 `!VK. ve_vk_ok VK
     ==> !N (mdl:num->int32) (va:num->int32) (vb:num->int32).
          mdl 1 = word N /\ 1 <= N /\ N <= 640
          ==> ensures wasm
               (\s. read wcode s = ve_vort_unapply_mc /\ read wpc s = word 21 /\
                    read wstatus s = WRunning /\ read wstack s = [] /\
                    read wlabels s = [] /\ read warity s = 0 /\
                    read wmemsize s = 2097152 /\
                    (!k. k < 1024 ==> read (wmem :> bytes32 (word (16640 + 4 * k))) s = mdl k) /\
                    (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1114112 + 4 * m))) s = vb m) /\
                    (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1122304 + 4 * m))) s = word_add (va m) (VK mdl vb m)))
               (\s. read wstatus s = WDone /\ read wstack s = [] /\
                    (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1114112 + 4 * m))) s = va m) /\
                    (!m. m < 3 * N ==> read (wmem :> bytes32 (word (1122304 + 4 * m))) s = vb m))
               (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
                MAYCHANGE [wstatus] ,,
                MAYCHANGE [wlocal 0; wlocal 1; wlocal 2; wlocal 3; wlocal 4; wlocal 5; wlocal 6; wlocal 7; wlocal 8; wlocal 9; wlocal 10; wlocal 11; wlocal 12; wlocal 13; wlocal 14; wlocal 15; wlocal 16; wlocal 17; wlocal 18; wlocal 19; wlocal 20; wlocal 21; wlocal 22; wlocal 23; wlocal 24; wlocal 25; wlocal 26; wlocal 27; wlocal 28; wlocal 29] ,,
                MAYCHANGE [wmem :> bytes(word 1114112,16384)] ,,
                MAYCHANGE [wmem :> bytes(word 1966080,73728)])`;;
theorem VE_FREDKIN_FWDN_CLAUSES
 `(!f s. ve_fredkin_fwdn f 0 s = s) /\
   (!f n s. ve_fredkin_fwdn f (SUC n) s = ve_fredkin_fwd (f n) (ve_fredkin_fwdn f n s))`;;
theorem VE_FREDKIN_BWDN_CLAUSES
 `(!f s. ve_fredkin_bwdn f 0 s = s) /\
   (!f n s. ve_fredkin_bwdn f (SUC n) s = ve_fredkin_bwdn f n (ve_fredkin_bwd (f n) s))`;;
theorem VE_VORT_STEPS_INVERSE
 `!(VK:(num->int32)->(num->int32)->num->int32) mdl n s.
     ve_fredkin_bwdn (\i. VK mdl) n (ve_fredkin_fwdn (\i. VK mdl) n s) = s`;;
definition ve_fredkin_fwd
 `ve_fredkin_fwd (f:(num->int32)->num->int32) (s:(num->int32)#(num->int32)) =
    (SND s,(\m. word_add (FST s m) (f (SND s) m)))`;;
definition ve_fredkin_bwd
 `ve_fredkin_bwd (f:(num->int32)->num->int32) (s:(num->int32)#(num->int32)) =
    ((\m. word_sub (SND s m) (f (FST s) m)),FST s)`;;
definition ve_kd_fwd
 `ve_kd_fwd (K:(num->int32)->num->int32) (D:(num->int32)->num->int32)
            (s:(num->int32)#(num->int32)) =
    let p1 = (\m. word_add (SND s m) (K (FST s) m)) in
    ((\m. word_add (FST s m) (D p1 m)),p1)`;;
definition ve_kd_bwd
 `ve_kd_bwd (K:(num->int32)->num->int32) (D:(num->int32)->num->int32)
            (s:(num->int32)#(num->int32)) =
    let q = (\m. word_sub (FST s m) (D (SND s) m)) in
    (q,(\m. word_sub (SND s m) (K q m)))`;;
definition ve_zrec
 `ve_zrec = (0,word 0,word 0,0,(\j:num. word 0)):num#int32#int32#num#(num->int32)`;;
definition ve_rbirth
 `ve_rbirth (r:num#int32#int32#num#(num->int32)) = FST(SND(SND(SND r)))`;;
definition ve_zq
 `ve_zq (s:(num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST s`;;
definition ve_zp
 `ve_zp (s:(num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST(SND s)`;;
definition ve_dq
 `ve_dq (s:(num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST(SND(SND s))`;;
definition ve_dp
 `ve_dp (s:(num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST(SND(SND(SND s)))`;;
definition ve_cnt
 `ve_cnt (s:(num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST(SND(SND(SND(SND s))))`;;
definition ve_slots
 `ve_slots (s:(num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    SND(SND(SND(SND(SND s))))`;;
definition ve_push1
 `ve_push1 (t:num) (b:num#int32#int32#(num->int32)) s =
    let c = ve_cnt s in let k = FST b in let dz = FST(SND b) in
    let de = FST(SND(SND b)) in let pay = SND(SND(SND b)) in
    ((\i. if i = k then word_sub (ve_zq s i) dz else ve_zq s i),
     (\i. if i = k then word_sub (ve_zp s i) de else ve_zp s i),
     (\m. if 3 * c <= m /\ m < 3 * c + 3 then pay (m - 3 * c) else ve_dq s m),
     (\m. if 3 * c <= m /\ m < 3 * c + 3 then pay (m - 3 * c + 3) else ve_dp s m),
     c + 1,
     (\i. if i = c then (k,dz,de,t + 1,pay) else ve_slots s i))`;;
definition ve_pop1
 `ve_pop1 s =
    let c = ve_cnt s - 1 in let r = ve_slots s c in
    let k = FST r in let dz = FST(SND r) in let de = FST(SND(SND r)) in
    ((\i. if i = k then word_add (ve_zq s i) dz else ve_zq s i),
     (\i. if i = k then word_add (ve_zp s i) de else ve_zp s i),
     (\m. if 3 * c <= m /\ m < 3 * c + 3 then word 0 else ve_dq s m),
     (\m. if 3 * c <= m /\ m < 3 * c + 3 then word 0 else ve_dp s m),
     c,
     (\i. if i = c then ve_zrec else ve_slots s i))`;;
definition ve_births_fwd
 `ve_births_fwd (B:(num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))
                   ->(num#int32#int32#(num->int32))list) (t:num) s =
    ve_push t (B s) s`;;
definition ve_births_bwd
 `ve_births_bwd (tt:num) s = ve_unb tt (ve_cnt s) s`;;
definition ve_free
 `ve_free s <=> (!i. ve_cnt s <= i ==> ve_slots s i = ve_zrec) /\
                (!m. 3 * ve_cnt s <= m ==> ve_dq s m = word 0 /\ ve_dp s m = word 0)`;;
definition ve_log_ok
 `ve_log_ok (t:num) s <=> (!i. i < ve_cnt s ==> ve_rbirth (ve_slots s i) <= t) /\ ve_free s`;;
definition ve_t
 `ve_t (s:num#num#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#
          (num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST s`;;
definition ve_pt
 `ve_pt (s:num#num#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#
           (num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST(SND s)`;;
definition ve_va
 `ve_va (s:num#num#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#
           (num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST(SND(SND s))`;;
definition ve_vb
 `ve_vb (s:num#num#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#
           (num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST(SND(SND(SND s)))`;;
definition ve_hm
 `ve_hm (s:num#num#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#
           (num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST(SND(SND(SND(SND s))))`;;
definition ve_ra
 `ve_ra (s:num#num#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#
           (num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST(SND(SND(SND(SND(SND s)))))`;;
definition ve_rb
 `ve_rb (s:num#num#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#
           (num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST(SND(SND(SND(SND(SND(SND s))))))`;;
definition ve_jq
 `ve_jq (s:num#num#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#
           (num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST(SND(SND(SND(SND(SND(SND(SND s)))))))`;;
definition ve_jp
 `ve_jp (s:num#num#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#
           (num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST(SND(SND(SND(SND(SND(SND(SND(SND s))))))))`;;
definition ve_bs
 `ve_bs (s:num#num#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#
           (num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    SND(SND(SND(SND(SND(SND(SND(SND(SND s))))))))`;;
definition ve_rim_fwd
 `ve_rim_fwd (fr:(num->int32)->(num->int32)->num->int32) s =
    let r = ve_fredkin_fwd (fr (ve_hm s)) (ve_ra s,ve_rb s) in
    (ve_t s,ve_pt s,ve_va s,ve_vb s,ve_hm s,FST r,SND r,ve_jq s,ve_jp s,ve_bs s)`;;
definition ve_rim_bwd
 `ve_rim_bwd (fr:(num->int32)->(num->int32)->num->int32) s =
    let r = ve_fredkin_bwd (fr (ve_hm s)) (ve_ra s,ve_rb s) in
    (ve_t s,ve_pt s,ve_va s,ve_vb s,ve_hm s,FST r,SND r,ve_jq s,ve_jp s,ve_bs s)`;;
definition ve_jig_fwd
 `ve_jig_fwd (kj:num->(num->int32)->(num->int32)->(num->int32)->num->int32)
             (dj:num->(num->int32)->(num->int32)->(num->int32)->num->int32) s =
    let tt = ve_t s - ve_pt s in
    let r = ve_kd_fwd (kj tt (ve_hm s) (ve_rb s)) (dj tt (ve_hm s) (ve_rb s)) (ve_jq s,ve_jp s) in
    (ve_t s,ve_pt s,ve_va s,ve_vb s,ve_hm s,ve_ra s,ve_rb s,FST r,SND r,ve_bs s)`;;
definition ve_jig_bwd
 `ve_jig_bwd (kj:num->(num->int32)->(num->int32)->(num->int32)->num->int32)
             (dj:num->(num->int32)->(num->int32)->(num->int32)->num->int32) s =
    let tt = ve_t s - ve_pt s in
    let r = ve_kd_bwd (kj tt (ve_hm s) (ve_rb s)) (dj tt (ve_hm s) (ve_rb s)) (ve_jq s,ve_jp s) in
    (ve_t s,ve_pt s,ve_va s,ve_vb s,ve_hm s,ve_ra s,ve_rb s,FST r,SND r,ve_bs s)`;;
definition ve_corr_fwd
 `ve_corr_fwd (kc:num->num->(num->int32)->(num->int32)->(num->int32)->num->int32)
              (dc:num->num->(num->int32)->(num->int32)->(num->int32)->num->int32) (nc:num) s =
    let tt = ve_t s - ve_pt s in let b = ve_bs s in
    let r = ve_kd_fwdn (\i. kc tt i (ve_hm s) (ve_rb s)) (\i. dc tt i (ve_hm s) (ve_rb s)) nc
                       (ve_zq b,ve_zp b) in
    (ve_t s,ve_pt s,ve_va s,ve_vb s,ve_hm s,ve_ra s,ve_rb s,ve_jq s,ve_jp s,
     (FST r,SND r,ve_dq b,ve_dp b,ve_cnt b,ve_slots b))`;;
definition ve_corr_bwd
 `ve_corr_bwd (kc:num->num->(num->int32)->(num->int32)->(num->int32)->num->int32)
              (dc:num->num->(num->int32)->(num->int32)->(num->int32)->num->int32) (nc:num) s =
    let tt = ve_t s - ve_pt s in let b = ve_bs s in
    let r = ve_kd_bwdn (\i. kc tt i (ve_hm s) (ve_rb s)) (\i. dc tt i (ve_hm s) (ve_rb s)) nc
                       (ve_zq b,ve_zp b) in
    (ve_t s,ve_pt s,ve_va s,ve_vb s,ve_hm s,ve_ra s,ve_rb s,ve_jq s,ve_jp s,
     (FST r,SND r,ve_dq b,ve_dp b,ve_cnt b,ve_slots b))`;;
definition ve_dmask
 `ve_dmask (c:num) (g:(num->int32)->num->int32) (v:num->int32) (m:num) =
    if m < 3 * c then g v m else word 0`;;
definition ve_drop_fwd
 `ve_drop_fwd (kd:num->num->(num->int32)->num->int32) (dd:num->num->(num->int32)->num->int32) s =
    let tt = ve_t s - ve_pt s in let b = ve_bs s in let c = ve_cnt b in
    let r = ve_kd_fwd (ve_dmask c (kd tt c)) (ve_dmask c (dd tt c)) (ve_dq b,ve_dp b) in
    (ve_t s,ve_pt s,ve_va s,ve_vb s,ve_hm s,ve_ra s,ve_rb s,ve_jq s,ve_jp s,
     (ve_zq b,ve_zp b,FST r,SND r,c,ve_slots b))`;;
definition ve_drop_bwd
 `ve_drop_bwd (kd:num->num->(num->int32)->num->int32) (dd:num->num->(num->int32)->num->int32) s =
    let tt = ve_t s - ve_pt s in let b = ve_bs s in let c = ve_cnt b in
    let r = ve_kd_bwd (ve_dmask c (kd tt c)) (ve_dmask c (dd tt c)) (ve_dq b,ve_dp b) in
    (ve_t s,ve_pt s,ve_va s,ve_vb s,ve_hm s,ve_ra s,ve_rb s,ve_jq s,ve_jp s,
     (ve_zq b,ve_zp b,FST r,SND r,c,ve_slots b))`;;
definition ve_birth_fwd
 `ve_birth_fwd bf s =
    (ve_t s,ve_pt s,ve_va s,ve_vb s,ve_hm s,ve_ra s,ve_rb s,ve_jq s,ve_jp s,
     ve_push (ve_t s) (bf s) (ve_bs s))`;;
definition ve_birth_bwd
 `ve_birth_bwd s =
    (ve_t s,ve_pt s,ve_va s,ve_vb s,ve_hm s,ve_ra s,ve_rb s,ve_jq s,ve_jp s,
     ve_births_bwd (ve_t s + 1) (ve_bs s))`;;
definition ve_vort_fwd
 `ve_vort_fwd (fv:(num->int32)->num->int32) (n:num) s =
    let r = ve_fredkin_fwdn (\i. fv) n (ve_va s,ve_vb s) in
    (ve_t s,ve_pt s,FST r,SND r,ve_hm s,ve_ra s,ve_rb s,ve_jq s,ve_jp s,ve_bs s)`;;
definition ve_vort_bwd
 `ve_vort_bwd (fv:(num->int32)->num->int32) (n:num) s =
    let r = ve_fredkin_bwdn (\i. fv) n (ve_va s,ve_vb s) in
    (ve_t s,ve_pt s,FST r,SND r,ve_hm s,ve_ra s,ve_rb s,ve_jq s,ve_jp s,ve_bs s)`;;
definition ve_tick_fwd
 `ve_tick_fwd s =
    (ve_t s + 1,ve_pt s,ve_va s,ve_vb s,ve_hm s,ve_ra s,ve_rb s,ve_jq s,ve_jp s,ve_bs s)`;;
definition ve_tick_bwd
 `ve_tick_bwd s =
    (ve_t s - 1,ve_pt s,ve_va s,ve_vb s,ve_hm s,ve_ra s,ve_rb s,ve_jq s,ve_jp s,ve_bs s)`;;
definition ve_punct
 `ve_punct i0 s =
    if ve_t s = ve_pt s then
      let z = i0 s in let b = ve_bs s in
      (ve_t s,ve_pt s,ve_va s,ve_vb s,FST z,FST(SND z),FST(SND(SND z)),FST(SND(SND(SND z))),
       FST(SND(SND(SND(SND z)))),
       (FST(SND(SND(SND(SND(SND z))))),SND(SND(SND(SND(SND(SND z))))),ve_dq b,ve_dp b,ve_cnt b,ve_slots b))
    else s`;;
definition ve_unpunct
 `ve_unpunct s =
    if ve_t s = ve_pt s then
      (ve_t s,ve_pt s,ve_va s,ve_vb s,(\m. word 0),(\m. word 0),(\m. word 0),(\m. word 0),(\m. word 0),
       ((\m. word 0),(\m. word 0),(\m. word 0),(\m. word 0),0,(\i. ve_zrec)))
    else s`;;
definition ve_pop_zero
 `ve_pop_zero s <=>
    ve_hm s = (\m. word 0) /\ ve_ra s = (\m. word 0) /\ ve_rb s = (\m. word 0) /\
    ve_jq s = (\m. word 0) /\ ve_jp s = (\m. word 0) /\
    ve_bs s = ((\m. word 0),(\m. word 0),(\m. word 0),(\m. word 0),0,(\i. ve_zrec))`;;
definition ve_step_fwd
 `ve_step_fwd fr kj dj kc dc kd dd bf fv i0 (nc:num) (nsw:num) (npo:num) s =
    if ve_pt s <= ve_t s
    then ve_tick_fwd (ve_vort_fwd fv npo (ve_birth_fwd bf (ve_drop_fwd kd dd
           (ve_corr_fwd kc dc nc (ve_jig_fwd kj dj (ve_rim_fwd fr s))))))
    else ve_punct i0 (ve_tick_fwd (ve_vort_fwd fv nsw s))`;;
definition ve_step_bwd
 `ve_step_bwd fr kj dj kc dc kd dd fv (nc:num) (nsw:num) (npo:num) s =
    if ve_t s = 0 then s
    else if ve_pt s < ve_t s
    then ve_rim_bwd fr (ve_jig_bwd kj dj (ve_corr_bwd kc dc nc (ve_drop_bwd kd dd
           (ve_birth_bwd (ve_vort_bwd fv npo (ve_tick_bwd s))))))
    else ve_vort_bwd fv nsw (ve_tick_bwd (ve_unpunct s))`;;
definition ve_step_ok
 `ve_step_ok s <=> (ve_pt s <= ve_t s ==> ve_log_ok (ve_t s) (ve_bs s)) /\
                   (ve_t s + 1 = ve_pt s ==> ve_pop_zero s)`;;
definition ve_run_ok
 `ve_run_ok s <=> (ve_pt s <= ve_t s ==> ve_log_ok (ve_t s) (ve_bs s)) /\
                  (ve_t s < ve_pt s ==> ve_pop_zero s)`;;
definition ve_vk_ok
 `ve_vk_ok (VK:(num->int32)->(num->int32)->num->int32) <=>
    (!N (mdl:num->int32) (va:num->int32) (vb:num->int32).
        mdl 1 = word N /\ 1 <= N /\ N <= 640
        ==> ensures wasm
             (\s. read wcode s = ve_vort_apply_mc /\ read wpc s = word 21 /\
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
             (\s. read wcode s = ve_vort_unapply_mc /\ read wpc s = word 21 /\
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
definition ve_vort_apply_mc
 `ve_vort_apply_mc:byte list = [word 0x0a; word 0x05; word 0x7f; word 0x01; word 0x7e; word 0x01; word 0x7f; word 0x01; word 0x7e; word 0x01; word 0x7f; word 0x05; word 0x7e; word 0x09; word 0x7f; word 0x03; word 0x7e; word 0x01; word 0x7f; word 0x03; word 0x7e; word 0x41; word 0x00; word 0x21; word 0x00; word 0x02; word 0x40; word 0x41; word 0x00; word 0x28; word 0x02; word 0x84; word 0x82; word 0x01; word 0x22; word 0x01; word 0x45; word 0x0d; word 0x00; word 0x20; word 0x01; word 0x41; word 0x80; word 0x05; word 0x20; word 0x01; word 0x41; word 0x80; word 0x05; word 0x49; word 0x1b; word 0x21; word 0x02; word 0x03; word 0x40; word 0x20; word 0x00; word 0x41; word 0x03; word 0x6c; word 0x22; word 0x03; word 0x41; word 0x01; word 0x6a; word 0x41; word 0x02; word 0x74; word 0x22; word 0x04; word 0x34; word 0x02; word 0x80; word 0xc0; word 0x44; word 0x22; word 0x05; word 0x20; word 0x05; word 0x7e; word 0x20; word 0x03; word 0x41; word 0x02; word 0x74; word 0x22; word 0x06; word 0x34; word 0x02; word 0x80; word 0xc0; word 0x44; word 0x22; word 0x07; word 0x20; word 0x07; word 0x7e; word 0x7c; word 0x20; word 0x03; word 0x41; word 0x02; word 0x6a; word 0x41; word 0x02; word 0x74; word 0x22; word 0x08; word 0x34; word 0x02; word 0x80; word 0xc0; word 0x44; word 0x22; word 0x09; word 0x20; word 0x09; word 0x7e; word 0x7c; word 0x21; word 0x0a; word 0x42; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0xc0; word 0x00; word 0x21; word 0x0b; word 0x41; word 0x20; word 0x21; word 0x03; word 0x42; word 0x00; word 0x21; word 0x0c; word 0x03; word 0x40; word 0x42; word 0x00; word 0x20; word 0x0b; word 0x20; word 0x0a; word 0x20; word 0x0b; word 0x20; word 0x0c; word 0x7c; word 0x22; word 0x0d; word 0x54; word 0x22; word 0x0e; word 0x1b; word 0x20; word 0x0c; word 0x42; word 0x01; word 0x88; word 0x7c; word 0x21; word 0x0c; word 0x20; word 0x0a; word 0x42; word 0x00; word 0x20; word 0x0d; word 0x20; word 0x0e; word 0x1b; word 0x7d; word 0x21; word 0x0a; word 0x20; word 0x0b; word 0x42; word 0x02; word 0x88; word 0x21; word 0x0b; word 0x20; word 0x03; word 0x41; word 0x7f; word 0x6a; word 0x22; word 0x03; word 0x0d; word 0x00; word 0x0b; word 0x20; word 0x04; word 0x20; word 0x05; word 0x42; word 0x1e; word 0x86; word 0x20; word 0x0c; word 0x42; word 0x01; word 0x20; word 0x0c; word 0x42; word 0x01; word 0x55; word 0x1b; word 0x22; word 0x0b; word 0x7f; word 0x3e; word 0x02; word 0x80; word 0x80; word 0x78; word 0x20; word 0x06; word 0x20; word 0x07; word 0x42; word 0x1e; word 0x86; word 0x20; word 0x0b; word 0x7f; word 0x3e; word 0x02; word 0x80; word 0x80; word 0x78; word 0x20; word 0x08; word 0x20; word 0x09; word 0x42; word 0x1e; word 0x86; word 0x20; word 0x0b; word 0x7f; word 0x3e; word 0x02; word 0x80; word 0x80; word 0x78; word 0x20; word 0x00; word 0x41; word 0x01; word 0x6a; word 0x22; word 0x00; word 0x20; word 0x02; word 0x47; word 0x0d; word 0x00; word 0x0b; word 0x20; word 0x02; word 0x41; word 0x03; word 0x6c; word 0x22; word 0x0f; word 0x41; word 0x07; word 0x71; word 0x21; word 0x0e; word 0x41; word 0x00; word 0x21; word 0x04; word 0x02; word 0x40; word 0x02; word 0x40; word 0x20; word 0x01; word 0x41; word 0x03; word 0x49; word 0x0d; word 0x00; word 0x20; word 0x0f; word 0x41; word 0x78; word 0x71; word 0x21; word 0x04; word 0x20; word 0x0f; word 0x41; word 0x03; word 0x74; word 0x41; word 0x40; word 0x71; word 0x21; word 0x00; word 0x41; word 0x00; word 0x21; word 0x03; word 0x03; word 0x40; word 0x20; word 0x03; word 0x41; word 0xb8; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0xb0; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0xa8; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0xa0; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0x98; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0x90; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0x88; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0x80; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x00; word 0x20; word 0x03; word 0x41; word 0xc0; word 0x00; word 0x6a; word 0x22; word 0x03; word 0x47; word 0x0d; word 0x00; word 0x0b; word 0x20; word 0x0e; word 0x45; word 0x0d; word 0x01; word 0x0b; word 0x20; word 0x04; word 0x41; word 0x03; word 0x74; word 0x41; word 0x80; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x21; word 0x03; word 0x03; word 0x40; word 0x20; word 0x03; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0x08; word 0x6a; word 0x21; word 0x03; word 0x20; word 0x0e; word 0x41; word 0x7f; word 0x6a; word 0x22; word 0x0e; word 0x0d; word 0x00; word 0x0b; word 0x0b; word 0x20; word 0x02; word 0x41; word 0x7f; word 0x6a; word 0x21; word 0x10; word 0x41; word 0x00; word 0x21; word 0x03; word 0x41; word 0x80; word 0x80; word 0xf9; word 0x00; word 0x21; word 0x11; word 0x41; word 0x94; word 0x80; word 0xf8; word 0x00; word 0x21; word 0x12; word 0x41; word 0xc4; word 0x82; word 0x01; word 0x21; word 0x13; word 0x03; word 0x40; word 0x20; word 0x03; word 0x41; word 0x03; word 0x6c; word 0x22; word 0x14; word 0x41; word 0x02; word 0x6a; word 0x21; word 0x15; word 0x20; word 0x14; word 0x41; word 0x01; word 0x6a; word 0x21; word 0x16; word 0x42; word 0x00; word 0x21; word 0x17; word 0x42; word 0x00; word 0x21; word 0x18; word 0x42; word 0x00; word 0x21; word 0x19; word 0x02; word 0x40; word 0x20; word 0x03; word 0x41; word 0x01; word 0x6a; word 0x22; word 0x1a; word 0x20; word 0x02; word 0x4f; word 0x0d; word 0x00; word 0x20; word 0x03; word 0x41; word 0x02; word 0x74; word 0x41; word 0xc0; word 0x82; word 0x01; word 0x6a; word 0x34; word 0x02; word 0x00; word 0x21; word 0x1b; word 0x20; word 0x14; word 0x41; word 0x02; word 0x74; word 0x34; word 0x02; word 0x80; word 0x80; word 0x78; word 0x21; word 0x0b; word 0x20; word 0x15; word 0x41; word 0x02; word 0x74; word 0x34; word 0x02; word 0x80; word 0x80; word 0x78; word 0x21; word 0x0c; word 0x20; word 0x16; word 0x41; word 0x02; word 0x74; word 0x34; word 0x02; word 0x80; word 0x80; word 0x78; word 0x21; word 0x0a; word 0x42; word 0x00; word 0x21; word 0x19; word 0x20; word 0x10; word 0x21; word 0x06; word 0x20; word 0x13; word 0x21; word 0x00; word 0x20; word 0x12; word 0x21; word 0x03; word 0x20; word 0x11; word 0x21; word 0x0e; word 0x42; word 0x00; word 0x21; word 0x18; word 0x42; word 0x00; word 0x21; word 0x17; word 0x03; word 0x40; word 0x20; word 0x0e; word 0x41; word 0x18; word 0x6a; word 0x22; word 0x04; word 0x42; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x20; word 0x42; word 0xc3; word 0xeb; word 0xa3; word 0x81; word 0x04; word 0x20; word 0x03; word 0x41; word 0x7c; word 0x6a; word 0x34; word 0x02; word 0x00; word 0x22; word 0x0d; word 0x20; word 0x0a; word 0x7e; word 0x20; word 0x03; word 0x41; word 0x78; word 0x6a; word 0x34; word 0x02; word 0x00; word 0x22; word 0x05; word 0x20; word 0x0b; word 0x7e; word 0x7c; word 0x20; word 0x03; word 0x34; word 0x02; word 0x00; word 0x22; word 0x07; word 0x20; word 0x0c; word 0x7e; word 0x7c; word 0x42; word 0x1e; word 0x87; word 0x7d; word 0x22; word 0x09; word 0x42; word 0xc3; word 0xeb; word 0xa3; word 0x01; word 0x20; word 0x09; word 0x42; word 0xc3; word 0xeb; word 0xa3; word 0x01; word 0x55; word 0x1b; word 0x80; word 0x22; word 0x1c; word 0x20; word 0x1b; word 0x7e; word 0x42; word 0x14; word 0x87; word 0x22; word 0x09; word 0x42; word 0x00; word 0x20; word 0x0d; word 0x20; word 0x0c; word 0x7e; word 0x20; word 0x07; word 0x20; word 0x0a; word 0x7e; word 0x7d; word 0x22; word 0x1d; word 0x7d; word 0x42; word 0x24; word 0x87; word 0x7e; word 0x42; word 0x0c; word 0x87; word 0x20; word 0x04; word 0x29; word 0x03; word 0x00; word 0x7c; word 0x37; word 0x03; word 0x00; word 0x20; word 0x0e; word 0x41; word 0x20; word 0x6a; word 0x22; word 0x08; word 0x20; word 0x09; word 0x42; word 0x00; word 0x20; word 0x07; word 0x20; word 0x0b; word 0x7e; word 0x20; word 0x05; word 0x20; word 0x0c; word 0x7e; word 0x7d; word 0x22; word 0x07; word 0x7d; word 0x42; word 0x24; word 0x87; word 0x7e; word 0x42; word 0x0c; word 0x87; word 0x20; word 0x08; word 0x29; word 0x03; word 0x00; word 0x7c; word 0x37; word 0x03; word 0x00; word 0x20; word 0x0e; word 0x41; word 0x28; word 0x6a; word 0x22; word 0x0e; word 0x20; word 0x0e; word 0x29; word 0x03; word 0x00; word 0x20; word 0x09; word 0x42; word 0x00; word 0x20; word 0x05; word 0x20; word 0x0a; word 0x7e; word 0x20; word 0x0d; word 0x20; word 0x0b; word 0x7e; word 0x7d; word 0x22; word 0x05; word 0x7d; word 0x42; word 0x24; word 0x87; word 0x7e; word 0x42; word 0x0c; word 0x87; word 0x7c; word 0x37; word 0x03; word 0x00; word 0x20; word 0x1c; word 0x20; word 0x00; word 0x34; word 0x02; word 0x00; word 0x7e; word 0x42; word 0x14; word 0x87; word 0x22; word 0x0d; word 0x20; word 0x05; word 0x42; word 0x24; word 0x87; word 0x7e; word 0x42; word 0x0c; word 0x87; word 0x20; word 0x17; word 0x7c; word 0x21; word 0x17; word 0x20; word 0x0d; word 0x20; word 0x07; word 0x42; word 0x24; word 0x87; word 0x7e; word 0x42; word 0x0c; word 0x87; word 0x20; word 0x18; word 0x7c; word 0x21; word 0x18; word 0x20; word 0x0d; word 0x20; word 0x1d; word 0x42; word 0x24; word 0x87; word 0x7e; word 0x42; word 0x0c; word 0x87; word 0x20; word 0x19; word 0x7c; word 0x21; word 0x19; word 0x20; word 0x00; word 0x41; word 0x04; word 0x6a; word 0x21; word 0x00; word 0x20; word 0x03; word 0x41; word 0x0c; word 0x6a; word 0x21; word 0x03; word 0x20; word 0x04; word 0x21; word 0x0e; word 0x20; word 0x06; word 0x41; word 0x7f; word 0x6a; word 0x22; word 0x06; word 0x0d; word 0x00; word 0x0b; word 0x0b; word 0x20; word 0x14; word 0x41; word 0x03; word 0x74; word 0x22; word 0x03; word 0x20; word 0x03; word 0x29; word 0x03; word 0x80; word 0x80; word 0x79; word 0x20; word 0x19; word 0x7c; word 0x37; word 0x03; word 0x80; word 0x80; word 0x79; word 0x20; word 0x16; word 0x41; word 0x03; word 0x74; word 0x22; word 0x03; word 0x20; word 0x03; word 0x29; word 0x03; word 0x80; word 0x80; word 0x79; word 0x20; word 0x18; word 0x7c; word 0x37; word 0x03; word 0x80; word 0x80; word 0x79; word 0x20; word 0x15; word 0x41; word 0x03; word 0x74; word 0x22; word 0x03; word 0x20; word 0x03; word 0x29; word 0x03; word 0x80; word 0x80; word 0x79; word 0x20; word 0x17; word 0x7c; word 0x37; word 0x03; word 0x80; word 0x80; word 0x79; word 0x20; word 0x10; word 0x41; word 0x7f; word 0x6a; word 0x21; word 0x10; word 0x20; word 0x13; word 0x41; word 0x04; word 0x6a; word 0x21; word 0x13; word 0x20; word 0x12; word 0x41; word 0x0c; word 0x6a; word 0x21; word 0x12; word 0x20; word 0x11; word 0x41; word 0x18; word 0x6a; word 0x21; word 0x11; word 0x20; word 0x1a; word 0x21; word 0x03; word 0x20; word 0x1a; word 0x20; word 0x02; word 0x47; word 0x0d; word 0x00; word 0x0b; word 0x20; word 0x0f; word 0x41; word 0x03; word 0x71; word 0x21; word 0x00; word 0x41; word 0x00; word 0x21; word 0x06; word 0x02; word 0x40; word 0x20; word 0x01; word 0x41; word 0x01; word 0x46; word 0x0d; word 0x00; word 0x20; word 0x0f; word 0x41; word 0x7c; word 0x71; word 0x21; word 0x06; word 0x20; word 0x0f; word 0x41; word 0x03; word 0x74; word 0x41; word 0x60; word 0x71; word 0x21; word 0x04; word 0x41; word 0x00; word 0x21; word 0x03; word 0x41; word 0x80; word 0xc0; word 0xf8; word 0x00; word 0x21; word 0x0e; word 0x03; word 0x40; word 0x20; word 0x0e; word 0x20; word 0x03; word 0x41; word 0x80; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x29; word 0x03; word 0x00; word 0x42; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x01; word 0x7c; word 0x42; word 0x24; word 0x87; word 0x3e; word 0x02; word 0x00; word 0x20; word 0x0e; word 0x41; word 0x04; word 0x6a; word 0x20; word 0x03; word 0x41; word 0x88; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x29; word 0x03; word 0x00; word 0x42; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x01; word 0x7c; word 0x42; word 0x24; word 0x87; word 0x3e; word 0x02; word 0x00; word 0x20; word 0x0e; word 0x41; word 0x08; word 0x6a; word 0x20; word 0x03; word 0x41; word 0x90; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x29; word 0x03; word 0x00; word 0x42; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x01; word 0x7c; word 0x42; word 0x24; word 0x87; word 0x3e; word 0x02; word 0x00; word 0x20; word 0x0e; word 0x41; word 0x0c; word 0x6a; word 0x20; word 0x03; word 0x41; word 0x98; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x29; word 0x03; word 0x00; word 0x42; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x01; word 0x7c; word 0x42; word 0x24; word 0x87; word 0x3e; word 0x02; word 0x00; word 0x20; word 0x0e; word 0x41; word 0x10; word 0x6a; word 0x21; word 0x0e; word 0x20; word 0x04; word 0x20; word 0x03; word 0x41; word 0x20; word 0x6a; word 0x22; word 0x03; word 0x47; word 0x0d; word 0x00; word 0x0b; word 0x20; word 0x00; word 0x45; word 0x0d; word 0x01; word 0x0b; word 0x20; word 0x06; word 0x41; word 0x03; word 0x74; word 0x41; word 0x80; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x21; word 0x03; word 0x20; word 0x06; word 0x41; word 0x02; word 0x74; word 0x41; word 0x80; word 0xc0; word 0xf8; word 0x00; word 0x6a; word 0x21; word 0x0e; word 0x03; word 0x40; word 0x20; word 0x0e; word 0x20; word 0x03; word 0x29; word 0x03; word 0x00; word 0x42; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x01; word 0x7c; word 0x42; word 0x24; word 0x87; word 0x3e; word 0x02; word 0x00; word 0x20; word 0x03; word 0x41; word 0x08; word 0x6a; word 0x21; word 0x03; word 0x20; word 0x0e; word 0x41; word 0x04; word 0x6a; word 0x21; word 0x0e; word 0x20; word 0x00; word 0x41; word 0x7f; word 0x6a; word 0x22; word 0x00; word 0x0d; word 0x00; word 0x0b; word 0x0b; word 0x02; word 0x40; word 0x41; word 0x00; word 0x28; word 0x02; word 0x84; word 0x82; word 0x01; word 0x22; word 0x03; word 0x45; word 0x0d; word 0x00; word 0x20; word 0x03; word 0x41; word 0x80; word 0x05; word 0x20; word 0x03; word 0x41; word 0x80; word 0x05; word 0x49; word 0x1b; word 0x41; word 0x03; word 0x6c; word 0x22; word 0x03; word 0x41; word 0xfe; word 0x1f; word 0x71; word 0x21; word 0x04; word 0x20; word 0x03; word 0x41; word 0x01; word 0x71; word 0x21; word 0x02; word 0x41; word 0x80; word 0xc0; word 0xc4; word 0x00; word 0x21; word 0x03; word 0x41; word 0x80; word 0x80; word 0xc4; word 0x00; word 0x21; word 0x0e; word 0x41; word 0x80; word 0xc0; word 0xf8; word 0x00; word 0x21; word 0x00; word 0x03; word 0x40; word 0x20; word 0x03; word 0x28; word 0x02; word 0x00; word 0x21; word 0x06; word 0x20; word 0x03; word 0x20; word 0x00; word 0x28; word 0x02; word 0x00; word 0x20; word 0x0e; word 0x28; word 0x02; word 0x00; word 0x6a; word 0x36; word 0x02; word 0x00; word 0x20; word 0x0e; word 0x20; word 0x06; word 0x36; word 0x02; word 0x00; word 0x20; word 0x03; word 0x41; word 0x04; word 0x6a; word 0x22; word 0x06; word 0x28; word 0x02; word 0x00; word 0x21; word 0x08; word 0x20; word 0x06; word 0x20; word 0x00; word 0x41; word 0x04; word 0x6a; word 0x28; word 0x02; word 0x00; word 0x20; word 0x0e; word 0x41; word 0x04; word 0x6a; word 0x22; word 0x14; word 0x28; word 0x02; word 0x00; word 0x6a; word 0x36; word 0x02; word 0x00; word 0x20; word 0x14; word 0x20; word 0x08; word 0x36; word 0x02; word 0x00; word 0x20; word 0x00; word 0x41; word 0x08; word 0x6a; word 0x21; word 0x00; word 0x20; word 0x0e; word 0x41; word 0x08; word 0x6a; word 0x21; word 0x0e; word 0x20; word 0x03; word 0x41; word 0x08; word 0x6a; word 0x21; word 0x03; word 0x20; word 0x04; word 0x41; word 0x7e; word 0x6a; word 0x22; word 0x04; word 0x0d; word 0x00; word 0x0b; word 0x20; word 0x02; word 0x45; word 0x0d; word 0x00; word 0x20; word 0x03; word 0x28; word 0x02; word 0x00; word 0x21; word 0x04; word 0x20; word 0x03; word 0x20; word 0x00; word 0x28; word 0x02; word 0x00; word 0x20; word 0x0e; word 0x28; word 0x02; word 0x00; word 0x6a; word 0x36; word 0x02; word 0x00; word 0x20; word 0x0e; word 0x20; word 0x04; word 0x36; word 0x02; word 0x00; word 0x0b; word 0x0b]`;;
definition ve_vort_unapply_mc
 `ve_vort_unapply_mc:byte list = [word 0x0a; word 0x05; word 0x7f; word 0x01; word 0x7e; word 0x01; word 0x7f; word 0x01; word 0x7e; word 0x01; word 0x7f; word 0x05; word 0x7e; word 0x09; word 0x7f; word 0x03; word 0x7e; word 0x01; word 0x7f; word 0x03; word 0x7e; word 0x41; word 0x00; word 0x21; word 0x00; word 0x02; word 0x40; word 0x41; word 0x00; word 0x28; word 0x02; word 0x84; word 0x82; word 0x01; word 0x22; word 0x01; word 0x45; word 0x0d; word 0x00; word 0x20; word 0x01; word 0x41; word 0x80; word 0x05; word 0x20; word 0x01; word 0x41; word 0x80; word 0x05; word 0x49; word 0x1b; word 0x21; word 0x02; word 0x03; word 0x40; word 0x20; word 0x00; word 0x41; word 0x03; word 0x6c; word 0x22; word 0x03; word 0x41; word 0x01; word 0x6a; word 0x41; word 0x02; word 0x74; word 0x22; word 0x04; word 0x34; word 0x02; word 0x80; word 0x80; word 0x44; word 0x22; word 0x05; word 0x20; word 0x05; word 0x7e; word 0x20; word 0x03; word 0x41; word 0x02; word 0x74; word 0x22; word 0x06; word 0x34; word 0x02; word 0x80; word 0x80; word 0x44; word 0x22; word 0x07; word 0x20; word 0x07; word 0x7e; word 0x7c; word 0x20; word 0x03; word 0x41; word 0x02; word 0x6a; word 0x41; word 0x02; word 0x74; word 0x22; word 0x08; word 0x34; word 0x02; word 0x80; word 0x80; word 0x44; word 0x22; word 0x09; word 0x20; word 0x09; word 0x7e; word 0x7c; word 0x21; word 0x0a; word 0x42; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0xc0; word 0x00; word 0x21; word 0x0b; word 0x41; word 0x20; word 0x21; word 0x03; word 0x42; word 0x00; word 0x21; word 0x0c; word 0x03; word 0x40; word 0x42; word 0x00; word 0x20; word 0x0b; word 0x20; word 0x0a; word 0x20; word 0x0b; word 0x20; word 0x0c; word 0x7c; word 0x22; word 0x0d; word 0x54; word 0x22; word 0x0e; word 0x1b; word 0x20; word 0x0c; word 0x42; word 0x01; word 0x88; word 0x7c; word 0x21; word 0x0c; word 0x20; word 0x0a; word 0x42; word 0x00; word 0x20; word 0x0d; word 0x20; word 0x0e; word 0x1b; word 0x7d; word 0x21; word 0x0a; word 0x20; word 0x0b; word 0x42; word 0x02; word 0x88; word 0x21; word 0x0b; word 0x20; word 0x03; word 0x41; word 0x7f; word 0x6a; word 0x22; word 0x03; word 0x0d; word 0x00; word 0x0b; word 0x20; word 0x04; word 0x20; word 0x05; word 0x42; word 0x1e; word 0x86; word 0x20; word 0x0c; word 0x42; word 0x01; word 0x20; word 0x0c; word 0x42; word 0x01; word 0x55; word 0x1b; word 0x22; word 0x0b; word 0x7f; word 0x3e; word 0x02; word 0x80; word 0x80; word 0x78; word 0x20; word 0x06; word 0x20; word 0x07; word 0x42; word 0x1e; word 0x86; word 0x20; word 0x0b; word 0x7f; word 0x3e; word 0x02; word 0x80; word 0x80; word 0x78; word 0x20; word 0x08; word 0x20; word 0x09; word 0x42; word 0x1e; word 0x86; word 0x20; word 0x0b; word 0x7f; word 0x3e; word 0x02; word 0x80; word 0x80; word 0x78; word 0x20; word 0x00; word 0x41; word 0x01; word 0x6a; word 0x22; word 0x00; word 0x20; word 0x02; word 0x47; word 0x0d; word 0x00; word 0x0b; word 0x20; word 0x02; word 0x41; word 0x03; word 0x6c; word 0x22; word 0x0f; word 0x41; word 0x07; word 0x71; word 0x21; word 0x0e; word 0x41; word 0x00; word 0x21; word 0x04; word 0x02; word 0x40; word 0x02; word 0x40; word 0x20; word 0x01; word 0x41; word 0x03; word 0x49; word 0x0d; word 0x00; word 0x20; word 0x0f; word 0x41; word 0x78; word 0x71; word 0x21; word 0x04; word 0x20; word 0x0f; word 0x41; word 0x03; word 0x74; word 0x41; word 0x40; word 0x71; word 0x21; word 0x00; word 0x41; word 0x00; word 0x21; word 0x03; word 0x03; word 0x40; word 0x20; word 0x03; word 0x41; word 0xb8; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0xb0; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0xa8; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0xa0; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0x98; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0x90; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0x88; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0x80; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x00; word 0x20; word 0x03; word 0x41; word 0xc0; word 0x00; word 0x6a; word 0x22; word 0x03; word 0x47; word 0x0d; word 0x00; word 0x0b; word 0x20; word 0x0e; word 0x45; word 0x0d; word 0x01; word 0x0b; word 0x20; word 0x04; word 0x41; word 0x03; word 0x74; word 0x41; word 0x80; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x21; word 0x03; word 0x03; word 0x40; word 0x20; word 0x03; word 0x42; word 0x00; word 0x37; word 0x03; word 0x00; word 0x20; word 0x03; word 0x41; word 0x08; word 0x6a; word 0x21; word 0x03; word 0x20; word 0x0e; word 0x41; word 0x7f; word 0x6a; word 0x22; word 0x0e; word 0x0d; word 0x00; word 0x0b; word 0x0b; word 0x20; word 0x02; word 0x41; word 0x7f; word 0x6a; word 0x21; word 0x10; word 0x41; word 0x00; word 0x21; word 0x03; word 0x41; word 0x80; word 0x80; word 0xf9; word 0x00; word 0x21; word 0x11; word 0x41; word 0x94; word 0x80; word 0xf8; word 0x00; word 0x21; word 0x12; word 0x41; word 0xc4; word 0x82; word 0x01; word 0x21; word 0x13; word 0x03; word 0x40; word 0x20; word 0x03; word 0x41; word 0x03; word 0x6c; word 0x22; word 0x14; word 0x41; word 0x02; word 0x6a; word 0x21; word 0x15; word 0x20; word 0x14; word 0x41; word 0x01; word 0x6a; word 0x21; word 0x16; word 0x42; word 0x00; word 0x21; word 0x17; word 0x42; word 0x00; word 0x21; word 0x18; word 0x42; word 0x00; word 0x21; word 0x19; word 0x02; word 0x40; word 0x20; word 0x03; word 0x41; word 0x01; word 0x6a; word 0x22; word 0x1a; word 0x20; word 0x02; word 0x4f; word 0x0d; word 0x00; word 0x20; word 0x03; word 0x41; word 0x02; word 0x74; word 0x41; word 0xc0; word 0x82; word 0x01; word 0x6a; word 0x34; word 0x02; word 0x00; word 0x21; word 0x1b; word 0x20; word 0x14; word 0x41; word 0x02; word 0x74; word 0x34; word 0x02; word 0x80; word 0x80; word 0x78; word 0x21; word 0x0b; word 0x20; word 0x15; word 0x41; word 0x02; word 0x74; word 0x34; word 0x02; word 0x80; word 0x80; word 0x78; word 0x21; word 0x0c; word 0x20; word 0x16; word 0x41; word 0x02; word 0x74; word 0x34; word 0x02; word 0x80; word 0x80; word 0x78; word 0x21; word 0x0a; word 0x42; word 0x00; word 0x21; word 0x19; word 0x20; word 0x10; word 0x21; word 0x06; word 0x20; word 0x13; word 0x21; word 0x00; word 0x20; word 0x12; word 0x21; word 0x03; word 0x20; word 0x11; word 0x21; word 0x0e; word 0x42; word 0x00; word 0x21; word 0x18; word 0x42; word 0x00; word 0x21; word 0x17; word 0x03; word 0x40; word 0x20; word 0x0e; word 0x41; word 0x18; word 0x6a; word 0x22; word 0x04; word 0x42; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x20; word 0x42; word 0xc3; word 0xeb; word 0xa3; word 0x81; word 0x04; word 0x20; word 0x03; word 0x41; word 0x7c; word 0x6a; word 0x34; word 0x02; word 0x00; word 0x22; word 0x0d; word 0x20; word 0x0a; word 0x7e; word 0x20; word 0x03; word 0x41; word 0x78; word 0x6a; word 0x34; word 0x02; word 0x00; word 0x22; word 0x05; word 0x20; word 0x0b; word 0x7e; word 0x7c; word 0x20; word 0x03; word 0x34; word 0x02; word 0x00; word 0x22; word 0x07; word 0x20; word 0x0c; word 0x7e; word 0x7c; word 0x42; word 0x1e; word 0x87; word 0x7d; word 0x22; word 0x09; word 0x42; word 0xc3; word 0xeb; word 0xa3; word 0x01; word 0x20; word 0x09; word 0x42; word 0xc3; word 0xeb; word 0xa3; word 0x01; word 0x55; word 0x1b; word 0x80; word 0x22; word 0x1c; word 0x20; word 0x1b; word 0x7e; word 0x42; word 0x14; word 0x87; word 0x22; word 0x09; word 0x42; word 0x00; word 0x20; word 0x0d; word 0x20; word 0x0c; word 0x7e; word 0x20; word 0x07; word 0x20; word 0x0a; word 0x7e; word 0x7d; word 0x22; word 0x1d; word 0x7d; word 0x42; word 0x24; word 0x87; word 0x7e; word 0x42; word 0x0c; word 0x87; word 0x20; word 0x04; word 0x29; word 0x03; word 0x00; word 0x7c; word 0x37; word 0x03; word 0x00; word 0x20; word 0x0e; word 0x41; word 0x20; word 0x6a; word 0x22; word 0x08; word 0x20; word 0x09; word 0x42; word 0x00; word 0x20; word 0x07; word 0x20; word 0x0b; word 0x7e; word 0x20; word 0x05; word 0x20; word 0x0c; word 0x7e; word 0x7d; word 0x22; word 0x07; word 0x7d; word 0x42; word 0x24; word 0x87; word 0x7e; word 0x42; word 0x0c; word 0x87; word 0x20; word 0x08; word 0x29; word 0x03; word 0x00; word 0x7c; word 0x37; word 0x03; word 0x00; word 0x20; word 0x0e; word 0x41; word 0x28; word 0x6a; word 0x22; word 0x0e; word 0x20; word 0x0e; word 0x29; word 0x03; word 0x00; word 0x20; word 0x09; word 0x42; word 0x00; word 0x20; word 0x05; word 0x20; word 0x0a; word 0x7e; word 0x20; word 0x0d; word 0x20; word 0x0b; word 0x7e; word 0x7d; word 0x22; word 0x05; word 0x7d; word 0x42; word 0x24; word 0x87; word 0x7e; word 0x42; word 0x0c; word 0x87; word 0x7c; word 0x37; word 0x03; word 0x00; word 0x20; word 0x1c; word 0x20; word 0x00; word 0x34; word 0x02; word 0x00; word 0x7e; word 0x42; word 0x14; word 0x87; word 0x22; word 0x0d; word 0x20; word 0x05; word 0x42; word 0x24; word 0x87; word 0x7e; word 0x42; word 0x0c; word 0x87; word 0x20; word 0x17; word 0x7c; word 0x21; word 0x17; word 0x20; word 0x0d; word 0x20; word 0x07; word 0x42; word 0x24; word 0x87; word 0x7e; word 0x42; word 0x0c; word 0x87; word 0x20; word 0x18; word 0x7c; word 0x21; word 0x18; word 0x20; word 0x0d; word 0x20; word 0x1d; word 0x42; word 0x24; word 0x87; word 0x7e; word 0x42; word 0x0c; word 0x87; word 0x20; word 0x19; word 0x7c; word 0x21; word 0x19; word 0x20; word 0x00; word 0x41; word 0x04; word 0x6a; word 0x21; word 0x00; word 0x20; word 0x03; word 0x41; word 0x0c; word 0x6a; word 0x21; word 0x03; word 0x20; word 0x04; word 0x21; word 0x0e; word 0x20; word 0x06; word 0x41; word 0x7f; word 0x6a; word 0x22; word 0x06; word 0x0d; word 0x00; word 0x0b; word 0x0b; word 0x20; word 0x14; word 0x41; word 0x03; word 0x74; word 0x22; word 0x03; word 0x20; word 0x03; word 0x29; word 0x03; word 0x80; word 0x80; word 0x79; word 0x20; word 0x19; word 0x7c; word 0x37; word 0x03; word 0x80; word 0x80; word 0x79; word 0x20; word 0x16; word 0x41; word 0x03; word 0x74; word 0x22; word 0x03; word 0x20; word 0x03; word 0x29; word 0x03; word 0x80; word 0x80; word 0x79; word 0x20; word 0x18; word 0x7c; word 0x37; word 0x03; word 0x80; word 0x80; word 0x79; word 0x20; word 0x15; word 0x41; word 0x03; word 0x74; word 0x22; word 0x03; word 0x20; word 0x03; word 0x29; word 0x03; word 0x80; word 0x80; word 0x79; word 0x20; word 0x17; word 0x7c; word 0x37; word 0x03; word 0x80; word 0x80; word 0x79; word 0x20; word 0x10; word 0x41; word 0x7f; word 0x6a; word 0x21; word 0x10; word 0x20; word 0x13; word 0x41; word 0x04; word 0x6a; word 0x21; word 0x13; word 0x20; word 0x12; word 0x41; word 0x0c; word 0x6a; word 0x21; word 0x12; word 0x20; word 0x11; word 0x41; word 0x18; word 0x6a; word 0x21; word 0x11; word 0x20; word 0x1a; word 0x21; word 0x03; word 0x20; word 0x1a; word 0x20; word 0x02; word 0x47; word 0x0d; word 0x00; word 0x0b; word 0x20; word 0x0f; word 0x41; word 0x03; word 0x71; word 0x21; word 0x00; word 0x41; word 0x00; word 0x21; word 0x06; word 0x02; word 0x40; word 0x20; word 0x01; word 0x41; word 0x01; word 0x46; word 0x0d; word 0x00; word 0x20; word 0x0f; word 0x41; word 0x7c; word 0x71; word 0x21; word 0x06; word 0x20; word 0x0f; word 0x41; word 0x03; word 0x74; word 0x41; word 0x60; word 0x71; word 0x21; word 0x04; word 0x41; word 0x00; word 0x21; word 0x03; word 0x41; word 0x80; word 0xc0; word 0xf8; word 0x00; word 0x21; word 0x0e; word 0x03; word 0x40; word 0x20; word 0x0e; word 0x20; word 0x03; word 0x41; word 0x80; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x29; word 0x03; word 0x00; word 0x42; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x01; word 0x7c; word 0x42; word 0x24; word 0x87; word 0x3e; word 0x02; word 0x00; word 0x20; word 0x0e; word 0x41; word 0x04; word 0x6a; word 0x20; word 0x03; word 0x41; word 0x88; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x29; word 0x03; word 0x00; word 0x42; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x01; word 0x7c; word 0x42; word 0x24; word 0x87; word 0x3e; word 0x02; word 0x00; word 0x20; word 0x0e; word 0x41; word 0x08; word 0x6a; word 0x20; word 0x03; word 0x41; word 0x90; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x29; word 0x03; word 0x00; word 0x42; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x01; word 0x7c; word 0x42; word 0x24; word 0x87; word 0x3e; word 0x02; word 0x00; word 0x20; word 0x0e; word 0x41; word 0x0c; word 0x6a; word 0x20; word 0x03; word 0x41; word 0x98; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x29; word 0x03; word 0x00; word 0x42; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x01; word 0x7c; word 0x42; word 0x24; word 0x87; word 0x3e; word 0x02; word 0x00; word 0x20; word 0x0e; word 0x41; word 0x10; word 0x6a; word 0x21; word 0x0e; word 0x20; word 0x04; word 0x20; word 0x03; word 0x41; word 0x20; word 0x6a; word 0x22; word 0x03; word 0x47; word 0x0d; word 0x00; word 0x0b; word 0x20; word 0x00; word 0x45; word 0x0d; word 0x01; word 0x0b; word 0x20; word 0x06; word 0x41; word 0x03; word 0x74; word 0x41; word 0x80; word 0x80; word 0xf9; word 0x00; word 0x6a; word 0x21; word 0x03; word 0x20; word 0x06; word 0x41; word 0x02; word 0x74; word 0x41; word 0x80; word 0xc0; word 0xf8; word 0x00; word 0x6a; word 0x21; word 0x0e; word 0x03; word 0x40; word 0x20; word 0x0e; word 0x20; word 0x03; word 0x29; word 0x03; word 0x00; word 0x42; word 0x80; word 0x80; word 0x80; word 0x80; word 0x80; word 0x01; word 0x7c; word 0x42; word 0x24; word 0x87; word 0x3e; word 0x02; word 0x00; word 0x20; word 0x03; word 0x41; word 0x08; word 0x6a; word 0x21; word 0x03; word 0x20; word 0x0e; word 0x41; word 0x04; word 0x6a; word 0x21; word 0x0e; word 0x20; word 0x00; word 0x41; word 0x7f; word 0x6a; word 0x22; word 0x00; word 0x0d; word 0x00; word 0x0b; word 0x0b; word 0x02; word 0x40; word 0x41; word 0x00; word 0x28; word 0x02; word 0x84; word 0x82; word 0x01; word 0x22; word 0x03; word 0x45; word 0x0d; word 0x00; word 0x20; word 0x03; word 0x41; word 0x80; word 0x05; word 0x20; word 0x03; word 0x41; word 0x80; word 0x05; word 0x49; word 0x1b; word 0x41; word 0x03; word 0x6c; word 0x22; word 0x03; word 0x41; word 0xfe; word 0x1f; word 0x71; word 0x21; word 0x04; word 0x20; word 0x03; word 0x41; word 0x01; word 0x71; word 0x21; word 0x02; word 0x41; word 0x80; word 0x80; word 0xc4; word 0x00; word 0x21; word 0x03; word 0x41; word 0x80; word 0xc0; word 0xc4; word 0x00; word 0x21; word 0x0e; word 0x41; word 0x80; word 0xc0; word 0xf8; word 0x00; word 0x21; word 0x00; word 0x03; word 0x40; word 0x20; word 0x03; word 0x28; word 0x02; word 0x00; word 0x21; word 0x06; word 0x20; word 0x03; word 0x20; word 0x0e; word 0x28; word 0x02; word 0x00; word 0x20; word 0x00; word 0x28; word 0x02; word 0x00; word 0x6b; word 0x36; word 0x02; word 0x00; word 0x20; word 0x0e; word 0x20; word 0x06; word 0x36; word 0x02; word 0x00; word 0x20; word 0x03; word 0x41; word 0x04; word 0x6a; word 0x22; word 0x06; word 0x28; word 0x02; word 0x00; word 0x21; word 0x08; word 0x20; word 0x06; word 0x20; word 0x0e; word 0x41; word 0x04; word 0x6a; word 0x22; word 0x14; word 0x28; word 0x02; word 0x00; word 0x20; word 0x00; word 0x41; word 0x04; word 0x6a; word 0x28; word 0x02; word 0x00; word 0x6b; word 0x36; word 0x02; word 0x00; word 0x20; word 0x14; word 0x20; word 0x08; word 0x36; word 0x02; word 0x00; word 0x20; word 0x00; word 0x41; word 0x08; word 0x6a; word 0x21; word 0x00; word 0x20; word 0x0e; word 0x41; word 0x08; word 0x6a; word 0x21; word 0x0e; word 0x20; word 0x03; word 0x41; word 0x08; word 0x6a; word 0x21; word 0x03; word 0x20; word 0x04; word 0x41; word 0x7e; word 0x6a; word 0x22; word 0x04; word 0x0d; word 0x00; word 0x0b; word 0x20; word 0x02; word 0x45; word 0x0d; word 0x00; word 0x20; word 0x03; word 0x28; word 0x02; word 0x00; word 0x21; word 0x04; word 0x20; word 0x03; word 0x20; word 0x0e; word 0x28; word 0x02; word 0x00; word 0x20; word 0x00; word 0x28; word 0x02; word 0x00; word 0x6b; word 0x36; word 0x02; word 0x00; word 0x20; word 0x0e; word 0x20; word 0x04; word 0x36; word 0x02; word 0x00; word 0x0b; word 0x0b]`;;
(* define'd recursive helpers: their meaning is pinned by the CLAUSES theorems above *)
allow ve_fredkin_fwdn;;
allow ve_fredkin_bwdn;;
allow ve_kd_fwdn;;
allow ve_kd_bwdn;;
allow ve_run;;
allow ve_unrun;;
allow ve_runok;;
allow ve_push;;
allow ve_unb;;
allow ve_step_fwdn;;
allow ve_step_bwdn;;
