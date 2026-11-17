(* Spec: Vortex Echo v1 (tasks/bubble-echo/vortex), the reversible tick at model level, pure HOL (no bytes); vectors num -> int32 with word_add / word_sub. (1) Fredkin pair step (a,b) -> (b, a + f b) and its inverse, one step and n substeps, any f; (2) kick-drift (kick reads q, updates p; drift reads p, updates q), one and n substeps, any K, D; (3) composition: reversed backward pieces invert the forward composition when each piece has a left inverse under a precondition that holds along the trajectory; (4) droplet births on a LIFO log: pushing a tick's births (birth tick t + 1, parent loses dz/deta, droplet words written) then popping every record born at t + 1 restores the state, under the named premise ve_log_ok t (records born <= t, log clean above the count); (5) the whole tick (rim Fredkin, jiggle kick-drift, nc corrugation kick-drift substeps, droplet kick-drift on the active slots, births, vortex Fredkin substeps: npo on pop ticks, nsw on swirl ticks; puncture at the event-log tick pt) with kernels as arbitrary functions: backward after forward is the identity under the named premise ve_step_ok, and over n ticks under the invariant ve_run_ok, which every forward tick keeps. *)
theorem FREDKIN_STEP_INVERSE
 `!f s. ve_fredkin_bwd f (ve_fredkin_fwd f s) = s`;;
theorem FREDKIN_STEP_FWD_BWD
 `!f s. ve_fredkin_fwd f (ve_fredkin_bwd f s) = s`;;
theorem VE_FREDKIN_FWDN_CLAUSES
 `(!f s. ve_fredkin_fwdn f 0 s = s) /\
   (!f n s. ve_fredkin_fwdn f (SUC n) s = ve_fredkin_fwd (f n) (ve_fredkin_fwdn f n s))`;;
theorem VE_FREDKIN_BWDN_CLAUSES
 `(!f s. ve_fredkin_bwdn f 0 s = s) /\
   (!f n s. ve_fredkin_bwdn f (SUC n) s = ve_fredkin_bwdn f n (ve_fredkin_bwd (f n) s))`;;
theorem FREDKIN_STEPS_INVERSE
 `!f n s. ve_fredkin_bwdn f n (ve_fredkin_fwdn f n s) = s`;;
theorem FREDKIN_STEPS_FWD_BWD
 `!f n s. ve_fredkin_fwdn f n (ve_fredkin_bwdn f n s) = s`;;
theorem KICK_DRIFT_INVERSE
 `!K D s. ve_kd_bwd K D (ve_kd_fwd K D s) = s`;;
theorem KICK_DRIFT_FWD_BWD
 `!K D s. ve_kd_fwd K D (ve_kd_bwd K D s) = s`;;
theorem VE_KD_FWDN_CLAUSES
 `(!K D s. ve_kd_fwdn K D 0 s = s) /\
   (!K D n s. ve_kd_fwdn K D (SUC n) s = ve_kd_fwd (K n) (D n) (ve_kd_fwdn K D n s))`;;
theorem VE_KD_BWDN_CLAUSES
 `(!K D s. ve_kd_bwdn K D 0 s = s) /\
   (!K D n s. ve_kd_bwdn K D (SUC n) s = ve_kd_bwdn K D n (ve_kd_bwd (K n) (D n) s))`;;
theorem KICK_DRIFT_STEPS_INVERSE
 `!K D n s. ve_kd_bwdn K D n (ve_kd_fwdn K D n s) = s`;;
theorem KICK_DRIFT_STEPS_FWD_BWD
 `!K D n s. ve_kd_fwdn K D n (ve_kd_bwdn K D n s) = s`;;
theorem VE_RUN_CLAUSES
 `(!s:A. ve_run [] s = s) /\
   (!(p:(A->A)#(A->A)#(A->bool)) ps s. ve_run (CONS p ps) s = ve_run ps (FST p s)) /\
   (!s:A. ve_unrun [] s = s) /\
   (!(p:(A->A)#(A->A)#(A->bool)) ps s. ve_unrun (CONS p ps) s = FST (SND p) (ve_unrun ps s)) /\
   (!s:A. ve_runok [] s <=> T) /\
   (!(p:(A->A)#(A->A)#(A->bool)) ps s. ve_runok (CONS p ps) s <=> SND (SND p) s /\ ve_runok ps (FST p s))`;;
theorem VE_COMPOSE_INVERSE
 `!(ps:((A->A)#(A->A)#(A->bool))list) (s:A).
     ALL (\p. !x. SND (SND p) x ==> FST (SND p) (FST p x) = x) ps /\ ve_runok ps s
     ==> ve_unrun ps (ve_run ps s) = s`;;
theorem VE_PUSH_CLAUSES
 `(!t s. ve_push t [] s = s) /\
   (!t b bs s. ve_push t (CONS b bs) s = ve_push t bs (ve_push1 t b s)) /\
   (!tt s. ve_unb tt 0 s = s) /\
   (!tt n s. ve_unb tt (SUC n) s =
             if 0 < ve_cnt s /\ ve_rbirth (ve_slots s (ve_cnt s - 1)) = tt
             then ve_unb tt n (ve_pop1 s) else s)`;;
theorem VE_PUSH_INVERSE
 `!L t s. ve_log_ok t s ==> ve_births_bwd (t + 1) (ve_push t L s) = s`;;
theorem LIFO_BIRTHS_INVERSE
 `!B t s. ve_log_ok t s ==> ve_births_bwd (t + 1) (ve_births_fwd B t s) = s`;;
theorem VE_LOG_OK_PUSH
 `!L t s. ve_log_ok t s ==> ve_log_ok (t + 1) (ve_push t L s)`;;
theorem VE_STEP_CLAUSES
 `(!fr kj dj kc dc kd dd bf fv i0 nc nsw npo s. ve_step_fwdn fr kj dj kc dc kd dd bf fv i0 nc nsw npo 0 s = s) /\
   (!fr kj dj kc dc kd dd bf fv i0 nc nsw npo n s. ve_step_fwdn fr kj dj kc dc kd dd bf fv i0 nc nsw npo (SUC n) s =
      ve_step_fwd fr kj dj kc dc kd dd bf fv i0 nc nsw npo (ve_step_fwdn fr kj dj kc dc kd dd bf fv i0 nc nsw npo n s)) /\
   (!fr kj dj kc dc kd dd fv nc nsw npo s. ve_step_bwdn fr kj dj kc dc kd dd fv nc nsw npo 0 s = s) /\
   (!fr kj dj kc dc kd dd fv nc nsw npo n s. ve_step_bwdn fr kj dj kc dc kd dd fv nc nsw npo (SUC n) s =
      ve_step_bwdn fr kj dj kc dc kd dd fv nc nsw npo n (ve_step_bwd fr kj dj kc dc kd dd fv nc nsw npo s))`;;
theorem VE_STEP_INVERSE_MODEL
 `!fr kj dj kc dc kd dd bf fv i0 nc nsw npo s.
     ve_step_ok s
     ==> ve_step_bwd fr kj dj kc dc kd dd fv nc nsw npo (ve_step_fwd fr kj dj kc dc kd dd bf fv i0 nc nsw npo s) = s`;;
theorem VE_STEP_INVERSE_MODEL_V1
 `!fr kj dj kc dc kd dd bf fv i0 s.
     ve_step_ok s
     ==> ve_step_bwd fr kj dj kc dc kd dd fv 4 16 1 (ve_step_fwd fr kj dj kc dc kd dd bf fv i0 4 16 1 s) = s`;;
theorem VE_RUN_OK_STEP_OK
 `!s. ve_run_ok s ==> ve_step_ok s`;;
theorem VE_RUN_OK_STEP
 `!fr kj dj kc dc kd dd bf fv i0 nc nsw npo s.
     ve_run_ok s ==> ve_run_ok (ve_step_fwd fr kj dj kc dc kd dd bf fv i0 nc nsw npo s)`;;
theorem VE_RUN_OK_INIT
 `!s. ve_t s = 0 /\ 0 < ve_pt s /\ ve_pop_zero s ==> ve_run_ok s`;;
theorem VE_RUN_INVERSE_MODEL
 `!fr kj dj kc dc kd dd bf fv i0 nc nsw npo n s.
     ve_run_ok s
     ==> ve_step_bwdn fr kj dj kc dc kd dd fv nc nsw npo n (ve_step_fwdn fr kj dj kc dc kd dd bf fv i0 nc nsw npo n s) = s`;;
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
