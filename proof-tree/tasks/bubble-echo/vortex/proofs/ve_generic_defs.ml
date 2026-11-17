(* ========================================================================= *)
(* Vortex Echo v1 (tasks/bubble-echo/vortex): model-level definitions of the *)
(* reversible tick, for ve_generic.ml (the theorems) and ve_unbirth_mutant.ml *)
(* (the control). Pure HOL; nothing here mentions the WASM module.           *)
(*                                                                           *)
(* Vectors are num -> int32 (index -> 32-bit word); + and - are word_add and *)
(* word_sub (WASM i32 wrap-around). Kernels (f, K, D, ...) are arbitrary HOL *)
(* functions: nonlinear, rounding inside them is irrelevant, because each    *)
(* backward update subtracts the increment recomputed from the same inputs.  *)
(*                                                                           *)
(* Statement constants are new_definition (pinned verbatim in the specs);    *)
(* the recursive helpers are made by define and pinned by CLAUSES theorems.  *)
(* ========================================================================= *)

(* ---- 1. Fredkin pair step: (a,b) -> (b, a + f b); back (a,b) -> (b - f a, a) *)

let ve_fredkin_fwd = new_definition
 `ve_fredkin_fwd (f:(num->int32)->num->int32) (s:(num->int32)#(num->int32)) =
    (SND s,(\m. word_add (FST s m) (f (SND s) m)))`;;

let ve_fredkin_bwd = new_definition
 `ve_fredkin_bwd (f:(num->int32)->num->int32) (s:(num->int32)#(num->int32)) =
    ((\m. word_sub (SND s m) (f (FST s) m)),FST s)`;;

(* n substeps; substep i uses f i (the vortex substeps use one f for all i). *)
(* Backward undoes substep n-1 first.                                        *)
let ve_fredkin_fwdn = define
 `(ve_fredkin_fwdn (f:num->(num->int32)->num->int32) 0 (s:(num->int32)#(num->int32)) = s) /\
  (ve_fredkin_fwdn f (SUC n) s = ve_fredkin_fwd (f n) (ve_fredkin_fwdn f n s))`;;

let ve_fredkin_bwdn = define
 `(ve_fredkin_bwdn (f:num->(num->int32)->num->int32) 0 (s:(num->int32)#(num->int32)) = s) /\
  (ve_fredkin_bwdn f (SUC n) s = ve_fredkin_bwdn f n (ve_fredkin_bwd (f n) s))`;;

(* ---- 2. kick-drift: the kick reads q only, updates p; the drift reads p    *)
(* only, updates q. State (q,p). Read-only parameters are curried into K, D. *)

let ve_kd_fwd = new_definition
 `ve_kd_fwd (K:(num->int32)->num->int32) (D:(num->int32)->num->int32)
            (s:(num->int32)#(num->int32)) =
    let p1 = (\m. word_add (SND s m) (K (FST s) m)) in
    ((\m. word_add (FST s m) (D p1 m)),p1)`;;

let ve_kd_bwd = new_definition
 `ve_kd_bwd (K:(num->int32)->num->int32) (D:(num->int32)->num->int32)
            (s:(num->int32)#(num->int32)) =
    let q = (\m. word_sub (FST s m) (D (SND s) m)) in
    (q,(\m. word_sub (SND s m) (K q m)))`;;

let ve_kd_fwdn = define
 `(ve_kd_fwdn (K:num->(num->int32)->num->int32) (D:num->(num->int32)->num->int32) 0
              (s:(num->int32)#(num->int32)) = s) /\
  (ve_kd_fwdn K D (SUC n) s = ve_kd_fwd (K n) (D n) (ve_kd_fwdn K D n s))`;;

let ve_kd_bwdn = define
 `(ve_kd_bwdn (K:num->(num->int32)->num->int32) (D:num->(num->int32)->num->int32) 0
              (s:(num->int32)#(num->int32)) = s) /\
  (ve_kd_bwdn K D (SUC n) s = ve_kd_bwdn K D n (ve_kd_bwd (K n) (D n) s))`;;

(* ---- 3. composition of pieces (forward f, backward g, precondition P):    *)
(* ve_run applies the forward maps head first; ve_unrun applies the backward *)
(* maps in reverse order; ve_runok says each P holds where its f is applied. *)

let ve_run = define
 `(ve_run ([]:((A->A)#(A->A)#(A->bool))list) (s:A) = s) /\
  (ve_run (CONS p ps) s = ve_run ps (FST p s))`;;

let ve_unrun = define
 `(ve_unrun ([]:((A->A)#(A->A)#(A->bool))list) (s:A) = s) /\
  (ve_unrun (CONS p ps) s = FST (SND p) (ve_unrun ps s))`;;

let ve_runok = define
 `(ve_runok ([]:((A->A)#(A->A)#(A->bool))list) (s:A) <=> T) /\
  (ve_runok (CONS p ps) s <=> SND (SND p) s /\ ve_runok ps (FST p s))`;;

(* ---- 4. droplet births on a last-in-first-out log.                        *)
(* Births state (zq, zp, dq, dp, cnt, slots): corrugation heights zq and     *)
(* rates zp (one word per rim bead), droplet positions dq and velocities dp  *)
(* (3 words per droplet slot), the record count cnt and the records. A       *)
(* record is (parent bead, dz, deta, birth tick, payload words). A birth     *)
(* item is (parent, dz, deta, payload); payload words 0..2 / 3..5 are the    *)
(* droplet's initial position / velocity.                                    *)

let ve_zrec = new_definition
 `ve_zrec = (0,word 0,word 0,0,(\j:num. word 0)):num#int32#int32#num#(num->int32)`;;

let ve_rbirth = new_definition
 `ve_rbirth (r:num#int32#int32#num#(num->int32)) = FST(SND(SND(SND r)))`;;

let ve_zq = new_definition
 `ve_zq (s:(num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST s`;;

let ve_zp = new_definition
 `ve_zp (s:(num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST(SND s)`;;

let ve_dq = new_definition
 `ve_dq (s:(num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST(SND(SND s))`;;

let ve_dp = new_definition
 `ve_dp (s:(num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST(SND(SND(SND s)))`;;

let ve_cnt = new_definition
 `ve_cnt (s:(num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST(SND(SND(SND(SND s))))`;;

let ve_slots = new_definition
 `ve_slots (s:(num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    SND(SND(SND(SND(SND s))))`;;

(* one birth at tick t: the parent loses (dz, deta), the droplet slot cnt    *)
(* gets its initial position and velocity, the record is pushed with birth   *)
(* tick t + 1.                                                               *)
let ve_push1 = new_definition
 `ve_push1 (t:num) (b:num#int32#int32#(num->int32)) s =
    let c = ve_cnt s in let k = FST b in let dz = FST(SND b) in
    let de = FST(SND(SND b)) in let pay = SND(SND(SND b)) in
    ((\i. if i = k then word_sub (ve_zq s i) dz else ve_zq s i),
     (\i. if i = k then word_sub (ve_zp s i) de else ve_zp s i),
     (\m. if 3 * c <= m /\ m < 3 * c + 3 then pay (m - 3 * c) else ve_dq s m),
     (\m. if 3 * c <= m /\ m < 3 * c + 3 then pay (m - 3 * c + 3) else ve_dp s m),
     c + 1,
     (\i. if i = c then (k,dz,de,t + 1,pay) else ve_slots s i))`;;

(* one un-birth: pop the top record, give its parent back (dz, deta), zero   *)
(* the freed record and the droplet's words.                                 *)
let ve_pop1 = new_definition
 `ve_pop1 s =
    let c = ve_cnt s - 1 in let r = ve_slots s c in
    let k = FST r in let dz = FST(SND r) in let de = FST(SND(SND r)) in
    ((\i. if i = k then word_add (ve_zq s i) dz else ve_zq s i),
     (\i. if i = k then word_add (ve_zp s i) de else ve_zp s i),
     (\m. if 3 * c <= m /\ m < 3 * c + 3 then word 0 else ve_dq s m),
     (\m. if 3 * c <= m /\ m < 3 * c + 3 then word 0 else ve_dp s m),
     c,
     (\i. if i = c then ve_zrec else ve_slots s i))`;;

(* the births of one tick, in list order *)
let ve_push = define
 `(ve_push (t:num) ([]:(num#int32#int32#(num->int32))list)
           (s:(num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) = s) /\
  (ve_push t (CONS b bs) s = ve_push t bs (ve_push1 t b s))`;;

(* pop while the top record has birth tick tt (at most n records) *)
let ve_unb = define
 `(ve_unb (tt:num) 0
          (s:(num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) = s) /\
  (ve_unb tt (SUC n) s =
     if 0 < ve_cnt s /\ ve_rbirth (ve_slots s (ve_cnt s - 1)) = tt
     then ve_unb tt n (ve_pop1 s) else s)`;;

(* forward births at tick t: a deterministic list B s of births *)
let ve_births_fwd = new_definition
 `ve_births_fwd (B:(num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))
                   ->(num#int32#int32#(num->int32))list) (t:num) s =
    ve_push t (B s) s`;;

(* backward births at tick tt: pop every record born at tt *)
let ve_births_bwd = new_definition
 `ve_births_bwd (tt:num) s = ve_unb tt (ve_cnt s) s`;;

(* records and droplet words above the count are zero *)
let ve_free = new_definition
 `ve_free s <=> (!i. ve_cnt s <= i ==> ve_slots s i = ve_zrec) /\
                (!m. 3 * ve_cnt s <= m ==> ve_dq s m = word 0 /\ ve_dp s m = word 0)`;;

(* the named premise of the births lemma: at tick t every record on the log  *)
(* has birth tick <= t, and the log is clean above the count.                *)
let ve_log_ok = new_definition
 `ve_log_ok (t:num) s <=> (!i. i < ve_cnt s ==> ve_rbirth (ve_slots s i) <= t) /\ ve_free s`;;

(* ---- 5. the whole tick at model level.                                    *)
(* State (t, pt, va, vb, hm, ra, rb, jq, jp, bs): tick, puncture tick (from  *)
(* the event log; read-only), vortex Fredkin pair, thickness map frozen at   *)
(* the puncture, rim Fredkin pair, jiggle ring (q,p), births state (above).  *)

let ve_t = new_definition
 `ve_t (s:num#num#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#
          (num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST s`;;

let ve_pt = new_definition
 `ve_pt (s:num#num#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#
           (num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST(SND s)`;;

let ve_va = new_definition
 `ve_va (s:num#num#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#
           (num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST(SND(SND s))`;;

let ve_vb = new_definition
 `ve_vb (s:num#num#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#
           (num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST(SND(SND(SND s)))`;;

let ve_hm = new_definition
 `ve_hm (s:num#num#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#
           (num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST(SND(SND(SND(SND s))))`;;

let ve_ra = new_definition
 `ve_ra (s:num#num#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#
           (num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST(SND(SND(SND(SND(SND s)))))`;;

let ve_rb = new_definition
 `ve_rb (s:num#num#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#
           (num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST(SND(SND(SND(SND(SND(SND s))))))`;;

let ve_jq = new_definition
 `ve_jq (s:num#num#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#
           (num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST(SND(SND(SND(SND(SND(SND(SND s)))))))`;;

let ve_jp = new_definition
 `ve_jp (s:num#num#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#
           (num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    FST(SND(SND(SND(SND(SND(SND(SND(SND s))))))))`;;

let ve_bs = new_definition
 `ve_bs (s:num#num#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#(num->int32)#
           (num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) =
    SND(SND(SND(SND(SND(SND(SND(SND(SND s))))))))`;;

(* rim Fredkin step; the rim displacement fr reads the frozen thickness map *)
let ve_rim_fwd = new_definition
 `ve_rim_fwd (fr:(num->int32)->(num->int32)->num->int32) s =
    let r = ve_fredkin_fwd (fr (ve_hm s)) (ve_ra s,ve_rb s) in
    (ve_t s,ve_pt s,ve_va s,ve_vb s,ve_hm s,FST r,SND r,ve_jq s,ve_jp s,ve_bs s)`;;

let ve_rim_bwd = new_definition
 `ve_rim_bwd (fr:(num->int32)->(num->int32)->num->int32) s =
    let r = ve_fredkin_bwd (fr (ve_hm s)) (ve_ra s,ve_rb s) in
    (ve_t s,ve_pt s,ve_va s,ve_vb s,ve_hm s,FST r,SND r,ve_jq s,ve_jp s,ve_bs s)`;;

(* jiggle kick-drift; kernels read tick - puncture tick, the map and rb *)
let ve_jig_fwd = new_definition
 `ve_jig_fwd (kj:num->(num->int32)->(num->int32)->(num->int32)->num->int32)
             (dj:num->(num->int32)->(num->int32)->(num->int32)->num->int32) s =
    let tt = ve_t s - ve_pt s in
    let r = ve_kd_fwd (kj tt (ve_hm s) (ve_rb s)) (dj tt (ve_hm s) (ve_rb s)) (ve_jq s,ve_jp s) in
    (ve_t s,ve_pt s,ve_va s,ve_vb s,ve_hm s,ve_ra s,ve_rb s,FST r,SND r,ve_bs s)`;;

let ve_jig_bwd = new_definition
 `ve_jig_bwd (kj:num->(num->int32)->(num->int32)->(num->int32)->num->int32)
             (dj:num->(num->int32)->(num->int32)->(num->int32)->num->int32) s =
    let tt = ve_t s - ve_pt s in
    let r = ve_kd_bwd (kj tt (ve_hm s) (ve_rb s)) (dj tt (ve_hm s) (ve_rb s)) (ve_jq s,ve_jp s) in
    (ve_t s,ve_pt s,ve_va s,ve_vb s,ve_hm s,ve_ra s,ve_rb s,FST r,SND r,ve_bs s)`;;

(* corrugation: nc kick-drift substeps on (zq, zp); kernels read the substep *)
(* index i too                                                               *)
let ve_corr_fwd = new_definition
 `ve_corr_fwd (kc:num->num->(num->int32)->(num->int32)->(num->int32)->num->int32)
              (dc:num->num->(num->int32)->(num->int32)->(num->int32)->num->int32) (nc:num) s =
    let tt = ve_t s - ve_pt s in let b = ve_bs s in
    let r = ve_kd_fwdn (\i. kc tt i (ve_hm s) (ve_rb s)) (\i. dc tt i (ve_hm s) (ve_rb s)) nc
                       (ve_zq b,ve_zp b) in
    (ve_t s,ve_pt s,ve_va s,ve_vb s,ve_hm s,ve_ra s,ve_rb s,ve_jq s,ve_jp s,
     (FST r,SND r,ve_dq b,ve_dp b,ve_cnt b,ve_slots b))`;;

let ve_corr_bwd = new_definition
 `ve_corr_bwd (kc:num->num->(num->int32)->(num->int32)->(num->int32)->num->int32)
              (dc:num->num->(num->int32)->(num->int32)->(num->int32)->num->int32) (nc:num) s =
    let tt = ve_t s - ve_pt s in let b = ve_bs s in
    let r = ve_kd_bwdn (\i. kc tt i (ve_hm s) (ve_rb s)) (\i. dc tt i (ve_hm s) (ve_rb s)) nc
                       (ve_zq b,ve_zp b) in
    (ve_t s,ve_pt s,ve_va s,ve_vb s,ve_hm s,ve_ra s,ve_rb s,ve_jq s,ve_jp s,
     (FST r,SND r,ve_dq b,ve_dp b,ve_cnt b,ve_slots b))`;;

(* droplets: one kick-drift on (dq, dp), acting on the active slots only *)
let ve_dmask = new_definition
 `ve_dmask (c:num) (g:(num->int32)->num->int32) (v:num->int32) (m:num) =
    if m < 3 * c then g v m else word 0`;;

let ve_drop_fwd = new_definition
 `ve_drop_fwd (kd:num->num->(num->int32)->num->int32) (dd:num->num->(num->int32)->num->int32) s =
    let tt = ve_t s - ve_pt s in let b = ve_bs s in let c = ve_cnt b in
    let r = ve_kd_fwd (ve_dmask c (kd tt c)) (ve_dmask c (dd tt c)) (ve_dq b,ve_dp b) in
    (ve_t s,ve_pt s,ve_va s,ve_vb s,ve_hm s,ve_ra s,ve_rb s,ve_jq s,ve_jp s,
     (ve_zq b,ve_zp b,FST r,SND r,c,ve_slots b))`;;

let ve_drop_bwd = new_definition
 `ve_drop_bwd (kd:num->num->(num->int32)->num->int32) (dd:num->num->(num->int32)->num->int32) s =
    let tt = ve_t s - ve_pt s in let b = ve_bs s in let c = ve_cnt b in
    let r = ve_kd_bwd (ve_dmask c (kd tt c)) (ve_dmask c (dd tt c)) (ve_dq b,ve_dp b) in
    (ve_t s,ve_pt s,ve_va s,ve_vb s,ve_hm s,ve_ra s,ve_rb s,ve_jq s,ve_jp s,
     (ve_zq b,ve_zp b,FST r,SND r,c,ve_slots b))`;;

(* births: the list bf s may read the whole state; stamped t + 1 *)
let ve_birth_fwd = new_definition
 `ve_birth_fwd bf s =
    (ve_t s,ve_pt s,ve_va s,ve_vb s,ve_hm s,ve_ra s,ve_rb s,ve_jq s,ve_jp s,
     ve_push (ve_t s) (bf s) (ve_bs s))`;;

(* un-births, run after the tick has been stepped back to t: pop birth t + 1 *)
let ve_birth_bwd = new_definition
 `ve_birth_bwd s =
    (ve_t s,ve_pt s,ve_va s,ve_vb s,ve_hm s,ve_ra s,ve_rb s,ve_jq s,ve_jp s,
     ve_births_bwd (ve_t s + 1) (ve_bs s))`;;

(* n vortex Fredkin substeps with one kernel fv *)
let ve_vort_fwd = new_definition
 `ve_vort_fwd (fv:(num->int32)->num->int32) (n:num) s =
    let r = ve_fredkin_fwdn (\i. fv) n (ve_va s,ve_vb s) in
    (ve_t s,ve_pt s,FST r,SND r,ve_hm s,ve_ra s,ve_rb s,ve_jq s,ve_jp s,ve_bs s)`;;

let ve_vort_bwd = new_definition
 `ve_vort_bwd (fv:(num->int32)->num->int32) (n:num) s =
    let r = ve_fredkin_bwdn (\i. fv) n (ve_va s,ve_vb s) in
    (ve_t s,ve_pt s,FST r,SND r,ve_hm s,ve_ra s,ve_rb s,ve_jq s,ve_jp s,ve_bs s)`;;

let ve_tick_fwd = new_definition
 `ve_tick_fwd s =
    (ve_t s + 1,ve_pt s,ve_va s,ve_vb s,ve_hm s,ve_ra s,ve_rb s,ve_jq s,ve_jp s,ve_bs s)`;;

let ve_tick_bwd = new_definition
 `ve_tick_bwd s =
    (ve_t s - 1,ve_pt s,ve_va s,ve_vb s,ve_hm s,ve_ra s,ve_rb s,ve_jq s,ve_jp s,ve_bs s)`;;

(* the puncture, when the tick reaches pt: i0 s gives the initial pop state  *)
(* (map, rim pair, jiggle ring, corrugation ring); the log stays as it is    *)
let ve_punct = new_definition
 `ve_punct i0 s =
    if ve_t s = ve_pt s then
      let z = i0 s in let b = ve_bs s in
      (ve_t s,ve_pt s,ve_va s,ve_vb s,FST z,FST(SND z),FST(SND(SND z)),FST(SND(SND(SND z))),
       FST(SND(SND(SND(SND z)))),
       (FST(SND(SND(SND(SND(SND z))))),SND(SND(SND(SND(SND(SND z))))),ve_dq b,ve_dp b,ve_cnt b,ve_slots b))
    else s`;;

(* the un-puncture, stepping back onto pt: the pop state becomes zero again *)
let ve_unpunct = new_definition
 `ve_unpunct s =
    if ve_t s = ve_pt s then
      (ve_t s,ve_pt s,ve_va s,ve_vb s,(\m. word 0),(\m. word 0),(\m. word 0),(\m. word 0),(\m. word 0),
       ((\m. word 0),(\m. word 0),(\m. word 0),(\m. word 0),0,(\i. ve_zrec)))
    else s`;;

(* the pop state is zero (the state before the puncture) *)
let ve_pop_zero = new_definition
 `ve_pop_zero s <=>
    ve_hm s = (\m. word 0) /\ ve_ra s = (\m. word 0) /\ ve_rb s = (\m. word 0) /\
    ve_jq s = (\m. word 0) /\ ve_jp s = (\m. word 0) /\
    ve_bs s = ((\m. word 0),(\m. word 0),(\m. word 0),(\m. word 0),0,(\i. ve_zrec))`;;

(* one tick forward. Pop tick (pt <= t): rim, jiggle, nc corrugation        *)
(* substeps, droplets, births, npo vortex substeps, tick + 1. Swirl tick:    *)
(* nsw vortex substeps, tick + 1, then the puncture if the new tick is pt.  *)
let ve_step_fwd = new_definition
 `ve_step_fwd fr kj dj kc dc kd dd bf fv i0 (nc:num) (nsw:num) (npo:num) s =
    if ve_pt s <= ve_t s
    then ve_tick_fwd (ve_vort_fwd fv npo (ve_birth_fwd bf (ve_drop_fwd kd dd
           (ve_corr_fwd kc dc nc (ve_jig_fwd kj dj (ve_rim_fwd fr s))))))
    else ve_punct i0 (ve_tick_fwd (ve_vort_fwd fv nsw s))`;;

(* one tick backward: the exact reverse (nothing at tick 0) *)
let ve_step_bwd = new_definition
 `ve_step_bwd fr kj dj kc dc kd dd fv (nc:num) (nsw:num) (npo:num) s =
    if ve_t s = 0 then s
    else if ve_pt s < ve_t s
    then ve_rim_bwd fr (ve_jig_bwd kj dj (ve_corr_bwd kc dc nc (ve_drop_bwd kd dd
           (ve_birth_bwd (ve_vort_bwd fv npo (ve_tick_bwd s))))))
    else ve_vort_bwd fv nsw (ve_tick_bwd (ve_unpunct s))`;;

(* the named premise of one tick: the log premise on pop ticks, and a zero  *)
(* pop state before the puncture tick                                        *)
let ve_step_ok = new_definition
 `ve_step_ok s <=> (ve_pt s <= ve_t s ==> ve_log_ok (ve_t s) (ve_bs s)) /\
                   (ve_t s + 1 = ve_pt s ==> ve_pop_zero s)`;;

(* the invariant of a run (kept by every forward tick) *)
let ve_run_ok = new_definition
 `ve_run_ok s <=> (ve_pt s <= ve_t s ==> ve_log_ok (ve_t s) (ve_bs s)) /\
                  (ve_t s < ve_pt s ==> ve_pop_zero s)`;;

let ve_step_fwdn = define
 `(ve_step_fwdn fr kj dj kc dc kd dd bf fv i0 nc nsw npo 0 s = s) /\
  (ve_step_fwdn fr kj dj kc dc kd dd bf fv i0 nc nsw npo (SUC n) s =
     ve_step_fwd fr kj dj kc dc kd dd bf fv i0 nc nsw npo
       (ve_step_fwdn fr kj dj kc dc kd dd bf fv i0 nc nsw npo n s))`;;

let ve_step_bwdn = define
 `(ve_step_bwdn fr kj dj kc dc kd dd fv nc nsw npo 0 s = s) /\
  (ve_step_bwdn fr kj dj kc dc kd dd fv nc nsw npo (SUC n) s =
     ve_step_bwdn fr kj dj kc dc kd dd fv nc nsw npo n
       (ve_step_bwd fr kj dj kc dc kd dd fv nc nsw npo s))`;;
