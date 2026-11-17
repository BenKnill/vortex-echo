(* ========================================================================= *)
(* Vortex Echo v1: the un-birth mutant of the Phase 1 control (mutant=1):    *)
(* popping a record gives the parent back its height dz but forgets the     *)
(* stored rate deta. Used only by the control leaf ve_unbirth_mutant.ml.    *)
(* ========================================================================= *)

let ve_pop1_mut = new_definition
 `ve_pop1_mut s =
    let c = ve_cnt s - 1 in let r = ve_slots s c in
    let k = FST r in let dz = FST(SND r) in
    ((\i. if i = k then word_add (ve_zq s i) dz else ve_zq s i),
     ve_zp s,
     (\m. if 3 * c <= m /\ m < 3 * c + 3 then word 0 else ve_dq s m),
     (\m. if 3 * c <= m /\ m < 3 * c + 3 then word 0 else ve_dp s m),
     c,
     (\i. if i = c then ve_zrec else ve_slots s i))`;;

let ve_unb_mut = define
 `(ve_unb_mut (tt:num) 0
          (s:(num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))) = s) /\
  (ve_unb_mut tt (SUC n) s =
     if 0 < ve_cnt s /\ ve_rbirth (ve_slots s (ve_cnt s - 1)) = tt
     then ve_unb_mut tt n (ve_pop1_mut s) else s)`;;

let ve_births_bwd_mut = new_definition
 `ve_births_bwd_mut (tt:num) s = ve_unb_mut tt (ve_cnt s) s`;;

(* the zero births state: no records, all words zero *)
let ve_bzero = new_definition
 `ve_bzero = ((\m:num. word 0:int32),(\m:num. word 0:int32),(\m:num. word 0:int32),(\m:num. word 0:int32),0,
              (\i:num. ve_zrec))`;;
