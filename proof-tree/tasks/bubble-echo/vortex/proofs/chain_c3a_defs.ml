needs "ve_vort.ml";;
needs "ve_tick.ml";;
needs "ve_vk.ml";;
needs "va1_code.ml";;
needs "va1_seq_final2.ml";;
needs "pop_design_defs.ml";;
needs "pop_design_stmts.ml";;
needs "pop_l2_cdrift.ml";;
needs "pop_l3_jdrift.ml";;
needs "pop_l4_drop.ml";;
needs "pop_l1_rimd.ml";;
needs "pop_l1_rim.ml";;
needs "pop_l5_unbirth.ml";;
needs "pop_h1_hol.ml";;
needs "pop_n1_sat.ml";;
needs "pop_q0_calls.ml";;
needs "pop_q1_untick.ml";;
needs "pop_q2_forward.ml";;
needs "pop_r5_jig_defs.ml";;
needs "pop_r5jig_dec.ml";;
needs "pop_r5jig_lem.ml";;
needs "pop_r5_corr_defs.ml";;
needs "pop_r5c_lem.ml";;
needs "pop_r5b_bdec.ml";;
needs "pop_r5bp_lem.ml";;
needs "pop_r5bp_lem2.ml";;
needs "pop_r5bp_lem3.ml";;
needs "pop_r5bp_lem4.ml";;
needs "pop_r5bp_lem5b.ml";;
needs "pop_r5bp_lem6.ml";;
needs "pop_s0_end.ml";;
needs "pop_r5_r4c_final.ml";;
needs "chain_c1_host.ml";;

(* ========================================================================= *)
(* Vortex chain, rung C3a, layer 1: definitions (C3A agent, Claude Opus 5.5, *)
(* 2026-11-13). Every new definition is the verbatim text of its entry in    *)
(* chain_c3a_final.spec; va1_f26_mc is function #26 of vortex_a1.wasm (the   *)
(* spec pins its byte list). No proofs beyond the entry-pc lint.             *)
(* ========================================================================= *)

let va1_f26_mc = define_from_wasm "va1_f26_mc" "../purist/vortex_a1.wasm" "#26";;  (* ve_unpuncture; 729 B, entry pc 5, 6 locals *)
let VA1_F26_CALLEE_RULE = WASM_CALLEE_RULE va1_f26_mc;;

let va1_rbv = new_definition
 `va1_rbv (tbl:num->int32) (k:num) =
    word_add (word_ishr (word_add (word_mul (word_sub (word_sx (tbl (128 * k + 1)):int64) (word_sx (tbl (128 * k)))) (word 251658)) (word 262144)) 19)
             (word_sx (tbl (128 * k)):int64)`;;

let va1_rbinit = new_definition
 `va1_rbinit (tbl:num->int32) (k:num) =
    word_add (word_zx (word_ushr (word_add (if ival (va1_rbv tbl k) > &1 then va1_rbv tbl k else word 1) (word 1)) 1):int32) (word 251658)`;;

let va1_zpx0 = new_definition
 `va1_zpx0 (mdl:num->int32) (k:num) =
    word_xor (word_add (word_mul (mdl 2) (word 3266489909)) (word 2769733223))
             (word_mul (word_xor (word k) (word 2654435769)) (word 2246822507)):int32`;;

let va1_zpx1 = new_definition
 `va1_zpx1 (mdl:num->int32) (k:num) =
    word_mul (word_xor (word_ushr (va1_zpx0 mdl k) 15) (va1_zpx0 mdl k)) (word 739982445):int32`;;

let va1_zpseed = new_definition
 `va1_zpseed (mdl:num->int32) (k:num) =
    word_zx (word_ishr (word_add (word_mul (word_zx (word_xor (word_ushr (va1_zpx1 mdl k) 12) (va1_zpx1 mdl k)):int64) (word 329853))
                                 (word 18446176457274163200)) 48):int32`;;

let va1_mis = new_definition
 `va1_mis (mdl:num->int32) (tbl:num->int32)
          ((ra:num->int32),(rb:num->int32),(jq:num->int32),(jp:num->int32),(zq:num->int32),(zp:num->int32)) (k:num) =
    bitval (~(ra k = word 251658)) + bitval (~(jq k = word 0)) + bitval (~(jp k = word 0)) +
    bitval (~(zq k = word 0)) + bitval (~(rb k = va1_rbinit tbl k)) + bitval (~(zp k = va1_zpseed mdl k))`;;

let va1_bad = new_definition
 `va1_bad (mdl:num->int32) (tbl:num->int32)
          ((ra:num->int32),(rb:num->int32),(jq:num->int32),(jp:num->int32),(zq:num->int32),(zp:num->int32),(nd:int32)) =
    word_add nd (word (nsum (0..2047) (\k. va1_mis mdl tbl (ra,rb,jq,jp,zq,zp) k)))`;;

let va1_unp_frame = new_definition
 `va1_unp_frame (m0:int64->byte) (m:int64->byte) <=>
    !a. a < 4194304 /\ ~(16392 <= a /\ a < 16512) /\ ~(65536 <= a /\ a < 2039808)
        ==> read (bytes8 (word a)) m = read (bytes8 (word a)) m0`;;

let VA1_F26_CALLEE = prove
 (`wasm_entry va1_f26_mc = SOME 5 /\
   wasm_decl_vals va1_f26_mc = SOME [I32 (word 0); I32 (word 0); I32 (word 0); I32 (word 0); I32 (word 0); I64 (word 0)]`,
  REWRITE_TAC[VA1_F26_CALLEE_RULE]);;
