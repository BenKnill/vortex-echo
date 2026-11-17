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
needs "c8a_born_defs.ml";;
(* vortex-chain C8a: pin probe leaf (row A1). Binds the fold CLAUSES, VA1_F13_ENTRY and VA1_PUSH_CLAUSES; the spec *)
(* c8a_born.spec checks every definition pin against the defs layer. *)
let VA1_FOLD1_CLAUSES = prove(`(!mdl hp tbl t rb nd0 st. va1_fold1 mdl hp tbl t rb nd0 0 st = st) /\
  (!mdl hp tbl t rb nd0 k st. va1_fold1 mdl hp tbl t rb nd0 (SUC k) st =
       va1_step1 mdl hp tbl t rb nd0 k (va1_fold1 mdl hp tbl t rb nd0 k st))`, REWRITE_TAC[va1_fold1]);;
let VA1_FOLD2_CLAUSES = prove(`(!mdl hp tbl t rb nd0 L. va1_fold2 mdl hp tbl t rb nd0 0 L = L) /\
  (!mdl hp tbl t rb nd0 k L. va1_fold2 mdl hp tbl t rb nd0 (SUC k) L =
       va1_step2 mdl hp tbl t rb nd0 k (va1_fold2 mdl hp tbl t rb nd0 k L))`, REWRITE_TAC[va1_fold2]);;
let VA1_FOLD3_CLAUSES = prove(`(!mdl hp tbl t ra rb nd0 L. va1_fold3 mdl hp tbl t ra rb nd0 0 L = L) /\
  (!mdl hp tbl t ra rb nd0 k L. va1_fold3 mdl hp tbl t ra rb nd0 (SUC k) L =
       va1_step3 mdl hp tbl t ra rb nd0 k (va1_fold3 mdl hp tbl t ra rb nd0 k L))`, REWRITE_TAC[va1_fold3]);;
let VA1_F13_ENTRY = prove(`wasm_entry va1_f13_mc = SOME 13`, ACCEPT_TAC VA1_F13_ENTRY);;
let VA1_PUSH_CLAUSES = prove(parse_term pop_spec_VA1_PUSH_CLAUSES, REWRITE_TAC[va1_push]);;
