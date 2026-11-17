needs "ve_vort.ml";;
needs "ve_tick.ml";;
needs "ve_vk.ml";;
needs "va1_code.ml";;
needs "va1_seq_final2.ml";;
(* ========================================================================= *)
(* Vortex chain, rung C1, layer 1 of 3: the generic host-call layer          *)
(* (PROVE-C1, Claude Opus 5.5, 2026-11-11). Spec chain_c1_final.spec        *)
(* (frozen sha256 3b62701f...). Pure HOL: definitions va1_hcall, va1_hrun,   *)
(* va1_cmds_ok, va1_cmds_end exactly as pinned, and the generic theorems     *)
(* VA1_*_CLAUSES, VA1_HCALL_ENSURES, VA1_HCALL_MONO, VA1_HRUN_MONO,          *)
(* VA1_HRUN_APPEND, VA1_HCALL_START_SAT, VA1_HCALL_RUNS, VA1_TICKF/B_CALLEE. *)
(* No no-pop specifics (rung C2 reuses this file). No decode rule, no        *)
(* stepping, no mk_thm / new_axiom / CHEAT_TAC. Helpers carry prefix C1_.    *)
(* ========================================================================= *)

let va1_hcall = new_definition
 `va1_hcall (step:wasmstate->wasmstate->bool) (code:byte list) (args:wval list) (r:int32)
            (Q:(num->wval)->(int64->byte)->bool) (gl:num->wval) (m:int64->byte) <=>
    ?e decls.
      wasm_entry code = SOME e /\ wasm_decl_vals code = SOME decls /\
      !s0. read wmemsize s0 = 4194304 /\ read wglobals s0 = gl /\ read wmem s0 = m
           ==> eventually step
                 (\s. read wstatus s = WDone /\ read wstack s = [I32 r] /\
                      read wmemsize s = 4194304 /\ Q (read wglobals s) (read wmem s))
                 (wcall_entry code (LENGTH args) 1 args e decls s0)`;;

let va1_hrun = new_definition
 `va1_hrun (step:wasmstate->wasmstate->bool) (cs:bool list) (Q:(num->wval)->(int64->byte)->bool) =
    ITLIST (\c R. va1_hcall step (if c then va1_tick_forward_mc else va1_tick_backward_mc) [] (word 1) R) cs Q`;;

let va1_cmds_ok = define
 `(!K u. va1_cmds_ok K u [] <=> T) /\
  (!K u c cs. va1_cmds_ok K u (CONS c cs) <=>
     if c then u < K /\ va1_cmds_ok K (u + 1) cs else 0 < u /\ va1_cmds_ok K (u - 1) cs)`;;

let va1_cmds_end = define
 `(!u. va1_cmds_end u [] = u) /\
  (!u c cs. va1_cmds_end u (CONS c cs) = va1_cmds_end (if c then u + 1 else u - 1) cs)`;;

let VA1_CMDS_OK_CLAUSES = prove
 (`(!K u. va1_cmds_ok K u [] <=> T) /\
  (!K u c cs. va1_cmds_ok K u (CONS c cs) <=>
     if c then u < K /\ va1_cmds_ok K (u + 1) cs else 0 < u /\ va1_cmds_ok K (u - 1) cs)`,
  ACCEPT_TAC va1_cmds_ok);;

let VA1_CMDS_END_CLAUSES = prove
 (`(!u. va1_cmds_end u [] = u) /\
  (!u c cs. va1_cmds_end u (CONS c cs) = va1_cmds_end (if c then u + 1 else u - 1) cs)`,
  ACCEPT_TAC va1_cmds_end);;

let VA1_HRUN_CLAUSES = prove
 (`(!(step:wasmstate->wasmstate->bool) (Q:(num->wval)->(int64->byte)->bool) gl m.
     va1_hrun step [] Q gl m <=> Q gl m) /\
  (!(step:wasmstate->wasmstate->bool) c cs (Q:(num->wval)->(int64->byte)->bool) gl m.
     va1_hrun step (CONS c cs) Q gl m <=>
     va1_hcall step (if c then va1_tick_forward_mc else va1_tick_backward_mc) [] (word 1)
               (va1_hrun step cs Q) gl m)`,
  REWRITE_TAC[va1_hrun; ITLIST]);;

(* eventually: monotone, implication form *)
let C1_EV_MONO = prove
 (`!(step:A->A->bool) P Q s.
     (!s. P s ==> Q s) ==> eventually step P s ==> eventually step Q s`,
  MESON_TAC[EVENTUALLY_MONO]);;

let C1_EV_MONO_CONJ = prove
 (`!(step:A->A->bool) P Q s.
     (!s. P s ==> Q s) /\ eventually step P s ==> eventually step Q s`,
  MESON_TAC[EVENTUALLY_MONO]);;

let VA1_HCALL_ENSURES = prove
 (`!(step:wasmstate->wasmstate->bool) (code:byte list) (e:num) (decls:wval list) (args:wval list) (r:int32)
   (P:wasmstate->bool) (Q:wasmstate->bool) (C:wasmstate->wasmstate->bool)
   (R:(num->wval)->(int64->byte)->bool) (gl:num->wval) (m:int64->byte).
     wasm_entry code = SOME e /\ wasm_decl_vals code = SOME decls /\ ensures step P Q C /\
     (!s0. read wmemsize s0 = 4194304 /\ read wglobals s0 = gl /\ read wmem s0 = m
           ==> P (wcall_entry code (LENGTH args) 1 args e decls s0)) /\
     (!s0 s. read wmemsize s0 = 4194304 /\ read wglobals s0 = gl /\ read wmem s0 = m /\
             Q s /\ C (wcall_entry code (LENGTH args) 1 args e decls s0) s
             ==> read wstatus s = WDone /\ read wstack s = [I32 r] /\
                 read wmemsize s = 4194304 /\ R (read wglobals s) (read wmem s))
     ==> va1_hcall step code args r R gl m`,
  MAP_EVERY X_GEN_TAC
   [`step:wasmstate->wasmstate->bool`; `code:byte list`; `e:num`; `decls:wval list`;
    `args:wval list`; `r:int32`; `pp:wasmstate->bool`; `qq:wasmstate->bool`;
    `cc:wasmstate->wasmstate->bool`; `rr:(num->wval)->(int64->byte)->bool`;
    `gl:num->wval`; `m:int64->byte`] THEN
  REWRITE_TAC[va1_hcall; ensures] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ens") (CONJUNCTS_THEN2 (LABEL_TAC "pre") (LABEL_TAC "post"))))) THEN
  MAP_EVERY EXISTS_TAC [`e:num`; `decls:wval list`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s0:wasmstate` THEN STRIP_TAC THEN
  MATCH_MP_TAC C1_EV_MONO_CONJ THEN
  EXISTS_TAC `\s'. (qq:wasmstate->bool) s' /\
                   cc (wcall_entry code (LENGTH (args:wval list)) 1 args e decls s0) s'` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
    REMOVE_THEN "post" (MP_TAC o SPECL [`s0:wasmstate`; `s:wasmstate`]) THEN
    ASM_REWRITE_TAC[];
    REMOVE_THEN "ens" MATCH_MP_TAC THEN REMOVE_THEN "pre" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let VA1_HCALL_MONO = prove
 (`!(step:wasmstate->wasmstate->bool) (code:byte list) (args:wval list) (r:int32)
   (Q:(num->wval)->(int64->byte)->bool) (Q':(num->wval)->(int64->byte)->bool) (gl:num->wval) (m:int64->byte).
     (!g x. Q g x ==> Q' g x) /\ va1_hcall step code args r Q gl m
     ==> va1_hcall step code args r Q' gl m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_hcall] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `e:num` (X_CHOOSE_THEN `decls:wval list` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`e:num`; `decls:wval list`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s0:wasmstate` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s0:wasmstate`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C1_EV_MONO THEN GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let VA1_HRUN_MONO = prove
 (`!(step:wasmstate->wasmstate->bool) (cs:bool list)
   (Q:(num->wval)->(int64->byte)->bool) (Q':(num->wval)->(int64->byte)->bool) (gl:num->wval) (m:int64->byte).
     (!g x. Q g x ==> Q' g x) /\ va1_hrun step cs Q gl m
     ==> va1_hrun step cs Q' gl m`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[VA1_HRUN_CLAUSES] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VA1_HCALL_MONO THEN
  EXISTS_TAC `va1_hrun (step:wasmstate->wasmstate->bool) t (Q:(num->wval)->(int64->byte)->bool)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `Q:(num->wval)->(int64->byte)->bool` THEN ASM_REWRITE_TAC[]);;

let VA1_HRUN_APPEND = prove
 (`!(step:wasmstate->wasmstate->bool) (cs1:bool list) (cs2:bool list) (Q:(num->wval)->(int64->byte)->bool).
     va1_hrun step (APPEND cs1 cs2) Q = va1_hrun step cs1 (va1_hrun step cs2 Q)`,
  REWRITE_TAC[va1_hrun; ITLIST_APPEND]);;

let VA1_HCALL_START_SAT = prove
 (`!(gl:num->wval) (m:int64->byte).
     ?s0. read wmemsize s0 = 4194304 /\ read wglobals s0 = gl /\ read wmem s0 = m`,
  REPEAT GEN_TAC THEN
  EXISTS_TAC `write wmem (m:int64->byte) (write wglobals (gl:num->wval)
                (write wmemsize 4194304 (ARB:wasmstate)))` THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN REWRITE_TAC[]);;

let VA1_HCALL_RUNS = prove
 (`!(fs:num->byte list#num#num) (code:byte list) (args:wval list) (r:int32)
   (Q:(num->wval)->(int64->byte)->bool) (gl:num->wval) (m:int64->byte).
     va1_hcall (wasmc fs) code args r Q gl m
     ==> ?e decls.
           wasm_entry code = SOME e /\ wasm_decl_vals code = SOME decls /\
           !s0. read wmemsize s0 = 4194304 /\ read wglobals s0 = gl /\ read wmem s0 = m
                ==> (?s. RTC (wasmc fs) (wcall_entry code (LENGTH args) 1 args e decls s0) s /\
                         read wstatus s = WDone /\ read wstack s = [I32 r] /\
                         read wmemsize s = 4194304 /\ Q (read wglobals s) (read wmem s)) /\
                    (!s. RTC (wasmc fs) (wcall_entry code (LENGTH args) 1 args e decls s0) s /\
                         ~(read wstatus s = WRunning)
                         ==> read wstatus s = WDone /\ read wstack s = [I32 r] /\
                             read wmemsize s = 4194304 /\ Q (read wglobals s) (read wmem s))`,
  MAP_EVERY X_GEN_TAC
   [`fs:num->byte list#num#num`; `code:byte list`; `args:wval list`; `r:int32`;
    `qq:(num->wval)->(int64->byte)->bool`; `gl:num->wval`; `m:int64->byte`] THEN
  REWRITE_TAC[va1_hcall] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:num` (X_CHOOSE_THEN `decls:wval list` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`e:num`; `decls:wval list`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s0:wasmstate` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s0:wasmstate`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP EVENTUALLY_RTC_EXISTS) THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `s:wasmstate` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`wasmc fs`;
    `\s:wasmstate. read wstatus s = WDone /\ read wstack s = [I32 r] /\
                   read wmemsize s = 4194304 /\ qq (read wglobals s) (read wmem s)`]
    EVENTUALLY_RTC_FINAL) THEN
  ANTS_TAC THENL
   [CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC WASMC_FINAL THEN ASM_REWRITE_TAC[distinctness "wstat"];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `wcall_entry code (LENGTH (args:wval list)) 1 args e decls s0`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s:wasmstate`) THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN MATCH_MP_TAC WASMC_FINAL THEN ASM_REWRITE_TAC[]);;

let VA1_TICKF_CALLEE = WASM_CALLEE_RULE va1_tick_forward_mc;;
let VA1_TICKB_CALLEE = WASM_CALLEE_RULE va1_tick_backward_mc;;

(* guard: the layer's theorems against the frozen statements *)
let C1_HOST_CHECK =
  let chk name th tm = if aconv (concl th) tm && hyp th = [] then ()
    else failwith ("C1_HOST_CHECK "^name) in
  chk "VA1_TICKF_CALLEE" VA1_TICKF_CALLEE `wasm_entry va1_tick_forward_mc = SOME 3 /\
  wasm_decl_vals va1_tick_forward_mc = SOME [I32 (word 0); I32 (word 0); I32 (word 0)]`;
  chk "VA1_TICKB_CALLEE" VA1_TICKB_CALLEE `wasm_entry va1_tick_backward_mc = SOME 3 /\
  wasm_decl_vals va1_tick_backward_mc = SOME [I32 (word 0); I32 (word 0)]`;;
