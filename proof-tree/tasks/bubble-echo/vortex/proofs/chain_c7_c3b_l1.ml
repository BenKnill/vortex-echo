needs "ve_vort.ml";;
needs "ve_tick.ml";;
needs "ve_vk.ml";;
needs "va1_code.ml";;
needs "va1_seq_final2.ml";;
needs "pop_design_defs.ml";;
needs "pop_design_stmts.ml";;
needs "chain_c3b_dec.ml";;
needs "chain_c7_c3b_defs.ml";;
(* ========================================================================= *)
(* Vortex chain rung C3b, layer 1 (vortex-chain-20261111-142342 c3b, Claude  *)
(* Opus 5.5, 2026-11-13): f25 ve_puncture on the exact bytes. Spec           *)
(* chain_c3b_final.spec (frozen 296578ea). Data-blind stepping driver copied *)
(* from the R5B birth prover (prove-birth src/r5b_drv.ml), load              *)
(* abbreviation, address normalisation and read-over-write conversions; the  *)
(* two isqrt loops by induction on the counter, the header/jiggle block      *)
(* unrolled, the 2048-bead loop (C3B_IT4/C3B_LOOP4) and the 24576-row DI      *)
(* zero loop (C3B_IT5/C3B_LOOP5) by induction; VA1_F25_GUARD_P,              *)
(* VA1_F25_GUARD_ARGS, VA1_F25_OK. No mk_thm / new_axiom / CHEAT_TAC.        *)
(* ========================================================================= *)
(* ========================================================================= *)
(* C3b (Claude Opus 5.5, 2026-11-13): copy of the R5B data-blind driver      *)
(* (vortex-r5birth prove-birth src/r5b_drv.ml), retargeted to f25. Steps one instruction at a time; a guard the stepper *)
(* leaves undecided is first retried with val-bound facts of its subterms    *)
(* (masks, shifts, sums: trap/bounds guards), then case-split (data branch). *)
(* ========================================================================= *)
let C3B_EXEC = C3B_F25_EXEC;;
let c3b_extra = ref ([]:thm list);;

let C3B_VADD = prove(`!a b:N word. val(word_add a b) <= val a + val b`, REWRITE_TAC[VAL_WORD_ADD; MOD_LE]);;
let C3B_VMUL = prove(`!a b:N word. val(word_mul a b) <= val a * val b`, REWRITE_TAC[VAL_WORD_MUL; MOD_LE]);;
let C3B_VSHL = prove(`!(a:N word) k. val(word_shl a k) <= 2 EXP k * val a`, REWRITE_TAC[VAL_WORD_SHL; MOD_LE]);;
let C3B_VZX = prove(`!(a:M word). val(word_zx a:N word) <= val a`, REWRITE_TAC[VAL_WORD_ZX_GEN; MOD_LE]);;
let C3B_VWORD = prove(`!e. val(word e:N word) <= e`, REWRITE_TAC[VAL_WORD; MOD_LE]);;
let C3B_VUSHR = prove(`!(a:N word) k. 2 EXP k * val(word_ushr a k) < 2 EXP dimindex(:N)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_USHR] THEN
  MP_TAC(ISPECL [`val(a:N word)`; `2 EXP k`] DIV_MUL_LE) THEN
  MP_TAC(ISPEC `a:N word` VAL_BOUND) THEN ARITH_TAC);;
let C3B_VAND32 = prove(`!x y:int32. val(word_and x y) <= val y /\ val(word_and x y) <= val x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM WORD_ULE] THEN CONJ_TAC THEN BITBLAST_TAC);;

let c3b_nred th = CONV_RULE(DEPTH_CONV(NUM_RED_CONV ORELSEC (fun t -> if t = `dimindex(:32)` then DIMINDEX_32 else
                    if t = `dimindex(:64)` then DIMINDEX_64 else failwith "")) THENC NUM_REDUCE_CONV) th;;

(* val-bound facts for t and its word subterms *)
let c3b_pm rule vt = c3b_nred (PART_MATCH lhand (SPEC_ALL rule) vt);;
let C3B_VCOND = prove(`!c (a:N word) b. val (if c then a else b) <= val a + val b`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ARITH_TAC);;
let rec c3b_tfacts t =
  let vt = mk_icomb(`val:N word->num`, t) in
  if is_cond t then
    let _,(a,b) = dest_cond t in
    (try [c3b_nred (PART_MATCH lhand (SPEC_ALL C3B_VCOND) vt)] with Failure _ -> []) @ c3b_tfacts a @ c3b_tfacts b @
    (try [c3b_nred (ISPEC t VAL_BOUND)] with Failure _ -> []) else
  let bnd = try [c3b_nred (ISPEC t VAL_BOUND)] with Failure _ -> [] in
  let sub = try
    let h,args = strip_comb t in
    match (fst(dest_const h), args) with
      ("word_add",[a;b]) -> c3b_pm C3B_VADD vt :: (c3b_tfacts a @ c3b_tfacts b)
    | ("word_mul",[a;b]) -> c3b_pm C3B_VMUL vt :: (c3b_tfacts a @ c3b_tfacts b)
    | ("word_shl",[a;k]) -> c3b_pm C3B_VSHL vt :: c3b_tfacts a
    | ("word_ushr",[a;k]) -> [c3b_nred (PART_MATCH (rand o lhand) (SPEC_ALL C3B_VUSHR) vt)]
    | ("word_and",[a;b]) when type_of t = `:int32` ->
         map (fun c -> PART_MATCH lhand c vt) (CONJUNCTS (SPEC_ALL C3B_VAND32)) @ c3b_tfacts a @ c3b_tfacts b
    | ("word_zx",[a]) -> c3b_pm C3B_VZX vt :: c3b_tfacts a
    | ("word",[e]) -> if is_numeral e then [c3b_pm VAL_WORD vt] else [c3b_pm C3B_VWORD vt]
    | _ -> []
    with Failure _ -> [] in
  bnd @ sub;;

let setify_thms ths =
  let rec go seen = function [] -> [] | th::r -> if mem (concl th) seen then go seen r else th :: go (concl th :: seen) r in
  go [] ths;;
let c3b_gfacts g =
  let vs = find_terms (fun t -> is_comb t && (match rator t with Const("val",_) -> true | _ -> false)) g in
  let ths = List.concat (map (fun v -> try c3b_tfacts (rand v) with Failure _ -> []) vs) in
  let ths = filter (fun th -> hyp th = [] && not (concl th = `T`)) ths in
  setify_thms ths;;

let c3b_mths asl = filter (fun th -> vk_is_memfact (concl th)) (map snd asl);;
let c3b_ctr = ref 0;;
let c3b_fresh () = incr c3b_ctr; "s" ^ string_of_int !c3b_ctr;;
let c3b_log = ref true;;

let C3B_STEP1 exec sname : tactic = fun (asl,w) ->
  (CAP_STEP_TAC exec (READ_COMPONENT_COMPOSE :: (!c3b_extra @ c3b_mths asl)) sname THEN
   CAP_DISCARD_OLD_TAC sname THEN WASM_COMPACT_HYPS_TAC) (asl,w);;

let c3b_pc asl s =
  let th = find (fun th -> let c = concl th in is_eq c &&
     (match lhs c with Comb(Comb(Const("read",_),Const("wpc",_)),s') -> s' = s | _ -> false)) (map snd asl) in
  dest_small_numeral(rand(rhs(concl th)));;

let c3b_status asl s =
  try let th = find (fun th -> let c = concl th in is_eq c &&
     (match lhs c with Comb(Comb(Const("read",_),Const("wstatus",_)),s') -> s' = s | _ -> false)) (map snd asl) in
  rhs(concl th) with Failure _ -> `WTrap`;;

let c3b_guard exec (asl,w) =
  let s = rand w in
  let s' = mk_var("s_c3bg",`:wasmstate`) in
  let th = WASM_CONV (snd exec) (READ_COMPONENT_COMPOSE :: (!c3b_extra @ c3b_mths asl)) (map snd asl)
             (mk_comb(mk_comb(`wasm`,s),s')) in
  let r = rhs(concl th) in
  let c = find_term is_cond r in
  lhand(rator c);;

let c3b_strip_neg g = if is_neg g then rand g else g;;

let c3b_is_statefree tm = not (can (find_term (fun t -> type_of t = `:wasmstate`)) tm);;
(* prove g (or ~g) from the state-free num assumptions and the val-bound facts *)
let c3b_decide asl g =
  let fs = c3b_gfacts g in
  let ants = filter (fun th -> let c = concl th in wasm_is_numrel c && c3b_is_statefree c && not (is_disj c)) (map snd asl) @ fs in
  let pr t = if ants = [] then ARITH_RULE t else
    MP (ARITH_RULE (mk_imp(list_mk_conj(map concl ants), t))) (end_itlist CONJ ants) in
  try EQT_INTRO (pr g) with Failure _ -> EQF_INTRO (pr (mk_neg g));;

let C3B_GSTEP exec sname : tactic = fun (asl,w) ->
  let pc = c3b_pc asl (rand w) in
  let g = try c3b_guard exec (asl,w) with Failure m ->
    ((try ignore(C3B_STEP1 exec sname (asl,w)) with Failure m2 ->
        Printf.printf "@@STUCK pc %d: %s\n%!" pc (String.sub m2 0 (min 600 (String.length m2))));
     failwith ("c3b stuck at pc " ^ string_of_int pc)) in
  (try let gth = c3b_decide asl g in
     (fun gl -> let old = !c3b_extra in
        c3b_extra := gth :: old;
        let r = (try C3B_STEP1 exec sname gl with e -> (c3b_extra := old; raise e)) in
        c3b_extra := old;
        if !c3b_log then Printf.printf "@@BOUND pc %d\n%!" pc; r)
   with Failure _ ->
   (fun gl -> let g' = c3b_strip_neg g in
    (if !c3b_log then let st = String.map (fun c -> if c = '\n' then ' ' else c) (string_of_term g') in
       Printf.printf "@@SPLIT pc %d: %s\n%!" pc (if String.length st > 400 then String.sub st 0 400 else st));
    (ASM_CASES_TAC g' THEN C3B_STEP1 exec sname) gl)) (asl,w);;

(* data-blind generalization: a stack/local value of the current state bigger than the threshold becomes a fresh
   variable (its defining equation is dropped, which only strengthens the goal) *)
let c3b_abbrev_thresh = ref 0;;
let rec c3b_tsize t = match t with Comb(a,b) -> c3b_tsize a + c3b_tsize b | Abs(_,b) -> 1 + c3b_tsize b | _ -> 1;;
let c3b_vctr = ref 0;;
let C3B_GEN_TAC : tactic = fun (asl,w) ->
  if !c3b_abbrev_thresh = 0 then ALL_TAC (asl,w) else
  let s = rand w in
  let vals = List.concat (map (fun (_,th) -> let c = concl th in
     if is_eq c && (match lhs c with Comb(Comb(Const("read",_),comp),s') ->
                      s' = s && (comp = `wstack` || (is_comb comp && rator comp = `wlocal`)) | _ -> false)
     then (let r = rhs c in
           let elems = if is_list r then dest_list r else [r] in
           mapfilter (fun e -> let h,a = strip_comb e in
                        if (h = `I32` || h = `I64`) && length a = 1 then hd a else fail()) elems)
     else []) asl) in
  let big = setify (filter (fun v -> c3b_tsize v > !c3b_abbrev_thresh && not (is_var v)) vals) in
  let big = sort (fun a b -> c3b_tsize a > c3b_tsize b) big in
  MAP_EVERY (fun v -> fun g -> incr c3b_vctr;
       let nv = mk_var("ab" ^ string_of_int !c3b_vctr, type_of v) in
       (ABBREV_TAC (mk_eq(nv, v)) THEN
        REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> let c = concl th in is_eq c && rhs c = nv)))) g) big (asl,w);;

(* run until the pc is in stops (or the status is not WRunning) *)
let rec C3B_RUN exec stops : tactic = fun (asl,w) ->
  let s = rand w in
  if c3b_status asl s <> `WRunning` then ALL_TAC (asl,w) else
  let pc = c3b_pc asl s in
  if mem pc stops then ALL_TAC (asl,w) else
  let sn = c3b_fresh() in
  ((C3B_STEP1 exec sn ORELSE C3B_GSTEP exec sn) THEN C3B_GEN_TAC THEN C3B_RUN exec stops) (asl,w);;

let C3B_RUN1 exec stops : tactic = fun (asl,w) ->
  let sn = c3b_fresh() in ((C3B_STEP1 exec sn ORELSE C3B_GSTEP exec sn) THEN C3B_RUN exec stops) (asl,w);;

let c3b_time name (tac:tactic) : tactic = fun g ->
  let t0 = Sys.time() in let r = tac g in
  Printf.printf "@@TIME %s %.1f s cpu\n%!" name (Sys.time() -. t0); r;;

(* ---- interface predicates: control shape, typed locals, tracked locals, memory m0 *)
let c3b_ity i = i <= 2 || i = 8 || i = 11 || i = 15;;
let c3b_rd i = mk_comb(mk_comb(`read:(wasmstate,wval)component->wasmstate->wval`, mk_comb(`wlocal`, mk_small_numeral i)), `s:wasmstate`);;
let c3b_typed i =
  let xv = mk_var("x" ^ string_of_int i, if c3b_ity i then `:int32` else `:int64`) in
  mk_exists(xv, mk_eq(c3b_rd i, mk_comb((if c3b_ity i then `I32` else `I64`), xv)));;
let c3b_trk i v = mk_eq(c3b_rd i, mk_comb((if c3b_ity i then `I32` else `I64`), v));;
let c3b_lbl l = mk_list(map (fun (a,b,c) -> mk_pair(mk_small_numeral a, mk_pair(mk_small_numeral b, mk_small_numeral c))) l,
                        `:num#num#num`);;
(* blk e = block whose end instruction is at e (continuation e+1); lp p = loop instruction at p *)
type c3b_lab = Blk of int | Lp of int;;
let c3b_lb = function Blk e -> (0,e+1,0) | Lp p -> (0,p,0);;
let c3b_body pc lbls tracked extra =
  let locs = map (fun i -> try c3b_trk i (assoc i tracked) with Failure _ -> c3b_typed i) (0--15) in
  list_mk_conj
   ([`read wcode s = va1_f25_mc`; mk_eq(`read wpc s`, mk_comb(`word:num->int64`, mk_small_numeral pc));
     `read wstatus s = WRunning`; `read wstack s = []`; mk_eq(`read wlabels s`, c3b_lbl (map c3b_lb lbls));
     `read warity s = 1`; `read wmemsize s = 4194304`] @ locs @ [`read wmem s = m0`] @ extra);;
let c3b_pred pc lbls tracked extra = mk_abs(`s:wasmstate`, c3b_body pc lbls tracked extra);;
let c3b_rest q = let s,b = dest_abs q in mk_abs(s, rand(rand b));;
let C3B_FRAME = `MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocal 0; wlocal 1; wlocal 2; wlocal 3; wlocal 4; wlocal 5; wlocal 6; wlocal 7;
                      wlocal 8; wlocal 9; wlocal 10; wlocal 11; wlocal 12; wlocal 13; wlocal 14; wlocal 15] ,,
           MAYCHANGE [wmem :> bytes(word 16396,8)] ,, MAYCHANGE [wmem :> bytes(word 16408,96)] ,,
           MAYCHANGE [wmem :> bytes(word 1130496,835584)]`;;
let c3b_ens p q = mk_comb(mk_comb(mk_comb(`ensures wasm`, p), q), C3B_FRAME);;
let C3B_EX_EQ = prove(`!t:A. (?x. t = x) <=> T`, MESON_TAC[]);;
(* close a post conjunction at the final state *)
let C3B_CLOSE_TAC =
  ASM_REWRITE_TAC[injectivity "wval"; C3B_EX_EQ] THEN
  CONV_TAC(DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV)) THEN ASM_REWRITE_TAC[injectivity "wval"; C3B_EX_EQ];;

(* the clamped divisors (select(v,1,v >s 1)) are never 0 *)
let c3b_sel_nz ty = let v = mk_var("v", ty) in
  let nn = if ty = `:int64` then `:64` else `:32` in
  let sel = inst [nn,`:N`] `(if ival (v:N word) > &1 then v else word 1)` in
  let c0,(a0,b0) = dest_cond sel in
  let sel' = mk_cond(mk_neg c0, b0, a0) in
  let z = inst [nn,`:N`] `word 0:N word` in
  let m1 = if ty = `:int64` then `word 18446744073709551615:int64` else `word 4294967295:int32` in
  let n1 = inst [nn,`:N`] `word_neg (word 1):N word` in
  let eqs = List.concat (map (fun t -> [mk_eq(t,z); mk_eq(z,t); mk_eq(t,m1); mk_eq(t,n1)]) [sel; sel']) in
  let eqs = mk_conj(c0, mk_eq(v,z)) :: eqs in
  let stmt = mk_forall(v, list_mk_conj(map (fun e -> mk_eq(e,`F`)) eqs)) in
  prove(stmt, GEN_TAC THEN ASM_CASES_TAC (mk_eq(v,z)) THENL
   [ASM_REWRITE_TAC[IVAL_WORD_0] THEN CONV_TAC(DEPTH_CONV(WORD_RED_CONV ORELSEC INT_RED_CONV)) THEN REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
    TRY(POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
        REWRITE_TAC[GSYM IVAL_EQ; IVAL_WORD_0] THEN CONV_TAC(DEPTH_CONV(WORD_RED_CONV ORELSEC INT_RED_CONV)) THEN
        INT_ARITH_TAC) THEN ASM_MESON_TAC[]]);;
let C3B_SEL1_NZ = CONJ (c3b_sel_nz `:int64`) (c3b_sel_nz `:int32`);;
let () = c3b_extra := [VK_COND_I64; VK_COND_I32; C3B_SEL1_NZ];;

let C3B_INIT_TAC = ENSURES_INIT_TAC "s0" THEN REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl)));;
(* final state: close one of the post disjuncts *)
let C3B_CLOSE1 = C3B_CLOSE_TAC THEN TRY(REPEAT CONJ_TAC THEN ASM_ARITH_TAC) THEN NO_TAC;;
let C3B_FIN_TAC : tactic =
  ENSURES_FINAL_STATE_TAC THEN
  FIRST [C3B_CLOSE1; DISJ1_TAC THEN C3B_CLOSE1; DISJ2_TAC THEN C3B_CLOSE1;
         DISJ2_TAC THEN DISJ1_TAC THEN C3B_CLOSE1; DISJ2_TAC THEN DISJ2_TAC THEN C3B_CLOSE1];;
let C3B_SEG_TAC name stops : tactic =
  REPEAT GEN_TAC THEN TRY(DISCH_THEN STRIP_ASSUME_TAC) THEN C3B_INIT_TAC THEN
  c3b_time name (C3B_RUN C3B_EXEC stops) THEN C3B_FIN_TAC;;

(* use a lemma |- !vars. [A ==>] ensures P Q C for a goal ensures P' Q' C (weakening by rewriting) *)
let C3B_USE_TAC th : tactic = fun (asl,w) ->
  let th1 = SPEC_ALL th in
  let th2 = if is_imp (concl th1) then MP th1 (TAC_PROOF((asl, lhand (concl th1)), ASM_ARITH_TAC)) else th1 in
  let th3 = try PART_MATCH I th2 w with Failure _ -> th2 in
  let c = concl th3 in
  let p = rand(rator(rator c)) and q = rand(rator c) in
  (MATCH_ACCEPT_TAC th3 ORELSE
   (MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC p THEN CONJ_TAC THENL
     [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN C3B_CLOSE_TAC;
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC q THEN CONJ_TAC THENL
       [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN C3B_CLOSE_TAC;
        ACCEPT_TAC th3]])) (asl,w);;

(* ---- the isqrt loops: loop instr at lp, body start bp = lp + 2, exit ep (after end), counter local ctr from c down *)
let C3B_DEC1 = prove
 (`!c. c < 4294967296 ==> word_add (word (SUC c)) (word 4294967295):int32 = word c /\ (word c:int32 = word 0 <=> c = 0)`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD; ARITH_RULE `SUC c + 4294967295 = c + 4294967296`] THEN
    REWRITE_TAC[WORD_ADD; WORD_RED_CONV `word 4294967296:int32`; WORD_ADD_0];
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_0; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT]]);;
let c3b_isq_stmt lp ep ctr outer trk =
  let bp = lp + 2 in
  let pre = c3b_pred bp (Lp lp :: outer) ((ctr, `word c:int32`) :: trk) [] in
  let post = c3b_pred ep outer trk [] in
  let e = c3b_ens pre post in
  let vs = subtract (frees e) [`c:num`] in
  mk_forall(`c:num`, mk_imp(`1 <= c /\ c <= 32`, list_mk_forall(vs, e)));;
let C3B_ISQ_TAC name lp ep ctr outer trk : tactic =
  let bp = lp + 2 in
  INDUCT_TAC THENL [ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC(SPEC `c:num` C3B_DEC1) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC)] THEN
  ASM_CASES_TAC `c = 0` THENL
   [C3B_INIT_TAC THEN c3b_time name (C3B_RUN1 C3B_EXEC [ep; bp]) THEN C3B_FIN_TAC;
    ENSURES_SEQUENCE_TAC (mk_small_numeral bp) (c3b_rest (c3b_pred bp (Lp lp :: outer) ((ctr, `word c:int32`) :: trk) [])) THEN
    CONJ_TAC THENL
     [C3B_INIT_TAC THEN c3b_time name (C3B_RUN1 C3B_EXEC [ep; bp]) THEN C3B_FIN_TAC;
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && is_forall(rand(concl th)))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(fun th -> C3B_USE_TAC th)]]];;

let C3B_DECLS = prove(`!decls. wasm_decl_vals va1_f25_mc = SOME decls <=> decls = [I64 (word 0); I64 (word 0); I64 (word 0); I64 (word 0); I64 (word 0); I32 (word 0); I64 (word 0); I64 (word 0); I32 (word 0); I64 (word 0); I64 (word 0); I64 (word 0); I32 (word 0)]`,
  REWRITE_TAC[CONJUNCT2 VA1_F25_CALLEE; option_INJ] THEN MESON_TAC[]);;

(* after ENSURES_INIT_TAC: the wlocals fact becomes 16 wlocal facts *)
let C3B_LOCALS_TAC : tactic = fun (asl,w) ->
  let s = rand w in
  let lth = find (fun th -> let c = concl th in is_eq c && lhs c = mk_comb(`read wlocals`, s)) (map snd asl) in
  let dth = find (fun th -> let c = concl th in is_eq c && can (find_term ((=) `wasm_decl_vals`)) c) (map snd asl) in
  let dth' = EQ_MP (SPEC (rand(rand(concl dth))) C3B_DECLS) dth in
  let mk i = let t = mk_comb(mk_comb(`read:(wasmstate,wval)component->wasmstate->wval`, mk_comb(`wlocal`, mk_small_numeral i)), s) in
    let th = (REWRITE_CONV[wlocal; READ_COMPONENT_COMPOSE; READ_ELEMENT; lth; dth'; wcall_locals; LENGTH] THENC
              NUM_REDUCE_CONV THENC REWRITE_CONV[] THENC ONCE_DEPTH_CONV EL_CONV THENC NUM_REDUCE_CONV THENC
              TRY_CONV(ONCE_DEPTH_CONV EL_CONV)) t in th in
  MAP_EVERY (fun i -> ASSUME_TAC (mk i)) (0--15) (asl,w);;

let GP = `!(a0:int32) (a1:int32) (a2:int32) (decls:wval list).
     wasm_decl_vals va1_f25_mc = SOME decls
     ==> ensures wasm
          (\s. read wcode s = va1_f25_mc /\ read wpc s = word 13 /\ read wstatus s = WRunning /\
               read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\
               read wlocals s = wcall_locals [I32 a2; I32 a1; I32 a0] decls /\
               ~(read (bytes32 (word 16396)) (read wmem s) = word 4294967295))
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 1)])
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus])`;;

let GA = `!(decls:wval list).
     wasm_decl_vals va1_f25_mc = SOME decls
     ==> ensures wasm
          (\s. read wcode s = va1_f25_mc /\ read wpc s = word 13 /\ read wstatus s = WRunning /\
               read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\
               read wlocals s = wcall_locals [I32 (word 0); I32 (word 0); I32 (word 0)] decls /\
               read (bytes32 (word 16396)) (read wmem s) = word 4294967295)
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 2)])
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus])`;;

let C3B_GUARD_TAC = REPEAT GEN_TAC THEN DISCH_TAC THEN ENSURES_INIT_TAC "s0" THEN C3B_LOCALS_TAC THEN
  ABBREV_TAC `m0 = read wmem s0` THEN C3B_RUN C3B_EXEC [] THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let VA1_F25_GUARD_P = prove(GP, C3B_GUARD_TAC);;

let VA1_F25_GUARD_ARGS = prove(GA, C3B_GUARD_TAC);;

let c3b_trkA = [0,`a0:int32`; 1,`a1:int32`; 2,`a2:int32`];;

let c3b_trk0 = c3b_trkA @ map (fun i -> i, if c3b_ity i then `word 0:int32` else `word 0:int64`) (3--15);;

let c3b_seg hyps p q = let e = c3b_ens p q in
  let vs = filter (fun v -> not (mem v [`s:wasmstate`])) (frees e @ frees hyps) in
  list_mk_forall(setify vs, mk_imp(hyps, e));;

let C3B_PRO = prove(c3b_seg `read (bytes32 (word 16396)) m0 = word 4294967295 /\ ~(word_or (word_or (a1:int32) a0) a2 = word 0)`
   (c3b_pred 13 [] c3b_trk0 []) (c3b_pred 98 [Lp 96] ((8,`word 32:int32`) :: c3b_trkA) []),
  C3B_SEG_TAC "pro" [98]);;

let C3B_ISQ1 = prove(c3b_isq_stmt 96 152 8 [] c3b_trkA, C3B_ISQ_TAC "isq1" 96 152 8 [] c3b_trkA);;

let C3B_MID = prove(c3b_seg `T` (c3b_pred 152 [] c3b_trkA []) (c3b_pred 275 [Lp 273] ((8,`word 32:int32`) :: c3b_trkA) []),
  C3B_SEG_TAC "mid" [275]);;

let C3B_ISQ2 = prove(c3b_isq_stmt 273 329 8 [] c3b_trkA, C3B_ISQ_TAC "isq2" 273 329 8 [] c3b_trkA);;

let CAP_B32_SAME_C3 = CAP_B32_SAME;;

let C3B_W32S_W32 = prove
 (`!base n f e (v:int32) m.
     va1_w32s base n f m /\ (e + 4 <= base \/ base + 4 * n <= e) /\
     base + 4 * n <= 4294967296 /\ e < 4294967296
     ==> va1_w32s base n f (write (bytes32 (word e)) v m)`,
  REWRITE_TAC[va1_w32s] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`base + 4 * k`; `e:num`; `v:int32`; `m:int64->byte`] VK_R32_W32) THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[]]));;

let C3B_MDL_W32S = prove(`!mdl m. va1_mdl mdl m <=> va1_w32s 16640 1024 mdl m`, REWRITE_TAC[va1_mdl; va1_w32s]);;

let C3B_R32_W32_NUM = prove
 (`!x a (v:int32) m. (x + 4 <= a \/ a + 4 <= x) /\ x < 4294967296 /\ a < 4294967296
     ==> read (bytes32 (word x)) (write (bytes32 (word a)) v m) = read (bytes32 (word x)) m`,
  REWRITE_TAC[VK_R32_W32]);;

let C3B_MEMFACT_TAC : tactic =
  REWRITE_TAC[C3B_MDL_W32S] THEN
  REPEAT((MATCH_MP_TAC C3B_W32S_W32 THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[]) ORELSE
         (W(fun (asl,w) -> let l = lhs w in
              let m = rand l in
              let a = rand(rand(rand(rator(rator m)))) and x = rand(rand(rand(rator l))) in
              if x = a then REWRITE_TAC[CAP_B32_SAME_C3]
              else (MP_TAC(SPECL [x; a; rand(rator m); rand m] C3B_R32_W32_NUM) THEN
                    CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC)))) THEN
  ASM_REWRITE_TAC[GSYM C3B_MDL_W32S];;

let c3b_trkL4 k = [8, mk_comb(`word:num->int32`, mk_binop `( * ):num->num->num` `4` k);
                   11, mk_comb(`word:num->int32`, mk_binop `(+):num->num->num` `65536` (mk_binop `( * ):num->num->num` `512` k));
                   15, mk_comb(`word:num->int32`, k)];;

let c3b_bodym mv pc lbls trk extra = subst [mv,`m0:int64->byte`] (c3b_body pc lbls trk extra);;

let c3b_F mv = subst [mv,`m:int64->byte`]
  `read (bytes32 (word 16396)) (m:int64->byte) = t /\ read (bytes32 (word 16408)) m = a0 /\
   read (bytes32 (word 16412)) m = a1 /\ read (bytes32 (word 16416)) m = (a2:int32) /\
   va1_mdl mdl m /\ va1_w32s 65536 262144 tbl m`;;

let C3B_HDR_STMT = c3b_seg `read (bytes32 (word 16392)) m0 = (t:int32) /\ va1_mdl mdl m0 /\ va1_w32s 65536 262144 tbl m0`
   (c3b_pred 329 [] c3b_trkA [])
   (mk_abs(`s:wasmstate`, mk_exists(`m1:int64->byte`, mk_conj(c3b_bodym `m1:int64->byte` 718 [Lp 716] (c3b_trkL4 `0`) [], c3b_F `m1:int64->byte`))));;

let C3B_VW32 = prove(`!n. n < 4294967296 ==> val (word n:int32) = n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_32] THEN ASM_ARITH_TAC);;

let C3B_VADD32 = prove(`!a b. a + b < 4294967296 ==> val (word_add (word a) (word b):int32) = a + b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN MATCH_MP_TAC C3B_VW32 THEN ASM_ARITH_TAC);;

let c3b_numasms asl = filter (fun th -> let c = concl th in wasm_is_numrel c && c3b_is_statefree c && not (is_disj c)) (map snd asl);;

let c3b_arith asl t = let ants = c3b_numasms asl in
  if ants = [] then ARITH_RULE t else MP (ARITH_RULE (mk_imp(list_mk_conj(map concl ants), t))) (end_itlist CONJ ants);;

(* canonical form of the number inside every word e (e not a numeral) *)
let C3B_WARG_CONV t = match t with
    Comb(Const("word",_),e) when type_of e = `:num` && not (is_numeral e) -> RAND_CONV NUM_NORMALIZE_CONV t
  | _ -> failwith "C3B_WARG_CONV";;

let C3B_WNORM_TAC = RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV C3B_WARG_CONV)) THEN CONV_TAC(ONCE_DEPTH_CONV C3B_WARG_CONV);;

let C3B_ROW = prove
 (`!x a (v:int32) m. (x = a \/ x + 4 <= a \/ a + 4 <= x) /\ x < 4294967296 /\ a < 4294967296
     ==> read (bytes32 (word x)) (write (bytes32 (word a)) v m) = if x = a then v else read (bytes32 (word x)) m`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x:num = a` THEN ASM_REWRITE_TAC[CAP_B32_SAME] THEN
  STRIP_TAC THEN MATCH_MP_TAC VK_R32_W32 THEN ASM_ARITH_TAC);;

let c3b_is_row t = match t with
    Comb(Comb(Const("read",_),Comb(Const("bytes32",_),Comb(Const("word",_),_))),
         Comb(Comb(Comb(Const("write",_),Comb(Const("bytes32",_),Comb(Const("word",_),_))),_),_)) -> true
  | _ -> false;;

let c3b_ldctr = ref 0;;

let c3b_is_ld t = match t with Comb(Comb(Const("read",_),Comb(Const("bytes32",_),_)),m) -> not (can (find_term (fun u -> type_of u = `:wasmstate`)) m) | _ -> false;;

let C3B_LDABBREV_TAC : tactic = fun (asl,w) ->
  let s = rand w in
  let facts = filter (fun th -> let c = concl th in is_eq c && (match lhs c with Comb(Comb(Const("read",_),comp),s') -> s' = s && (comp = `wstack` || (is_comb comp && rator comp = `wlocal`)) | _ -> false)) (map snd asl) in
  let lds = setify (List.concat (map (fun th -> find_terms c3b_is_ld (rhs(concl th))) facts)) in
  MAP_EVERY (fun t g -> incr c3b_ldctr; ABBREV_TAC (mk_eq(mk_var("ld"^string_of_int !c3b_ldctr, type_of t), t)) g) lds (asl,w);;

let rec C3B_RUN exec stops : tactic = fun (asl,w) ->
  let s = rand w in
  if c3b_status asl s <> `WRunning` then ALL_TAC (asl,w) else
  let pc = c3b_pc asl s in
  if mem pc stops then ALL_TAC (asl,w) else
  let sn = c3b_fresh() in
  ((C3B_STEP1 exec sn ORELSE C3B_GSTEP exec sn) THEN C3B_LDABBREV_TAC THEN C3B_GEN_TAC THEN C3B_RUN exec stops) (asl,w);;

let C3B_RUN1 exec stops : tactic = fun (asl,w) ->
  let sn = c3b_fresh() in ((C3B_STEP1 exec sn ORELSE C3B_GSTEP exec sn) THEN C3B_LDABBREV_TAC THEN C3B_RUN exec stops) (asl,w);;

let C3B_EXIT4 = prove(`!k. k < 2048 ==> (word_add (word (4 * k)) (word 4):int32 = word 8192 <=> k + 1 = 2048)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM WORD_ADD; GSYM VAL_EQ] THEN
  SUBGOAL_THEN `val (word (4 * k + 4):int32) = 4 * k + 4 /\ val (word 8192:int32) = 8192` (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC C3B_VW32 THEN ASM_ARITH_TAC; ARITH_TAC]);;

let C3B_EXISTS_MEM_TAC : tactic = W(fun (asl,w) -> let th = find (fun th -> let c = concl th in is_eq c && is_comb(lhs c) && rator(lhs c) = `read wmem` ) (map snd (rev asl)) in EXISTS_TAC (rhs(concl th)));;

let C3B_ARITH_TAC : tactic = fun (asl,w) -> ACCEPT_TAC (c3b_arith asl w) (asl,w);;

let C3B_DISJ_CLOSE_TAC = FIRST [DISJ1_TAC THEN CONJ_TAC THENL [C3B_CLOSE_TAC THEN NO_TAC; C3B_ARITH_TAC];
                                DISJ2_TAC THEN CONJ_TAC THENL [C3B_CLOSE_TAC THEN NO_TAC; C3B_ARITH_TAC]];;

let PL5_R32_W64_ZERO_C3 = prove
 (`!(x:int64) (m:int64->byte).
     read (bytes32 x) (write (bytes64 x) (word 0) m) = word 0 /\
     read (bytes32 (word_add x (word 4))) (write (bytes64 x) (word 0) m) = word 0`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!y (mm:int64->byte). read (bytes32 y) mm = word (read (bytes(y,4)) mm)`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[bytes32; READ_COMPONENT_COMPOSE; asword; through; read]; ALL_TAC] THEN
  SUBGOAL_THEN `write (bytes64 x) (word 0:int64) (m:int64->byte) = write (bytes(x,8)) 0 m`
    SUBST1_TAC THENL
   [REWRITE_TAC[bytes64; WRITE_COMPONENT_COMPOSE; asword; through; write; read; VAL_WORD_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x:int64`; `4`; `4`; `write (bytes(x:int64,8)) 0 (m:int64->byte)`] READ_BYTES_COMBINE) THEN
  REWRITE_TAC[ARITH_RULE `4 + 4 = 8`] THEN
  SIMP_TAC[READ_WRITE_BYTES; DIMINDEX_64; ARITH_RULE `8 <= 2 EXP 64`; MOD_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[ADD_EQ_0; MULT_EQ_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN SIMP_TAC[]);;

let C3B_VADD32W = prove(`!a b. 4294967296 <= a + b /\ a + b < 8589934592 ==> val (word_add (word a) (word b):int32) = (a + b) - 4294967296`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_ADD_MOD] THEN MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN ASM_ARITH_TAC);;

let c3b_veq asl t =
  let lt a b = mk_binop `(<):num->num->bool` a b and le a b = mk_binop `(<=):num->num->bool` a b
  and pl a b = mk_binop `(+):num->num->num` a b in
  match rand t with
      Comb(Const("word",_),e) -> MP (SPEC e C3B_VW32) (c3b_arith asl (lt e `4294967296`))
    | x -> let a = rand(lhand x) and b = rand(rand x) in
           (try MP (SPECL [a;b] C3B_VADD32) (c3b_arith asl (lt (pl a b) `4294967296`))
            with Failure _ ->
              let th = MP (SPECL [a;b] C3B_VADD32W) (c3b_arith asl (mk_conj(le `4294967296` (pl a b), lt (pl a b) `8589934592`))) in
              let n = rhs(concl(NUM_NORMALIZE_CONV (pl a b))) in
              let (x,k) = try let l,r = dest_binop `(+):num->num->num` n in
                                if is_numeral r then (l,r) else if is_numeral l then (r,l) else failwith "" with Failure _ -> failwith "wrapnorm" in
              let k' = mk_numeral (Num.sub_num (dest_numeral k) (Num.num_of_string "4294967296")) in
              let tgt = mk_binop `(+):num->num->num` x k' in
              TRANS th (c3b_arith asl (mk_eq(rhs(concl th), tgt))));;

let c3b_is_v t = match t with
      Comb(Const("val",_),Comb(Const("word",_),e)) -> type_of (rand t) = `:int32`
    | Comb(Const("val",_),Comb(Comb(Const("word_add",_),Comb(Const("word",_),_)),Comb(Const("word",_),_))) -> type_of (rand t) = `:int32`
    | _ -> false;;

let C3B_VNORM_TAC : tactic = fun (asl,w) ->
  let tms = w :: map (concl o snd) asl in
  let vs = setify (List.concat (map (find_terms c3b_is_v) tms)) in
  let ths = mapfilter (c3b_veq asl) vs in
  if ths = [] then ALL_TAC (asl,w) else (RULE_ASSUM_TAC(REWRITE_RULE ths) THEN REWRITE_TAC ths) (asl,w);;

(* add val facts for given int32 terms as assumptions (for the stepper's bound decisions) *)
let C3B_VFACTS_TAC (ts:term list) : tactic = fun (asl,w) ->
  MAP_EVERY (fun t -> ASSUME_TAC (c3b_veq asl (mk_comb(`val:int32->num`, t)))) ts (asl,w);;

let C3B_R32_W64Z = prove
 (`!x a (m:int64->byte). (x = a \/ x = a + 4 \/ x + 4 <= a \/ a + 8 <= x) /\ x < 4294967296 /\ a + 4 < 4294967296
     ==> read (bytes32 (word x)) (write (bytes64 (word a)) (word 0) m) =
         if x = a \/ x = a + 4 then word 0 else read (bytes32 (word x)) m`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x:num = a` THEN ASM_REWRITE_TAC[PL5_R32_W64_ZERO_C3] THEN
  ASM_CASES_TAC `x:num = a + 4` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_TAC THEN REWRITE_TAC[WORD_ADD] THEN REWRITE_TAC[PL5_R32_W64_ZERO_C3];
    STRIP_TAC THEN MATCH_MP_TAC VK_R32_W64 THEN ASM_ARITH_TAC]);;

let c3b_is_row64 t = match t with
    Comb(Comb(Const("read",_),Comb(Const("bytes32",_),Comb(Const("word",_),_))),
         Comb(Comb(Comb(Const("write",_),Comb(Const("bytes64",_),Comb(Const("word",_),_))),z),_)) -> z = `word 0:int64`
  | _ -> false;;

let rec C3B_ROWC asl t =
  if c3b_is_row t then
    let x = rand(rand(rand(rator t))) and m = rand t in
    let a = rand(rand(rand(rator(rator m)))) and v = rand(rator m) and m' = rand m in
    let th = SPECL [x;a;v;m'] C3B_ROW in
    let th = MP th (c3b_arith asl (lhand(concl th))) in
    let c = mk_eq(x,a) in
    let d = try EQT_INTRO (c3b_arith asl c) with Failure _ -> EQF_INTRO (c3b_arith asl (mk_neg c)) in
    let th2 = CONV_RULE(RAND_CONV(REWRITE_CONV[d])) th in
    TRANS th2 (C3B_ROWC asl (rhs(concl th2)))
  else if c3b_is_row64 t then
    let x = rand(rand(rand(rator t))) and m = rand t in
    let a = rand(rand(rand(rator(rator m)))) and m' = rand m in
    let th = SPECL [x;a;m'] C3B_R32_W64Z in
    let th = MP th (c3b_arith asl (lhand(concl th))) in
    let c = rand(rator(rator(rhs(concl th)))) in
    let d = try EQT_INTRO (c3b_arith asl c) with Failure _ -> EQF_INTRO (c3b_arith asl (mk_neg c)) in
    let th2 = CONV_RULE(RAND_CONV(REWRITE_CONV[d])) th in
    TRANS th2 (C3B_ROWC asl (rhs(concl th2)))
  else REFL t;;

let C3B_ROW1_TAC : tactic = fun (asl,w) ->
  let ts = find_terms (fun t -> c3b_is_row t || c3b_is_row64 t) w in
  let rec go = function [] -> failwith "C3B_ROW1_TAC"
    | t::r -> (try let th = C3B_ROWC asl t in if rhs(concl th) = t then go r else th with Failure _ -> go r) in
  let th = go ts in REWRITE_TAC[th] (asl,w);;

let C3B_ROW_TAC = REPEAT C3B_ROW1_TAC;;

let C3B_W32S_W64 = prove
 (`!base n f e (v:int64) m.
     va1_w32s base n f m /\ (e + 8 <= base \/ base + 4 * n <= e) /\
     base + 4 * n <= 4294967296 /\ e < 4294967296
     ==> va1_w32s base n f (write (bytes64 (word e)) v m)`,
  REWRITE_TAC[va1_w32s] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`base + 4 * k`; `e:num`; `v:int64`; `m:int64->byte`] VK_R32_W64) THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[]]));;

let C3B_W32S_TAC = REWRITE_TAC[C3B_MDL_W32S] THEN
  REPEAT ((MATCH_MP_TAC C3B_W32S_W32 ORELSE MATCH_MP_TAC C3B_W32S_W64) THEN CONJ_TAC THENL [ALL_TAC; C3B_ARITH_TAC]) THEN
  ASM_REWRITE_TAC[GSYM C3B_MDL_W32S];;

let c3b_is_ldeq c = is_eq c && is_var (rhs c) && (let n = fst(dest_var(rhs c)) in String.length n > 2 && String.sub n 0 2 = "ld") && c3b_is_ld (lhs c);;

let c3b_wn th = CONV_RULE(ONCE_DEPTH_CONV C3B_WARG_CONV) th;;

(* replace every load abbreviation ldN by the fact it reads (facts: |- read (bytes32 (word X)) m0 = value) *)
let C3B_LDFIX_TAC (facts:thm list) : tactic = fun (asl,w) ->
  let facts = map c3b_wn facts in
  let lds = filter (fun th -> c3b_is_ldeq (concl th)) (map snd asl) in
  let fix th = let l = lhs(concl th) in
    let r = C3B_ROWC asl l in
    let th' = c3b_wn (TRANS (SYM r) th) in
    let f = find (fun f -> lhs(concl f) = lhs(concl th')) facts in
    TRANS (SYM th') f in
  let eqs = mapfilter fix lds in
  MAP_EVERY (fun e -> SUBST_ALL_TAC e) eqs (asl,w);;

(* the table and model facts the bead loop reads, at bead k *)
let c3b_l4facts asl =
  let tb = find (fun th -> match strip_comb (concl th) with (Const("va1_w32s",_),[b;_;_;m]) -> b = `65536` && m = `m0:int64->byte` | _ -> false) (map snd asl) in
  let tb' = REWRITE_RULE[va1_w32s] tb in
  let inst e = MP (SPEC e tb') (c3b_arith asl (mk_binop `(<):num->num->bool` e `262144`)) in
  let md = find (fun th -> let c = concl th in is_eq c && is_comb (lhs c) && lhs c = `read (bytes32 (word 16648)) (m0:int64->byte)`) (map snd asl) in
  [inst `128 * k`; inst `128 * k + 1`; md];;

let C3B_HDR = prove(C3B_HDR_STMT,
  REPEAT GEN_TAC THEN TRY(DISCH_THEN STRIP_ASSUME_TAC) THEN C3B_INIT_TAC THEN
  (fun g -> c3b_abbrev_thresh := 60; let r = (try C3B_RUN C3B_EXEC [718] g with e -> (c3b_abbrev_thresh := 0; raise e)) in c3b_abbrev_thresh := 0; r) THEN
  ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN C3B_EXISTS_MEM_TAC THEN C3B_CLOSE_TAC THEN
  REPEAT CONJ_TAC THEN C3B_MEMFACT_TAC);;

let C3B_L4MEM_TAC : tactic =
  W(fun (asl,w) -> C3B_LDFIX_TAC (c3b_l4facts asl)) THEN
  CONJ_TAC THENL
   [REPEAT CONJ_TAC THEN TRY C3B_ROW_TAC THEN TRY C3B_W32S_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC;
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_CASES_TAC `j:num = k` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN C3B_ROW_TAC THEN
      REWRITE_TAC[va1_rbinit_b; va1_zpseed_b; LET_DEF; LET_END_DEF; COND_SWAP];
      C3B_ROW_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (is_forall o concl)) THEN
      ANTS_TAC THENL [C3B_ARITH_TAC; SIMP_TAC[]]]];;

let c3b_A kk mv = subst [kk,`k:num`; mv,`m:int64->byte`]
  `!j. j < k ==> read (bytes32 (word (1130496 + 4 * j))) (m:int64->byte) = word 251658 /\
                 read (bytes32 (word (1138688 + 4 * j))) m = va1_rbinit_b tbl j /\
                 read (bytes32 (word (1146880 + 4 * j))) m = word 0 /\
                 read (bytes32 (word (1155072 + 4 * j))) m = word 0 /\
                 read (bytes32 (word (1163264 + 4 * j))) m = word 0 /\
                 read (bytes32 (word (1171456 + 4 * j))) m = va1_zpseed_b mdl j`;;

let C3B_IT4_STMT = c3b_seg (list_mk_conj [`k < 2048`; c3b_F `m0:int64->byte`; c3b_A `k:num` `m0:int64->byte`;
      `read (bytes32 (word 16648)) m0 = (mdl:num->int32) 2`])
   (c3b_pred 718 [Lp 716] (c3b_trkL4 `k:num`) [])
   (mk_abs(`s:wasmstate`, mk_exists(`m1:int64->byte`, list_mk_conj
      [mk_disj(mk_conj(c3b_bodym `m1:int64->byte` 718 [Lp 716] (c3b_trkL4 `k + 1`) [], `k + 1 < 2048`),
               mk_conj(c3b_bodym `m1:int64->byte` 964 [] [] [], `k + 1 = 2048`));
       c3b_F `m1:int64->byte`; c3b_A `k + 1` `m1:int64->byte`])));;

let C3B_IT4 = prove(C3B_IT4_STMT,
  REPEAT GEN_TAC THEN TRY(DISCH_THEN STRIP_ASSUME_TAC) THEN C3B_INIT_TAC THEN c3b_time "it4" (C3B_RUN1 C3B_EXEC [718; 964]) THEN
  ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  (CONJ_TAC THENL [ALL_TAC; C3B_VNORM_TAC THEN MONOTONE_MAYCHANGE_TAC]) THEN
  C3B_EXISTS_MEM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `k:num` C3B_EXIT4) (ASSUME `k < 2048`)]) THEN
  C3B_VNORM_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD]) THEN C3B_WNORM_TAC THEN
  (CONJ_TAC THENL [C3B_DISJ_CLOSE_TAC; ALL_TAC]) THEN
  c3b_time "l4mem" C3B_L4MEM_TAC);;

let C3B_ENS_PRE_CONJ = prove(`!A c Q (C:wasmstate->wasmstate->bool). (c ==> ensures wasm A Q C) ==> ensures wasm (\s. A s /\ c) Q C`, REWRITE_TAC[ensures] THEN MESON_TAC[]);;

let C3B_ENS_TRANS = prove(mk_forall(`P:wasmstate->bool`, mk_forall(`Q:wasmstate->bool`, mk_forall(`R:wasmstate->bool`,
   mk_imp(mk_conj(c3b_ens `P:wasmstate->bool` `Q:wasmstate->bool`, c3b_ens `Q:wasmstate->bool` `R:wasmstate->bool`),
          c3b_ens `P:wasmstate->bool` `R:wasmstate->bool`)))),
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN EXISTS_TAC `Q:wasmstate->bool` THEN
  ASM_REWRITE_TAC[] THEN MAYCHANGE_IDEMPOT_TAC);;

let C3B_ENS_CASES = prove
 (`!P A B R (C:wasmstate->wasmstate->bool).
     (!s. P s ==> A s \/ B s) /\ ensures wasm A R C /\ ensures wasm B R C ==> ensures wasm P R C`,
  REWRITE_TAC[ensures] THEN MESON_TAC[]);;

let C3B_ENS_EXISTS = prove
 (`!P R (C:wasmstate->wasmstate->bool). (!m:int64->byte. ensures wasm (P m) R C) ==> ensures wasm (\s. ?m. P m s) R C`,
  REWRITE_TAC[ensures] THEN MESON_TAC[]);;

let C3B_ENS_FALSE = prove
 (`!P R (C:wasmstate->wasmstate->bool). (!s. ~P s) ==> ensures wasm P R C`,
  REWRITE_TAC[ensures] THEN MESON_TAC[]);;

let C3B_ENS_NOW = prove(mk_forall(`P:wasmstate->bool`, mk_forall(`Q:wasmstate->bool`,
   mk_imp(`!s:wasmstate. P s ==> Q s`, c3b_ens `P:wasmstate->bool` `Q:wasmstate->bool`))),
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_SIMP_TAC[]);;

let C3B_ENS_PRE = prove
 (`!P P' Q (C:wasmstate->wasmstate->bool). (!s. P s ==> P' s) /\ ensures wasm P' Q C ==> ensures wasm P Q C`,
  REWRITE_TAC[ensures] THEN MESON_TAC[]);;

let c3b_L4post = mk_abs(`s:wasmstate`, mk_exists(`m1:int64->byte`, list_mk_conj
   [c3b_bodym `m1:int64->byte` 964 [] [] []; c3b_F `m1:int64->byte`; c3b_A `2048` `m1:int64->byte`]));;

let C3B_LOOP4_STMT = mk_forall(`d:num`, list_mk_forall([`k:num`;`m0:int64->byte`;`t:int32`;`a0:int32`;`a1:int32`;`a2:int32`;`mdl:num->int32`;`tbl:num->int32`],
   mk_imp(list_mk_conj [`k + d = 2047`; c3b_F `m0:int64->byte`; c3b_A `k:num` `m0:int64->byte`],
          c3b_ens (c3b_pred 718 [Lp 716] (c3b_trkL4 `k:num`) []) c3b_L4post)));;

let C3B_MDL2 = prove(`!mdl m. va1_mdl mdl m ==> read (bytes32 (word 16648)) m = mdl 2`,
  REWRITE_TAC[va1_mdl] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `2`) THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let C3B_LOOP4 = prove(C3B_LOOP4_STMT,
  INDUCT_TAC THEN (REPEAT GEN_TAC THEN STRIP_TAC THEN
  (MATCH_MP_TAC C3B_ENS_TRANS THEN
   W(fun (asl,w) -> let it = SPEC_ALL C3B_IT4 in
     EXISTS_TAC (rand(rator(snd(dest_imp(concl it))))) THEN CONJ_TAC THENL
      [MATCH_MP_TAC it THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; MATCH_MP_TAC C3B_MDL2 THEN ASM_REWRITE_TAC[]];
       ALL_TAC]) THEN
   MATCH_MP_TAC C3B_ENS_EXISTS THEN X_GEN_TAC `m1:int64->byte` THEN
   MATCH_MP_TAC C3B_ENS_CASES THEN
   EXISTS_TAC (mk_abs(`s:wasmstate`, list_mk_conj [c3b_bodym `m1:int64->byte` 718 [Lp 716] (c3b_trkL4 `k + 1`) []; `k + 1 < 2048`;
                    c3b_F `m1:int64->byte`; c3b_A `k + 1` `m1:int64->byte`])) THEN
   EXISTS_TAC (mk_abs(`s:wasmstate`, list_mk_conj [c3b_bodym `m1:int64->byte` 964 [] [] []; `k + 1 = 2048`;
                    c3b_F `m1:int64->byte`; c3b_A `k + 1` `m1:int64->byte`])) THEN
   REPEAT CONJ_TAC THENL
    [GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONV_TAC TAUT;
     ALL_TAC;
     MATCH_MP_TAC C3B_ENS_NOW THEN GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
     EXISTS_TAC `m1:int64->byte` THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `k + 1 = 2048`)) THEN
     ASM_REWRITE_TAC[] THEN REWRITE_TAC[injectivity "wval"; C3B_EX_EQ]]) THEN
  (ASM_CASES_TAC `k + 1 < 2048` THENL
   [ALL_TAC; MATCH_MP_TAC C3B_ENS_FALSE THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[]]) THEN
  TRY(MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC) THEN
  MATCH_MP_TAC C3B_ENS_PRE THEN EXISTS_TAC (mk_abs(`s:wasmstate`, mk_conj(c3b_bodym `m1:int64->byte` 718 [Lp 716] (c3b_trkL4 `k + 1`) [],
     list_mk_conj [c3b_F `m1:int64->byte`; c3b_A `k + 1` `m1:int64->byte`]))) THEN
  (CONJ_TAC THENL [GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONV_TAC TAUT; ALL_TAC]) THEN
  MATCH_MP_TAC C3B_ENS_PRE_CONJ THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k + 1`; `m1:int64->byte`; `t:int32`;`a0:int32`;`a1:int32`;`a2:int32`;`mdl:num->int32`;`tbl:num->int32`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC));;

let c3b_D ii mv = subst [ii,`i:num`; mv,`m:int64->byte`]
  `!j. j < 8 * i ==> read (bytes32 (word (1179648 + 4 * j))) (m:int64->byte) = word 0`;;

let c3b_trkL5 ii = [8, mk_comb(`word:num->int32`, mk_binop `(+):num->num->num` `4294180864` (mk_binop `( * ):num->num->num` `32` ii))];;

let C3B_EXIT5 = prove(`!i. i < 24576 ==> (word_add (word (4294180864 + 32 * i)) (word 32):int32 = word 0 <=> i + 1 = 24576)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `i = 24575` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV)) THEN REWRITE_TAC[];
    REWRITE_TAC[GSYM WORD_ADD; GSYM VAL_EQ; VAL_WORD_0] THEN
    SUBGOAL_THEN `val (word ((4294180864 + 32 * i) + 32):int32) = (4294180864 + 32 * i) + 32` SUBST1_TAC THENL
     [MATCH_MP_TAC C3B_VW32 THEN ASM_ARITH_TAC; ASM_ARITH_TAC]]);;

let C3B_IT5_STMT = c3b_seg (list_mk_conj [`i < 24576`; c3b_F `m0:int64->byte`; c3b_A `2048` `m0:int64->byte`; c3b_D `i:num` `m0:int64->byte`])
   (c3b_pred 972 [Lp 970] (c3b_trkL5 `i:num`) [])
   (mk_abs(`s:wasmstate`, mk_exists(`m1:int64->byte`, list_mk_conj
      [mk_disj(mk_conj(c3b_bodym `m1:int64->byte` 972 [Lp 970] (c3b_trkL5 `i + 1`) [], `i + 1 < 24576`),
               mk_conj(c3b_bodym `m1:int64->byte` 1034 [] [] [], `i + 1 = 24576`));
       c3b_F `m1:int64->byte`; c3b_A `2048` `m1:int64->byte`; c3b_D `i + 1` `m1:int64->byte`])));;

let C3B_R8_TAC : tactic =
  SUBGOAL_THEN `?r. r < 8 /\ j = 8 * i + r` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `j - 8 * i` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC (DISJ_CASES_THEN2 SUBST_ALL_TAC (DISJ_CASES_THEN2 SUBST_ALL_TAC
     (DISJ_CASES_THEN2 SUBST_ALL_TAC (DISJ_CASES_THEN2 SUBST_ALL_TAC (DISJ_CASES_THEN2 SUBST_ALL_TAC
     (DISJ_CASES_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC)))))) o MATCH_MP (ARITH_RULE `r < 8 ==> r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7`)) THEN
  C3B_WNORM_TAC THEN C3B_ROW_TAC;;

let C3B_L5MEM_TAC : tactic =
  CONJ_TAC THENL [REPEAT CONJ_TAC THEN TRY C3B_ROW_TAC THEN TRY C3B_W32S_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN C3B_ROW_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) && can (find_term ((=) `251658`)) (concl th))) THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_CASES_TAC `j < 8 * i` THENL
     [C3B_ROW_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) && can (find_term ((=) `1179648`)) (concl th))) THEN
      ASM_SIMP_TAC[];
      C3B_R8_TAC]];;

let C3B_IT5 = prove(C3B_IT5_STMT,
  REPEAT GEN_TAC THEN TRY(DISCH_THEN STRIP_ASSUME_TAC) THEN C3B_INIT_TAC THEN
  C3B_VFACTS_TAC (map (fun c -> mk_binop `word_add:int32->int32->int32` `word (4294180864 + 32 * i):int32` (mk_comb(`word:num->int32`, mk_small_numeral c))) [1966104;1966096;1966088;1966080]) THEN c3b_time "it5" (C3B_RUN1 C3B_EXEC [972; 1034]) THEN
  ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  TRY(CONJ_TAC THENL [ALL_TAC; C3B_VNORM_TAC THEN MONOTONE_MAYCHANGE_TAC]) THEN
  C3B_EXISTS_MEM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `i:num` C3B_EXIT5) (ASSUME `i < 24576`)]) THEN
  C3B_VNORM_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD]) THEN C3B_WNORM_TAC THEN
  (CONJ_TAC THENL [C3B_DISJ_CLOSE_TAC; ALL_TAC]) THEN
  c3b_time "l5mem" C3B_L5MEM_TAC);;

let c3b_L5post = mk_abs(`s:wasmstate`, mk_exists(`m1:int64->byte`, list_mk_conj
   [c3b_bodym `m1:int64->byte` 1034 [] [] []; c3b_F `m1:int64->byte`; c3b_A `2048` `m1:int64->byte`; c3b_D `24576` `m1:int64->byte`]));;

let C3B_LOOP5_STMT = mk_forall(`d:num`, list_mk_forall([`i:num`;`m0:int64->byte`;`t:int32`;`a0:int32`;`a1:int32`;`a2:int32`;`mdl:num->int32`;`tbl:num->int32`],
   mk_imp(list_mk_conj [`i + d = 24575`; c3b_F `m0:int64->byte`; c3b_A `2048` `m0:int64->byte`; c3b_D `i:num` `m0:int64->byte`],
          c3b_ens (c3b_pred 972 [Lp 970] (c3b_trkL5 `i:num`) []) c3b_L5post)));;

let C3B_LOOP5 = prove(C3B_LOOP5_STMT,
  INDUCT_TAC THEN (REPEAT GEN_TAC THEN STRIP_TAC THEN
  (MATCH_MP_TAC C3B_ENS_TRANS THEN
   W(fun (asl,w) -> let it = SPEC_ALL C3B_IT5 in
     EXISTS_TAC (rand(rator(snd(dest_imp(concl it))))) THEN CONJ_TAC THENL
      [MATCH_MP_TAC it THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
       ALL_TAC]) THEN
   MATCH_MP_TAC C3B_ENS_EXISTS THEN X_GEN_TAC `m1:int64->byte` THEN
   MATCH_MP_TAC C3B_ENS_CASES THEN
   EXISTS_TAC (mk_abs(`s:wasmstate`, list_mk_conj [c3b_bodym `m1:int64->byte` 972 [Lp 970] (c3b_trkL5 `i + 1`) []; `i + 1 < 24576`;
                    c3b_F `m1:int64->byte`; c3b_A `2048` `m1:int64->byte`; c3b_D `i + 1` `m1:int64->byte`])) THEN
   EXISTS_TAC (mk_abs(`s:wasmstate`, list_mk_conj [c3b_bodym `m1:int64->byte` 1034 [] [] []; `i + 1 = 24576`;
                    c3b_F `m1:int64->byte`; c3b_A `2048` `m1:int64->byte`; c3b_D `i + 1` `m1:int64->byte`])) THEN
   REPEAT CONJ_TAC THENL
    [GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONV_TAC TAUT;
     ALL_TAC;
     MATCH_MP_TAC C3B_ENS_NOW THEN GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
     EXISTS_TAC `m1:int64->byte` THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `i + 1 = 24576`)) THEN
     ASM_REWRITE_TAC[] THEN REWRITE_TAC[injectivity "wval"; C3B_EX_EQ]]) THEN
  (ASM_CASES_TAC `i + 1 < 24576` THENL
   [ALL_TAC; MATCH_MP_TAC C3B_ENS_FALSE THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[]]) THEN
  TRY(MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC) THEN
  MATCH_MP_TAC C3B_ENS_PRE THEN EXISTS_TAC (mk_abs(`s:wasmstate`, mk_conj(c3b_bodym `m1:int64->byte` 972 [Lp 970] (c3b_trkL5 `i + 1`) [],
     list_mk_conj [c3b_F `m1:int64->byte`; c3b_A `2048` `m1:int64->byte`; c3b_D `i + 1` `m1:int64->byte`]))) THEN
  (CONJ_TAC THENL [GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONV_TAC TAUT; ALL_TAC]) THEN
  MATCH_MP_TAC C3B_ENS_PRE_CONJ THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i + 1`; `m1:int64->byte`; `t:int32`;`a0:int32`;`a1:int32`;`a2:int32`;`mdl:num->int32`;`tbl:num->int32`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC));;

let C3B_L5E = prove(c3b_seg `T` (c3b_pred 964 [] [] []) (c3b_pred 972 [Lp 970] (c3b_trkL5 `0`) []),
  C3B_SEG_TAC "l5e" [972]);;

let C3B_TAIL_STMT = c3b_seg (list_mk_conj [c3b_F `m0:int64->byte`; c3b_A `2048` `m0:int64->byte`; c3b_D `24576` `m0:int64->byte`])
   (c3b_pred 1034 [] [] [])
   `\s. read wstatus s = WDone /\ read wstack s = [I32 (word 0)] /\ va1_f25_post t mdl tbl a0 a1 a2 (read wmem s)`;;

let C3B_ASPLIT_TAC : tactic =
  ASM_CASES_TAC `k < 2048` THENL
   [ALL_TAC;
    ASM_CASES_TAC `k < 4096` THENL
     [SUBGOAL_THEN `?j. j < 2048 /\ k = 2048 + j` STRIP_ASSUME_TAC THENL [EXISTS_TAC `k - 2048` THEN ASM_ARITH_TAC; ALL_TAC];
      SUBGOAL_THEN `?j. j < 2048 /\ k = 4096 + j` STRIP_ASSUME_TAC THENL [EXISTS_TAC `k - 4096` THEN ASM_ARITH_TAC; ALL_TAC]] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN C3B_WNORM_TAC];;

let c3b_asm_with c = fun (asl:(string*thm)list) -> find (fun th -> is_forall(concl th) && can (find_term ((=) c)) (concl th)) (map snd asl);;

let C3B_USEFACT_TAC c v : tactic = fun (asl,w) ->
  let th = c3b_asm_with c asl in
  (MP_TAC (SPEC v th) THEN ANTS_TAC THENL [C3B_ARITH_TAC; SIMP_TAC[]]) (asl,w);;

let C3B_TAILMEM_TAC : tactic =
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN C3B_ROW_TAC THEN
  FIRST [C3B_USEFACT_TAC `1130496` `k:num` THEN NO_TAC;
         C3B_USEFACT_TAC `1179648` `k:num` THEN NO_TAC;
         C3B_ASPLIT_TAC THEN FIRST [C3B_USEFACT_TAC `1130496` `k:num` THEN NO_TAC; C3B_USEFACT_TAC `1130496` `j:num` THEN NO_TAC]];;

let C3B_TAIL = prove(C3B_TAIL_STMT,
  REPEAT GEN_TAC THEN TRY(DISCH_THEN STRIP_ASSUME_TAC) THEN C3B_INIT_TAC THEN C3B_RUN C3B_EXEC [] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[injectivity "wval"] THEN
  REWRITE_TAC[va1_f25_post; va1_w32s] THEN C3B_WNORM_TAC THEN REPEAT CONJ_TAC THEN
  TRY(C3B_ROW_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN C3B_TAILMEM_TAC);;

let C3B_F25_OK_STMT = `!(a0:int32) (a1:int32) (a2:int32) (t:int32) (mdl:num->int32) (tbl:num->int32) (decls:wval list).
     ~(a0 = word 0 /\ a1 = word 0 /\ a2 = word 0) /\ wasm_decl_vals va1_f25_mc = SOME decls
     ==> ensures wasm
          (\s. read wcode s = va1_f25_mc /\ read wpc s = word 13 /\ read wstatus s = WRunning /\
               read wstack s = [] /\ read wlabels s = [] /\ read warity s = 1 /\
               read wmemsize s = 4194304 /\
               read wlocals s = wcall_locals [I32 a2; I32 a1; I32 a0] decls /\
               va1_tick t (read wmem s) /\ read (bytes32 (word 16396)) (read wmem s) = word 4294967295 /\
               va1_mdl mdl (read wmem s) /\ va1_w32s 65536 262144 tbl (read wmem s))
          (\s. read wstatus s = WDone /\ read wstack s = [I32 (word 0)] /\
               va1_f25_post t mdl tbl a0 a1 a2 (read wmem s))
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocal 0; wlocal 1; wlocal 2; wlocal 3; wlocal 4; wlocal 5; wlocal 6; wlocal 7;
                      wlocal 8; wlocal 9; wlocal 10; wlocal 11; wlocal 12; wlocal 13; wlocal 14; wlocal 15] ,,
           MAYCHANGE [wmem :> bytes(word 16396,8)] ,, MAYCHANGE [wmem :> bytes(word 16408,96)] ,,
           MAYCHANGE [wmem :> bytes(word 1130496,835584)])`;;

let c3b_chain ths = end_itlist (fun a b -> MATCH_MP C3B_ENS_TRANS (CONJ a b)) ths;;

let c3b_mp asl th = let th1 = SPEC_ALL th in
  if is_imp (concl th1) then MP th1 (TAC_PROOF((asl, lhand(concl th1)), ASM_REWRITE_TAC[] THEN TRY C3B_ARITH_TAC)) else th1;;

let C3B_ENTRY_LOCALS_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `wlocals`)) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `wasm_decl_vals`)) (concl th))) THEN
  REWRITE_TAC[C3B_DECLS] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[wlocal; READ_COMPONENT_COMPOSE] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[wcall_locals; LENGTH; READ_ELEMENT] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV);;

let C3B_A0 = prove(c3b_A `0` `m:int64->byte`, REWRITE_TAC[LT]);;

let C3B_D0 = prove(c3b_D `0` `m:int64->byte`, REWRITE_TAC[MULT_CLAUSES; LT]);;

let c3b_mpi asl th inst = let th1 = INST inst (SPEC_ALL th) in
  if is_imp (concl th1) then MP th1 (TAC_PROOF((asl, lhand(concl th1)), ASM_REWRITE_TAC[C3B_A0; C3B_D0] THEN TRY C3B_ARITH_TAC)) else th1;;

let c3b_isq32 th = SPEC_ALL (MP (SPEC `32` th) (ARITH_RULE `1 <= 32 /\ 32 <= 32`));;

let C3B_STEP_TO_TAC (th:thm) : tactic =
  MATCH_MP_TAC C3B_ENS_TRANS THEN EXISTS_TAC (rand(rator(concl th))) THEN CONJ_TAC THENL [ACCEPT_TAC th; ALL_TAC];;

let C3B_OPEN_TAC v : tactic = MATCH_MP_TAC C3B_ENS_EXISTS THEN X_GEN_TAC v THEN BETA_TAC THEN MATCH_MP_TAC C3B_ENS_PRE_CONJ THEN STRIP_TAC;;

let VA1_F25_OK = prove(C3B_F25_OK_STMT,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC C3B_ENS_PRE THEN
  EXISTS_TAC (mk_abs(`s:wasmstate`, mk_exists(`m0:int64->byte`, list_mk_conj [c3b_body 13 [] c3b_trk0 [];
     `read (bytes32 (word 16396)) (m0:int64->byte) = word 4294967295 /\ ~(word_or (word_or (a1:int32) a0) a2 = word 0) /\
      read (bytes32 (word 16392)) m0 = (t:int32) /\ va1_mdl mdl m0 /\ va1_w32s 65536 262144 tbl m0`]))) THEN
  (CONJ_TAC THENL
   [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN EXISTS_TAC `read wmem (s:wasmstate)` THEN
    C3B_ENTRY_LOCALS_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[va1_tick]) THEN ASM_REWRITE_TAC[WORD_OR_EQ_0] THEN ASM_MESON_TAC[];
    ALL_TAC]) THEN
  C3B_OPEN_TAC `m0:int64->byte` THEN
  W(fun (asl,w) -> C3B_STEP_TO_TAC (c3b_chain [c3b_mp asl C3B_PRO; c3b_isq32 C3B_ISQ1; c3b_mp asl C3B_MID; c3b_isq32 C3B_ISQ2; c3b_mp asl C3B_HDR])) THEN
  C3B_OPEN_TAC `m1:int64->byte` THEN
  W(fun (asl,w) -> C3B_STEP_TO_TAC (c3b_mpi asl C3B_LOOP4 [`2047`,`d:num`; `0`,`k:num`; `m1:int64->byte`,`m0:int64->byte`])) THEN
  C3B_OPEN_TAC `m2:int64->byte` THEN
  W(fun (asl,w) -> C3B_STEP_TO_TAC (c3b_chain [c3b_mpi asl C3B_L5E [`m2:int64->byte`,`m0:int64->byte`];
                                                 c3b_mpi asl C3B_LOOP5 [`24575`,`d:num`; `0`,`i:num`; `m2:int64->byte`,`m0:int64->byte`]])) THEN
  C3B_OPEN_TAC `m3:int64->byte` THEN
  W(fun (asl,w) -> ACCEPT_TAC (c3b_mpi asl C3B_TAIL [`m3:int64->byte`,`m0:int64->byte`])));;
