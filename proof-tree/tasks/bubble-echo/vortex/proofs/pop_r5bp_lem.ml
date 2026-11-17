(* ========================================================================= *)
(* Vortex pop R5, droplet birth (vortex-r5birth PROVE-birth r1, Claude Opus  *)
(* 5.5, 2026-11-11): lemma layer toward va1_birth_ok (f13 birth_apply of     *)
(* vortex_a1.wasm, frozen spec pop_r5_birth.spec b4f30c76). LEAFCHAIN layer  *)
(* on the decode layer pop_r5b_bdec.ml (POP_R5B_F13_EXEC). Contents:         *)
(*  - a data-blind stepping driver (R5B_RUN): one instruction at a time;     *)
(*    undecided trap/bounds guards are decided from val-bound facts of their *)
(*    subterms, data branches are case-split, big values are generalized;    *)
(*  - R5B_SEL1_NZ (clamped divisors), R5B_SPD_NZ (SPD_BOUND: the rounded     *)
(*    interpolation stays below 2^31, so spd * spd does not wrap to 0);       *)
(*  - loop 1 (pinch-off) segment lemmas on a typed-locals interface with the *)
(*    memory as a variable m0: SEGA 146->469|2586, SEGB 469->573, ISQ1-3     *)
(*    (isqrt loops by induction on the counter), SEGC 627->1755, SEGD        *)
(*    1809->1964, BACK1 2586->146|2612;                                       *)
(*  - pure push lemmas and R5B_BIRTH_APPEND1 (a pinch-off birth keeps the    *)
(*    loop memory invariant).                                                *)
(* Not in this layer (open): SEGE 2018->2586 closure, loops 2/3, glue.       *)
(* ========================================================================= *)
(* ========================================================================= *)
(* R5 PROVE-birth (Claude Opus 5.5, 2026-11-11): data-blind stepping driver  *)
(* for f13 birth_apply. Steps one instruction at a time; a guard the stepper *)
(* leaves undecided is first retried with val-bound facts of its subterms    *)
(* (masks, shifts, sums: trap/bounds guards), then case-split (data branch). *)
(* ========================================================================= *)
let R5B_EXEC = POP_R5B_F13_EXEC;;
let r5b_extra = ref ([]:thm list);;

let R5B_VADD = prove(`!a b:N word. val(word_add a b) <= val a + val b`, REWRITE_TAC[VAL_WORD_ADD; MOD_LE]);;
let R5B_VMUL = prove(`!a b:N word. val(word_mul a b) <= val a * val b`, REWRITE_TAC[VAL_WORD_MUL; MOD_LE]);;
let R5B_VSHL = prove(`!(a:N word) k. val(word_shl a k) <= 2 EXP k * val a`, REWRITE_TAC[VAL_WORD_SHL; MOD_LE]);;
let R5B_VZX = prove(`!(a:M word). val(word_zx a:N word) <= val a`, REWRITE_TAC[VAL_WORD_ZX_GEN; MOD_LE]);;
let R5B_VWORD = prove(`!e. val(word e:N word) <= e`, REWRITE_TAC[VAL_WORD; MOD_LE]);;
let R5B_VUSHR = prove(`!(a:N word) k. 2 EXP k * val(word_ushr a k) < 2 EXP dimindex(:N)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_USHR] THEN
  MP_TAC(ISPECL [`val(a:N word)`; `2 EXP k`] DIV_MUL_LE) THEN
  MP_TAC(ISPEC `a:N word` VAL_BOUND) THEN ARITH_TAC);;
let R5B_VAND32 = prove(`!x y:int32. val(word_and x y) <= val y /\ val(word_and x y) <= val x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM WORD_ULE] THEN CONJ_TAC THEN BITBLAST_TAC);;

let r5b_nred th = CONV_RULE(DEPTH_CONV(NUM_RED_CONV ORELSEC (fun t -> if t = `dimindex(:32)` then DIMINDEX_32 else
                    if t = `dimindex(:64)` then DIMINDEX_64 else failwith "")) THENC NUM_REDUCE_CONV) th;;

(* val-bound facts for t and its word subterms *)
let r5b_pm rule vt = r5b_nred (PART_MATCH lhand (SPEC_ALL rule) vt);;
let R5B_VCOND = prove(`!c (a:N word) b. val (if c then a else b) <= val a + val b`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ARITH_TAC);;
let rec r5b_tfacts t =
  let vt = mk_icomb(`val:N word->num`, t) in
  if is_cond t then
    let _,(a,b) = dest_cond t in
    (try [r5b_nred (PART_MATCH lhand (SPEC_ALL R5B_VCOND) vt)] with Failure _ -> []) @ r5b_tfacts a @ r5b_tfacts b @
    (try [r5b_nred (ISPEC t VAL_BOUND)] with Failure _ -> []) else
  let bnd = try [r5b_nred (ISPEC t VAL_BOUND)] with Failure _ -> [] in
  let sub = try
    let h,args = strip_comb t in
    match (fst(dest_const h), args) with
      ("word_add",[a;b]) -> r5b_pm R5B_VADD vt :: (r5b_tfacts a @ r5b_tfacts b)
    | ("word_mul",[a;b]) -> r5b_pm R5B_VMUL vt :: (r5b_tfacts a @ r5b_tfacts b)
    | ("word_shl",[a;k]) -> r5b_pm R5B_VSHL vt :: r5b_tfacts a
    | ("word_ushr",[a;k]) -> [r5b_nred (PART_MATCH (rand o lhand) (SPEC_ALL R5B_VUSHR) vt)]
    | ("word_and",[a;b]) when type_of t = `:int32` ->
         map (fun c -> PART_MATCH lhand c vt) (CONJUNCTS (SPEC_ALL R5B_VAND32)) @ r5b_tfacts a @ r5b_tfacts b
    | ("word_zx",[a]) -> r5b_pm R5B_VZX vt :: r5b_tfacts a
    | ("word",[e]) -> if is_numeral e then [r5b_pm VAL_WORD vt] else [r5b_pm R5B_VWORD vt]
    | _ -> []
    with Failure _ -> [] in
  bnd @ sub;;

let setify_thms ths =
  let rec go seen = function [] -> [] | th::r -> if mem (concl th) seen then go seen r else th :: go (concl th :: seen) r in
  go [] ths;;
let r5b_gfacts g =
  let vs = find_terms (fun t -> is_comb t && (match rator t with Const("val",_) -> true | _ -> false)) g in
  let ths = List.concat (map (fun v -> try r5b_tfacts (rand v) with Failure _ -> []) vs) in
  let ths = filter (fun th -> hyp th = [] && not (concl th = `T`)) ths in
  setify_thms ths;;

let r5b_mths asl = filter (fun th -> vk_is_memfact (concl th)) (map snd asl);;
let r5b_ctr = ref 0;;
let r5b_fresh () = incr r5b_ctr; "s" ^ string_of_int !r5b_ctr;;
let r5b_log = ref true;;

let R5B_STEP1 exec sname : tactic = fun (asl,w) ->
  (CAP_STEP_TAC exec (READ_COMPONENT_COMPOSE :: (!r5b_extra @ r5b_mths asl)) sname THEN
   CAP_DISCARD_OLD_TAC sname THEN WASM_COMPACT_HYPS_TAC) (asl,w);;

let r5b_pc asl s =
  let th = find (fun th -> let c = concl th in is_eq c &&
     (match lhs c with Comb(Comb(Const("read",_),Const("wpc",_)),s') -> s' = s | _ -> false)) (map snd asl) in
  dest_small_numeral(rand(rhs(concl th)));;

let r5b_status asl s =
  try let th = find (fun th -> let c = concl th in is_eq c &&
     (match lhs c with Comb(Comb(Const("read",_),Const("wstatus",_)),s') -> s' = s | _ -> false)) (map snd asl) in
  rhs(concl th) with Failure _ -> `WTrap`;;

let r5b_guard exec (asl,w) =
  let s = rand w in
  let s' = mk_var("s_r5bg",`:wasmstate`) in
  let th = WASM_CONV (snd exec) (READ_COMPONENT_COMPOSE :: (!r5b_extra @ r5b_mths asl)) (map snd asl)
             (mk_comb(mk_comb(`wasm`,s),s')) in
  let r = rhs(concl th) in
  let c = find_term is_cond r in
  lhand(rator c);;

let r5b_strip_neg g = if is_neg g then rand g else g;;

let r5b_is_statefree tm = not (can (find_term (fun t -> type_of t = `:wasmstate`)) tm);;
(* prove g (or ~g) from the state-free num assumptions and the val-bound facts *)
let r5b_decide asl g =
  let fs = r5b_gfacts g in
  let ants = filter (fun th -> let c = concl th in wasm_is_numrel c && r5b_is_statefree c && not (is_disj c)) (map snd asl) @ fs in
  let pr t = if ants = [] then ARITH_RULE t else
    MP (ARITH_RULE (mk_imp(list_mk_conj(map concl ants), t))) (end_itlist CONJ ants) in
  try EQT_INTRO (pr g) with Failure _ -> EQF_INTRO (pr (mk_neg g));;

let R5B_GSTEP exec sname : tactic = fun (asl,w) ->
  let pc = r5b_pc asl (rand w) in
  let g = try r5b_guard exec (asl,w) with Failure m ->
    ((try ignore(R5B_STEP1 exec sname (asl,w)) with Failure m2 ->
        Printf.printf "@@STUCK pc %d: %s\n%!" pc (String.sub m2 0 (min 600 (String.length m2))));
     failwith ("r5b stuck at pc " ^ string_of_int pc)) in
  (try let gth = r5b_decide asl g in
     (fun gl -> let old = !r5b_extra in
        r5b_extra := gth :: old;
        let r = (try R5B_STEP1 exec sname gl with e -> (r5b_extra := old; raise e)) in
        r5b_extra := old;
        if !r5b_log then Printf.printf "@@BOUND pc %d\n%!" pc; r)
   with Failure _ ->
   (fun gl -> let g' = r5b_strip_neg g in
    (if !r5b_log then let st = String.map (fun c -> if c = '\n' then ' ' else c) (string_of_term g') in
       Printf.printf "@@SPLIT pc %d: %s\n%!" pc (if String.length st > 400 then String.sub st 0 400 else st));
    (ASM_CASES_TAC g' THEN R5B_STEP1 exec sname) gl)) (asl,w);;

(* data-blind generalization: a stack/local value of the current state bigger than the threshold becomes a fresh
   variable (its defining equation is dropped, which only strengthens the goal) *)
let r5b_abbrev_thresh = ref 0;;
let rec r5b_tsize t = match t with Comb(a,b) -> r5b_tsize a + r5b_tsize b | Abs(_,b) -> 1 + r5b_tsize b | _ -> 1;;
let r5b_vctr = ref 0;;
let R5B_GEN_TAC : tactic = fun (asl,w) ->
  if !r5b_abbrev_thresh = 0 then ALL_TAC (asl,w) else
  let s = rand w in
  let vals = List.concat (map (fun (_,th) -> let c = concl th in
     if is_eq c && (match lhs c with Comb(Comb(Const("read",_),comp),s') ->
                      s' = s && (comp = `wstack` || (is_comb comp && rator comp = `wlocal`)) | _ -> false)
     then (let r = rhs c in
           let elems = if is_list r then dest_list r else [r] in
           mapfilter (fun e -> let h,a = strip_comb e in
                        if (h = `I32` || h = `I64`) && length a = 1 then hd a else fail()) elems)
     else []) asl) in
  let big = setify (filter (fun v -> r5b_tsize v > !r5b_abbrev_thresh && not (is_var v)) vals) in
  let big = sort (fun a b -> r5b_tsize a > r5b_tsize b) big in
  MAP_EVERY (fun v -> fun g -> incr r5b_vctr;
       let nv = mk_var("ab" ^ string_of_int !r5b_vctr, type_of v) in
       (ABBREV_TAC (mk_eq(nv, v)) THEN
        REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> let c = concl th in is_eq c && rhs c = nv)))) g) big (asl,w);;

(* run until the pc is in stops (or the status is not WRunning) *)
let rec R5B_RUN exec stops : tactic = fun (asl,w) ->
  let s = rand w in
  if r5b_status asl s <> `WRunning` then ALL_TAC (asl,w) else
  let pc = r5b_pc asl s in
  if mem pc stops then ALL_TAC (asl,w) else
  let sn = r5b_fresh() in
  ((R5B_STEP1 exec sn ORELSE R5B_GSTEP exec sn) THEN R5B_GEN_TAC THEN R5B_RUN exec stops) (asl,w);;

let R5B_RUN1 exec stops : tactic = fun (asl,w) ->
  let sn = r5b_fresh() in ((R5B_STEP1 exec sn ORELSE R5B_GSTEP exec sn) THEN R5B_RUN exec stops) (asl,w);;

let r5b_time name (tac:tactic) : tactic = fun g ->
  let t0 = Sys.time() in let r = tac g in
  Printf.printf "@@TIME %s %.1f s cpu\n%!" name (Sys.time() -. t0); r;;

(* ---- interface predicates: control shape, typed locals, tracked locals, memory m0 *)
let r5b_ity i = i <= 15 || i = 19 || i = 32 || i = 33;;
let r5b_rd i = mk_comb(mk_comb(`read:(wasmstate,wval)component->wasmstate->wval`, mk_comb(`wlocal`, mk_small_numeral i)), `s:wasmstate`);;
let r5b_typed i =
  let xv = mk_var("x" ^ string_of_int i, if r5b_ity i then `:int32` else `:int64`) in
  mk_exists(xv, mk_eq(r5b_rd i, mk_comb((if r5b_ity i then `I32` else `I64`), xv)));;
let r5b_trk i v = mk_eq(r5b_rd i, mk_comb((if r5b_ity i then `I32` else `I64`), v));;
let r5b_lbl l = mk_list(map (fun (a,b,c) -> mk_pair(mk_small_numeral a, mk_pair(mk_small_numeral b, mk_small_numeral c))) l,
                        `:num#num#num`);;
(* blk e = block whose end instruction is at e (continuation e+1); lp p = loop instruction at p *)
type r5b_lab = Blk of int | Lp of int;;
let r5b_lb = function Blk e -> (0,e+1,0) | Lp p -> (0,p,0);;
let r5b_body pc lbls tracked extra =
  let locs = map (fun i -> try r5b_trk i (assoc i tracked) with Failure _ -> r5b_typed i) (0--41) in
  list_mk_conj
   ([`read wcode s = va1_f13_mc`; mk_eq(`read wpc s`, mk_comb(`word:num->int64`, mk_small_numeral pc));
     `read wstatus s = WRunning`; `read wstack s = []`; mk_eq(`read wlabels s`, r5b_lbl (map r5b_lb lbls));
     `read warity s = 1`; `read wmemsize s = 4194304`] @ locs @ [`read wmem s = m0`] @ extra);;
let r5b_pred pc lbls tracked extra = mk_abs(`s:wasmstate`, r5b_body pc lbls tracked extra);;
let r5b_rest q = let s,b = dest_abs q in mk_abs(s, rand(rand b));;
let R5B_FRAME = `MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
            MAYCHANGE [wstatus] ,, MAYCHANGE [wlocal 0; wlocal 1; wlocal 2; wlocal 3; wlocal 4; wlocal 5; wlocal 6; wlocal 7; wlocal 8; wlocal 9; wlocal 10; wlocal 11; wlocal 12; wlocal 13; wlocal 14; wlocal 15; wlocal 16; wlocal 17; wlocal 18; wlocal 19; wlocal 20; wlocal 21; wlocal 22; wlocal 23; wlocal 24; wlocal 25; wlocal 26; wlocal 27; wlocal 28; wlocal 29; wlocal 30; wlocal 31; wlocal 32; wlocal 33; wlocal 34; wlocal 35; wlocal 36; wlocal 37; wlocal 38; wlocal 39; wlocal 40; wlocal 41] ,,
            MAYCHANGE [wmem :> bytes(word 16400,4)] ,,
            MAYCHANGE [wmem :> bytes(word 1163264,16384)] ,,
            MAYCHANGE [wmem :> bytes(word 1179648,786432)] ,,
            MAYCHANGE [wmem :> bytes(word 1966080,73728)]`;;
let r5b_ens p q = mk_comb(mk_comb(mk_comb(`ensures wasm`, p), q), R5B_FRAME);;
let R5B_EX_EQ = prove(`!t:A. (?x. t = x) <=> T`, MESON_TAC[]);;
(* close a post conjunction at the final state *)
let R5B_CLOSE_TAC =
  ASM_REWRITE_TAC[injectivity "wval"; R5B_EX_EQ] THEN
  CONV_TAC(DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV)) THEN ASM_REWRITE_TAC[injectivity "wval"; R5B_EX_EQ];;

(* the clamped divisors (select(v,1,v >s 1)) are never 0 *)
let r5b_sel_nz ty = let v = mk_var("v", ty) in
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
let R5B_SEL1_NZ = CONJ (r5b_sel_nz `:int64`) (r5b_sel_nz `:int32`);;
let () = r5b_extra := [VK_COND_I64; VK_COND_I32; R5B_SEL1_NZ];;

let R5B_INIT_TAC = ENSURES_INIT_TAC "s0" THEN REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl)));;
(* final state: close one of the post disjuncts *)
let R5B_CLOSE1 = R5B_CLOSE_TAC THEN TRY(REPEAT CONJ_TAC THEN ASM_ARITH_TAC) THEN NO_TAC;;
let R5B_FIN_TAC : tactic =
  ENSURES_FINAL_STATE_TAC THEN
  FIRST [R5B_CLOSE1; DISJ1_TAC THEN R5B_CLOSE1; DISJ2_TAC THEN R5B_CLOSE1;
         DISJ2_TAC THEN DISJ1_TAC THEN R5B_CLOSE1; DISJ2_TAC THEN DISJ2_TAC THEN R5B_CLOSE1];;
let R5B_SEG_TAC name stops : tactic =
  REPEAT GEN_TAC THEN TRY(DISCH_THEN STRIP_ASSUME_TAC) THEN R5B_INIT_TAC THEN
  r5b_time name (R5B_RUN R5B_EXEC stops) THEN R5B_FIN_TAC;;

(* use a lemma |- !vars. [A ==>] ensures P Q C for a goal ensures P' Q' C (weakening by rewriting) *)
let R5B_USE_TAC th : tactic = fun (asl,w) ->
  let th1 = SPEC_ALL th in
  let th2 = if is_imp (concl th1) then MP th1 (TAC_PROOF((asl, lhand (concl th1)), ASM_ARITH_TAC)) else th1 in
  let th3 = try PART_MATCH I th2 w with Failure _ -> th2 in
  let c = concl th3 in
  let p = rand(rator(rator c)) and q = rand(rator c) in
  (MATCH_ACCEPT_TAC th3 ORELSE
   (MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC p THEN CONJ_TAC THENL
     [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN R5B_CLOSE_TAC;
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC q THEN CONJ_TAC THENL
       [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN R5B_CLOSE_TAC;
        ACCEPT_TAC th3]])) (asl,w);;

(* ---- the isqrt loops: loop instr at lp, body start bp = lp + 2, exit ep (after end), counter local ctr from c down *)
let R5B_DEC1 = prove
 (`!c. c < 4294967296 ==> word_add (word (SUC c)) (word 4294967295):int32 = word c /\ (word c:int32 = word 0 <=> c = 0)`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD; ARITH_RULE `SUC c + 4294967295 = c + 4294967296`] THEN
    REWRITE_TAC[WORD_ADD; WORD_RED_CONV `word 4294967296:int32`; WORD_ADD_0];
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_0; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT]]);;
let r5b_isq_stmt lp ep ctr outer trk =
  let bp = lp + 2 in
  let pre = r5b_pred bp (Lp lp :: outer) ((ctr, `word c:int32`) :: trk) [] in
  let post = r5b_pred ep outer trk [] in
  let e = r5b_ens pre post in
  let vs = subtract (frees e) [`c:num`] in
  mk_forall(`c:num`, mk_imp(`1 <= c /\ c <= 32`, list_mk_forall(vs, e)));;
let R5B_ISQ_TAC name lp ep ctr outer trk : tactic =
  let bp = lp + 2 in
  INDUCT_TAC THENL [ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC(SPEC `c:num` R5B_DEC1) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC)] THEN
  ASM_CASES_TAC `c = 0` THENL
   [R5B_INIT_TAC THEN r5b_time name (R5B_RUN1 R5B_EXEC [ep; bp]) THEN R5B_FIN_TAC;
    ENSURES_SEQUENCE_TAC (mk_small_numeral bp) (r5b_rest (r5b_pred bp (Lp lp :: outer) ((ctr, `word c:int32`) :: trk) [])) THEN
    CONJ_TAC THENL
     [R5B_INIT_TAC THEN r5b_time name (R5B_RUN1 R5B_EXEC [ep; bp]) THEN R5B_FIN_TAC;
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && is_forall(rand(concl th)))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(fun th -> R5B_USE_TAC th)]]];;
(* ---- R5 PROVE-birth: SPD_BOUND. The rounded interpolation v = b + ((a - b) f + 2^18) >>s 19 (f < 2^19) never
   exceeds max(a, b) < 2^31, so spd = max(v, 1) is in [1, 2^31) and spd * spd does not wrap to 0 (div_s D2/D13). *)
let R5B_SPD_CORE = prove
 (`!a b f:int. a < &2147483648 /\ b < &2147483648 /\ &0 <= f /\ f < &524288
     ==> b + ((a - b) * f + &262144) div &524288 < &2147483648`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`(a - b) * f + &262144:int`; `&524288:int`] INT_DIVISION) THEN
  ANTS_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN REWRITE_TAC[INT_ABS_NUM] THEN
  ABBREV_TAC `q = ((a - b) * f + &262144:int) div &524288` THEN
  ABBREV_TAC `r = ((a - b) * f + &262144:int) rem &524288` THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= a - b:int` THENL
   [MP_TAC(SPECL [`a - b:int`; `f:int`; `&524287:int`] INT_LE_LMUL) THEN
    ANTS_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC];
    MP_TAC(SPECL [`--(a - b):int`; `f:int`] INT_LE_MUL) THEN
    ANTS_TAC THENL [ASM_INT_ARITH_TAC; REWRITE_TAC[INT_MUL_LNEG]]] THEN
  ASM_INT_ARITH_TAC);;

let R5B_ZX_IWORD = prove(`!y:int32. word_zx y:int64 = iword(&(val y))`, REWRITE_TAC[word_zx; WORD_IWORD]);;
let R5B_W262144 = prove(`word 262144:int64 = iword(&262144)`, REWRITE_TAC[WORD_IWORD]);;
let R5B_W1 = prove(`word 1:int64 = iword(&1)`, REWRITE_TAC[WORD_IWORD]);;

let r5b_spdi_v = `word_add (word_ishr (word_add (word_mul (word_sub (iword a) (iword b)) (iword y)) (iword (&262144))) 19) (iword b):int64`;;
let r5b_spdi_s = subst [r5b_spdi_v,`V:int64`] `if ~(ival (V:int64) > &1) then word 1 else V`;;
let R5B_SPD_INT = prove
 (list_mk_forall([`a:int`;`b:int`;`y:int`], mk_imp(`-- &2147483648 <= a:int /\ a < &2147483648 /\ -- &2147483648 <= b:int /\ b < &2147483648 /\ &0 <= y:int /\ y < &524288`,
    mk_neg(mk_eq(mk_comb(mk_comb(`word_mul:int64->int64->int64`, r5b_spdi_s), r5b_spdi_s), `word 0:int64`)))),
  (REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM IWORD_INT_SUB; GSYM IWORD_INT_MUL; GSYM IWORD_INT_ADD]) THEN
  (ABBREV_TAC `P = (a - b) * y + &262144:int`) THEN
  (SUBGOAL_THEN `-- &2251799813685248 <= P:int /\ P < &2251799813685248` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN ASM_CASES_TAC `&0 <= a - b:int` THENL
     [MP_TAC(SPECL [`a - b:int`; `y:int`; `&524287:int`] INT_LE_LMUL) THEN MP_TAC(SPECL [`a - b:int`; `y:int`] INT_LE_MUL);
      MP_TAC(SPECL [`--(a - b):int`; `y:int`; `&524287:int`] INT_LE_LMUL) THEN MP_TAC(SPECL [`--(a - b):int`; `y:int`] INT_LE_MUL)] THEN
    REWRITE_TAC[INT_MUL_LNEG] THEN ASM_INT_ARITH_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN `word_ishr (iword (P:int):int64) 19 = iword (P div &524288)` SUBST1_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM IWORD_IVAL] THEN REWRITE_TAC[IVAL_WORD_ISHR] THEN
    MP_TAC(ISPEC `P:int` (INST_TYPE [`:64`,`:N`] IVAL_IWORD)) THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN
    ANTS_TAC THENL [ASM_INT_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN REWRITE_TAC[];
    ALL_TAC]) THEN
  (REWRITE_TAC[GSYM IWORD_INT_ADD]) THEN
  (SUBGOAL_THEN `(P:int) div &524288 + b < &2147483648 /\ -- &4294967296 <= (P:int) div &524288` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "P" THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN MATCH_MP_TAC R5B_SPD_CORE THEN ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`P:int`; `&524288:int`] INT_DIVISION) THEN ANTS_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[INT_ABS_NUM] THEN ASM_INT_ARITH_TAC];
    ALL_TAC]) THEN
  (ABBREV_TAC `v = (P:int) div &524288 + b` THEN
  SUBGOAL_THEN `ival (iword v:int64) = v` SUBST1_TAC THENL
   [MATCH_MP_TAC (INST_TYPE [`:64`,`:N`] IVAL_IWORD) THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN ASM_INT_ARITH_TAC; ALL_TAC]) THEN
  (ABBREV_TAC `u = if ~(v > &1) then &1 else v:int` THEN
  SUBGOAL_THEN `(if ~(v > &1) then word 1 else iword v:int64) = iword u` SUBST1_TAC THENL
   [EXPAND_TAC "u" THEN COND_CASES_TAC THEN REWRITE_TAC[R5B_W1]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= u:int /\ u < &2147483648` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN COND_CASES_TAC THEN ASM_INT_ARITH_TAC; ALL_TAC]) THEN
  (REWRITE_TAC[GSYM IWORD_INT_MUL] THEN DISCH_THEN(MP_TAC o AP_TERM `ival:int64->int`) THEN
  SUBGOAL_THEN `ival (iword (u * u):int64) = u * u` SUBST1_TAC THENL
   [MATCH_MP_TAC (INST_TYPE [`:64`,`:N`] IVAL_IWORD) THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN
    MP_TAC(SPECL [`u:int`; `&2147483648:int`; `u:int`; `&2147483648:int`] INT_LT_MUL2) THEN
    MP_TAC(SPECL [`u:int`; `u:int`] INT_LE_MUL) THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IVAL_WORD_0] THEN MP_TAC(SPECL [`u:int`; `u:int`] INT_LT_MUL) THEN ASM_INT_ARITH_TAC));;

let r5b_spd_v = `word_add (word_ishr (word_add (word_mul (word_sub (word_sx (A:int32)) (word_sx (B:int32)))
                      (word_zx (word_and (X:int32) (word 524287)))) (word 262144)) 19) (word_sx B):int64`;;
let r5b_spd_s = subst [r5b_spd_v,`V:int64`] `if ~(ival (V:int64) > &1) then word 1 else V`;;
let R5B_SPD_NZ = prove
 (list_mk_forall([`A:int32`;`B:int32`;`X:int32`],
    mk_eq(mk_eq(mk_comb(mk_comb(`word_mul:int64->int64->int64`, r5b_spd_s), r5b_spd_s), `word 0:int64`), `F`)),
  REPEAT GEN_TAC THEN REWRITE_TAC[word_sx; R5B_ZX_IWORD; R5B_W262144] THEN
  MATCH_MP_TAC R5B_SPD_INT THEN
  MP_TAC(ISPEC `A:int32` IVAL_BOUND) THEN MP_TAC(ISPEC `B:int32` IVAL_BOUND) THEN
  MP_TAC(CONJUNCT1 (ISPECL [`X:int32`; `word 524287:int32`] R5B_VAND32)) THEN
  REWRITE_TAC[DIMINDEX_32; VAL_WORD; INT_POS; INT_OF_NUM_LT] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;
(* ---- R5 PROVE-birth: memory interface of the record-store segments and peeling (cf. R5J_PEEL_TAC, pop_r5jig_lem.ml) *)
let R5B_SHL2 = prove(`!n. word_shl (word n) 2:int32 = word (4 * n)`,
  REWRITE_TAC[VK_WSHL] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[]);;
let R5B_MUL48 = prove(`!n. word_mul (word n) (word 48):int32 = word (48 * n)`,
  REWRITE_TAC[GSYM WORD_MUL; MULT_SYM]);;
let R5B_INC1 = prove(`!n. word_add (word n) (word 1):int32 = word (n + 1)`, REWRITE_TAC[GSYM WORD_ADD]);;
let R5B_ADDZQ = prove(`!k. word_add (word (4 * k)) (word 1163264):int32 = word (4 * k + 1163264)`, REWRITE_TAC[GSYM WORD_ADD]);;

(* peel bytes32 reads through bytes32 and bytes64 writes; same cell decided syntactically after normalization,
   otherwise disjointness first (cheap when true), then equality *)
let r5b_nnorm t = try rhs(concl(NUM_NORMALIZE_CONV t)) with Failure _ -> t;;
let R5B_PEEL_TAC : tactic =
  let p32 = `read (bytes32 (word (x:num))) (write (bytes32 (word (a:num))) (v:int32) (m:int64->byte))` in
  let p64 = `read (bytes32 (word (x:num))) (write (bytes64 (word (a:num))) (v:int64) (m:int64->byte))` in
  fun (asl,w) ->
    try
      let t = find_term (can (term_match [] p32)) w in
      let i = term_match [] p32 t in
      let x = instantiate i `x:num` and a = instantiate i `a:num`
      and v = instantiate i `v:int32` and m = instantiate i `m:int64->byte` in
      let same = (fun g -> (SUBGOAL_THEN (mk_eq(x,a)) ASSUME_TAC THENL
                   [VK_ARITH_TAC; FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP CAP_B32_SAME_EQ th])]) g) in
      let disj = (fun g -> (MP_TAC(SPECL [x; a; v; m] VK_R32_W32) THEN ANTS_TAC THENL
                   [VK_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])]) g) in
      (if r5b_nnorm x = r5b_nnorm a then same else disj ORELSE same) (asl,w)
    with Failure _ ->
      let t = find_term (can (term_match [] p64)) w in
      let i = term_match [] p64 t in
      let x = instantiate i `x:num` and a = instantiate i `a:num`
      and v = instantiate i `v:int64` and m = instantiate i `m:int64->byte` in
      (MP_TAC(SPECL [x; a; v; m] VK_R32_W64) THEN ANTS_TAC THENL
         [VK_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])]) (asl,w);;
let r5b_di j = subst [j,`j:num`] `read (bytes32 (word (1179648 + 4 * (12 * n + j)))) (m:int64->byte)`;;
(* born1 t k n m0 m: one pinch-off record pushed at slot n (words 0..9 written, word 6 = T+1, word 7 = k) and the
   parent k debited by words 8/9; nothing else of DI, ZQ, ZP, ND changed *)
let r5b_born1 =
  `\(m0:int64->byte) (m:int64->byte).
   (!w. w < 196608 /\ ~(12 * n <= w /\ w < 12 * n + 10) ==>
        read (bytes32 (word (1179648 + 4 * w))) m = read (bytes32 (word (1179648 + 4 * w))) m0) /\
   read (bytes32 (word (1179648 + 4 * (12 * n + 6)))) m = word_add t (word 1) /\
   read (bytes32 (word (1179648 + 4 * (12 * n + 7)))) m = word k /\
   (!i. i < 2048 ==> read (bytes32 (word (1163264 + 4 * i))) m =
        (if i = k then word_sub (read (bytes32 (word (1163264 + 4 * i))) m0) (read (bytes32 (word (1179648 + 4 * (12 * n + 8)))) m)
         else read (bytes32 (word (1163264 + 4 * i))) m0)) /\
   (!i. i < 2048 ==> read (bytes32 (word (1171456 + 4 * i))) m =
        (if i = k then word_sub (read (bytes32 (word (1171456 + 4 * i))) m0) (read (bytes32 (word (1179648 + 4 * (12 * n + 9)))) m)
         else read (bytes32 (word (1171456 + 4 * i))) m0)) /\
   read (bytes32 (word 16400)) m = read (bytes32 (word 16400)) m0`;;

(* body with an explicit memory clause instead of read wmem s = m0 *)
let r5b_body_m pc lbls tracked memc =
  let b = r5b_body pc lbls tracked [] in
  let cs = conjuncts b in
  list_mk_conj(map (fun c -> if c = `read wmem s = (m0:int64->byte)` then memc else c) cs);;

let r5b_close_extra = ref ([]:thm list);;
(* ---- R5 PROVE-birth: loop 1 (pinch-off) segment lemmas on the generic interface (memory m0 unchanged) *)
let () = r5b_extra := [VK_COND_I64; VK_COND_I32; R5B_SEL1_NZ; R5B_SPD_NZ; R5B_SHL2; R5B_ADDZQ; R5B_MUL48; R5B_INC1];;
let r5b_L1 = [Lp 144; Blk 2611];;
let r5b_L1B = [Blk 2585; Lp 144; Blk 2611];;
let r5b_trk1 = [0,`word k:int32`; 1,`word n:int32`; 3,`word_add t (word 1):int32`];;
let r5b_trk1x = r5b_trk1 @ [11,`word (4 * k):int32`; 19,`word (4 * k + 1163264):int32`];;
let r5b_seg1 p q = list_mk_forall([`m0:int64->byte`;`k:num`;`n:num`;`t:int32`], mk_imp(`k < 2048 /\ n < 16384`, r5b_ens p q));;
let r5b_with_thresh n f x = let old = !r5b_abbrev_thresh in r5b_abbrev_thresh := n;
  let r = (try f x with e -> (r5b_abbrev_thresh := old; raise e)) in r5b_abbrev_thresh := old; r;;
(* 146 -> 469 (live) | 2586 (four early continues): band, local max of ZQ, spd, D1, zp_of, D2 (SPD_NZ), D3 *)
let R5B_SEGA = prove(r5b_seg1 (r5b_pred 146 r5b_L1 r5b_trk1 [])
     (mk_abs(`s:wasmstate`, mk_disj(r5b_body 469 r5b_L1B r5b_trk1x [], r5b_body 2586 r5b_L1 r5b_trk1 []))),
  R5B_SEG_TAC "segA" [469; 2586]);;
(* 469 -> 573 (inside isqrt loop 1, counter l13 = 32) *)
let R5B_SEGB = prove(r5b_seg1 (r5b_pred 469 r5b_L1B r5b_trk1x []) (r5b_pred 573 (Lp 571 :: r5b_L1B) ((13,`word 32:int32`) :: r5b_trk1x) []),
  R5B_SEG_TAC "segB" [573]);;
(* isqrt loop 1: 573 (l13 = c, 1 <= c <= 32) -> 627 *)
let R5B_ISQ1 = prove(r5b_isq_stmt 571 627 13 r5b_L1B r5b_trk1x, R5B_ISQ_TAC "isq1" 571 627 13 r5b_L1B r5b_trk1x);;
(* 627 -> 1755 (geometry; inside isqrt loop 2, l13 = 32); big values generalized *)
let R5B_SEGC = r5b_with_thresh 60 (fun () -> prove(r5b_seg1 (r5b_pred 627 r5b_L1B r5b_trk1x []) (r5b_pred 1755 (Lp 1753 :: r5b_L1B) ((13,`word 32:int32`) :: r5b_trk1x) []),
  R5B_SEG_TAC "segC" [1755])) ();;
(* ---- R5 PROVE-birth: small ensures combinators *)
let R5B_ENS_DISJ = prove
 (`!P1 P2 Q C. ensures wasm P1 Q C /\ ensures wasm P2 Q C ==> ensures wasm (\s. P1 s \/ P2 s) Q C`,
  REWRITE_TAC[ensures] THEN MESON_TAC[]);;
let R5B_ENS_EXISTS = prove
 (`!P Q C. (!x:A. ensures wasm (P x) Q C) ==> ensures wasm (\s. ?x. P x s) Q C`,
  REWRITE_TAC[ensures] THEN MESON_TAC[]);;
(* the back edge of loop 1: 2586 -> 146 (k+1, n' < 16384) | 2612 (k = 2047 or n' = 16384) *)
let r5b_back1_stmt =
  let trk = [0,`word k:int32`; 1,`word n:int32`; 3,`word_add t (word 1):int32`] in
  list_mk_forall([`m0:int64->byte`;`k:num`;`n:num`;`t:int32`],
   mk_imp(`k < 2048 /\ n <= 16384`,
    r5b_ens (r5b_pred 2586 r5b_L1 trk [])
     (mk_abs(`s:wasmstate`, mk_disj(
        r5b_body 146 r5b_L1 [0,`word (k + 1):int32`; 1,`word n:int32`; 3,`word_add t (word 1):int32`] [`k + 1 < 2048`; `n < 16384`],
        r5b_body 2612 [] [1,`word n:int32`; 3,`word_add t (word 1):int32`] [`n <= 16384`])))));;
let R5B_BACK1 = prove(r5b_back1_stmt,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val (word k:int32) = k /\ val (word n:int32) = n` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  R5B_SEG_TAC "back1" [146; 2612]);;
let R5B_ISQ2 = prove(r5b_isq_stmt 1753 1809 13 r5b_L1B r5b_trk1x, R5B_ISQ_TAC "isq2" 1753 1809 13 r5b_L1B r5b_trk1x);;
(* 1809 -> 1964 (D4-D6 constant divisors; inside isqrt loop 3, l13 = 32) *)
let R5B_SEGD = r5b_with_thresh 60 (fun () -> prove(r5b_seg1 (r5b_pred 1809 r5b_L1B r5b_trk1x []) (r5b_pred 1964 (Lp 1962 :: r5b_L1B) ((13,`word 32:int32`) :: r5b_trk1x) []),
  R5B_SEG_TAC "segD" [1964])) ();;
let R5B_ISQ3 = prove(r5b_isq_stmt 1962 2018 13 r5b_L1B r5b_trk1x, R5B_ISQ_TAC "isq3" 1962 2018 13 r5b_L1B r5b_trk1x);;
(* ---- R5 PROVE-birth: pure push lemmas and the loop memory invariant *)
let R5B_PUSH_SNOC = prove
 (`!L r bs. va1_push (APPEND L [r]) bs = va1_push1 r (va1_push L bs)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; va1_push]);;

let R5B_PUSH1_ND = prove
 (`!r bs. SND(SND(SND(va1_push1 r bs))) = word_add (SND(SND(SND bs))) (word 1) /\
          FST(va1_push1 r bs) = (\w. if 12 * val (SND(SND(SND bs))) <= w /\ w < 12 * val (SND(SND(SND bs))) + 12
                                     then r (w - 12 * val (SND(SND(SND bs)))) else FST bs w) /\
          FST(SND(va1_push1 r bs)) = (\i. if val (r 7) < 65536 /\ i = val (r 7) MOD 2048
                                          then word_sub (FST(SND bs) i) (r 8) else FST(SND bs) i) /\
          FST(SND(SND(va1_push1 r bs))) = (\i. if val (r 7) < 65536 /\ i = val (r 7) MOD 2048
                                          then word_sub (FST(SND(SND bs)) i) (r 9) else FST(SND(SND bs)) i)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; va1_push1] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

let R5B_PUSH_ND = prove
 (`!L bs. SND(SND(SND(va1_push L bs))) = word_add (SND(SND(SND bs))) (word (LENGTH L))`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[va1_push; LENGTH; WORD_ADD_0; R5B_PUSH1_ND] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ADD1; ADD_SYM]);;

let R5B_VAL_INC = prove
 (`!x:int32 j. val x + j < 4294967296 ==> val (word_add x (word j)) = val x + j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC MOD_DOWN_CONV THEN ASM_SIMP_TAC[MOD_LT]);;

let R5B_PUSH_DI_BEYOND = prove
 (`!L bs w. val (SND(SND(SND bs))) + LENGTH L < 4294967296 /\ 12 * (val (SND(SND(SND bs))) + LENGTH L) <= w
            ==> FST (va1_push L bs) w = FST bs w`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[va1_push; LENGTH; ADD_CLAUSES] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`va1_push1 h bs`; `w:num`]) THEN
  REWRITE_TAC[R5B_PUSH1_ND] THEN
  SUBGOAL_THEN `val (word_add (SND(SND(SND (bs:(num->int32)#(num->int32)#(num->int32)#int32)))) (word 1)) =
                val (SND(SND(SND bs))) + 1` SUBST1_TAC THENL
   [MATCH_MP_TAC R5B_VAL_INC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* the loop memory invariant at count n *)
let r5b_mi_tm = `\(t:int32) (di:num->int32) (zq:num->int32) (zp:num->int32) (nd:int32) (n:num) (m:int64->byte).
   ?L. ALL (\r:num->int32. r 6 = word_add t (word 1) /\ r 10 = word 0 /\ r 11 = word 0) L /\
       val nd + LENGTH L = n /\
       va1_w32s 1179648 196608 (FST (va1_push L (di,zq,zp,nd))) m /\
       va1_w32s 1163264 2048 (FST (SND (va1_push L (di,zq,zp,nd)))) m /\
       va1_w32s 1171456 2048 (FST (SND (SND (va1_push L (di,zq,zp,nd))))) m /\
       read (bytes32 (word 16400)) m = nd`;;
let r5b_mi n m = rhs(concl(TOP_DEPTH_CONV BETA_CONV
   (list_mk_comb(r5b_mi_tm, [`t:int32`;`di:num->int32`;`zq:num->int32`;`zp:num->int32`;`nd:int32`; n; m]))));;
let r5b_born1_at m0 m = rhs(concl(TOP_DEPTH_CONV BETA_CONV (list_mk_comb(r5b_born1, [m0; m]))));;
let r5b_zero_beyond = `!w. 12 * val (nd:int32) <= w /\ w < 196608 ==> (di:num->int32) w = word 0`;;

(* one pinch-off birth keeps the invariant *)
let r5b_ba1 = list_mk_forall([`t:int32`;`di:num->int32`;`zq:num->int32`;`zp:num->int32`;`nd:int32`;`n:num`;`k:num`;`m0:int64->byte`;`m:int64->byte`],
   mk_imp(list_mk_conj [r5b_mi `n:num` `m0:int64->byte`; `n < 16384`; `k < 2048`; r5b_zero_beyond;
                        r5b_born1_at `m0:int64->byte` `m:int64->byte`],
          r5b_mi `n + 1` `m:int64->byte`));;
let r5b_frame1 = hd(conjuncts(r5b_born1_at `m0:int64->byte` `m:int64->byte`));;
let r5b_w32di = `!k. k < 196608 ==> read (bytes32 (word (1179648 + 4 * k))) (m0:int64->byte) = FST (va1_push L (di,zq,zp,nd)) k`;;
let r5b_beyond = `!j. 12 * n <= j /\ j < 196608 ==> FST (va1_push L (di:num->int32,zq:num->int32,zp:num->int32,nd:int32)) j = word 0`;;
let R5B_W10_TAC j = MP_TAC(SPEC j (ASSUME r5b_frame1)) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPEC j (ASSUME r5b_w32di)) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC(ASSUME r5b_beyond) THEN ASM_ARITH_TAC;;
let R5B_BIRTH_APPEND1 = prove(r5b_ba1,
  (REPEAT GEN_TAC THEN STRIP_TAC) THEN
  (EXISTS_TAC `APPEND (L:(num->int32)list) [\i. read (bytes32 (word (1179648 + 4 * (12 * n + i)))) (m:int64->byte)]`) THEN
  (REWRITE_TAC[ALL_APPEND; ALL; LENGTH_APPEND; LENGTH; R5B_PUSH_SNOC; R5B_PUSH1_ND; R5B_PUSH_ND]) THEN
  (REWRITE_TAC[va1_w32s] THEN RULE_ASSUM_TAC(REWRITE_RULE[va1_w32s])) THEN
  (SUBGOAL_THEN `val (word_add nd (word (LENGTH (L:(num->int32)list))):int32) = n` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`nd:int32`; `LENGTH (L:(num->int32)list)`] R5B_VAL_INC) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC]) THEN
  (SUBGOAL_THEN `val (word k:int32) = k /\ k MOD 2048 = k` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC]; ALL_TAC]) THEN
  (SUBGOAL_THEN `!j. 12 * n <= j /\ j < 196608 ==> FST (va1_push L (di,zq,zp,nd)) j = word 0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`L:(num->int32)list`; `(di,zq,zp,nd):(num->int32)#(num->int32)#(num->int32)#int32`; `j:num`] R5B_PUSH_DI_BEYOND) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC]) THEN
  (ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  (SUBGOAL_THEN `k < 65536` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [R5B_W10_TAC `12 * n + 10`; R5B_W10_TAC `12 * n + 11`; ASM_ARITH_TAC;
    X_GEN_TAC `w:num` THEN DISCH_TAC THEN COND_CASES_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `12 * n <= w ==> 12 * n + (w - 12 * n) = w`];
      MP_TAC(SPEC `w:num` (ASSUME r5b_frame1)) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      ASM_SIMP_TAC[]];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[]]));;
