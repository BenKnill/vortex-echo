(* ========================================================================= *)
(* Vortex pop, rung R5 (PROVE-jig, Claude Opus 5.5, 2026-11-11): the wobble  *)
(* kick contract VA1_JIGK_OK (va1_jigk_ok va1_jigk, pop_design_defs.ml) on   *)
(* the exact bytes of f21 ve_jig_kick / f22 ve_jig_unkick of vortex_a1.wasm, *)
(* for the witness va1_jigk of pop_r5_jig_defs.ml (frozen spec               *)
(* pop_r5_jig.spec, sha256 588c302b...). LEAFCHAIN layer on the decode layer *)
(* pop_r5jig_dec.ml. Structure:                                              *)
(*   loop 1 (pc 13 .. 1813, shared bytes) for a code variable MC under the   *)
(*   decode antecedent (VK_SEG2_GEN pattern): entry (flag set), body split   *)
(*   at the six inlined isin blocks (stack [partial sum; sg; s2]) plus the   *)
(*   stopped-bead branch, back edge, exit;                                   *)
(*   loop 2 (pc 1813 .. WDone, JP (op)= KJ) per export, as the L3 drift loop; *)
(*   flag clear per export (no store; va1_jigk = 0).                         *)
(* ========================================================================= *)
(* ---- R5 PROVE-jig: generic code variable MC for the shared prefix pc 13 .. 1812 of f21/f22 (VK_SEG2_GEN pattern).  *)
(* The decode antecedent (~1000 conjuncts) and the theorems that carry it are kept in refs / a table so that the      *)
(* toplevel does not print them.                                                                                     *)
let r5j_mcv = `MC:byte list`;;
let r5j_dec_pcs ((_:thm), (arr:thm option array)) =
  filter (fun pc -> pc >= 13 && pc <= 1812 && arr.(pc) <> None) (0--(Array.length arr - 1));;
let r5j_dec_th (arr:thm option array) pc =
  match arr.(pc) with Some th -> th | None -> failwith "r5j_dec_th";;
let R5J_DEC_H_REF = ref `T`;;
let () = R5J_DEC_H_REF :=
  (let (_,arr) = POP_R5J_F21_EXEC in
   list_mk_conj (map (fun pc ->
     let th = r5j_dec_th arr pc in
     let l = lhs(concl th) in
     mk_eq(mk_comb(mk_comb(rator(rator l), r5j_mcv), rand l), rhs(concl th)))
    (r5j_dec_pcs POP_R5J_F21_EXEC)));;
let R5J_GEN_EXEC_REF = ref (TRUTH, ([||]:thm option array));;
let () = R5J_GEN_EXEC_REF :=
  (let (lth,arr) = POP_R5J_F21_EXEC in
   let pcs = r5j_dec_pcs POP_R5J_F21_EXEC in
   let ths = CONJUNCTS (ASSUME !R5J_DEC_H_REF) in
   let garr = Array.make (Array.length arr) None in
   List.iter2 (fun pc th -> garr.(pc) <- Some th) pcs ths;
   (lth, garr));;
let r5j_gen_prove (stmt:term) (tac:tactic) = prove(mk_imp(!R5J_DEC_H_REF, stmt), DISCH_THEN(K tac));;
let r5j_time name f x =
  let t0 = Sys.time() in let y = f x in
  Printf.printf "@@TIME %s %.1f s cpu\n%!" name (Sys.time() -. t0); y;;
let r5j_thm_tbl : (string, thm) Hashtbl.t = Hashtbl.create 16;;
let r5j_put name th = Hashtbl.replace r5j_thm_tbl name th;;
let r5j_get name = Hashtbl.find r5j_thm_tbl name;;
(* ---- R5 PROVE-jig: stepping, frame, helper lemmas *)
let R5J_FRAME = `MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,
            MAYCHANGE [wstatus] ,, MAYCHANGE [wlocal 0; wlocal 1; wlocal 2; wlocal 3; wlocal 4; wlocal 5; wlocal 6; wlocal 7; wlocal 8; wlocal 9; wlocal 10; wlocal 11; wlocal 12; wlocal 13; wlocal 14; wlocal 15; wlocal 16; wlocal 17; wlocal 18; wlocal 19; wlocal 20; wlocal 21] ,,
            MAYCHANGE [wmem :> bytes(word 1155072,8192)] ,,
            MAYCHANGE [wmem :> bytes(word 1966080,73728)]`;;

(* the byte at a is the low byte of the 32-bit word at a (copy of POP_L3_B8_LOW, pop_l3_jdrift.ml) *)
let R5J_B8_LOW = prove
 (`!(a:int64) (m:int64->byte). read (bytes8 a) m = word_zx (read (bytes32 a) m)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; DIMINDEX_8] THEN
  REWRITE_TAC[GSYM READ_BYTES_BYTES8] THEN
  MP_TAC(ISPECL [`a:int64`; `m:int64->byte`] (INST_TYPE [`:32`,`:N`] VAL_READ_WBYTES)) THEN
  REWRITE_TAC[GSYM BYTES32_WBYTES; DIMINDEX_32] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `4`; `1`; `m:int64->byte`] READ_BYTES_MOD) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN(ACCEPT_TAC o SYM));;

(* load8_u, and 1 = bit 0 of the word (copy of POP_L3_FLAG_AND) *)
let R5J_FLAG_AND = prove
 (`!x:int32. word_and (word_zx (word_zx x:byte):int32) (word 1) =
             (if bit 0 x then word 1 else word 0)`,
  GEN_TAC THEN BITBLAST_TAC);;

(* one step + discard old state + compact hypotheses; passes state-free bytes32/bytes8 facts as rewrites *)
let r5j_is_memfact tm =
  let ws = `:wasmstate` in
  not (can (find_term (fun t -> type_of t = ws)) tm) &&
  can (find_term (fun t -> is_const t && (fst(dest_const t) = "bytes32" || fst(dest_const t) = "bytes8"))) tm &&
  not (is_imp (snd(strip_forall tm))) && not (is_forall tm);;

let r5j_extra = ref ([]:thm list);;
let R5J_MSTEPS_TAC execth snums =
  MAP_EVERY (fun s (asl,w) ->
     let mths = filter (fun th -> r5j_is_memfact (concl th)) (map snd asl) in
     (CAP_STEP_TAC execth (READ_COMPONENT_COMPOSE :: (!r5j_extra @ mths)) s THEN
      CAP_DISCARD_OLD_TAC s THEN WASM_COMPACT_HYPS_TAC) (asl,w))
   (statenames "s" snums);;

let r5j_tstep name execth snums : tactic = fun g ->
  let t0 = Sys.time() in let r = R5J_MSTEPS_TAC execth snums g in
  Printf.printf "@@TIME %s %d steps %.1f s cpu\n%!" name (length snums) (Sys.time() -. t0); r;;

(* name the memory: every assumption about wmem (forall or not) becomes a fact about mm = read wmem s0 *)
let R5J_MEMNAME_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "wmem")) (concl th)))) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ABBREV_TAC `mm = read wmem (s0:wasmstate)` THEN REPEAT DISCH_TAC;;
(* ---- R5 PROVE-jig: loop 2 of f21/f22 (pc 1813 .. WDone): JP[k] := JP[k] (op) KJ[k], k < 2048, KJ = 2031616 + 4k *)
(* adapted from the L3 jdrift loop (pop_l3_jdrift.ml): l2 = -8192 + 16 i (num 4294959104 + 16 i), 512 iterations; *)
(* i32 address l2 + 1163264 wraps to JP 1155072 + 16 i, l2 + 2039808 to KJ 2031616 + 16 i.                        *)
let R5J_WRAP = prove
 (`!a b c. a + b = c + 4294967296 ==> word_add (word a) (word b):int32 = word c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
  REWRITE_TAC[WORD_ADD_0]);;

let r5j_kjf = `va1_jigk (mdl:num->int32) (hp:num->int32) (tbl:num->int32) (t:int32) (p:int32) (rb:num->int32) (jq:num->int32)`;;

let r5j_l2_inv mc op =
  let t = subst [mc,`MC:byte list`; op,`OP:int32->int32->int32`; r5j_kjf,`KJ:num->int32`]
   `\i s. read wcode s = MC /\ read wstatus s = WRunning /\
          read wmemsize s = 4194304 /\ read warity s = 0 /\
          read wlabels s = [0,1818,0; 0,1951,0] /\
          read (wlocal 2) s = I32 (word (4294959104 + 16 * i)) /\
          read wstack s = (if read wpc s = word 1820 then [] else [I32 (word (4294959104 + 16 * i))]) /\
          (!k. k < 2048 ==> read (wmem :> bytes32 (word (1155072 + 4 * k))) s =
                            (if k < 4 * i then (OP:int32->int32->int32) ((jp:num->int32) k) ((KJ:num->int32) k) else jp k)) /\
          (!k. k < 2048 ==> read (wmem :> bytes32 (word (2031616 + 4 * k))) s = KJ k)` in
  rhs(concl(TOP_DEPTH_CONV BETA_CONV t));;

(* the state after loop 1 (pc 1813), as the generic loop-1 lemma leaves it *)
let r5j_mid1813 mc =
  subst [mc,`MC:byte list`; r5j_kjf,`KJ:num->int32`]
   `\s. read wcode s = MC /\ read wpc s = word 1813 /\ read wstatus s = WRunning /\
        read wstack s = [] /\ read wlabels s = [0,1951,0] /\ read warity s = 0 /\
        read wmemsize s = 4194304 /\
        (!k. k < 2048 ==> read (wmem :> bytes32 (word (2031616 + 4 * k))) s = KJ k) /\
        (!k. k < 2048 ==> read (wmem :> bytes32 (word (1155072 + 4 * k))) s = (jp:num->int32) k)`;;

let r5j_num n = mk_small_numeral n;;
let r5j_cell b = mk_binop `(+):num->num->num` (r5j_num b) `16 * i`;;
let r5j_idx j = if j = 0 then `4 * i` else mk_binop `(+):num->num->num` `4 * i` (r5j_num j);;

let R5J_L2_ENTRY_TAC exec =
  ENSURES_INIT_TAC "s0" THEN MEMNAME_TAC THEN
  CAP_MSTEPS_TAC exec (1--3) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LT];;

let R5J_L2_BODY_TAC exec =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MAP_EVERY (fun c ->
    SUBGOAL_THEN (subst [r5j_num c,`cc:num`; r5j_cell (c - 8192),`bb:num`]
       `word_add (word (4294959104 + 16 * i)) (word cc):int32 = word bb`) ASSUME_TAC THENL
     [MATCH_MP_TAC R5J_WRAP THEN ARITH_TAC; ALL_TAC])
   [1163264; 2039808; 1163268; 2039812; 1163272; 2039816; 1163276; 2039820] THEN
  MAP_EVERY (fun b -> VAL_TAC (subst [r5j_cell b,`bb:num`] `val(word bb:int32) = bb`))
   [1155072; 2031616; 1155076; 2031620; 1155080; 2031624; 1155084; 2031628] THEN
  SUBGOAL_THEN `word_add (word (4294959104 + 16 * i)) (word 16):int32 =
                word (4294959104 + 16 * (i + 1))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  MAP_EVERY (fun (base,f,j) ->
    let a = r5j_cell (base + 4 * j) and k = r5j_idx j in
    SUBGOAL_THEN (subst [a,`aa:num`; f,`ff:num->int32`; k,`kk:num`]
                   `read (bytes32 (word aa)) mm = (ff:num->int32) kk`) ASSUME_TAC THENL
     [SUBGOAL_THEN (subst [a,`aa:num`; r5j_num base,`bb:num`; k,`kk:num`] `aa = bb + 4 * kk`)
        SUBST1_TAC THENL
       [ARITH_TAC;
        SUBGOAL_THEN (subst [k,`kk:num`] `kk < 2048 /\ ~(kk < 4 * i)`) STRIP_ASSUME_TAC THENL
         [ASM_ARITH_TAC; ASM_SIMP_TAC[]]];
      ALL_TAC])
   (allpairs (fun (b,f) j -> (b,f,j)) [1155072,`jp:num->int32`; 2031616,r5j_kjf] [0;1;2;3]) THEN
  MAP_EVERY (fun (r,wj) -> B32O_TAC (r5j_cell r) (r5j_cell (1155072 + 4 * wj)))
   (List.concat (map (fun j -> List.concat (map (fun wj -> if wj < j then
       [(1155072 + 4 * j, wj); (2031616 + 4 * j, wj)] else []) [0;1;2;3])) [0;1;2;3])) THEN
  CAP_MSTEPS_TAC exec (1--52) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MAP_EVERY (fun j -> let c = r5j_idx j in
      ASM_CASES_TAC (subst [c,`cc:num`] `k:num = cc`) THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN REPEAT B32_PEEL_TAC THEN
        REWRITE_TAC[ARITH_RULE (subst [c,`cc:num`] `cc < 4 * (i + 1) <=> T`)];
        ALL_TAC]) [0;1;2;3] THEN
    REPEAT B32_PEEL_TAC THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(k < 4 * (i + 1) <=> k < 4 * i)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[]];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN REPEAT B32_PEEL_TAC THEN ASM_SIMP_TAC[]];;

let R5J_L2_BACK_TAC exec =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(word (4294959104 + 16 * i):int32 = word 0) <=> F` ASSUME_TAC THENL
   [REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN
    SUBGOAL_THEN `val(word (4294959104 + 16 * i):int32) = 4294959104 + 16 * i` SUBST1_TAC THENL
     [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC;
      REWRITE_TAC[VAL_WORD_0] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  CAP_MSTEPS_TAC exec (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[];;

let R5J_L2_EXIT_TAC exec =
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN MEMNAME_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV)) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV WORD_RED_CONV)) THEN
  CAP_MSTEPS_TAC exec (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[va1_w32s] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[];;

(* pc 1813 -> WDone: the loop-2 statement for one export *)
let r5j_l2_stmt mc op =
  let post = subst [op,`OP:int32->int32->int32`; r5j_kjf,`KJ:num->int32`]
    `\s. read wstatus s = WDone /\ read wstack s = [] /\
         va1_w32s 1155072 2048 (\k. (OP:int32->int32->int32) ((jp:num->int32) k) ((KJ:num->int32) k)) (read wmem s)` in
  list_mk_forall([`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;`t:int32`;`p:int32`;`jq:num->int32`;`rb:num->int32`;`jp:num->int32`],
    mk_comb(mk_comb(mk_comb(`ensures wasm`, r5j_mid1813 mc), post), R5J_FRAME));;

let R5J_L2_TAC mc exec op =
  REPEAT GEN_TAC THEN
  ENSURES_WHILE_UP_TAC `512` `1820` `1947` (r5j_l2_inv mc op) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; R5J_L2_ENTRY_TAC exec; R5J_L2_BODY_TAC exec;
    R5J_L2_BACK_TAC exec; R5J_L2_EXIT_TAC exec];;
(* ---- R5 PROVE-jig: loop 1 (pc 13 .. 1813, shared by f21/f22): statements, invariant, segment predicates      *)
let r5j_pre0 = `\s. read wcode s = MC /\ read wpc s = word 13 /\ read wstatus s = WRunning /\
      read wstack s = [] /\ read wlabels s = [] /\ read warity s = 0 /\ read wmemsize s = 4194304 /\
      read (wmem :> bytes32 (word 16392)) s = t /\ read (wmem :> bytes32 (word 16396)) s = p /\
      (!k. k < 1024 ==> read (wmem :> bytes32 (word (16640 + 4 * k))) s = (mdl:num->int32) k) /\
      (!k. k < 26 ==> read (wmem :> bytes32 (word (16408 + 4 * k))) s = (hp:num->int32) k) /\
      (!k. k < 262144 ==> read (wmem :> bytes32 (word (65536 + 4 * k))) s = (tbl:num->int32) k) /\
      (!k. k < 2048 ==> read (wmem :> bytes32 (word (1146880 + 4 * k))) s = (jq:num->int32) k) /\
      (!k. k < 2048 ==> read (wmem :> bytes32 (word (1138688 + 4 * k))) s = (rb:num->int32) k) /\
      (!k. k < 2048 ==> read (wmem :> bytes32 (word (1155072 + 4 * k))) s = (jp:num->int32) k)`;;

let r5j_rest q = let s,b = dest_abs q in mk_abs(s, rand(rand b));;

(* phase i: (local, c_i, d_i); amplitude i: local *)
let r5j_phl = [0,119790980,48234496; 6,120558376,77594624; 5,121765983,109051904;
               4,123240517,138412032; 3,125175750,169869312; 2,127622235,203423744];;
let r5j_ampl = [12; 11; 10; 9; 8; 7];;
let r5j_ph i k = let (_,c,d) = el i r5j_phl in
  list_mk_comb(`va1_jg_ph (hp:num->int32) (t:int32) (p:int32)`, [r5j_num i; mk_numeral(Num.num_of_int c); mk_numeral(Num.num_of_int d); k]);;
let r5j_term i k = let (_,c,d) = el i r5j_phl in
  list_mk_comb(`va1_jg_term (hp:num->int32) (t:int32) (p:int32)`, [r5j_num i; mk_numeral(Num.num_of_int c); mk_numeral(Num.num_of_int d); k]);;
let r5j_wl n v = mk_eq(mk_comb(mk_comb(`read:(wasmstate,wval)component->wasmstate->wval`, mk_comb(`wlocal`, r5j_num n)), `s:wasmstate`), v);;

(* the loop-1 locals at bead k (phase, amplitude, pointer locals) *)
let r5j_locals k =
  let i32 x = mk_comb(`I32`, x) and i64 x = mk_comb(`I64`, x) in
  let ph = map (fun i -> let (l,_,_) = el i r5j_phl in r5j_wl l (i32 (r5j_ph i k))) (0--5) in
  let am = map (fun i -> r5j_wl (el i r5j_ampl) (i64 (subst [r5j_num (18 + i),`n:num`] `word_sx ((hp:num->int32) n):int64`))) (0--5) in
  let pt = map (fun (l,tm) -> r5j_wl l (i32 (subst [k,`k:num`] tm)))
    [1, `word (1138688 + 4 * k):int32`; 13, `word (2031616 + 4 * k):int32`; 14, `word (1146880 + 4 * k):int32`;
     15, `word (65536 + 512 * k):int32`; 16, `word (2047 + k):int32`; 17, `word k:int32`] in
  list_mk_conj (ph @ am @ pt);;

let r5j_memin = `(!k. k < 262144 ==> read (wmem :> bytes32 (word (65536 + 4 * k))) s = (tbl:num->int32) k) /\
      (!k. k < 2048 ==> read (wmem :> bytes32 (word (1146880 + 4 * k))) s = (jq:num->int32) k) /\
      (!k. k < 2048 ==> read (wmem :> bytes32 (word (1138688 + 4 * k))) s = (rb:num->int32) k) /\
      (!k. k < 2048 ==> read (wmem :> bytes32 (word (1155072 + 4 * k))) s = (jp:num->int32) k)`;;
let r5j_memkj n = subst [n,`n:num`]
  `!k. k < n ==> read (wmem :> bytes32 (word (2031616 + 4 * k))) s = va1_jigk (mdl:num->int32) (hp:num->int32) (tbl:num->int32) (t:int32) (p:int32) (rb:num->int32) (jq:num->int32) k`;;

let r5j_lbl_loop = `[0,294,0; 0,1951,0]:(num#num#num)list`;;
let r5j_lbl_blk = `[0,1700,0; 0,294,0; 0,1951,0]:(num#num#num)list`;;

(* the loop-1 invariant *)
let r5j_l1_inv =
  let body = list_mk_conj
    [`read wcode s = MC`; `read wstatus s = WRunning`; `read wmemsize s = 4194304`; `read warity s = 0`;
     mk_eq(`read wlabels s`, r5j_lbl_loop);
     r5j_locals `i:num`;
     `read wstack s = (if read wpc s = word 296 then []
                       else [I32 (word (bitval (~(word (2047 + i) = word 4095:int32))))])`;
     r5j_memin; r5j_memkj `i:num`] in
  mk_abs(`i:num`, mk_abs(`s:wasmstate`, body));;

(* a segment predicate inside bead i: pc, labels, stack, extra facts *)
let r5j_mid pc lbl stk extra =
  let body = list_mk_conj
    ([`read wcode s = MC`; mk_eq(`read wpc s`, mk_comb(`word:num->int64`, r5j_num pc));
      `read wstatus s = WRunning`; `read wmemsize s = 4194304`; `read warity s = 0`;
      mk_eq(`read wlabels s`, lbl); r5j_locals `i:num`; mk_eq(`read wstack s`, stk);
      r5j_memin; r5j_memkj `i:num`] @ extra) in
  mk_abs(`s:wasmstate`, body);;

let r5j_l1_stmt =
  list_mk_forall([`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;`t:int32`;`p:int32`;`jq:num->int32`;`rb:num->int32`;`jp:num->int32`],
    mk_imp(`bit 0 ((mdl:num->int32) 3)`,
      mk_comb(mk_comb(mk_comb(`ensures wasm`, r5j_pre0), r5j_mid1813 r5j_mcv), R5J_FRAME)));;

(* the stack values of the live branch at the block boundaries (the witness's own subterms after let_CONV) *)
let r5j_s2w = `word_add (word_mul (word_sx ((jq:num->int32) i):int64) (word 18446744073578719430))
                        (word_mul (word_sub (word_shl (word_sx (jq i):int64) 1)
                                            (word_add (word_sx (jq ((i + 2047) MOD 2048)))
                                                      (word_sx (jq ((i + 1) MOD 2048)))))
                                  (word 18446744073494803251)):int64`;;
let r5j_sgw = `word_ushr (word_mul (va1_jg_spd (tbl:num->int32) ((rb:num->int32) i) i) (word 427228)) 16:int64`;;
(* partial drive sum after blocks 0..b *)
let rec r5j_psum b = if b = 0 then r5j_term 0 `i:num`
  else mk_binop `word_add:int64->int64->int64` (r5j_psum (b - 1)) (r5j_term b `i:num`);;
let r5j_stk vs = mk_list(map (fun v -> mk_comb(`I64`, v)) vs, `:wval`);;
(* block b starts at r5j_bpc b (b = 0..5); 1671 = after the last add *)
let r5j_bpc b = el b [466; 666; 867; 1068; 1269; 1470; 1671];;
let r5j_live_extra = [`bit 0 ((mdl:num->int32) 3)`; `ival ((rb:num->int32) i) < &52371634`; `i < 2048`];;

let r5j_inv_at k =
  let s = `s:wasmstate` in
  rhs(concl(TOP_DEPTH_CONV BETA_CONV (mk_comb(mk_comb(r5j_l1_inv, k), s))));;
let r5j_pre296 = mk_abs(`s:wasmstate`, list_mk_conj [`read wcode s = MC`; `read wpc s = word 296`; r5j_inv_at `i:num`]);;
let r5j_post1810 = mk_abs(`s:wasmstate`, list_mk_conj [`read wcode s = MC`; `read wpc s = word 1810`; r5j_inv_at `i + 1`]);;
let r5j_mid_b b =
  let stk = if b = 0 then r5j_stk [r5j_sgw; r5j_s2w]
            else if b = 6 then r5j_stk [`va1_jg_f (hp:num->int32) (t:int32) (p:int32) i`; r5j_sgw; r5j_s2w]
            else r5j_stk [r5j_psum (b - 1); r5j_sgw; r5j_s2w] in
  r5j_mid (r5j_bpc b) r5j_lbl_blk stk [];;
let r5j_allv = [`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;`t:int32`;`p:int32`;`jq:num->int32`;`rb:num->int32`;`jp:num->int32`;`i:num`];;
let r5j_ens p q = mk_comb(mk_comb(mk_comb(`ensures wasm`, p), q), R5J_FRAME);;
let r5j_seg_stmt ants p q =
  list_mk_forall(r5j_allv, if ants = [] then r5j_ens p q else mk_imp(list_mk_conj ants, r5j_ens p q));;

(* use th: |- ensures wasm P Q C for a goal ensures wasm P' Q' C (P' ==> P, Q ==> Q' by rewriting) *)
let R5J_USE_TAC th =
  let c = concl th in
  let p = rand(rator(rator c)) and q = rand(rator c) in
  MATCH_ACCEPT_TAC th ORELSE
  (MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC p THEN CONJ_TAC THENL
    [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC q THEN CONJ_TAC THENL
      [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
       ACCEPT_TAC th]]);;
(* ---- R5 PROVE-jig: index arithmetic for the ring neighbours (pc 347-378) *)
let R5J_AND2047 = prove
 (`!n. word_and (word n) (word 2047):int32 = word (n MOD 2048)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  MP_TAC(ISPECL [`word n:int32`; `11`] VAL_WORD_AND_MASK_WORD) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  SUBGOAL_THEN `n MOD 2048 < 4294967296` (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL
   [MP_TAC(SPECL [`n:num`; `2048`] MOD_LT_EQ) THEN ARITH_TAC; ALL_TAC] THEN
  SUBST1_TAC(ARITH_RULE `4294967296 = 2048 * 2097152`) THEN
  SIMP_TAC[MOD_MOD; ARITH_EQ]);;

let R5J_SHL2 = prove
 (`!n. word_shl (word n) 2:int32 = word (4 * n)`,
  REWRITE_TAC[VK_WSHL] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[]);;

(* the facts the live branch uses at bead i (state-free rewrites and load instances) *)
let R5J_NEIGH_TAC =
  SUBGOAL_THEN `word_and (word (2047 + i)) (word 2047):int32 = word ((i + 2047) MOD 2048) /\
                word_add (word (2047 + i)) (word 4294965250):int32 = word (i + 1) /\
                word_and (word (i + 1)) (word 2047):int32 = word ((i + 1) MOD 2048) /\
                word_shl (word ((i + 2047) MOD 2048)) 2:int32 = word (4 * ((i + 2047) MOD 2048)) /\
                word_shl (word ((i + 1) MOD 2048)) 2:int32 = word (4 * ((i + 1) MOD 2048)) /\
                (i + 2047) MOD 2048 < 2048 /\ (i + 1) MOD 2048 < 2048`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[R5J_AND2047; R5J_SHL2; MOD_LT_EQ; ARITH_EQ] THEN
    REWRITE_TAC[ARITH_RULE `2047 + i = i + 2047`] THEN
    MATCH_MP_TAC R5J_WRAP THEN ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY VK_VAL_TAC [`4 * ((i + 2047) MOD 2048)`; `4 * ((i + 1) MOD 2048)`];;

let R5J_NEIGH_LOAD_TAC =
  MAP_EVERY (fun n ->
    SUBGOAL_THEN (subst [n,`n:num`] `read (bytes32 (word (4 * n + 1146880))) mm = (jq:num->int32) n`) ASSUME_TAC THENL
     [SUBST1_TAC(SYM(ISPECL [`1146880`; mk_binop `( * ):num->num->num` `4` n] ADD_SYM)) THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC])
   [`(i + 2047) MOD 2048`; `(i + 1) MOD 2048`];;

(* ---- copied from pop_l1_rimd.ml (SEG-L1 prover, 2026-11-11), renamed R5J_*: table column and clamped radius *)
let R5J_RIM_J = prove
 (`!r:int32. val r <= 52371633 ==>
     word_and (word_ushr r 17) (word 16380) =
       word (4 * (val (word_and (word_ushr r 17) (word 16380):int32) DIV 4)) /\
     val (word_and (word_ushr r 17) (word 16380):int32) DIV 4 <= 99`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val (r:int32) DIV 524288 <= 99` ASSUME_TAC THENL
   [MP_TAC(SPECL [`val (r:int32)`; `52371633`; `524288`] DIV_MONO) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `word_and (word_ushr r 17) (word 16380):int32 = word (4 * (val (r:int32) DIV 524288))`
    SUBST1_TAC THENL
   [SUBGOAL_THEN `word_and (word_ushr r 17) (word 16380):int32 =
                  word_shl (word_and (word_ushr r 19) (word 4095)) 2` SUBST1_TAC THENL
     [BITBLAST_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `word_and (word_ushr r 19) (word 4095):int32 = word (val (r:int32) DIV 524288)`
      SUBST1_TAC THENL
     [REWRITE_TAC[GSYM VAL_EQ] THEN
      MP_TAC(ISPECL [`word_ushr r 19:int32`; `12`] VAL_WORD_AND_MASK_WORD) THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[VAL_WORD_USHR; VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
      SUBGOAL_THEN `val (r:int32) DIV 524288 < 4096 /\ val (r:int32) DIV 524288 < 4294967296`
        STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[MOD_LT]];
      REWRITE_TAC[CAP_SHL2]];
    ALL_TAC] THEN
  SUBGOAL_THEN `val (word (4 * (val (r:int32) DIV 524288)):int32) = 4 * (val (r:int32) DIV 524288)`
    SUBST1_TAC THENL [MATCH_MP_TAC CAP_VAL_WORD32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ; ARITH_RULE `4 * x = x * 4`] THEN ASM_REWRITE_TAC[]);;

(* the clamped radius max(r,0) of an in-range bead is a small value          *)
let R5J_RIM_RR = prove
 (`!x:int32. ~(ival x > &52371633) ==> val (if ival x > &0 then x else word 0) <= 52371633`,
  GEN_TAC THEN DISCH_TAC THEN COND_CASES_TAC THENL [ALL_TAC; REWRITE_TAC[VAL_WORD_0; LE_0]] THEN
  MP_TAC(ISPEC `x:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[IVAL_VAL; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_CASES_TAC `bit 31 (x:int32)` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_LE] THEN
  CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN INT_ARITH_TAC);;

let R5J_WADD_TAC t =
  SUBGOAL_THEN t ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN VK_ARITH_TAC; ALL_TAC];;

(* pc 389-465: the clamped radius rr, the table column JJ (RIM_J), the two table loads (as pop_l1_rimd.ml) *)
let R5J_SPD_PREP_TAC =
  ABBREV_TAC `rr = if ival ((rb:num->int32) i) > &0 then rb i else word 0:int32` THEN
  SUBGOAL_THEN `val (rr:int32) <= 52371633` ASSUME_TAC THENL
   [EXPAND_TAC "rr" THEN MATCH_MP_TAC R5J_RIM_RR THEN
    UNDISCH_TAC `ival ((rb:num->int32) i) < &52371634` THEN INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(if ~(ival ((rb:num->int32) i) > &0) then word 0 else rb i) = rr:int32`
    ASSUME_TAC THENL [EXPAND_TAC "rr" THEN REWRITE_TAC[COND_SWAP]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP R5J_RIM_J) THEN
  ABBREV_TAC `JJ = val (word_and (word_ushr rr 17) (word 16380):int32) DIV 4` THEN STRIP_TAC THEN
  R5J_WADD_TAC `word_add (word (65536 + 512 * i)) (word (4 * JJ)):int32 = word (65536 + 4 * (128 * i + JJ))` THEN
  R5J_WADD_TAC `word_add (word (65536 + 4 * (128 * i + JJ))) (word 4):int32 = word (65536 + 4 * (128 * i + JJ + 1))` THEN
  MAP_EVERY VK_VAL_TAC [`65536 + 4 * (128 * i + JJ)`; `65536 + 4 * (128 * i + JJ + 1)`] THEN
  VK_LOADFACT_TAC `read (bytes32 (word (65536 + 4 * (128 * i + JJ)))) mm = (tbl:num->int32) (128 * i + JJ)` THEN
  VK_LOADFACT_TAC `read (bytes32 (word (65536 + 4 * (128 * i + JJ + 1)))) mm = (tbl:num->int32) (128 * i + JJ + 1)` THEN
  MP_TAC VK_COND_I64 THEN MP_TAC VK_COND_I32 THEN REPEAT DISCH_TAC;;

(* the selects of the loop body: (if c then I32 a else I32 b) = I32 (if c then a else b), likewise I64 *)
let () = r5j_extra := [VK_COND_I64; VK_COND_I32];;
(* ---- R5 PROVE-jig: loop-1 segment lemmas (generic MC) *)
(* the stepper's form of the inlined isin (select on i32.lt_s ph 0), folded to the witness va1_jg_sin *)
let R5J_SIN =
  let x = `x:int32` in
  let u = rhs(concl((REWRITE_CONV[va1_jg_sin] THENC TOP_DEPTH_CONV let_CONV) (mk_comb(`va1_jg_sin`, x)))) in
  let c,(a,b) = dest_cond u in
  prove(mk_forall(x, mk_eq(mk_cond(mk_neg c, b, a), mk_comb(`va1_jg_sin`, x))),
        GEN_TAC THEN REWRITE_TAC[va1_jg_sin] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[COND_SWAP]);;

let R5J_PH_SUC = prove
 (`!hp t p n c d k. word_add (va1_jg_ph hp t p n c d k) (word d) = va1_jg_ph hp t p n c d (k + 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[va1_jg_ph; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* peel one bytes32 write off a bytes32 read in the goal (same cell or disjoint), cf. RIM_PEEL_TAC *)
let R5J_PEEL_TAC : tactic =
  let p32 = `read (bytes32 (word (x:num))) (write (bytes32 (word (a:num))) (v:int32) (m:int64->byte))` in
  fun (asl,w) ->
    let t = find_term (can (term_match [] p32)) w in
    let i = term_match [] p32 t in
    let x = instantiate i `x:num` and a = instantiate i `a:num`
    and v = instantiate i `v:int32` and m = instantiate i `m:int64->byte` in
    ((SUBGOAL_THEN (mk_eq(x,a)) ASSUME_TAC THENL
       [VK_ARITH_TAC; FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP CAP_B32_SAME_EQ th])]) ORELSE
     (MP_TAC(SPECL [x; a; v; m] VK_R32_W32) THEN ANTS_TAC THENL
       [VK_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])])) (asl,w);;

(* final-state memory goals over the one KJ store at bead i *)
let R5J_MEMGOALS_TAC (close:tactic) =
  REPEAT CONJ_TAC THEN
  TRY(X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      ((REPEAT R5J_PEEL_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN VK_ARITH_TAC) ORELSE
       (ASM_CASES_TAC `k:num = i` THENL
         [FIRST_X_ASSUM SUBST_ALL_TAC THEN REPEAT R5J_PEEL_TAC THEN close;
          REPEAT R5J_PEEL_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN VK_ARITH_TAC])));;

let R5J_STACK_TAC = REWRITE_TAC[CONS_11; injectivity "wval"];;

(* SEG A: pc 296 -> 466, live bead (guard, s2, sg) *)
let r5j_sega_stmt = r5j_seg_stmt [`i < 2048`; `ival ((rb:num->int32) i) < &52371634`] r5j_pre296 (r5j_mid_b 0);;
let R5J_SEGA_TAC exec =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY VK_VAL_TAC [`1138688 + 4 * i`; `1146880 + 4 * i`] THEN
  R5J_NEIGH_TAC THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN R5J_MEMNAME_TAC THEN
  VK_LOADFACT_TAC `read (bytes32 (word (1138688 + 4 * i))) mm = (rb:num->int32) i` THEN
  VK_LOADFACT_TAC `read (bytes32 (word (1146880 + 4 * i))) mm = (jq:num->int32) i` THEN
  R5J_NEIGH_LOAD_TAC THEN R5J_SPD_PREP_TAC THEN
  R5J_MSTEPS_TAC exec (1--77) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  R5J_STACK_TAC THEN
  REWRITE_TAC[va1_jg_spd] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ASSUME `(if ival ((rb:num->int32) i) > &0 then rb i else word 0:int32) = rr`] THEN
  REWRITE_TAC[ASSUME `val (word_and (word_ushr rr 17) (word 16380):int32) DIV 4 = JJ`] THEN
  REWRITE_TAC[COND_SWAP];;

(* BLOCK b: pc r5j_bpc b -> r5j_bpc (b+1), the inlined isin of phase b times amplitude b (+ add for b > 0) *)
let r5j_blk_stmt b = r5j_seg_stmt [] (r5j_mid_b b) (r5j_mid_b (b + 1));;
let R5J_BLOCK_TAC exec b =
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN R5J_MEMNAME_TAC THEN
  R5J_MSTEPS_TAC exec (1--(if b = 0 then 92 else 93)) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  R5J_STACK_TAC THEN REWRITE_TAC[R5J_SIN; va1_jg_term; va1_jg_f] THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[];;

(* the increments at the end of bead i (pc 1707-1810) and l17 += 1, as stepper rewrites *)
let R5J_INC_TAC =
  MAP_EVERY (fun (n,(_,c,d)) ->
     ASSUME_TAC(SPECL [`hp:num->int32`;`t:int32`;`p:int32`; r5j_num n; mk_numeral(Num.num_of_int c);
                       mk_numeral(Num.num_of_int d); `i:num`] R5J_PH_SUC))
   (zip (0--5) r5j_phl) THEN
  MAP_EVERY R5J_WADD_TAC
   [`word_add (word (65536 + 512 * i)) (word 512):int32 = word (65536 + 512 * (i + 1))`;
    `word_add (word (1146880 + 4 * i)) (word 4):int32 = word (1146880 + 4 * (i + 1))`;
    `word_add (word (2031616 + 4 * i)) (word 4):int32 = word (2031616 + 4 * (i + 1))`;
    `word_add (word (1138688 + 4 * i)) (word 4):int32 = word (1138688 + 4 * (i + 1))`;
    `word_add (word (2047 + i)) (word 1):int32 = word (2047 + (i + 1))`;
    `word_add (word i) (word 1):int32 = word (i + 1)`] THEN
  VK_VAL_TAC `2031616 + 4 * i`;;

let r5j_kj_close =
  REWRITE_TAC[va1_jigk] THEN ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[];;

(* SEG Z: pc 1671 -> 1810, live bead: drive, rounding, store KJ[i], increments *)
let r5j_segz_stmt = r5j_seg_stmt [`i < 2048`; `bit 0 ((mdl:num->int32) 3)`; `ival ((rb:num->int32) i) < &52371634`]
                      (r5j_mid_b 6) r5j_post1810;;
let R5J_SEGZ_TAC exec =
  REPEAT GEN_TAC THEN STRIP_TAC THEN R5J_INC_TAC THEN
  ENSURES_INIT_TAC "s0" THEN R5J_MEMNAME_TAC THEN
  R5J_MSTEPS_TAC exec (1--66) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
  R5J_MEMGOALS_TAC r5j_kj_close;;

(* STOP: pc 296 -> 1810, stopped bead: KJ[i] = 0 *)
let r5j_stop_stmt = r5j_seg_stmt [`i < 2048`; `~(ival ((rb:num->int32) i) < &52371634)`] r5j_pre296 r5j_post1810;;
let R5J_STOP_TAC exec =
  REPEAT GEN_TAC THEN STRIP_TAC THEN R5J_INC_TAC THEN
  VK_VAL_TAC `1138688 + 4 * i` THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN R5J_MEMNAME_TAC THEN
  VK_LOADFACT_TAC `read (bytes32 (word (1138688 + 4 * i))) mm = (rb:num->int32) i` THEN
  R5J_MSTEPS_TAC exec (1--64) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
  R5J_MEMGOALS_TAC r5j_kj_close;;

(* ---- the segment lemmas of loop 1 (generic MC; each |- DEC_H ==> ...) *)
let () = r5j_put "SEGA" (r5j_time "SEGA" (fun () -> r5j_gen_prove r5j_sega_stmt (R5J_SEGA_TAC !R5J_GEN_EXEC_REF)) ());;
let () = List.iter (fun b -> r5j_put ("BLK" ^ string_of_int b)
   (r5j_time ("BLK" ^ string_of_int b) (fun () -> r5j_gen_prove (r5j_blk_stmt b) (R5J_BLOCK_TAC !R5J_GEN_EXEC_REF b)) ())) (0--5);;
let () = r5j_put "SEGZ" (r5j_time "SEGZ" (fun () -> r5j_gen_prove r5j_segz_stmt (R5J_SEGZ_TAC !R5J_GEN_EXEC_REF)) ());;
let () = r5j_put "STOP" (r5j_time "STOP" (fun () -> r5j_gen_prove r5j_stop_stmt (R5J_STOP_TAC !R5J_GEN_EXEC_REF)) ());;
(* ---- R5 PROVE-jig: loop 1 assembled (generic MC): entry, body from the segment lemmas, back edge, exit *)
let R5J_L1_ENTRY_TAC exec =
  ENSURES_INIT_TAC "s0" THEN R5J_MEMNAME_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `3` o check (fun th -> can (find_term ((=) `16640`)) (concl th))) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN DISCH_TAC THEN
  SUBGOAL_THEN `word_and (word_zx (read (bytes8 (word 16652)) mm):int32) (word 1) = word 1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[R5J_B8_LOW; R5J_FLAG_AND]; ALL_TAC] THEN
  MAP_EVERY (fun k ->
     FIRST_ASSUM(MP_TAC o SPEC (mk_small_numeral k) o check (fun th -> can (find_term ((=) `16408`)) (concl th))) THEN
     CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_TAC) (12--23) THEN
  R5J_MSTEPS_TAC exec (1--108) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[va1_jg_ph] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[WORD_ADD_0; LT] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[];;

let R5J_L1_BACK_TAC exec =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`2047 + i`; `4095`] VK_WORD_NE) THEN ANTS_TAC THENL [VK_ARITH_TAC; DISCH_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN R5J_MEMNAME_TAC THEN
  R5J_MSTEPS_TAC exec (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[];;

let R5J_L1_EXIT_TAC exec =
  ENSURES_INIT_TAC "s0" THEN RESOLVE_PC_COND_TAC THEN R5J_MEMNAME_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV)) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV WORD_RED_CONV)) THEN
  R5J_MSTEPS_TAC exec (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[];;

(* a segment lemma |- DEC_H ==> !vars. [A ==>] ensures .. for the current goal (A from the assumptions) *)
let R5J_USE_LEMMA_TAC th : tactic = fun (asl,w) ->
  let th1 = SPEC_ALL (UNDISCH th) in
  let th2 = if is_imp (concl th1) then
      MP th1 (TAC_PROOF((asl, lhand (concl th1)), ASM_REWRITE_TAC[]))
    else th1 in
  R5J_USE_TAC th2 (asl,w);;

let R5J_L1_BODY_TAC sega blks segz stop =
  let rec chain b =
    if b = 6 then R5J_USE_LEMMA_TAC segz else
    ENSURES_SEQUENCE_TAC (r5j_num (r5j_bpc (b + 1))) (r5j_rest (r5j_mid_b (b + 1))) THEN CONJ_TAC THENL
     [R5J_USE_LEMMA_TAC (el b blks); chain (b + 1)] in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `ival ((rb:num->int32) i) < &52371634` THENL
   [ENSURES_SEQUENCE_TAC `466` (r5j_rest (r5j_mid_b 0)) THEN CONJ_TAC THENL
     [R5J_USE_LEMMA_TAC sega; chain 0];
    R5J_USE_LEMMA_TAC stop];;

let R5J_L1_TAC sega blks segz stop =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ENSURES_WHILE_UP_TAC `2048` `296` `1810` r5j_l1_inv THEN REPEAT CONJ_TAC THENL
   [ARITH_TAC; R5J_L1_ENTRY_TAC !R5J_GEN_EXEC_REF; R5J_L1_BODY_TAC sega blks segz stop;
    R5J_L1_BACK_TAC !R5J_GEN_EXEC_REF; R5J_L1_EXIT_TAC !R5J_GEN_EXEC_REF];;

(* ---- loop 1, pc 13 -> 1813, flag set (generic MC) *)
let () = r5j_put "L1_GEN" (r5j_time "L1_GEN" (fun () -> r5j_gen_prove r5j_l1_stmt
  (R5J_L1_TAC (r5j_get "SEGA") (map (fun b -> r5j_get ("BLK" ^ string_of_int b)) (0--5)) (r5j_get "SEGZ") (r5j_get "STOP"))) ());;
(* ---- R5 PROVE-jig: one export (f21 add / f22 sub): flag clear (pc 13 -> WDone, no store) or flag set:      *)
(* generic loop 1 (pc 13 -> 1813, instance of R5J_L1_GEN) ; loop 2 (pc 1813 -> WDone)                        *)
let R5J_CLEAR_TAC exec =
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[va1_mdl; va1_w32s; va1_tick; va1_pop]) THEN MEMNAME_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `3` o check (fun th -> can (find_term ((=) `16640`)) (concl th))) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN DISCH_TAC THEN
  SUBGOAL_THEN `word_and (word_zx (read (bytes8 (word 16652)) mm):int32) (word 1) = word 0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[R5J_B8_LOW; R5J_FLAG_AND]; ALL_TAC] THEN
  R5J_MSTEPS_TAC exec (1--8) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[va1_w32s; va1_jigk; WORD_ADD_0; WORD_SUB_0];;

(* the decode antecedent of R5J_L1_GEN for one export's code *)
let r5j_inst_l1 mc exec =
  let (_,arr) = exec in
  let ths = map (r5j_dec_th arr) (r5j_dec_pcs POP_R5J_F21_EXEC) in
  let th0 = INST [mc, r5j_mcv] (r5j_get "L1_GEN") in
  MP th0 (end_itlist CONJ ths);;

let R5J_EXPORT_TAC mc exec l1 l2 =
  REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_CASES_TAC `bit 0 ((mdl:num->int32) 3)` THENL
   [ENSURES_SEQUENCE_TAC `1813` (r5j_rest (r5j_mid1813 mc)) THEN CONJ_TAC THENL
     [MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
      EXISTS_TAC (subst [mc, r5j_mcv] r5j_pre0) THEN CONJ_TAC THENL
       [X_GEN_TAC `s:wasmstate` THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
        REWRITE_TAC[va1_tick; va1_pop; va1_mdl; va1_w32s; READ_COMPONENT_COMPOSE] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[];
        MP_TAC(SPECL [`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;`t:int32`;`p:int32`;`jq:num->int32`;`rb:num->int32`;`jp:num->int32`] l1) THEN
        ASM_REWRITE_TAC[]];
      ACCEPT_TAC(SPECL [`mdl:num->int32`;`hp:num->int32`;`tbl:num->int32`;`t:int32`;`p:int32`;`jq:num->int32`;`rb:num->int32`;`jp:num->int32`] l2)];
    R5J_CLEAR_TAC exec];;

(* ---- the two exports and the contract *)
let R5J_L2_F21 = r5j_time "L2 f21" (fun () -> prove(r5j_l2_stmt `va1_f21_mc` `word_add:int32->int32->int32`,
   R5J_L2_TAC `va1_f21_mc` POP_R5J_F21_EXEC `word_add:int32->int32->int32`)) ();;
let R5J_L2_F22 = r5j_time "L2 f22" (fun () -> prove(r5j_l2_stmt `va1_f22_mc` `word_sub:int32->int32->int32`,
   R5J_L2_TAC `va1_f22_mc` POP_R5J_F22_EXEC `word_sub:int32->int32->int32`)) ();;
let R5J_L1_F21 = r5j_inst_l1 `va1_f21_mc` POP_R5J_F21_EXEC;;
let R5J_L1_F22 = r5j_inst_l1 `va1_f22_mc` POP_R5J_F22_EXEC;;
let r5j_ok_tm = rhs(concl(ISPEC `va1_jigk` va1_jigk_ok));;
let R5J_F21_OK = r5j_time "f21 export" (fun () -> prove(lhand r5j_ok_tm,
   R5J_EXPORT_TAC `va1_f21_mc` POP_R5J_F21_EXEC R5J_L1_F21 R5J_L2_F21)) ();;
let R5J_F22_OK = r5j_time "f22 export" (fun () -> prove(rand r5j_ok_tm,
   R5J_EXPORT_TAC `va1_f22_mc` POP_R5J_F22_EXEC R5J_L1_F22 R5J_L2_F22)) ();;
let VA1_JIGK_OK = prove(parse_term pop_spec_VA1_JIGK_OK, REWRITE_TAC[va1_jigk_ok; R5J_F21_OK; R5J_F22_OK]);;
let VA1_JIGK_EXISTS = prove(parse_term pop_spec_VA1_JIGK_EXISTS, EXISTS_TAC `va1_jigk` THEN ACCEPT_TAC VA1_JIGK_OK);;
