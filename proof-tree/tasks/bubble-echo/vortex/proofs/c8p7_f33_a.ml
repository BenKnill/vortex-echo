(* C8p P6/P7 copy (2026-11-15) for the C7/C8b context: byte-identical to c8p_f33_a.ml except the needs lines (C7 host file, c8p7 copies). *)
(* ========================================================================= *)
(* Vortex chain C8p rows P3/P4, layer A (lane vortex-chain-20261111-142342,  *)
(* Claude Opus 5.5, 2026-11-15): value-carrying f33 tactics (calls through   *)
(* VA1_F32_VALUE / VA1_F34_VALUE, load normalisation, tee folding), table     *)
(* and counter lemmas, the cell invariant va1_p8_iv, mid-cell assertion       *)
(* builders, and cell segments A (pc 433 -> 559) and B (559 -> 629).          *)
(* Definitions come from c8p_f33_defs.ml (never redefined). Stable layer.     *)
(* ========================================================================= *)
needs "chain_c7_c6b_host.ml";;
needs "c8p_leaves2_pf.ml";;
needs "c8p_f33_defs.ml";;
let c8p_loc asl s j = rhs(concl(find (fun th -> let c = concl th in is_eq c && lhs c = mk_comb(mk_comb(`read:(wasmstate,wval)component->wasmstate->wval`, mk_comb(`wlocal`, mk_small_numeral j)), s)) asl));;
let C8P_F32_CALL_TAC sname : tactic = fun (asl,w) ->
  let s = rand w in
  let stk = rhs(concl(find_read_th "wstack" s (map snd asl))) in
  let k = rand(rand(rator stk)) and x = rand(rand(rator(rand stk))) in
  C5_CALL_TAC C5_F33_EXEC (SPECL [x;k] VA1_F32_VALUE) VA1_F32_CALLEE sname (asl,w);;
let C8P_ORTHS = [C8P_ORTH `bytes64 (word 16352)` `bytes64 (word 16368)`; C8P_ORTH `bytes64 (word 16352)` `bytes64 (word 16360)`;
              C8P_ORTH `bytes64 (word 16360)` `bytes64 (word 16368)`];;
let C8P_F34MEM_TAC : tactic = fun (asl,w) ->
  let s = rand w in
  let mth = find_read_th "wmem" s (map snd asl) in
  let fact a = let t = subst [s,`s:wasmstate`; mk_small_numeral a, `a:num`] `read (bytes64 (word a)) (read wmem (s:wasmstate))` in
    let th = (REWRITE_CONV[mth] THENC REWRITE_CONV C8P_ORTHS THENC TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) t in th in
  MAP_EVERY (fun a -> ASSUME_TAC (fact a)) [16352;16360;16368] (asl,w);;
let has_sub s p = let n = String.length s and m = String.length p in
  let rec go i = i + m <= n && (String.sub s i m = p || go (i+1)) in go 0;;
let C8P_ADDRS = map (fun a -> mk_comb(`bytes64`, mk_comb(`word:num->int64`, mk_small_numeral a))) [16288;16296;16304;16320;16328;16336;16352;16360;16368];;
let C8P_ORTHS9 = List.concat (map (fun a -> mapfilter (fun b -> if a = b then fail() else C8P_ORTH a b) C8P_ADDRS) C8P_ADDRS);;
let C8P_RDCONV = REWRITE_CONV C8P_ORTHS9 THENC TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV;;
let C8P_YFACTS_TAC : tactic = fun (asl,w) ->
  let mc1 = find (fun th -> let c = concl th in is_eq c && lhs c = `read wmem (c1:wasmstate)`) (map snd asl) in
  let news = mapfilter (fun (_,th) -> let c = concl th in
     let l,r = dest_eq c in
     if not (free_in `read wmem (c1:wasmstate)` l) || l = `read wmem (c1:wasmstate)` then fail() else
     let th' = CONV_RULE(LAND_CONV(REWRITE_CONV[mc1] THENC C8P_RDCONV)) th in
     if is_var(lhs(concl th')) then th' else fail()) asl in
  MAP_EVERY ASSUME_TAC news (asl,w);;
let C8P_DONE_CONT (sname:string) s pc_num n np c0tm : tactic =
  let npc = mk_binop `(+):num->num->num` pc_num n in
  let sv' = mk_var(sname,`:wasmstate`) in
  let pc_th_tm = mk_eq(mk_comb(`read wpc`,s), mk_comb(`word:num->int64`,pc_num)) in
  let is_rmem_c1 th = let c = concl th in
     is_eq c && lhs c = `read wmem (c1:wasmstate)` in
       X_GEN_TAC `c1:wasmstate` THEN
       ABBREV_TAC (mk_eq(`c0:wasmstate`, c0tm)) THEN
       SUBGOAL_THEN (subst [s,`s:wasmstate`]
          `read wmem (c0:wasmstate) = read wmem (s:wasmstate) /\
           read wmemsize c0 = read wmemsize (s:wasmstate) /\
           read wglobals c0 = read wglobals (s:wasmstate)`)
         STRIP_ASSUME_TAC THENL
        [EXPAND_TAC "c0" THEN REWRITE_TAC[WCALL_ENTRY_READS]; ALL_TAC] THEN
       (fun (asl,w) ->
          let mth = find_read_th "wmem" s (map snd asl) in
          RULE_ASSUM_TAC(fun th -> let c = concl th in
            if is_eq c && lhs c = `read wmem (c0:wasmstate)` then REWRITE_RULE[mth] th else th) (asl,w)) THEN
       DISCH_THEN(CONJUNCTS_THEN2
         (STRIP_ASSUME_TAC o CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) MP_TAC) THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [MAYCHANGE; SEQ_ID] THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [GSYM SEQ_ASSOC] THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_SEQ] THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_THM] THEN
       REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
       WASMC_MEM_UPDATE_TAC THEN ASSUMPTION_STATE_UPDATE_TAC THEN
       DISCH_THEN(K ALL_TAC) THEN
       SUBGOAL_THEN
         (mk_eq(list_mk_comb(`wcall_return`,
                  [mk_binop `(+):num->num->num` (mk_comb(`val:int64->num`,
                     mk_comb(`read wpc`,s))) n; np; `c1:wasmstate`; s]),
                list_mk_comb(`write wpc`,
                  [mk_comb(`word:num->int64`, npc);
                   list_mk_comb(`write wstack`,
                     [list_mk_comb(`APPEND:wval list->wval list->wval list`,
                        [`read wstack (c1:wasmstate)`;
                         list_mk_comb(`wdrop:num->wval list->wval list`,
                                      [np; mk_comb(`read wstack`,s)])]);
                      list_mk_comb(`write wmem`, [`read wmem (c1:wasmstate)`; s])])])))
         SUBST1_TAC THENL
        [SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`, mk_comb(`read wpc`,s)), pc_num))
           SUBST1_TAC THENL
          [REWRITE_TAC[ASSUME pc_th_tm; VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV;
           ALL_TAC] THEN
         MATCH_MP_TAC CP_WCALL_RETURN_N THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
       FIRST_ASSUM(fun th -> if is_rmem_c1 th then REWRITE_TAC[th] else NO_TAC) THEN
       REWRITE_TAC[WMEM_SVC; WCALL_WRITE_MEM1; WCALL_WRITE_MEM2] THEN
       ASM_REWRITE_TAC[] THEN
       CONV_TAC(ONCE_DEPTH_CONV CP_LOCALS_EVAL_CONV) THEN
       CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
       WASMC_GEN_STATE_TAC sv' THEN
       X_GEN_TAC sv' THEN
       WASMC_MEM_UPDATE_TAC THEN ASSUMPTION_STATE_UPDATE_TAC THEN
       MAYCHANGE_STATE_UPDATE_TAC THEN
       DISCH_THEN(fun th ->
         let thl = STATE_UPDATE_NEW_RULE th in
         if thl = [] then ALL_TAC else MP_TAC(end_itlist CONJ thl) THEN STRIP_TAC) THEN
       C8P_YFACTS_TAC THEN DISCARD_OLD_WASMSTATE_TAC sname THEN WASM_COMPACT_HYPS_TAC;;
let C8P_F34_CALL_TAC sname : tactic = fun (asl,w) ->
  let s = rand w in let ths = map snd asl in
  let v j = rand(c8p_loc ths s j) in
  CP_CALL_GEN_TAC C5_F33_EXEC (SPECL [v 10; v 9; v 8] VA1_F34_VALUE) VA1_F34_CALLEE (C8P_DONE_CONT sname) (asl,w);;
let C8P_POSTMEM_TAC : tactic = fun (asl,w) ->
  let s = rand w in
  let mth = find_read_th "wmem" s (map snd asl) in
  let ys = filter (fun th -> let c = concl th in is_eq c && is_var(lhs c) && type_of(lhs c) = `:int64`) (map snd asl) in
  let fact a = let t = subst [s,`s:wasmstate`; mk_small_numeral a, `a:num`] `read (bytes64 (word a)) (read wmem (s:wasmstate))` in
    (REWRITE_CONV[mth] THENC C8P_RDCONV THENC REWRITE_CONV ys) t in
  MAP_EVERY (fun a -> ASSUME_TAC (fact a)) [16288;16296;16304;16320;16328;16336] (asl,w);;
let C8P_LDNORM_TAC : tactic = fun (asl,w) ->
  let s = rand w in
  RULE_ASSUM_TAC(fun th -> let c = concl th in
    if is_eq c && (match lhs c with Comb(Comb(Const("read",_),_),s') -> s' = s | _ -> false) &&
       can (find_term (fun t -> match t with Comb(Comb(Const("read",_),Comb(Const("bytes64",_),_)),Comb(Comb(Comb(Const("write",_),_),_),_)) -> true | _ -> false)) (rhs c)
    then CONV_RULE(RAND_CONV C8P_RDCONV) th else th) (asl,w);;
let c8p_folds = ref ([]:(int*thm) list);;
let C8P_FOLD_TAC pc : tactic = fun (asl,w) ->
  try let th = assoc pc !c8p_folds in RULE_ASSUM_TAC(PURE_REWRITE_RULE[th]) (asl,w) with Failure _ -> ALL_TAC (asl,w);;
let rec C8P_DRIVE stops : tactic = fun (asl,w) ->
  let s = rand w in
  if not (c5_running asl s) then ALL_TAC (asl,w) else
  let pc = c5_pc asl s in
  if mem pc stops then ALL_TAC (asl,w) else
  (incr c5_ctr; let sn = "r" ^ string_of_int !c5_ctr in
   let one = if pc = 180 then C8P_F34MEM_TAC THEN C8P_F34_CALL_TAC sn THENL [CONV_TAC C8P_RDCONV THEN REWRITE_TAC[]; C8P_POSTMEM_TAC]
     else if mem pc c5_call_pcs32 then C8P_F32_CALL_TAC sn
     else C5T_STEP C5_F33_EXEC sn THEN C8P_LDNORM_TAC THEN C8P_FOLD_TAC pc in
   C5_GUARD_TAC THEN (one ORELSE (WASM_F64_CASES_TAC THEN one)) THEN C8P_DRIVE stops) (asl,w);;
let c8p_cellfolds = map (fun (pc,d) -> pc, GSYM(SPECL [`a0:int32`;`a1:int32`;`a2:int32`;`w:int32`;`k:num`;`i:num`] d))
  [757,va1_pd6; 767,va1_pd28; 826,va1_pd29; 839,va1_pd30; 979,va1_pd5; 1016,va1_pd5b];;
c8p_folds := c8p_cellfolds;;
let C8P_CNT0 = prove
 (`va1_pcnt 0 = word 0`, REWRITE_TAC[va1_pcnt; ITER]);;
let C8P_CNTS = prove
 (`!n. va1_pcnt (n + 1) = wfbin 160 (va1_pcnt n) (word 4607182418800017408)`,
  REWRITE_TAC[va1_pcnt; GSYM ADD1; ITER]);;
let C8P_TBLIDX = prove
 (`!a0 a1 a2 w k i. i < 128 ==> va1_ptbl a0 a1 a2 w (128 * k + i) = va1_pcell a0 a1 a2 w k i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[va1_ptbl] THEN
  SUBGOAL_THEN `(128 * k + i) DIV 128 = k /\ (128 * k + i) MOD 128 = i` (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THENL [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `i:num`; MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `k:num`] THEN ASM_ARITH_TAC);;
let C8P_B32_W32_OTHER = prove
 (`!a b (y:int32) (m:int64->byte).
     (a + 4 <= b \/ b + 4 <= a) /\ a + 4 < 2 EXP 64 /\ b + 4 < 2 EXP 64
     ==> read (bytes32 (word a)) (write (bytes32 (word b)) y m) = read (bytes32 (word a)) m`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC READ_WRITE_ORTHOGONAL_COMPONENTS THEN
  REWRITE_TAC[bytes32] THEN MATCH_MP_TAC ORTHOGONAL_COMPONENTS_SUB_LEFT THEN
  MATCH_MP_TAC ORTHOGONAL_COMPONENTS_SUB_RIGHT THEN
  REWRITE_TAC[ORTHOGONAL_COMPONENTS_BYTES; DIMINDEX_64] THEN
  MATCH_MP_TAC NONOVERLAPPING_MODULO_SIMPLE THEN
  SUBGOAL_THEN `val(word a:int64) = a /\ val(word b:int64) = b`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;
let C8P_TBL_STEP = prove
 (`!a0 a1 a2 w k i v (mm:int64->byte). k < 2048 /\ i < 128 /\
     (!j. j < 128 * k + i ==> read (bytes32 (word (65536 + 4 * j))) mm = va1_ptbl a0 a1 a2 w j) /\
     v = va1_pcell a0 a1 a2 w k i
     ==> !j. j < 128 * k + (i + 1)
             ==> read (bytes32 (word (65536 + 4 * j))) (write (bytes32 (word (65536 + 512 * k + 4 * i))) v mm) =
                 va1_ptbl a0 a1 a2 w j`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `j = 128 * k + i` THENL
   [ASM_REWRITE_TAC[ARITH_RULE `65536 + 4 * (128 * k + i) = 65536 + 512 * k + 4 * i`] THEN
    CONV_TAC(LAND_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN ASM_SIMP_TAC[C8P_TBLIDX];
    W(MP_TAC o PART_MATCH (lhand o rand) C8P_B32_W32_OTHER o lhand o snd) THEN
    ANTS_TAC THENL [REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;
let c8p_vals_o = [8,"F64","va1_pu2 a0 a1 a2"; 9,"F64","va1_pu1 a0 a1 a2"; 10,"F64","va1_pu0 a0 a1 a2";
  12,"F64","va1_pg12 w"; 13,"F64","va1_pg13 w"; 14,"F64","va1_pg14 w"; 15,"F64","va1_pg15 w";
  16,"F64","va1_pe2z a0 a1 a2"; 17,"F64","va1_pe1z a0 a1 a2"; 18,"F64","va1_pe2y a0 a1 a2"; 19,"F64","va1_pe1y a0 a1 a2";
  20,"F64","va1_pe2x a0 a1 a2"; 21,"F64","va1_pe1x a0 a1 a2"; 22,"F64","va1_pcnt k"];;
let c8p_vals_i = c8p_vals_o @ [24,"F64","va1_pr24 a0 a1 a2 k"; 25,"F64","va1_pr25 a0 a1 a2 k"; 26,"F64","va1_pr26 a0 a1 a2 k";
  27,"F64","va1_pcnt i"];;
let c8p_vtext vals = String.concat "" (map (fun (l,c,t) -> Printf.sprintf " /\\ read (wlocal %d) s = %s (%s)" l c t) vals);;
let c8p_ttext n = Printf.sprintf " /\\ (!j. j < %s ==> read (bytes32 (word (65536 + 4 * j))) (read wmem s) = va1_ptbl a0 a1 a2 w j)" n;;
let va1_p8_iv = new_definition (parse_term (
  "va1_p8_iv (a0:int32) (a1:int32) (a2:int32) (w:int32) (m:int64->byte) (k:num) (i:num) (s:wasmstate) <=>
    read wcode s = va1_puncture_mc /\\ read wstatus s = WRunning /\\
    read wstack s = (if read wpc s = word 433 then [] else [I32 (word (bitval (~(word (4 * i) = (word 512:int32)))))]) /\\
    read wlabels s = [0,431,0; 0,333,0; 0,1241,0] /\\ read warity s = 1 /\\ read wmemsize s = 4194304 /\\
    read (wglobal 0) s = I32 (word 16288) /\\ read (wlocal 0) s = I32 a0 /\\ read (wlocal 1) s = I32 a1 /\\
    read (wlocal 2) s = I32 a2 /\\ read (wlocal 3) s = I32 (word 16288) /\\
    read (wlocal 4) s = I32 (word (4 * i)) /\\ read (wlocal 11) s = I32 (word (65536 + 512 * k)) /\\
    read (wlocal 23) s = I32 (word k) /\\ va1_f33_frame m (read wmem s)" ^ c8p_vtext c8p_vals_i ^ c8p_ttext "128 * k + i"));;
(* mid-cell assertion without the pc conjunct (C8P_SEQ_TAC adds it) *)
let c8p_mid stk lbl vals =
  parse_term (Printf.sprintf
  "\\s. read wcode s = va1_puncture_mc /\\ read wstatus s = WRunning /\\
   %s /\\ read wlabels s = %s /\\ read warity s = 1 /\\ read wmemsize s = 4194304 /\\
   read (wglobal 0) s = I32 (word 16288) /\\ read (wlocal 0) s = I32 a0 /\\ read (wlocal 1) s = I32 a1 /\\
   read (wlocal 2) s = I32 a2 /\\ read (wlocal 3) s = I32 (word 16288) /\\
   read (wlocal 4) s = I32 (word (4 * i)) /\\ read (wlocal 11) s = I32 (word (65536 + 512 * k)) /\\
   read (wlocal 23) s = I32 (word k) /\\ va1_f33_frame m (read wmem s)%s%s"
   stk lbl (c8p_vtext vals) (c8p_ttext "128 * k + i"));;
let CP6 = "a0 a1 a2 w k i";;
let c8p_v559 = c8p_vals_i @ [5,"F64","va1_pcl " ^ CP6; 28,"F64","va1_pc28 " ^ CP6; 29,"F64","va1_pc29 " ^ CP6; 30,"F64","va1_pc30 " ^ CP6];;
let c8p_v629 = c8p_v559 @ [6,"F64","va1_pch " ^ CP6; 7,"F64","va1_pc7 " ^ CP6; 31,"F64","va1_pc31 " ^ CP6];;
let c8p_v1152 = c8p_vals_i @ [32,"I32","va1_pcell " ^ CP6];;
let C8P_SEG_INIT_TAC =
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[va1_p8_iv]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_TAC o check (is_exists o concl))) THEN
  (fun (asl,w) -> let pth = find_read_th "wpc" `s0:wasmstate` (map snd asl) in
     RULE_ASSUM_TAC(fun th -> if can (find_term is_cond) (concl th) && not (is_forall (concl th)) then
        CONV_RULE(DEPTH_CONV WORD_RED_CONV) (REWRITE_RULE[pth] th) else th) (asl,w)) THEN
  ABBREV_TAC `mm = read wmem (s0:wasmstate)`;;
let C8P_SEQ_TAC pc asrt =
  let s,b = dest_abs asrt in
  let q = mk_abs(s, mk_conj(mk_eq(mk_comb(`read wpc`,s), mk_comb(`word:num->int64`, mk_small_numeral pc)), b)) in
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN EXISTS_TAC q THEN
  CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; CONJ_TAC];;
let c8p_cell_goal = `!fs a0 a1 a2 w m k i. fs 32 = (va1_f32_mc,2,1) /\ k < 2048 /\ i < 128
     ==> ensures (wasmc fs)
          (\s. read wpc s = word 433 /\ va1_p8_iv a0 a1 a2 w m k i s)
          (\s. read wpc s = word 1187 /\ va1_p8_iv a0 a1 a2 w m k (i + 1) s)
          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocals] ,, MAYCHANGE [wglobal 0] ,, MAYCHANGE [wmem])`;;
let C8P_CLOSE_TAC defs =
  ENSURES_FINAL_STATE_TAC THEN REPEAT CONJ_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(REWRITE_TAC(injectivity "wval" :: defs) THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN ASM_REWRITE_TAC[] THEN NO_TAC);;
let c8p_dC = [va1_pcell; va1_pcp; va1_pcn; va1_pd5b; va1_pd5; va1_pd30; va1_pd29; va1_pd28; va1_pd6];;
let c8p_dA = [va1_pcl; va1_pc28; va1_pc29; va1_pc30; va1_pcs; va1_pcc; va1_pct];;
let c8p_dB = [va1_pch; va1_pc7; va1_pc31];;
let c8p_pcabs pc asrt = let s,b = dest_abs asrt in
  mk_abs(s, mk_conj(mk_eq(mk_comb(`read wpc`,s), mk_comb(`word:num->int64`, mk_small_numeral pc)), b));;
let c8p_seg_goal p ap q aq =
  let frame = `MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,, MAYCHANGE [wstatus] ,,
           MAYCHANGE [wlocals] ,, MAYCHANGE [wglobal 0] ,, MAYCHANGE [wmem]` in
  let e = list_mk_comb(`ensures (wasmc fs)`, [c8p_pcabs p ap; c8p_pcabs q aq; frame]) in
  list_mk_forall([`fs:num->byte list#num#num`; `a0:int32`; `a1:int32`; `a2:int32`; `w:int32`; `m:int64->byte`; `k:num`; `i:num`],
    mk_imp(`fs 32 = (va1_f32_mc,2,1) /\ k < 2048 /\ i < 128`, e));;
let C8P_SEG_TAC stop defs =
  REPEAT GEN_TAC THEN STRIP_TAC THEN C8P_SEG_INIT_TAC THEN
  MP_TAC(SPECL [`k:num`; `i:num`] VA1_C5_ADDR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C8P_DRIVE [stop] THEN C8P_CLOSE_TAC defs;;
let c8p_a433 = `\s:wasmstate. va1_p8_iv a0 a1 a2 w m k i s`;;
let c8p_a559 = c8p_mid "read wstack s = []" c5_L3 c8p_v559;;
let c8p_a629 = c8p_mid "read wstack s = []" c5_L3 c8p_v629;;
let C8P_SEG_A = prove(c8p_seg_goal 433 c8p_a433 559 c8p_a559, C8P_SEG_TAC 559 c8p_dA);;
let C8P_SEG_B = prove(c8p_seg_goal 559 c8p_a559 629 c8p_a629, C8P_SEG_TAC 629 c8p_dB);;
