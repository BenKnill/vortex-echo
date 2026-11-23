(* ========================================================================= *)
(* WebAssembly (MVP integer ISA) semantics in s2n-bignum style.             *)
(*                                                                           *)
(* Harvard model: the code of one function body (a byte list, exactly the   *)
(* Code-section entry body: local declarations then the expression ending  *)
(* in 0x0B) is a state component that no instruction writes. The program   *)
(* counter is a byte offset into it. Instructions are decoded in the logic  *)
(* from the bytes (LEB128 immediates, opcode table, blocktypes, memargs).  *)
(*                                                                           *)
(* Instructions: unreachable nop block loop if else end br br_if br_table  *)
(* return drop select local.get/set/tee global.get/set, all i32/i64 loads  *)
(* and stores (incl. 8/16/32-bit sign/zero-extending forms), memory.size,  *)
(* i32/i64 const eqz comparisons add sub mul div_s div_u rem_s rem_u and   *)
(* or xor shl shr_s shr_u rotl rotr clz ctz popcnt, i32.wrap_i64,          *)
(* i64.extend_i32_s/u. Traps: unreachable, out-of-bounds memory, division  *)
(* by zero, div_s overflow. Checked against wasmtime by wasm/conformance.  *)
(*                                                                           *)
(* Extension (lane WASM2, 2026-11-04), for the opcodes of the shipped       *)
(* HOL-on-Workers hol.wasm: sign-extension operators (i32.extend8_s,        *)
(* i32.extend16_s, i64.extend8_s/16_s/32_s); f32/f64 values as raw IEEE     *)
(* bit patterns with const, load, store and the four reinterpret ops;       *)
(* bulk memory.fill and memory.copy (bounds checked before any write, as   *)
(* in the bulk-memory spec). Decoded but not executed (no successor, so no *)
(* theorem can run through them): call, call_indirect, memory.grow.        *)
(* Blocktypes f32/f64 have arity 1.                                        *)
(*                                                                           *)
(* Extension (lane hearth-f64, 2026-11-06; claims qualified 2026-11-07     *)
(* after review): the float numeric, compare, convert and trunc ops        *)
(* execute, as UNINTERPRETED functions of the raw bit patterns: wfbin /    *)
(* wfun / wfrel / wfcvt / wftrap, indexed by the opcode (0xFC trunc_sat    *)
(* sub-opcode n is index 256 + n). Each is defined as @f. T: one fixed (so *)
(* deterministic) but unspecified function. Carrying a theorem over to     *)
(* real engines is a METATHEORETIC argument, not a HOL theorem: a proof    *)
(* that never unfolds these definitions (treats the constants opaquely)    *)
(* can be replayed with other functions in their place. The replacement    *)
(* has one constraint: constants of the same type share their epsilon      *)
(* term, so HOL proves for example wfun = wfcvt at equal word sizes, and   *)
(* one family must then serve both. IEEE-754 fits, because ops sharing a   *)
(* family have disjoint opcode indices. Exact, because the spec defines    *)
(* them on bits: abs, neg, copysign (sign-bit operations). Compares return *)
(* 0 or 1. Trapping truncs trap iff the unspecified predicate wftrap       *)
(* holds; trunc_sat never traps. NaN: the Wasm spec lets an arithmetic NaN *)
(* result carry any payload (nondeterministic); this model fixes one       *)
(* function, so the argument covers runs whose NaN bits agree (always true *)
(* for NaN-free runs).                                                     *)
(*                                                                           *)
(* Extension (hol-hearth wasm tooling H1, 2026-11-11): the operations that  *)
(* never round are now DEFINED on the bits, exactly as the Wasm spec: all   *)
(* compares (wfrel), the trapping truncs' trap and result (wftrap, wfcvt), *)
(* the saturating truncs and f64.convert_i32_s/u (wfcvt); see the float     *)
(* block. Theorems about them no longer need the metatheoretic argument.   *)
(* wfbin, wfun and the other wfcvt opcodes (which round, or choose NaN     *)
(* payloads) stay uninterpreted as described above; the shared-epsilon     *)
(* remark now applies to wfbin, wfun and wfcvt's uninterpreted fallback.   *)
(*                                                                           *)
(* Extension (tooling sprint 2, lane 1, 2026-11-08): a memory access trace *)
(* beside the unchanged state. wasm_mem_events s lists the accesses of the  *)
(* instruction at the pc of s (is_write, address, width), program order;   *)
(* wasmt (s,t) (s',t') <=> wasm s s' /\ t' = APPEND t (wasm_mem_events s). *)
(* See the end of this file; access tactics are in wasm_tactics.ml.        *)
(*                                                                           *)
(* Requires the s2n-bignum common layer (components, relational).           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Values, status, operators, instructions.                                  *)
(* ------------------------------------------------------------------------- *)

let wval_INDUCT,wval_RECURSION = define_type
  "wval = I32 int32 | I64 int64 | F32 int32 | F64 int64";;

let wstat_INDUCT,wstat_RECURSION = define_type
  "wstat = WRunning | WTrapped | WDone";;

let wbinop_INDUCT,wbinop_RECURSION = define_type
  "wbinop = Badd | Bsub | Bmul | Band | Bor | Bxor
          | Bshl | Bshr_s | Bshr_u | Brotl | Brotr
          | Bdiv_s | Bdiv_u | Brem_s | Brem_u";;

let wunop_INDUCT,wunop_RECURSION = define_type
  "wunop = Uclz | Uctz | Upopcnt";;

(* Order matches the opcode order eq ne lt_s lt_u gt_s gt_u le_s le_u ge_s ge_u *)
let wrelop_INDUCT,wrelop_RECURSION = define_type
  "wrelop = Req | Rne | Rlt_s | Rlt_u | Rgt_s | Rgt_u
          | Rle_s | Rle_u | Rge_s | Rge_u";;

(* Wblock a e: result arity a, continuation e = offset after matching end.  *)
(* Wif a e1 e2: arity a; e1 = offset after the matching else, or (no else) *)
(* the offset of the matching end itself; e2 = offset after matching end.  *)
(* Loads/stores carry the memarg offset (alignment hint is decoded, unused).*)
let winstr_INDUCT,winstr_RECURSION = define_type
  "winstr = Wunreachable | Wnop | Wblock num num | Wloop | Wend
          | Wif num num num | Welse | Wbr_table (num list) num
          | Wbr num | Wbr_if num | Wreturn | Wdrop | Wselect
          | Wlocal_get num | Wlocal_set num | Wlocal_tee num
          | Wglobal_get num | Wglobal_set num
          | Wi32_load num | Wi32_load8_u num | Wi32_store num | Wi32_store8 num
          | Wi64_load num | Wi32_load8_s num | Wi32_load16_s num
          | Wi32_load16_u num | Wi64_load8_s num | Wi64_load8_u num
          | Wi64_load16_s num | Wi64_load16_u num | Wi64_load32_s num
          | Wi64_load32_u num | Wi64_store num | Wi32_store16 num
          | Wi64_store8 num | Wi64_store16 num | Wi64_store32 num
          | Wmemory_size
          | Wi32_const int32 | Wi64_const int64
          | Wi32_eqz | Wi32_rel wrelop | Wi32_bin wbinop | Wi32_un wunop
          | Wi64_eqz | Wi64_rel wrelop | Wi64_bin wbinop | Wi64_un wunop
          | Wi32_wrap_i64 | Wi64_extend_i32_s | Wi64_extend_i32_u
          | Wi32_extend8_s | Wi32_extend16_s
          | Wi64_extend8_s | Wi64_extend16_s | Wi64_extend32_s
          | Wf32_const int32 | Wf64_const int64
          | Wf32_load num | Wf64_load num | Wf32_store num | Wf64_store num
          | Wi32_reinterpret_f32 | Wi64_reinterpret_f64
          | Wf32_reinterpret_i32 | Wf64_reinterpret_i64
          | Wmemory_fill | Wmemory_copy | Wmemory_grow
          | Wcall num | Wcall_indirect num num
          | Wf32_rel num | Wf64_rel num | Wf32_un num | Wf64_un num
          | Wf32_bin num | Wf64_bin num
          | Wf32_abs | Wf32_neg | Wf32_copysign
          | Wf64_abs | Wf64_neg | Wf64_copysign
          | Wi32_trunc_f32 num | Wi32_trunc_f64 num
          | Wi64_trunc_f32 num | Wi64_trunc_f64 num
          | Wi32_trunc_sat_f32 num | Wi32_trunc_sat_f64 num
          | Wi64_trunc_sat_f32 num | Wi64_trunc_sat_f64 num
          | Wf32_convert_i32 num | Wf32_convert_i64 num
          | Wf64_convert_i32 num | Wf64_convert_i64 num
          | Wf32_demote_f64 | Wf64_promote_f32";;

(* ------------------------------------------------------------------------- *)
(* Float operations (lane hearth-f64; exact rounding-free cases, hol-hearth   *)
(* wasm tooling H1, 2026-11-11). Arguments are the raw IEEE bit patterns    *)
(* (int32 for f32, int64 for f64); the first argument is the opcode (0xFC   *)
(* trunc_sat sub-opcode n: 256 + n).                                        *)
(*                                                                           *)
(* EXACT (defined on the bits; the cases that never round):                 *)
(*   wfrel     all f32/f64 compares (0x5B-0x60, 0x61-0x66): false when an   *)
(*             operand is NaN (ne: true), +0 = -0, otherwise the order of   *)
(*             the values, read off the sign-magnitude key wf_key;          *)
(*   wftrap    the trapping truncs (0xA8-0xAB, 0xAE-0xB1): trap iff NaN,    *)
(*             infinite, or the value truncated toward zero (wf_trunc) is  *)
(*             outside the target range;                                    *)
(*   wfcvt     the trapping truncs' results (iword of wf_trunc), the        *)
(*             saturating truncs (256-263: NaN -> 0, else clamped), and     *)
(*             f64.convert_i32_s/u (0xB7/0xB8; every i32 is an f64).        *)
(* UNINTERPRETED (rounding or NaN payload choice): wfbin, wfun, and wfcvt   *)
(* at every other opcode (f32.convert_*, f64.convert_i64_*, demote,         *)
(* promote) are one fixed but unspecified function (@f. T), as before;     *)
(* see the header for what that means for carrying a result to an engine.  *)
(* Formats: wf_ebits = 8 (f32) or 11 (f64) exponent bits, wf_fbits the      *)
(* fraction bits, bias 2^(E-1) - 1, subnormals with exponent field 0.       *)
(* Conformance: wasm/conformance/conf_float.ml (HOL evaluation of these     *)
(* definitions against engine-recorded results) and float_cases.json.       *)
(* ------------------------------------------------------------------------- *)

let wfbin = new_definition
 `wfbin = (@f:num->N word->N word->N word. T)`;;

let wfun = new_definition
 `wfun = (@f:num->N word->N word. T)`;;

let wf_ebits = new_definition
 `wf_ebits (a:N word) = if dimindex(:N) = 32 then 8 else 11`;;

let wf_fbits = new_definition
 `wf_fbits (a:N word) = dimindex(:N) - 1 - wf_ebits a`;;

let wf_exp = new_definition
 `wf_exp (a:N word) = (val a DIV 2 EXP wf_fbits a) MOD 2 EXP wf_ebits a`;;

let wf_frac = new_definition
 `wf_frac (a:N word) = val a MOD 2 EXP wf_fbits a`;;

let wf_sign = new_definition
 `wf_sign (a:N word) <=> val a DIV 2 EXP (dimindex(:N) - 1) = 1`;;

let wf_nan = new_definition
 `wf_nan (a:N word) <=> wf_exp a = 2 EXP wf_ebits a - 1 /\ ~(wf_frac a = 0)`;;

let wf_inf = new_definition
 `wf_inf (a:N word) <=> wf_exp a = 2 EXP wf_ebits a - 1 /\ wf_frac a = 0`;;

(* sign-magnitude key: for non-NaN a, b the IEEE order of the values is the  *)
(* integer order of the keys, and +0, -0 both have key 0                     *)
let wf_key = new_definition
 `wf_key (a:N word) =
    if wf_sign a then --(&(val a MOD 2 EXP (dimindex(:N) - 1)))
    else &(val a MOD 2 EXP (dimindex(:N) - 1)):int`;;

(* |value| truncated toward zero, for finite a (an infinity gives 2^(bias+1), *)
(* beyond every target range)                                                *)
let wf_mag = new_definition
 `wf_mag (a:N word) =
    let bias = 2 EXP (wf_ebits a - 1) - 1 in
    let sig = if wf_exp a = 0 then wf_frac a else wf_frac a + 2 EXP wf_fbits a in
    let ee = if wf_exp a = 0 then 1 else wf_exp a in
    if bias + wf_fbits a <= ee then sig * 2 EXP (ee - (bias + wf_fbits a))
    else sig DIV 2 EXP ((bias + wf_fbits a) - ee)`;;

let wf_trunc = new_definition
 `wf_trunc (a:N word) = if wf_sign a then --(&(wf_mag a)) else &(wf_mag a):int`;;

(* trunc targets: index 0-7 = i32 f32 s/u, i32 f64 s/u, i64 f32 s/u, i64 f64 s/u *)
let wf_tidx = new_definition
 `wf_tidx k = if 256 <= k then k - 256 else if k <= 0xAB then k - 0xA8 else k - 0xAA`;;

let wf_tbits = new_definition
 `wf_tbits k = if wf_tidx k < 4 then 32 else 64`;;

let wf_tlo = new_definition
 `wf_tlo k = if EVEN (wf_tidx k) then --(&2 pow (wf_tbits k - 1)) else &0:int`;;

let wf_thi = new_definition
 `wf_thi k = if EVEN (wf_tidx k) then &2 pow (wf_tbits k - 1) - &1
             else &2 pow wf_tbits k - &1:int`;;

(* exact encoding of -m (neg) or m when bitsize m - 1 <= the fraction bits *)
let wf_of_int = new_definition
 `wf_of_int (neg:bool) (m:num) : N word =
    if m = 0 then word 0 else
    word ((if neg then 2 EXP (dimindex(:N) - 1) else 0) +
          (bitsize m - 1 + (2 EXP (wf_ebits (word 0:N word) - 1) - 1)) *
            2 EXP wf_fbits (word 0:N word) +
          (m - 2 EXP (bitsize m - 1)) * 2 EXP (wf_fbits (word 0:N word) - (bitsize m - 1)))`;;

let wfrel = new_definition
 `wfrel k (a:N word) (b:N word) <=>
    if k = 0x5C \/ k = 0x62 then wf_nan a \/ wf_nan b \/ ~(wf_key a = wf_key b)
    else ~wf_nan a /\ ~wf_nan b /\
         (if k = 0x5B \/ k = 0x61 then wf_key a = wf_key b
          else if k = 0x5D \/ k = 0x63 then wf_key a < wf_key b
          else if k = 0x5E \/ k = 0x64 then wf_key a > wf_key b
          else if k = 0x5F \/ k = 0x65 then wf_key a <= wf_key b
          else if k = 0x60 \/ k = 0x66 then wf_key a >= wf_key b
          else F)`;;

let wfcvt = new_definition
 `wfcvt k (a:M word) : N word =
    if 0xA8 <= k /\ k <= 0xAB \/ 0xAE <= k /\ k <= 0xB1 then iword (wf_trunc a)
    else if 256 <= k /\ k <= 263 then
      (if wf_nan a then word 0
       else iword (max (wf_tlo k) (min (wf_thi k) (wf_trunc a))))
    else if k = 0xB7 then wf_of_int (ival a < &0) (num_of_int (abs (ival a)))
    else if k = 0xB8 then wf_of_int F (val a)
    else (@f:num->M word->N word. T) k a`;;

let wftrap = new_definition
 `wftrap k (a:M word) <=>
    (0xA8 <= k /\ k <= 0xAB \/ 0xAE <= k /\ k <= 0xB1) /\
    (wf_nan a \/ wf_inf a \/ ~(wf_tlo k <= wf_trunc a /\ wf_trunc a <= wf_thi k))`;;

(* Integer division truncating toward zero, as WASM div_s / rem_s.        *)
let wtdiv = new_definition
 `wtdiv (x:int) (y:int) =
    if (x < &0 <=> y < &0) then abs x div abs y else --(abs x div abs y)`;;

let wbinop_sem = define
 `(wbinop_sem Badd (a:N word) b = word_add a b) /\
  (wbinop_sem Bsub a b = word_sub a b) /\
  (wbinop_sem Bmul a b = word_mul a b) /\
  (wbinop_sem Band a b = word_and a b) /\
  (wbinop_sem Bor a b = word_or a b) /\
  (wbinop_sem Bxor a b = word_xor a b) /\
  (wbinop_sem Bshl a b = word_shl a (val b MOD dimindex(:N))) /\
  (wbinop_sem Bshr_s a b = word_ishr a (val b MOD dimindex(:N))) /\
  (wbinop_sem Bshr_u a b = word_ushr a (val b MOD dimindex(:N))) /\
  (wbinop_sem Brotl a b = word_rol a (val b MOD dimindex(:N))) /\
  (wbinop_sem Brotr a b = word_ror a (val b MOD dimindex(:N))) /\
  (wbinop_sem Bdiv_u a b = word_udiv a b) /\
  (wbinop_sem Brem_u a b = word_umod a b) /\
  (wbinop_sem Bdiv_s a b = iword (wtdiv (ival a) (ival b))) /\
  (wbinop_sem Brem_s a b = iword (ival a - ival b * wtdiv (ival a) (ival b)))`;;

(* Integer traps: division or remainder by zero, and signed overflow of    *)
(* div_s (INT_MIN / -1). rem_s INT_MIN (-1) is 0 and does not trap.        *)
let wbinop_trap = define
 `(wbinop_trap Badd (a:N word) (b:N word) <=> F) /\
  (wbinop_trap Bsub a b <=> F) /\
  (wbinop_trap Bmul a b <=> F) /\
  (wbinop_trap Band a b <=> F) /\
  (wbinop_trap Bor a b <=> F) /\
  (wbinop_trap Bxor a b <=> F) /\
  (wbinop_trap Bshl a b <=> F) /\
  (wbinop_trap Bshr_s a b <=> F) /\
  (wbinop_trap Bshr_u a b <=> F) /\
  (wbinop_trap Brotl a b <=> F) /\
  (wbinop_trap Brotr a b <=> F) /\
  (wbinop_trap Bdiv_u a b <=> b = word 0) /\
  (wbinop_trap Brem_u a b <=> b = word 0) /\
  (wbinop_trap Brem_s a b <=> b = word 0) /\
  (wbinop_trap Bdiv_s a b <=>
     b = word 0 \/
     a = word (2 EXP (dimindex(:N) - 1)) /\ b = word_neg (word 1))`;;

let wunop_sem = define
 `(wunop_sem Uclz (a:N word) = (word (word_clz a):N word)) /\
  (wunop_sem Uctz a = word (word_ctz a)) /\
  (wunop_sem Upopcnt a = word (word_popcount a))`;;

let wrelop_sem = define
 `(wrelop_sem Req (a:N word) b <=> a = b) /\
  (wrelop_sem Rne a b <=> ~(a = b)) /\
  (wrelop_sem Rlt_s a b <=> ival a < ival b) /\
  (wrelop_sem Rlt_u a b <=> val a < val b) /\
  (wrelop_sem Rgt_s a b <=> ival a > ival b) /\
  (wrelop_sem Rgt_u a b <=> val a > val b) /\
  (wrelop_sem Rle_s a b <=> ival a <= ival b) /\
  (wrelop_sem Rle_u a b <=> val a <= val b) /\
  (wrelop_sem Rge_s a b <=> ival a >= ival b) /\
  (wrelop_sem Rge_u a b <=> val a >= val b)`;;

(* ------------------------------------------------------------------------- *)
(* Machine state.                                                            *)
(*   wpc      byte offset into wcode                                        *)
(*   wcode    the function body bytes (never written)                       *)
(*   wstack   operand stack, head = top                                     *)
(*   wlocals  locals (params first, then declared locals)                   *)
(*   wlabels  label stack, head = innermost: (arity, continuation, height)  *)
(*   warity   number of function results                                    *)
(*   wmem     linear memory, addressed by zero-extended effective address  *)
(*   wmemsize current memory size in bytes                                  *)
(*   wglobals global variables (mutability is a validation matter)          *)
(*   wstatus  WRunning / WTrapped / WDone                                   *)
(* ------------------------------------------------------------------------- *)

let wasmstate_INDUCT,wasmstate_RECURSION,wasmstate_COMPONENTS =
  define_auto_record_type
   "wasmstate =
     { wpc: int64;
       wcode: byte list;
       wstack: wval list;
       wlocals: num -> wval;
       wlabels: (num#num#num) list;
       warity: num;
       wmem: int64 -> byte;
       wmemsize: num;
       wglobals: num -> wval;
       wstatus: wstat
     }";;

let wlocal = define `wlocal n = wlocals :> element n`;;

let wglobal = define `wglobal n = wglobals :> element n`;;

add_component_alias_thms [wlocal; wglobal];;

(* ------------------------------------------------------------------------- *)
(* Small list/option helpers (structural, so they evaluate by rewriting).   *)
(* ------------------------------------------------------------------------- *)

let wobind = define
 `(wobind (NONE:A option) (f:A->B option) = NONE) /\
  (wobind (SOME x) f = f x)`;;

let whd = define
 `(whd ([]:A list) = NONE) /\
  (whd (CONS h t) = SOME h)`;;

let wdrop = define
 `(wdrop n ([]:A list) = []) /\
  (wdrop n (CONS h t) = if n = 0 then CONS h t else wdrop (n - 1) t)`;;

let wtake = define
 `(wtake n ([]:A list) = []) /\
  (wtake n (CONS h t) = if n = 0 then [] else CONS h (wtake (n - 1) t))`;;

(* Typed pops: continuation k receives the popped value and the rest;      *)
(* an empty stack or a value of the wrong type has no successor (stuck).   *)

let wpop = define
 `(wpop ([]:wval list) (k:wval->wval list->B option) = NONE) /\
  (wpop (CONS v r) k = k v r)`;;

let wpop_i32 = define
 `(wpop_i32 ([]:wval list) (k:int32->wval list->B option) = NONE) /\
  (wpop_i32 (CONS (I32 w) r) k = k w r) /\
  (wpop_i32 (CONS (I64 d) r) k = NONE) /\
  (wpop_i32 (CONS (F32 e) r) k = NONE) /\
  (wpop_i32 (CONS (F64 g) r) k = NONE)`;;

let wpop_i64 = define
 `(wpop_i64 ([]:wval list) (k:int64->wval list->B option) = NONE) /\
  (wpop_i64 (CONS (I64 w) r) k = k w r) /\
  (wpop_i64 (CONS (I32 d) r) k = NONE) /\
  (wpop_i64 (CONS (F32 e) r) k = NONE) /\
  (wpop_i64 (CONS (F64 g) r) k = NONE)`;;

let wpop_f32 = define
 `(wpop_f32 ([]:wval list) (k:int32->wval list->B option) = NONE) /\
  (wpop_f32 (CONS (F32 w) r) k = k w r) /\
  (wpop_f32 (CONS (I32 d) r) k = NONE) /\
  (wpop_f32 (CONS (I64 e) r) k = NONE) /\
  (wpop_f32 (CONS (F64 g) r) k = NONE)`;;

let wpop_f64 = define
 `(wpop_f64 ([]:wval list) (k:int64->wval list->B option) = NONE) /\
  (wpop_f64 (CONS (F64 w) r) k = k w r) /\
  (wpop_f64 (CONS (I32 d) r) k = NONE) /\
  (wpop_f64 (CONS (I64 e) r) k = NONE) /\
  (wpop_f64 (CONS (F32 g) r) k = NONE)`;;

(* ------------------------------------------------------------------------- *)
(* Execution of one decoded instruction. pc = its offset, npc = next offset.*)
(* Result NONE = no successor (only for ill-typed / invalid code).          *)
(* ------------------------------------------------------------------------- *)

let wasm_return = new_definition
 `wasm_return (stk:wval list) (s:wasmstate) =
    SOME (write wstatus WDone (write wstack (wtake (read warity s) stk) s))`;;

(* br l: pops l+1 labels, keeps the label arity many top values on top of  *)
(* the stack height recorded at label entry, jumps to the continuation.   *)
(* l = number of labels means the implicit function label: a return.      *)
let wasm_branch = new_definition
 `wasm_branch l (stk:wval list) (s:wasmstate) =
    if l < LENGTH (read wlabels s) then
      SOME (write wpc (word (FST (SND (EL l (read wlabels s)))))
           (write wlabels (wdrop (l + 1) (read wlabels s))
           (write wstack
              (APPEND (wtake (FST (EL l (read wlabels s))) stk)
                      (wdrop (LENGTH stk - SND (SND (EL l (read wlabels s))))
                             stk)) s)))
    else if l = LENGTH (read wlabels s) then wasm_return stk s
    else NONE`;;

(* new_recursive_definition: define would take minutes on 57 clauses *)
let wasm_exec = new_recursive_definition winstr_RECURSION
 `(wasm_exec Wunreachable pc npc s = SOME (write wstatus WTrapped s)) /\
  (wasm_exec Wnop pc npc s = SOME (write wpc (word npc) s)) /\
  (wasm_exec (Wblock a e) pc npc s =
     SOME (write wpc (word npc)
          (write wlabels (CONS (a,e,LENGTH (read wstack s)) (read wlabels s))
            s))) /\
  (wasm_exec Wloop pc npc s =
     SOME (write wpc (word npc)
          (write wlabels (CONS (0,pc,LENGTH (read wstack s)) (read wlabels s))
            s))) /\
  (wasm_exec Wend pc npc s =
     if read wlabels s = [] then wasm_return (read wstack s) s
     else SOME (write wpc (word npc) (write wlabels (TL (read wlabels s)) s))) /\
  (wasm_exec (Wbr l) pc npc s = wasm_branch l (read wstack s) s) /\
  (wasm_exec (Wbr_if l) pc npc s =
     wpop_i32 (read wstack s) (\c r.
       if c = word 0 then SOME (write wpc (word npc) (write wstack r s))
       else wasm_branch l r s)) /\
  (wasm_exec (Wif ar e1 e2) pc npc s =
     wpop_i32 (read wstack s) (\c r.
       SOME (write wpc (word (if c = word 0 then e1 else npc))
            (write wlabels (CONS (ar,e2,LENGTH r) (read wlabels s))
            (write wstack r s))))) /\
  (wasm_exec Welse pc npc s = wasm_branch 0 (read wstack s) s) /\
  (wasm_exec (Wbr_table ls dflt) pc npc s =
     wpop_i32 (read wstack s) (\i r.
       wasm_branch (if val i < LENGTH ls then EL (val i) ls else dflt) r s)) /\
  (wasm_exec Wreturn pc npc s = wasm_return (read wstack s) s) /\
  (wasm_exec Wdrop pc npc s =
     wpop (read wstack s) (\v r.
       SOME (write wpc (word npc) (write wstack r s)))) /\
  (wasm_exec Wselect pc npc s =
     wpop_i32 (read wstack s) (\c r. wpop r (\v2 r. wpop r (\v1 r.
       SOME (write wpc (word npc)
            (write wstack (CONS (if c = word 0 then v2 else v1) r) s)))))) /\
  (wasm_exec (Wlocal_get n) pc npc s =
     SOME (write wpc (word npc)
          (write wstack (CONS (read (wlocal n) s) (read wstack s)) s))) /\
  (wasm_exec (Wlocal_set n) pc npc s =
     wpop (read wstack s) (\v r.
       SOME (write wpc (word npc) (write (wlocal n) v (write wstack r s))))) /\
  (wasm_exec (Wlocal_tee n) pc npc s =
     wpop (read wstack s) (\v r.
       SOME (write wpc (word npc) (write (wlocal n) v s)))) /\
  (wasm_exec (Wglobal_get n) pc npc s =
     SOME (write wpc (word npc)
          (write wstack (CONS (read (wglobal n) s) (read wstack s)) s))) /\
  (wasm_exec (Wglobal_set n) pc npc s =
     wpop (read wstack s) (\v r.
       SOME (write wpc (word npc) (write (wglobal n) v (write wstack r s))))) /\
  (wasm_exec Wmemory_size pc npc s =
     SOME (write wpc (word npc)
          (write wstack (CONS (I32 (word (read wmemsize s DIV 65536)))
                              (read wstack s)) s))) /\
  (wasm_exec (Wi32_const c) pc npc s =
     SOME (write wpc (word npc) (write wstack (CONS (I32 c) (read wstack s)) s))) /\
  (wasm_exec (Wi64_const d) pc npc s =
     SOME (write wpc (word npc) (write wstack (CONS (I64 d) (read wstack s)) s))) /\
  (wasm_exec Wi32_eqz pc npc s =
     wpop_i32 (read wstack s) (\a r.
       SOME (write wpc (word npc)
            (write wstack (CONS (I32 (word (bitval (a = word 0)))) r) s)))) /\
  (wasm_exec (Wi32_rel rop) pc npc s =
     wpop_i32 (read wstack s) (\b r. wpop_i32 r (\a r.
       SOME (write wpc (word npc)
            (write wstack (CONS (I32 (word (bitval (wrelop_sem rop a b)))) r)
               s))))) /\
  (wasm_exec (Wi32_bin bop) pc npc s =
     wpop_i32 (read wstack s) (\b r. wpop_i32 r (\a r.
       if wbinop_trap bop a b then SOME (write wstatus WTrapped s) else
       SOME (write wpc (word npc)
            (write wstack (CONS (I32 (wbinop_sem bop a b)) r) s))))) /\
  (wasm_exec Wi64_eqz pc npc s =
     wpop_i64 (read wstack s) (\a r.
       SOME (write wpc (word npc)
            (write wstack (CONS (I32 (word (bitval (a = word 0)))) r) s)))) /\
  (wasm_exec (Wi64_rel rop) pc npc s =
     wpop_i64 (read wstack s) (\b r. wpop_i64 r (\a r.
       SOME (write wpc (word npc)
            (write wstack (CONS (I32 (word (bitval (wrelop_sem rop a b)))) r)
               s))))) /\
  (wasm_exec (Wi64_bin bop) pc npc s =
     wpop_i64 (read wstack s) (\b r. wpop_i64 r (\a r.
       if wbinop_trap bop a b then SOME (write wstatus WTrapped s) else
       SOME (write wpc (word npc)
            (write wstack (CONS (I64 (wbinop_sem bop a b)) r) s))))) /\
  (wasm_exec (Wi32_un uop) pc npc s =
     wpop_i32 (read wstack s) (\a r.
       SOME (write wpc (word npc)
            (write wstack (CONS (I32 (wunop_sem uop a)) r) s)))) /\
  (wasm_exec (Wi64_un uop) pc npc s =
     wpop_i64 (read wstack s) (\a r.
       SOME (write wpc (word npc)
            (write wstack (CONS (I64 (wunop_sem uop a)) r) s)))) /\
  (wasm_exec Wi32_wrap_i64 pc npc s =
     wpop_i64 (read wstack s) (\a r.
       SOME (write wpc (word npc)
            (write wstack (CONS (I32 (word_zx a)) r) s)))) /\
  (wasm_exec Wi64_extend_i32_s pc npc s =
     wpop_i32 (read wstack s) (\a r.
       SOME (write wpc (word npc)
            (write wstack (CONS (I64 (word_sx a)) r) s)))) /\
  (wasm_exec Wi64_extend_i32_u pc npc s =
     wpop_i32 (read wstack s) (\a r.
       SOME (write wpc (word npc)
            (write wstack (CONS (I64 (word_zx a)) r) s)))) /\
  (wasm_exec (Wi32_load off) pc npc s =
     wpop_i32 (read wstack s) (\a r.
       if val a + off + 4 <= read wmemsize s then
         SOME (write wpc (word npc)
              (write wstack
                 (CONS (I32 (read (wmem :> bytes32 (word (val a + off))) s)) r)
                 s))
       else SOME (write wstatus WTrapped s))) /\
  (wasm_exec (Wi32_load8_u off) pc npc s =
     wpop_i32 (read wstack s) (\a r.
       if val a + off + 1 <= read wmemsize s then
         SOME (write wpc (word npc)
              (write wstack
                 (CONS (I32 (word_zx (read (wmem :> bytes8 (word (val a + off)))
                                       s))) r)
                 s))
       else SOME (write wstatus WTrapped s))) /\
  (wasm_exec (Wi32_store off) pc npc s =
     wpop_i32 (read wstack s) (\v r. wpop_i32 r (\a r.
       if val a + off + 4 <= read wmemsize s then
         SOME (write wpc (word npc) (write wstack r
              (write (wmem :> bytes32 (word (val a + off))) v s)))
       else SOME (write wstatus WTrapped s)))) /\
  (wasm_exec (Wi32_store8 off) pc npc s =
     wpop_i32 (read wstack s) (\v r. wpop_i32 r (\a r.
       if val a + off + 1 <= read wmemsize s then
         SOME (write wpc (word npc) (write wstack r
              (write (wmem :> bytes8 (word (val a + off))) (word_zx v) s)))
       else SOME (write wstatus WTrapped s)))) /\
  (wasm_exec (Wi64_load off) pc npc s =
     wpop_i32 (read wstack s) (\a r.
       if val a + off + 8 <= read wmemsize s then
         SOME (write wpc (word npc)
              (write wstack
                 (CONS (I64 ((read (wmem :> bytes64 (word (val a + off)))
                                       s))) r)
                 s))
       else SOME (write wstatus WTrapped s))) /\
  (wasm_exec (Wi32_load8_s off) pc npc s =
     wpop_i32 (read wstack s) (\a r.
       if val a + off + 1 <= read wmemsize s then
         SOME (write wpc (word npc)
              (write wstack
                 (CONS (I32 (word_sx (read (wmem :> bytes8 (word (val a + off)))
                                       s))) r)
                 s))
       else SOME (write wstatus WTrapped s))) /\
  (wasm_exec (Wi32_load16_s off) pc npc s =
     wpop_i32 (read wstack s) (\a r.
       if val a + off + 2 <= read wmemsize s then
         SOME (write wpc (word npc)
              (write wstack
                 (CONS (I32 (word_sx (read (wmem :> bytes16 (word (val a + off)))
                                       s))) r)
                 s))
       else SOME (write wstatus WTrapped s))) /\
  (wasm_exec (Wi32_load16_u off) pc npc s =
     wpop_i32 (read wstack s) (\a r.
       if val a + off + 2 <= read wmemsize s then
         SOME (write wpc (word npc)
              (write wstack
                 (CONS (I32 (word_zx (read (wmem :> bytes16 (word (val a + off)))
                                       s))) r)
                 s))
       else SOME (write wstatus WTrapped s))) /\
  (wasm_exec (Wi64_load8_s off) pc npc s =
     wpop_i32 (read wstack s) (\a r.
       if val a + off + 1 <= read wmemsize s then
         SOME (write wpc (word npc)
              (write wstack
                 (CONS (I64 (word_sx (read (wmem :> bytes8 (word (val a + off)))
                                       s))) r)
                 s))
       else SOME (write wstatus WTrapped s))) /\
  (wasm_exec (Wi64_load8_u off) pc npc s =
     wpop_i32 (read wstack s) (\a r.
       if val a + off + 1 <= read wmemsize s then
         SOME (write wpc (word npc)
              (write wstack
                 (CONS (I64 (word_zx (read (wmem :> bytes8 (word (val a + off)))
                                       s))) r)
                 s))
       else SOME (write wstatus WTrapped s))) /\
  (wasm_exec (Wi64_load16_s off) pc npc s =
     wpop_i32 (read wstack s) (\a r.
       if val a + off + 2 <= read wmemsize s then
         SOME (write wpc (word npc)
              (write wstack
                 (CONS (I64 (word_sx (read (wmem :> bytes16 (word (val a + off)))
                                       s))) r)
                 s))
       else SOME (write wstatus WTrapped s))) /\
  (wasm_exec (Wi64_load16_u off) pc npc s =
     wpop_i32 (read wstack s) (\a r.
       if val a + off + 2 <= read wmemsize s then
         SOME (write wpc (word npc)
              (write wstack
                 (CONS (I64 (word_zx (read (wmem :> bytes16 (word (val a + off)))
                                       s))) r)
                 s))
       else SOME (write wstatus WTrapped s))) /\
  (wasm_exec (Wi64_load32_s off) pc npc s =
     wpop_i32 (read wstack s) (\a r.
       if val a + off + 4 <= read wmemsize s then
         SOME (write wpc (word npc)
              (write wstack
                 (CONS (I64 (word_sx (read (wmem :> bytes32 (word (val a + off)))
                                       s))) r)
                 s))
       else SOME (write wstatus WTrapped s))) /\
  (wasm_exec (Wi64_load32_u off) pc npc s =
     wpop_i32 (read wstack s) (\a r.
       if val a + off + 4 <= read wmemsize s then
         SOME (write wpc (word npc)
              (write wstack
                 (CONS (I64 (word_zx (read (wmem :> bytes32 (word (val a + off)))
                                       s))) r)
                 s))
       else SOME (write wstatus WTrapped s))) /\
  (wasm_exec (Wi64_store off) pc npc s =
     wpop_i64 (read wstack s) (\v r. wpop_i32 r (\a r.
       if val a + off + 8 <= read wmemsize s then
         SOME (write wpc (word npc) (write wstack r
              (write (wmem :> bytes64 (word (val a + off))) (v) s)))
       else SOME (write wstatus WTrapped s)))) /\
  (wasm_exec (Wi32_store16 off) pc npc s =
     wpop_i32 (read wstack s) (\v r. wpop_i32 r (\a r.
       if val a + off + 2 <= read wmemsize s then
         SOME (write wpc (word npc) (write wstack r
              (write (wmem :> bytes16 (word (val a + off))) (word_zx v) s)))
       else SOME (write wstatus WTrapped s)))) /\
  (wasm_exec (Wi64_store8 off) pc npc s =
     wpop_i64 (read wstack s) (\v r. wpop_i32 r (\a r.
       if val a + off + 1 <= read wmemsize s then
         SOME (write wpc (word npc) (write wstack r
              (write (wmem :> bytes8 (word (val a + off))) (word_zx v) s)))
       else SOME (write wstatus WTrapped s)))) /\
  (wasm_exec (Wi64_store16 off) pc npc s =
     wpop_i64 (read wstack s) (\v r. wpop_i32 r (\a r.
       if val a + off + 2 <= read wmemsize s then
         SOME (write wpc (word npc) (write wstack r
              (write (wmem :> bytes16 (word (val a + off))) (word_zx v) s)))
       else SOME (write wstatus WTrapped s)))) /\
  (wasm_exec (Wi64_store32 off) pc npc s =
     wpop_i64 (read wstack s) (\v r. wpop_i32 r (\a r.
       if val a + off + 4 <= read wmemsize s then
         SOME (write wpc (word npc) (write wstack r
              (write (wmem :> bytes32 (word (val a + off))) (word_zx v) s)))
       else SOME (write wstatus WTrapped s)))) /\
  (wasm_exec Wi32_extend8_s pc npc s =
     wpop_i32 (read wstack s) (\a r.
       SOME (write wpc (word npc)
            (write wstack (CONS (I32 (word_sx (word_zx a:byte))) r) s)))) /\
  (wasm_exec Wi32_extend16_s pc npc s =
     wpop_i32 (read wstack s) (\a r.
       SOME (write wpc (word npc)
            (write wstack (CONS (I32 (word_sx (word_zx a:int16))) r) s)))) /\
  (wasm_exec Wi64_extend8_s pc npc s =
     wpop_i64 (read wstack s) (\a r.
       SOME (write wpc (word npc)
            (write wstack (CONS (I64 (word_sx (word_zx a:byte))) r) s)))) /\
  (wasm_exec Wi64_extend16_s pc npc s =
     wpop_i64 (read wstack s) (\a r.
       SOME (write wpc (word npc)
            (write wstack (CONS (I64 (word_sx (word_zx a:int16))) r) s)))) /\
  (wasm_exec Wi64_extend32_s pc npc s =
     wpop_i64 (read wstack s) (\a r.
       SOME (write wpc (word npc)
            (write wstack (CONS (I64 (word_sx (word_zx a:int32))) r) s)))) /\
  (wasm_exec (Wf32_const c) pc npc s =
     SOME (write wpc (word npc) (write wstack (CONS (F32 c) (read wstack s)) s))) /\
  (wasm_exec (Wf64_const d) pc npc s =
     SOME (write wpc (word npc) (write wstack (CONS (F64 d) (read wstack s)) s))) /\
  (wasm_exec (Wf32_load off) pc npc s =
     wpop_i32 (read wstack s) (\a r.
       if val a + off + 4 <= read wmemsize s then
         SOME (write wpc (word npc)
              (write wstack
                 (CONS (F32 (read (wmem :> bytes32 (word (val a + off))) s)) r)
                 s))
       else SOME (write wstatus WTrapped s))) /\
  (wasm_exec (Wf64_load off) pc npc s =
     wpop_i32 (read wstack s) (\a r.
       if val a + off + 8 <= read wmemsize s then
         SOME (write wpc (word npc)
              (write wstack
                 (CONS (F64 (read (wmem :> bytes64 (word (val a + off))) s)) r)
                 s))
       else SOME (write wstatus WTrapped s))) /\
  (wasm_exec (Wf32_store off) pc npc s =
     wpop_f32 (read wstack s) (\v r. wpop_i32 r (\a r.
       if val a + off + 4 <= read wmemsize s then
         SOME (write wpc (word npc) (write wstack r
              (write (wmem :> bytes32 (word (val a + off))) v s)))
       else SOME (write wstatus WTrapped s)))) /\
  (wasm_exec (Wf64_store off) pc npc s =
     wpop_f64 (read wstack s) (\v r. wpop_i32 r (\a r.
       if val a + off + 8 <= read wmemsize s then
         SOME (write wpc (word npc) (write wstack r
              (write (wmem :> bytes64 (word (val a + off))) v s)))
       else SOME (write wstatus WTrapped s)))) /\
  (wasm_exec Wi32_reinterpret_f32 pc npc s =
     wpop_f32 (read wstack s) (\a r.
       SOME (write wpc (word npc) (write wstack (CONS (I32 a) r) s)))) /\
  (wasm_exec Wi64_reinterpret_f64 pc npc s =
     wpop_f64 (read wstack s) (\a r.
       SOME (write wpc (word npc) (write wstack (CONS (I64 a) r) s)))) /\
  (wasm_exec Wf32_reinterpret_i32 pc npc s =
     wpop_i32 (read wstack s) (\a r.
       SOME (write wpc (word npc) (write wstack (CONS (F32 a) r) s)))) /\
  (wasm_exec Wf64_reinterpret_i64 pc npc s =
     wpop_i64 (read wstack s) (\a r.
       SOME (write wpc (word npc) (write wstack (CONS (F64 a) r) s)))) /\
  (wasm_exec Wmemory_fill pc npc s =
     wpop_i32 (read wstack s) (\n r. wpop_i32 r (\v r. wpop_i32 r (\d r.
       if val d + val n <= read wmemsize s then
         SOME (write wpc (word npc) (write wstack r
              (write wmem (\x:int64. if val d <= val x /\ val x < val d + val n
                                      then (word_zx v:byte)
                                      else read wmem s x) s)))
       else SOME (write wstatus WTrapped s))))) /\
  (wasm_exec Wmemory_copy pc npc s =
     wpop_i32 (read wstack s) (\n r. wpop_i32 r (\a r. wpop_i32 r (\d r.
       if val a + val n <= read wmemsize s /\ val d + val n <= read wmemsize s
       then
         SOME (write wpc (word npc) (write wstack r
              (write wmem (\x:int64. if val d <= val x /\ val x < val d + val n
                                      then read wmem s (word (val a + (val x - val d)))
                                      else read wmem s x) s)))
       else SOME (write wstatus WTrapped s))))) /\
  (wasm_exec Wmemory_grow pc npc s = NONE) /\
  (wasm_exec (Wcall f) pc npc s = NONE) /\
  (wasm_exec (Wcall_indirect t tb) pc npc s = NONE) /\
  (wasm_exec (Wf32_rel k) pc npc s =
     wpop_f32 (read wstack s) (\b r. wpop_f32 r (\a r.
       SOME (write wpc (word npc)
            (write wstack (CONS (I32 (word (bitval (wfrel k a b)))) r) s))))) /\
  (wasm_exec (Wf64_rel k) pc npc s =
     wpop_f64 (read wstack s) (\b r. wpop_f64 r (\a r.
       SOME (write wpc (word npc)
            (write wstack (CONS (I32 (word (bitval (wfrel k a b)))) r) s))))) /\
  (wasm_exec (Wf32_un k) pc npc s =
     wpop_f32 (read wstack s) (\a r.
       SOME (write wpc (word npc) (write wstack (CONS (F32 (wfun k a)) r) s)))) /\
  (wasm_exec (Wf64_un k) pc npc s =
     wpop_f64 (read wstack s) (\a r.
       SOME (write wpc (word npc) (write wstack (CONS (F64 (wfun k a)) r) s)))) /\
  (wasm_exec (Wf32_bin k) pc npc s =
     wpop_f32 (read wstack s) (\b r. wpop_f32 r (\a r.
       SOME (write wpc (word npc) (write wstack (CONS (F32 (wfbin k a b)) r) s))))) /\
  (wasm_exec (Wf64_bin k) pc npc s =
     wpop_f64 (read wstack s) (\b r. wpop_f64 r (\a r.
       SOME (write wpc (word npc) (write wstack (CONS (F64 (wfbin k a b)) r) s))))) /\
  (wasm_exec Wf32_abs pc npc s =
     wpop_f32 (read wstack s) (\a r.
       SOME (write wpc (word npc)
            (write wstack (CONS (F32 (word_and a (word 2147483647))) r) s)))) /\
  (wasm_exec Wf32_neg pc npc s =
     wpop_f32 (read wstack s) (\a r.
       SOME (write wpc (word npc)
            (write wstack (CONS (F32 (word_xor a (word 2147483648))) r) s)))) /\
  (wasm_exec Wf32_copysign pc npc s =
     wpop_f32 (read wstack s) (\b r. wpop_f32 r (\a r.
       SOME (write wpc (word npc)
            (write wstack (CONS (F32 (word_or (word_and a (word 2147483647))
                                              (word_and b (word 2147483648)))) r)
               s))))) /\
  (wasm_exec Wf64_abs pc npc s =
     wpop_f64 (read wstack s) (\a r.
       SOME (write wpc (word npc)
            (write wstack (CONS (F64 (word_and a (word 9223372036854775807))) r)
               s)))) /\
  (wasm_exec Wf64_neg pc npc s =
     wpop_f64 (read wstack s) (\a r.
       SOME (write wpc (word npc)
            (write wstack (CONS (F64 (word_xor a (word 9223372036854775808))) r)
               s)))) /\
  (wasm_exec Wf64_copysign pc npc s =
     wpop_f64 (read wstack s) (\b r. wpop_f64 r (\a r.
       SOME (write wpc (word npc)
            (write wstack
               (CONS (F64 (word_or (word_and a (word 9223372036854775807))
                                   (word_and b (word 9223372036854775808)))) r)
               s))))) /\
  (wasm_exec (Wi32_trunc_f32 k) pc npc s =
     wpop_f32 (read wstack s) (\a r.
       if wftrap k a then SOME (write wstatus WTrapped s) else
       SOME (write wpc (word npc) (write wstack (CONS (I32 (wfcvt k a)) r) s)))) /\
  (wasm_exec (Wi32_trunc_f64 k) pc npc s =
     wpop_f64 (read wstack s) (\a r.
       if wftrap k a then SOME (write wstatus WTrapped s) else
       SOME (write wpc (word npc) (write wstack (CONS (I32 (wfcvt k a)) r) s)))) /\
  (wasm_exec (Wi64_trunc_f32 k) pc npc s =
     wpop_f32 (read wstack s) (\a r.
       if wftrap k a then SOME (write wstatus WTrapped s) else
       SOME (write wpc (word npc) (write wstack (CONS (I64 (wfcvt k a)) r) s)))) /\
  (wasm_exec (Wi64_trunc_f64 k) pc npc s =
     wpop_f64 (read wstack s) (\a r.
       if wftrap k a then SOME (write wstatus WTrapped s) else
       SOME (write wpc (word npc) (write wstack (CONS (I64 (wfcvt k a)) r) s)))) /\
  (wasm_exec (Wi32_trunc_sat_f32 k) pc npc s =
     wpop_f32 (read wstack s) (\a r.
       SOME (write wpc (word npc) (write wstack (CONS (I32 (wfcvt k a)) r) s)))) /\
  (wasm_exec (Wi32_trunc_sat_f64 k) pc npc s =
     wpop_f64 (read wstack s) (\a r.
       SOME (write wpc (word npc) (write wstack (CONS (I32 (wfcvt k a)) r) s)))) /\
  (wasm_exec (Wi64_trunc_sat_f32 k) pc npc s =
     wpop_f32 (read wstack s) (\a r.
       SOME (write wpc (word npc) (write wstack (CONS (I64 (wfcvt k a)) r) s)))) /\
  (wasm_exec (Wi64_trunc_sat_f64 k) pc npc s =
     wpop_f64 (read wstack s) (\a r.
       SOME (write wpc (word npc) (write wstack (CONS (I64 (wfcvt k a)) r) s)))) /\
  (wasm_exec (Wf32_convert_i32 k) pc npc s =
     wpop_i32 (read wstack s) (\a r.
       SOME (write wpc (word npc) (write wstack (CONS (F32 (wfcvt k a)) r) s)))) /\
  (wasm_exec (Wf32_convert_i64 k) pc npc s =
     wpop_i64 (read wstack s) (\a r.
       SOME (write wpc (word npc) (write wstack (CONS (F32 (wfcvt k a)) r) s)))) /\
  (wasm_exec (Wf64_convert_i32 k) pc npc s =
     wpop_i32 (read wstack s) (\a r.
       SOME (write wpc (word npc) (write wstack (CONS (F64 (wfcvt k a)) r) s)))) /\
  (wasm_exec (Wf64_convert_i64 k) pc npc s =
     wpop_i64 (read wstack s) (\a r.
       SOME (write wpc (word npc) (write wstack (CONS (F64 (wfcvt k a)) r) s)))) /\
  (wasm_exec Wf32_demote_f64 pc npc s =
     wpop_f64 (read wstack s) (\a r.
       SOME (write wpc (word npc) (write wstack (CONS (F32 (wfcvt 182 a)) r) s)))) /\
  (wasm_exec Wf64_promote_f32 pc npc s =
     wpop_f32 (read wstack s) (\a r.
       SOME (write wpc (word npc) (write wstack (CONS (F64 (wfcvt 187 a)) r) s))))`;;

(* ------------------------------------------------------------------------- *)
(* Decoding from bytes.                                                      *)
(* LEB128 is decoded without the spec maximal-length / unused-bit checks    *)
(* (a permissive decoder: it accepts every valid encoding).                 *)
(* ------------------------------------------------------------------------- *)

let wuleb = define
 `(wuleb [] = NONE) /\
  (wuleb (CONS (b:byte) l) =
     if val b < 128 then SOME (val b,1)
     else wobind (wuleb l) (\p. SOME (val b - 128 + 128 * FST p, SND p + 1)))`;;

let wsleb = define
 `(wsleb [] = NONE) /\
  (wsleb (CONS (b:byte) l) =
     if val b < 128
     then SOME ((if val b < 64 then &(val b) else &(val b) - &128):int, 1)
     else wobind (wsleb l)
            (\p. SOME (&(val b - 128) + &128 * FST p, SND p + 1)))`;;

(* a vector of n u32 LEB128 values: (values, byte length) *)
let wulebs = new_recursive_definition num_RECURSION
 `(wulebs 0 (l:byte list) = SOME ([],0)) /\
  (wulebs (SUC n) l =
     wobind (wuleb l) (\p. wobind (wulebs n (wdrop (SND p) l))
       (\q. SOME (CONS (FST p) (FST q), SND p + SND q))))`;;

(* blocktype: 0x40 = empty, 0x7F = i32, 0x7E = i64; returns result arity *)
let wblocktype = new_definition
 `wblocktype (b:byte) =
    if val b = 0x40 then SOME 0
    else if val b = 0x7F \/ val b = 0x7E \/ val b = 0x7D \/ val b = 0x7C
    then SOME 1
    else NONE`;;

(* memarg: align then offset, both u32; returns (offset, byte length) *)
let wmemarg = new_definition
 `wmemarg (l:byte list) =
    wobind (wuleb l) (\p. wobind (wuleb (wdrop (SND p) l))
                       (\q. SOME (FST q, SND p + SND q)))`;;

(* n-byte little-endian immediate (f32.const: 4, f64.const: 8) *)
let wbytes_le = new_recursive_definition num_RECURSION
 `(wbytes_le 0 (l:byte list) = SOME 0) /\
  (wbytes_le (SUC n) l =
     wobind (whd l) (\b. wobind (wbytes_le n (wdrop 1 l))
       (\v. SOME (val b + 256 * v))))`;;

let wrelop_of = new_definition
 `wrelop_of k =
    if k = 0 then Req else if k = 1 then Rne else
    if k = 2 then Rlt_s else if k = 3 then Rlt_u else
    if k = 4 then Rgt_s else if k = 5 then Rgt_u else
    if k = 6 then Rle_s else if k = 7 then Rle_u else
    if k = 8 then Rge_s else Rge_u`;;

(* opcode op (one byte), immediates in l: (instruction, immediate length) *)
let wdecode_op = new_definition
 `wdecode_op op (l:byte list) =
    if op = 0x00 then SOME (Wunreachable,0) else
    if op = 0x01 then SOME (Wnop,0) else
    if op = 0x02 then
      wobind (whd l) (\b. wobind (wblocktype b) (\a. SOME (Wblock a 0,1))) else
    if op = 0x03 then
      wobind (whd l) (\b. wobind (wblocktype b) (\a. SOME (Wloop,1))) else
    if op = 0x04 then
      wobind (whd l) (\b. wobind (wblocktype b) (\a. SOME (Wif a 0 0,1))) else
    if op = 0x05 then SOME (Welse,0) else
    if op = 0x0B then SOME (Wend,0) else
    if op = 0x0C then wobind (wuleb l) (\p. SOME (Wbr (FST p),SND p)) else
    if op = 0x0D then wobind (wuleb l) (\p. SOME (Wbr_if (FST p),SND p)) else
    if op = 0x0E then
      wobind (wuleb l) (\p. wobind (wulebs (FST p) (wdrop (SND p) l)) (\q.
        wobind (wuleb (wdrop (SND p + SND q) l)) (\d.
          SOME (Wbr_table (FST q) (FST d),SND p + SND q + SND d)))) else
    if op = 0x0F then SOME (Wreturn,0) else
    if op = 0x10 then wobind (wuleb l) (\p. SOME (Wcall (FST p),SND p)) else
    if op = 0x11 then
      wobind (wuleb l) (\p. wobind (wuleb (wdrop (SND p) l)) (\q.
        SOME (Wcall_indirect (FST p) (FST q),SND p + SND q))) else
    if op = 0x1A then SOME (Wdrop,0) else
    if op = 0x1B then SOME (Wselect,0) else
    if op = 0x20 then wobind (wuleb l) (\p. SOME (Wlocal_get (FST p),SND p)) else
    if op = 0x21 then wobind (wuleb l) (\p. SOME (Wlocal_set (FST p),SND p)) else
    if op = 0x22 then wobind (wuleb l) (\p. SOME (Wlocal_tee (FST p),SND p)) else
    if op = 0x23 then wobind (wuleb l) (\p. SOME (Wglobal_get (FST p),SND p)) else
    if op = 0x24 then wobind (wuleb l) (\p. SOME (Wglobal_set (FST p),SND p)) else
    if op = 0x28 then wobind (wmemarg l) (\p. SOME (Wi32_load (FST p),SND p)) else
    if op = 0x29 then wobind (wmemarg l) (\p. SOME (Wi64_load (FST p),SND p)) else
    if op = 0x2A then wobind (wmemarg l) (\p. SOME (Wf32_load (FST p),SND p)) else
    if op = 0x2B then wobind (wmemarg l) (\p. SOME (Wf64_load (FST p),SND p)) else
    if op = 0x2C then wobind (wmemarg l) (\p. SOME (Wi32_load8_s (FST p),SND p)) else
    if op = 0x2D then wobind (wmemarg l) (\p. SOME (Wi32_load8_u (FST p),SND p)) else
    if op = 0x2E then wobind (wmemarg l) (\p. SOME (Wi32_load16_s (FST p),SND p)) else
    if op = 0x2F then wobind (wmemarg l) (\p. SOME (Wi32_load16_u (FST p),SND p)) else
    if op = 0x30 then wobind (wmemarg l) (\p. SOME (Wi64_load8_s (FST p),SND p)) else
    if op = 0x31 then wobind (wmemarg l) (\p. SOME (Wi64_load8_u (FST p),SND p)) else
    if op = 0x32 then wobind (wmemarg l) (\p. SOME (Wi64_load16_s (FST p),SND p)) else
    if op = 0x33 then wobind (wmemarg l) (\p. SOME (Wi64_load16_u (FST p),SND p)) else
    if op = 0x34 then wobind (wmemarg l) (\p. SOME (Wi64_load32_s (FST p),SND p)) else
    if op = 0x35 then wobind (wmemarg l) (\p. SOME (Wi64_load32_u (FST p),SND p)) else
    if op = 0x36 then wobind (wmemarg l) (\p. SOME (Wi32_store (FST p),SND p)) else
    if op = 0x37 then wobind (wmemarg l) (\p. SOME (Wi64_store (FST p),SND p)) else
    if op = 0x38 then wobind (wmemarg l) (\p. SOME (Wf32_store (FST p),SND p)) else
    if op = 0x39 then wobind (wmemarg l) (\p. SOME (Wf64_store (FST p),SND p)) else
    if op = 0x3A then wobind (wmemarg l) (\p. SOME (Wi32_store8 (FST p),SND p)) else
    if op = 0x3B then wobind (wmemarg l) (\p. SOME (Wi32_store16 (FST p),SND p)) else
    if op = 0x3C then wobind (wmemarg l) (\p. SOME (Wi64_store8 (FST p),SND p)) else
    if op = 0x3D then wobind (wmemarg l) (\p. SOME (Wi64_store16 (FST p),SND p)) else
    if op = 0x3E then wobind (wmemarg l) (\p. SOME (Wi64_store32 (FST p),SND p)) else
    if op = 0x3F then
      wobind (whd l) (\b. if val b = 0 then SOME (Wmemory_size,1) else NONE) else
    if op = 0x40 then
      wobind (whd l) (\b. if val b = 0 then SOME (Wmemory_grow,1) else NONE) else
    if op = 0x41 then
      wobind (wsleb l) (\p. SOME (Wi32_const (iword (FST p)),SND p)) else
    if op = 0x42 then
      wobind (wsleb l) (\p. SOME (Wi64_const (iword (FST p)),SND p)) else
    if op = 0x43 then
      wobind (wbytes_le 4 l) (\v. SOME (Wf32_const (word v),4)) else
    if op = 0x44 then
      wobind (wbytes_le 8 l) (\v. SOME (Wf64_const (word v),8)) else
    if op = 0x45 then SOME (Wi32_eqz,0) else
    if 0x46 <= op /\ op <= 0x4F then SOME (Wi32_rel (wrelop_of (op - 0x46)),0) else
    if op = 0x50 then SOME (Wi64_eqz,0) else
    if 0x51 <= op /\ op <= 0x5A then SOME (Wi64_rel (wrelop_of (op - 0x51)),0) else
    if 0x5B <= op /\ op <= 0x60 then SOME (Wf32_rel op,0) else
    if 0x61 <= op /\ op <= 0x66 then SOME (Wf64_rel op,0) else
    if op = 0x67 then SOME (Wi32_un Uclz,0) else
    if op = 0x68 then SOME (Wi32_un Uctz,0) else
    if op = 0x69 then SOME (Wi32_un Upopcnt,0) else
    if op = 0x6A then SOME (Wi32_bin Badd,0) else
    if op = 0x6B then SOME (Wi32_bin Bsub,0) else
    if op = 0x6C then SOME (Wi32_bin Bmul,0) else
    if op = 0x6D then SOME (Wi32_bin Bdiv_s,0) else
    if op = 0x6E then SOME (Wi32_bin Bdiv_u,0) else
    if op = 0x6F then SOME (Wi32_bin Brem_s,0) else
    if op = 0x70 then SOME (Wi32_bin Brem_u,0) else
    if op = 0x71 then SOME (Wi32_bin Band,0) else
    if op = 0x72 then SOME (Wi32_bin Bor,0) else
    if op = 0x73 then SOME (Wi32_bin Bxor,0) else
    if op = 0x74 then SOME (Wi32_bin Bshl,0) else
    if op = 0x75 then SOME (Wi32_bin Bshr_s,0) else
    if op = 0x76 then SOME (Wi32_bin Bshr_u,0) else
    if op = 0x77 then SOME (Wi32_bin Brotl,0) else
    if op = 0x78 then SOME (Wi32_bin Brotr,0) else
    if op = 0x79 then SOME (Wi64_un Uclz,0) else
    if op = 0x7A then SOME (Wi64_un Uctz,0) else
    if op = 0x7B then SOME (Wi64_un Upopcnt,0) else
    if op = 0x7C then SOME (Wi64_bin Badd,0) else
    if op = 0x7D then SOME (Wi64_bin Bsub,0) else
    if op = 0x7E then SOME (Wi64_bin Bmul,0) else
    if op = 0x7F then SOME (Wi64_bin Bdiv_s,0) else
    if op = 0x80 then SOME (Wi64_bin Bdiv_u,0) else
    if op = 0x81 then SOME (Wi64_bin Brem_s,0) else
    if op = 0x82 then SOME (Wi64_bin Brem_u,0) else
    if op = 0x83 then SOME (Wi64_bin Band,0) else
    if op = 0x84 then SOME (Wi64_bin Bor,0) else
    if op = 0x85 then SOME (Wi64_bin Bxor,0) else
    if op = 0x86 then SOME (Wi64_bin Bshl,0) else
    if op = 0x87 then SOME (Wi64_bin Bshr_s,0) else
    if op = 0x88 then SOME (Wi64_bin Bshr_u,0) else
    if op = 0x89 then SOME (Wi64_bin Brotl,0) else
    if op = 0x8A then SOME (Wi64_bin Brotr,0) else
    if op = 0x8B then SOME (Wf32_abs,0) else
    if op = 0x8C then SOME (Wf32_neg,0) else
    if 0x8D <= op /\ op <= 0x91 then SOME (Wf32_un op,0) else
    if 0x92 <= op /\ op <= 0x97 then SOME (Wf32_bin op,0) else
    if op = 0x98 then SOME (Wf32_copysign,0) else
    if op = 0x99 then SOME (Wf64_abs,0) else
    if op = 0x9A then SOME (Wf64_neg,0) else
    if 0x9B <= op /\ op <= 0x9F then SOME (Wf64_un op,0) else
    if 0xA0 <= op /\ op <= 0xA5 then SOME (Wf64_bin op,0) else
    if op = 0xA6 then SOME (Wf64_copysign,0) else
    if op = 0xA7 then SOME (Wi32_wrap_i64,0) else
    if op = 0xA8 \/ op = 0xA9 then SOME (Wi32_trunc_f32 op,0) else
    if op = 0xAA \/ op = 0xAB then SOME (Wi32_trunc_f64 op,0) else
    if op = 0xAC then SOME (Wi64_extend_i32_s,0) else
    if op = 0xAD then SOME (Wi64_extend_i32_u,0) else
    if op = 0xAE \/ op = 0xAF then SOME (Wi64_trunc_f32 op,0) else
    if op = 0xB0 \/ op = 0xB1 then SOME (Wi64_trunc_f64 op,0) else
    if op = 0xB2 \/ op = 0xB3 then SOME (Wf32_convert_i32 op,0) else
    if op = 0xB4 \/ op = 0xB5 then SOME (Wf32_convert_i64 op,0) else
    if op = 0xB6 then SOME (Wf32_demote_f64,0) else
    if op = 0xB7 \/ op = 0xB8 then SOME (Wf64_convert_i32 op,0) else
    if op = 0xB9 \/ op = 0xBA then SOME (Wf64_convert_i64 op,0) else
    if op = 0xBB then SOME (Wf64_promote_f32,0) else
    if op = 0xBC then SOME (Wi32_reinterpret_f32,0) else
    if op = 0xBD then SOME (Wi64_reinterpret_f64,0) else
    if op = 0xBE then SOME (Wf32_reinterpret_i32,0) else
    if op = 0xBF then SOME (Wf64_reinterpret_i64,0) else
    if op = 0xC0 then SOME (Wi32_extend8_s,0) else
    if op = 0xC1 then SOME (Wi32_extend16_s,0) else
    if op = 0xC2 then SOME (Wi64_extend8_s,0) else
    if op = 0xC3 then SOME (Wi64_extend16_s,0) else
    if op = 0xC4 then SOME (Wi64_extend32_s,0) else
    if op = 0xFC then
      wobind (wuleb l) (\p.
        if FST p = 10 then
          wobind (whd (wdrop (SND p) l)) (\m1.
          wobind (whd (wdrop (SND p + 1) l)) (\m2.
            if val m1 = 0 /\ val m2 = 0 then SOME (Wmemory_copy,SND p + 2)
            else NONE))
        else if FST p = 11 then
          wobind (whd (wdrop (SND p) l)) (\m.
            if val m = 0 then SOME (Wmemory_fill,SND p + 1) else NONE)
        else if FST p = 0 \/ FST p = 1 then
          SOME (Wi32_trunc_sat_f32 (256 + FST p),SND p)
        else if FST p = 2 \/ FST p = 3 then
          SOME (Wi32_trunc_sat_f64 (256 + FST p),SND p)
        else if FST p = 4 \/ FST p = 5 then
          SOME (Wi64_trunc_sat_f32 (256 + FST p),SND p)
        else if FST p = 6 \/ FST p = 7 then
          SOME (Wi64_trunc_sat_f64 (256 + FST p),SND p)
        else NONE) else
    NONE`;;

(* decode at offset pc ignoring block continuations: (instruction, length) *)
let wdecode_raw = new_definition
 `wdecode_raw (code:byte list) pc =
    wobind (whd (wdrop pc code))
      (\b. wobind (wdecode_op (val b) (TL (wdrop pc code)))
                  (\p. SOME (FST p,SND p + 1)))`;;

(* scan forward from pc at nesting depth d for the matching end; returns  *)
(* the offset just after it. Fuel f bounds the number of instructions.    *)
let wscan = new_recursive_definition num_RECURSION
 `(wscan 0 (code:byte list) pc d = NONE) /\
  (wscan (SUC f) code pc d =
     wobind (whd (wdrop pc code)) (\b. wobind (wdecode_raw code pc) (\p.
       if val b = 0x02 \/ val b = 0x03 \/ val b = 0x04
       then wscan f code (pc + SND p) (d + 1)
       else if val b = 0x0B then
         (if d = 0 then SOME (pc + SND p) else wscan f code (pc + SND p) (d - 1))
       else wscan f code (pc + SND p) d)))`;;

(* for an if: the offset after its else at depth 0, or (no else) the     *)
(* offset of its matching end                                             *)
let welse_scan = new_recursive_definition num_RECURSION
 `(welse_scan 0 (code:byte list) pc d = NONE) /\
  (welse_scan (SUC f) code pc d =
     wobind (whd (wdrop pc code)) (\b. wobind (wdecode_raw code pc) (\p.
       if val b = 0x02 \/ val b = 0x03 \/ val b = 0x04
       then welse_scan f code (pc + SND p) (d + 1)
       else if val b = 0x0B then
         (if d = 0 then SOME pc else welse_scan f code (pc + SND p) (d - 1))
       else if val b = 0x05 /\ d = 0 then SOME (pc + SND p)
       else welse_scan f code (pc + SND p) d)))`;;

let wblock_arity = define
 `(wblock_arity (Wblock a e) = a) /\
  (wblock_arity (Wif ar e1 e2) = ar)`;;

(* full decode: a block gets its continuation (offset after matching end), *)
(* an if its else target and its continuation                             *)
let wasm_decode = new_definition
 `wasm_decode (code:byte list) pc =
    wobind (wdecode_raw code pc) (\p.
      if val (HD (wdrop pc code)) = 0x02 then
        wobind (wscan (LENGTH code) code (pc + SND p) 0)
               (\e. SOME (Wblock (wblock_arity (FST p)) e,SND p))
      else if val (HD (wdrop pc code)) = 0x04 then
        wobind (wscan (LENGTH code) code (pc + SND p) 0) (\e.
        wobind (welse_scan (LENGTH code) code (pc + SND p) 0) (\e1.
          SOME (Wif (wblock_arity (FST p)) e1 e,SND p)))
      else SOME p)`;;

(* ------------------------------------------------------------------------- *)
(* The step relation: fetch at wpc, decode, execute. Only running states   *)
(* step; trapped and done states are final.                                 *)
(* ------------------------------------------------------------------------- *)

let wasm = new_definition
 `wasm s s' <=>
    read wstatus s = WRunning /\
    ?i n. wasm_decode (read wcode s) (val (read wpc s)) = SOME (i,n) /\
          wasm_exec i (val (read wpc s)) (val (read wpc s) + n) s = SOME s'`;;

let WASM_DETERMINISTIC = prove
 (`!s s1 s2. wasm s s1 /\ wasm s s2 ==> s1 = s2`,
  REWRITE_TAC[wasm] THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   `wasm_decode (read wcode s) (val (read wpc s)) = SOME (i,n)`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC o
    check (fun th -> is_conj(concl th) && is_eq(lhand(concl th))))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   `wasm_exec i (val (read wpc s)) (val (read wpc s) + n) s = SOME s1`]) THEN
  ASM_MESON_TAC[option_INJ]);;

let WASM_FINAL = prove
 (`!s s'. ~(read wstatus s = WRunning) ==> ~(wasm s s')`,
  SIMP_TAC[wasm]);;

(* ------------------------------------------------------------------------- *)
(* Traps are explicit: an out-of-bounds access moves to WTrapped and stops. *)
(* ------------------------------------------------------------------------- *)

let WASM_DECODED_STEP = prove
 (`!s s' i n.
     read wstatus s = WRunning /\
     wasm_decode (read wcode s) (val (read wpc s)) = SOME (i,n)
     ==> (wasm s s' <=>
          wasm_exec i (val (read wpc s)) (val (read wpc s) + n) s = SOME s')`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[wasm; option_INJ; PAIR_EQ] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN EXISTS_TAC `i:winstr` THEN EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[]]);;

let WASM_I32_LOAD_TRAP = prove
 (`!s s' a r off n.
     read wstatus s = WRunning /\
     wasm_decode (read wcode s) (val (read wpc s)) = SOME (Wi32_load off,n) /\
     read wstack s = CONS (I32 a) r /\
     read wmemsize s < val a + off + 4
     ==> (wasm s s' <=> s' = write wstatus WTrapped s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `s':wasmstate` o MATCH_MP WASM_DECODED_STEP o
              CONJ (ASSUME `read wstatus s = WRunning`)) THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[wasm_exec; wpop_i32; GSYM NOT_LT; option_INJ] THEN
  MESON_TAC[]);;

let WASM_I32_STORE_TRAP = prove
 (`!s s' v a r off n.
     read wstatus s = WRunning /\
     wasm_decode (read wcode s) (val (read wpc s)) = SOME (Wi32_store off,n) /\
     read wstack s = CONS (I32 v) (CONS (I32 a) r) /\
     read wmemsize s < val a + off + 4
     ==> (wasm s s' <=> s' = write wstatus WTrapped s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `s':wasmstate` o MATCH_MP WASM_DECODED_STEP o
              CONJ (ASSUME `read wstatus s = WRunning`)) THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[wasm_exec; wpop_i32; GSYM NOT_LT; option_INJ] THEN
  MESON_TAC[]);;

let WASM_TRAPPED_FINAL = prove
 (`!s s'. read wstatus s = WTrapped ==> ~(wasm s s')`,
  SIMP_TAC[wasm; distinctness "wstat"]);;

(* ------------------------------------------------------------------------- *)
(* Function entry: the offset after the local-declaration vector.           *)
(* ------------------------------------------------------------------------- *)

let wdecls = new_recursive_definition num_RECURSION
 `(wdecls 0 (code:byte list) pc = SOME pc) /\
  (wdecls (SUC k) code pc =
     wobind (wuleb (wdrop pc code)) (\p. wdecls k code (pc + SND p + 1)))`;;

let wasm_entry = new_definition
 `wasm_entry (code:byte list) = wobind (wuleb code) (\p. wdecls (FST p) code (SND p))`;;

(* ------------------------------------------------------------------------- *)
(* Memory access trace (tooling sprint 2, lane 1, 2026-11-08).               *)
(*                                                                           *)
(* wasm_mem_events s lists the linear-memory accesses of the instruction at  *)
(* the pc of s, in program order, as (is_write, address, width):            *)
(*   every load and store width: one event at the effective address        *)
(*     (zero-extended i32 address operand + memarg offset; the address      *)
(*     operand is the top of stack for loads, the second entry for stores);  *)
(*   memory.fill: one write range (d, n); memory.copy: the read range        *)
(*     (src, n) then the write range (dst, n);                               *)
(*   memory.size: the capacity event (F, wmemsize, 0); memory.grow: the     *)
(*     capacity event (T, wmemsize, 0) (grow has no successor in this model);*)
(*   every other instruction: none.                                          *)
(* Events are a function of the pre-state that never reads wmem. A trapping *)
(* step still reports the attempted access (its write commits nothing).     *)
(*                                                                           *)
(* wasmt is the traced step: the state steps by wasm and the trace grows by *)
(* the events of the step, appended newest last (program order). wasmstate  *)
(* is unchanged, so every existing statement keeps its meaning.             *)
(* ------------------------------------------------------------------------- *)

let wasm_ev_top = new_definition
 `wasm_ev_top (k:num) (s:wasmstate) =
    match EL k (read wstack s) with I32 a -> val a | _ -> 0`;;

let wasm_ldst = new_definition
 `wasm_ldst (i:winstr) =
    match i with
      Wi32_load off -> SOME (F,off,4) | Wi64_load off -> SOME (F,off,8)
    | Wf32_load off -> SOME (F,off,4) | Wf64_load off -> SOME (F,off,8)
    | Wi32_load8_s off -> SOME (F,off,1) | Wi32_load8_u off -> SOME (F,off,1)
    | Wi32_load16_s off -> SOME (F,off,2) | Wi32_load16_u off -> SOME (F,off,2)
    | Wi64_load8_s off -> SOME (F,off,1) | Wi64_load8_u off -> SOME (F,off,1)
    | Wi64_load16_s off -> SOME (F,off,2) | Wi64_load16_u off -> SOME (F,off,2)
    | Wi64_load32_s off -> SOME (F,off,4) | Wi64_load32_u off -> SOME (F,off,4)
    | Wi32_store off -> SOME (T,off,4) | Wi64_store off -> SOME (T,off,8)
    | Wf32_store off -> SOME (T,off,4) | Wf64_store off -> SOME (T,off,8)
    | Wi32_store8 off -> SOME (T,off,1) | Wi32_store16 off -> SOME (T,off,2)
    | Wi64_store8 off -> SOME (T,off,1) | Wi64_store16 off -> SOME (T,off,2)
    | Wi64_store32 off -> SOME (T,off,4)
    | _ -> NONE`;;

let wasm_instr_events = new_definition
 `wasm_instr_events (i:winstr) (s:wasmstate) =
    match i with
      Wmemory_size -> [(F,read wmemsize s,0)]
    | Wmemory_grow -> [(T,read wmemsize s,0)]
    | Wmemory_fill -> [(T,wasm_ev_top 2 s,wasm_ev_top 0 s)]
    | Wmemory_copy -> [(F,wasm_ev_top 1 s,wasm_ev_top 0 s);
                       (T,wasm_ev_top 2 s,wasm_ev_top 0 s)]
    | _ -> (match wasm_ldst i with
              SOME (w,off,k) -> [(w,wasm_ev_top (if w then 1 else 0) s + off,k)]
            | NONE -> [])`;;

let wasm_mem_events = new_definition
 `wasm_mem_events (s:wasmstate) =
    match wasm_decode (read wcode s) (val (read wpc s)) with
      SOME (i,n) -> wasm_instr_events i s
    | NONE -> []`;;

let wasmt = new_definition
 `wasmt (x:wasmstate#(bool#num#num)list) (y:wasmstate#(bool#num#num)list) <=>
    wasm (FST x) (FST y) /\ SND y = APPEND (SND x) (wasm_mem_events (FST x))`;;

(* ------------------------------------------------------------------------- *)
(* Generic trace lifting (any step relation, any trace update).              *)
(* ------------------------------------------------------------------------- *)

let EVENTUALLY_TRACE_LIFT = prove
 (`!(step:S->S->bool) (upd:S->T->T) (R:S->bool) s.
     eventually step R s
     ==> !t. eventually (\x y. step (FST x) (FST y) /\ SND y = upd (FST x) (SND x))
                        (\y. R (FST y)) (s,t)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC eventually_INDUCT THEN
  CONJ_TAC THEN X_GEN_TAC `s:S` THENL
   [DISCH_TAC THEN GEN_TAC THEN MATCH_MP_TAC(CONJUNCT1(SPEC_ALL eventually_RULES)) THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN X_GEN_TAC `t:T` THEN
    MATCH_MP_TAC(CONJUNCT2(SPEC_ALL eventually_RULES)) THEN
    REWRITE_TAC[FORALL_PAIR_THM; EXISTS_PAIR_THM; FST; SND] THEN
    CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`s':S`; `upd (s:S) (t:T):T`] THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]]]);;

(* A guarded run (each stepping state satisfies G) lifts to a traced run    *)
(* whose trace keeps an invariant Inv that every guarded step preserves.      *)
let EVENTUALLY_GUARD_TRACE = prove
 (`!(step:S->S->bool) (G:S->bool) (upd:S->T->T) (Inv:T->bool) (R:S->bool).
     (!s t. G s /\ Inv t ==> Inv (upd s t))
     ==> !s. eventually (\s s'. G s /\ step s s') R s
             ==> !t. Inv t
                     ==> eventually
                           (\x y. step (FST x) (FST y) /\ SND y = upd (FST x) (SND x))
                           (\y. R (FST y) /\ Inv (SND y)) (s,t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC eventually_INDUCT THEN
  CONJ_TAC THEN X_GEN_TAC `s:S` THENL
   [DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(CONJUNCT1(SPEC_ALL eventually_RULES)) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN STRIP_TAC THEN X_GEN_TAC `t:T` THEN DISCH_TAC THEN
    MATCH_MP_TAC(CONJUNCT2(SPEC_ALL eventually_RULES)) THEN
    REWRITE_TAC[FORALL_PAIR_THM; EXISTS_PAIR_THM; FST; SND] THEN
    CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`s':S`; `upd (s:S) (t:T):T`] THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]]]);;

let EVENTUALLY_GUARD_ERASE = prove
 (`!(step:S->S->bool) (G:S->bool) (R:S->bool) s.
     eventually (\s s'. G s /\ step s s') R s ==> eventually step R s`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC eventually_INDUCT THEN
  REWRITE_TAC[] THEN MESON_TAC[eventually_RULES]);;

(* ------------------------------------------------------------------------- *)
(* The trace interface theorems.                                              *)
(* ------------------------------------------------------------------------- *)


let WASMT_ALT = prove
 (`wasmt = \x y. wasm (FST x) (FST y) /\
                 SND y = (\s t. APPEND t (wasm_mem_events s)) (FST x) (SND x)`,
  REWRITE_TAC[FUN_EQ_THM; wasmt]);;

(* ------------------------------------------------------------------------- *)
(* The trace interface: wasmt erases to wasm, and every ensures wasm theorem *)
(* lifts to wasmt unchanged (the trace is unconstrained).                     *)
(* ------------------------------------------------------------------------- *)

let WASMT_ERASE = prove
 (`(!(s:wasmstate) (t:(bool#num#num)list) (s':wasmstate) (t':(bool#num#num)list).
      wasmt (s,t) (s',t') <=> wasm s s' /\ t' = APPEND t (wasm_mem_events s)) /\
   (!(s:wasmstate) (t:(bool#num#num)list) (s':wasmstate).
      (?t'. wasmt (s,t) (s',t')) <=> wasm s s')`,
  REWRITE_TAC[wasmt; FST; SND] THEN MESON_TAC[]);;

let WASMT_ENSURES_LIFT = prove
 (`!(P:wasmstate->bool) (Q:wasmstate->bool) (C:wasmstate->wasmstate->bool).
    ensures wasm P Q C
    ==> ensures wasmt (\x:wasmstate#(bool#num#num)list. P (FST x))
                      (\x:wasmstate#(bool#num#num)list. Q (FST x))
                      (\(x:wasmstate#(bool#num#num)list) (y:wasmstate#(bool#num#num)list). C (FST x) (FST y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures; FORALL_PAIR_THM; FST] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`s:wasmstate`; `t:(bool#num#num)list`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`wasm`; `\s:wasmstate t:(bool#num#num)list. APPEND t (wasm_mem_events s)`;
                 `\s':wasmstate. Q s' /\ C (s:wasmstate) s'`; `s:wasmstate`]
                EVENTUALLY_TRACE_LIFT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `t:(bool#num#num)list`) THEN
  REWRITE_TAC[WASMT_ALT] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[]);;
