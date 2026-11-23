(* ========================================================================= *)
(* WASM proof base: the s2n-bignum generic layer (as in x86/proofs/base.ml *)
(* minus the ISA files) followed by the WASM semantics and tactics.        *)
(* On the s2n-arm profile the s2n part is already loaded; there a demo    *)
(* needs only wasm/proofs/wasm_tactics.ml (which needs wasm.ml) and, to   *)
(* bind bytes from a .wasm artifact, wasm/proofs/wasm_loader.ml.          *)
(* ========================================================================= *)

needs "Library/iter.ml";;
needs "Library/rstc.ml";;
needs "Library/bitsize.ml";;
needs "Library/pocklington.ml";;
needs "Library/integer.ml";;
needs "Library/words.ml";;
needs "Library/bitmatch.ml";;
needs "Library/records.ml";;
needs "common/overlap.ml";;
needs "common/for_hollight.ml";;
needs "common/words2.ml";;
needs "common/misc.ml";;
needs "common/components.ml";;
needs "common/alignment.ml";;
needs "common/relational.ml";;
needs "common/interval.ml";;
needs "common/elf.ml";;
needs "common/safety.ml";;
prioritize_num();;

needs "wasm_loader.ml";;
needs "wasm.ml";;
needs "wasm_tactics.ml";;
needs "wasm_bigdecode.ml";;
