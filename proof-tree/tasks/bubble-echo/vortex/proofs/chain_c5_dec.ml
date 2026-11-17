(* Vortex chain rung C5 (lane vortex-chain-20261111-142342 c5, Claude Opus 5.5, 2026-11-13): code definitions and  *)
(* decode tables of the click-puncture functions of vortex_a1.wasm (sha256 a3cf8c82...): f32 (sin/cos, 513 B,     *)
(* entry pc 5), f34 (orthonormal frame, 244 B, entry pc 7) and f33 = export "puncture" (1256 B, entry pc 17), by   *)
(* the profile's linear-time rule WASM_BIG_MK_EXEC_RULE. Stable basis layer: never edit (new files get new names). *)
needs "../../capillary/proofs/wasm_fastdec.ml";;
needs "wasm_call.ml";;
let va1_f32_mc = define_from_wasm "va1_f32_mc" "../purist/vortex_a1.wasm" "#32";;
let va1_f34_mc = define_from_wasm "va1_f34_mc" "../purist/vortex_a1.wasm" "#34";;
let va1_puncture_mc = define_from_wasm "va1_puncture_mc" "../purist/vortex_a1.wasm" "puncture";;
let VA1_F32_CALLEE = WASM_CALLEE_RULE va1_f32_mc;;
let VA1_F34_CALLEE = WASM_CALLEE_RULE va1_f34_mc;;
let VA1_PUNCTURE_CALLEE = WASM_CALLEE_RULE va1_puncture_mc;;
let C5_F32_EXEC = WASM_BIG_MK_EXEC_RULE va1_f32_mc 5;;
let C5_F34_EXEC = WASM_BIG_MK_EXEC_RULE va1_f34_mc 7;;
let C5_F33_EXEC = WASM_BIG_MK_EXEC_RULE va1_puncture_mc 17;;
