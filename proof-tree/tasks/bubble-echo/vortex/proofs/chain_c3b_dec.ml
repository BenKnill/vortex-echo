(* Vortex chain rung C3b (vortex-chain-20261111-142342 c3b, Claude Opus 5.5, 2026-11-13): code definition and      *)
(* decode table of f25 ve_puncture of vortex_a1.wasm (1046 B body, entry pc 13, 16 locals, no calls), by the       *)
(* profile's linear-time rule WASM_BIG_MK_EXEC_RULE (wasm_bigdecode.ml). Stable basis layer: never edit.          *)
let va1_f25_mc = define_from_wasm "va1_f25_mc" "../purist/vortex_a1.wasm" "#25";;
let VA1_F25_CALLEE = WASM_CALLEE_RULE va1_f25_mc;;
let C3B_F25_EXEC = WASM_BIG_MK_EXEC_RULE va1_f25_mc 13;;
