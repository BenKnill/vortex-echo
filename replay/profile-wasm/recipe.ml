(* HOL_WORKBENCH_RECIPE_SOURCE_ROOT wasm bundled path=profiles/roots/wasm tree=fb0bf26395fa1513752a026e45d76ca12159c44f37bfd10e8e285a790084e78f *)
(* Harness: load a pinned second-root file with its own directory first on load_path. *)
let hol_workbench_recipe_root_needs alias relative =
  let variable = "HOL_WORKBENCH_RECIPE_SOURCE_ROOT_" ^ alias in
  let root = try Sys.getenv variable with Not_found ->
    failwith ("profile builder did not provide recipe source root " ^ variable) in
  let path = Filename.concat root relative in
  let saved_path = !load_path and saved_raise = !use_file_raise_failure in
  let restore () = load_path := saved_path; use_file_raise_failure := saved_raise in
  load_path := Filename.dirname path :: saved_path;
  use_file_raise_failure := true;
  (try needs path with error -> (restore (); raise error));
  restore ();;
hol_workbench_recipe_root_needs "wasm" "proofs/base.ml";;
let HOL_WORKBENCH_WASM_WARMUP = end_itlist CONJ [WASM_DETERMINISTIC; WASM_STEP_THM];;
