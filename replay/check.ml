(* Loaded after bare HOL Light, before the profile or project sources. *)
let replay_axioms = axioms ();;
let replay_check_axioms stage =
  let current = axioms () in
  if current <> replay_axioms then
    failwith (Printf.sprintf "%s axioms changed: bare=%d, current=%d"
      stage (List.length replay_axioms) (List.length current));;

let () =
  if List.length replay_axioms <> 3 ||
     not (List.for_all (fun th -> List.mem th replay_axioms)
                      [ETA_AX; SELECT_AX; INFINITY_AX])
  then failwith "bare HOL Light did not load exactly ETA_AX, SELECT_AX and INFINITY_AX";;

let replay_foundation () =
  List.map (fun n -> n ())
    [(fun () -> List.length (axioms ()));
     (fun () -> List.length (constants ()));
     (fun () -> List.length (definitions ()));
     (fun () -> List.length (types ()))];;

let replay_check_delta stage before expected =
  let delta = List.map2 ( - ) (replay_foundation ()) before in
  Printf.printf "\nFOUNDATION %s (axioms constants definitions types): %s\n%!"
    stage (String.concat " " (List.map string_of_int delta));
  if delta <> expected then failwith (stage ^ " foundation delta mismatch");;

let replay_parser_context () =
  (!the_interface, !the_overload_skeletons, !the_implicit_types, infixes (),
   prefixes (), binders (), type_abbrevs (), reserved_words (),
   List.map fst (installed_parsers ()),
   List.filter is_hidden (List.map fst (constants ())),
   !ignore_constant_varstruct, !comment_token);;

let replay_check_binding, replay_check_pin =
  let parse = parse_term and conclusion = concl and hypotheses = hyp in
  let registry = definitions in
  let canonical tm =
    let vars = type_vars_in_term tm in
    let substitutions =
      List.mapi (fun i ty -> mk_vartype ("vortex_replay_ty_" ^ string_of_int i), ty)
        vars in
    inst substitutions tm in
  let same a b = aconv a b || aconv (canonical a) (canonical b) in
  let binding name (th : thm) text =
    if hypotheses th <> [] then failwith ("hypotheses in " ^ name);
    if not (same (conclusion th) (parse text)) then
      failwith ("spec statement mismatch: " ^ name);
    Printf.printf "\nBINDING %s\n%!" name in
  let definition_name th =
    try Some (fst (dest_const (lhs (conclusion th)))) with Failure _ -> None in
  let pin name text =
    let stored =
      match List.find_opt (fun th -> definition_name th = Some name) (registry ()) with
      | Some th -> th
      | None -> failwith ("no definition in registry: " ^ name) in
    let left, right = dest_eq (snd (strip_forall (parse text))) in
    let head, args = strip_comb left in
    if not (is_const head) || fst (dest_const head) <> name then
      failwith ("invalid left-hand side for pin: " ^ name);
    let expected = mk_eq (head, list_mk_abs (args, right)) in
    if hypotheses stored <> [] || not (same (conclusion stored) expected) then
      failwith ("spec definition mismatch: " ^ name);
    Printf.printf "\nPIN %s\n%!" name in
  binding, pin;;
