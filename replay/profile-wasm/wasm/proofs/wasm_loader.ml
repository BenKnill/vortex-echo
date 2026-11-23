(* ========================================================================= *)
(* Bind the exact bytes of one WebAssembly function from a real .wasm file.  *)
(*                                                                           *)
(* The WebAssembly analogue of the s2n-bignum ELF loaders (common/elf.ml and *)
(* define_from_elf / define_assert_from_elf in {arm,x86}/proofs/decode.ml):  *)
(*                                                                           *)
(*   define_from_wasm "name" "path/file.wasm" "export_or_#index"             *)
(*   define_assert_from_wasm "name" "path/file.wasm" "export_or_#index"      *)
(*     [0x..; ...]                                                           *)
(*                                                                           *)
(* define the constant `name : byte list` as the body of the Code-section    *)
(* entry of that function: the bytes after the entry-size LEB128, i.e. the   *)
(* local-declaration vector and then the expression, ending in 0x0B.  The    *)
(* assert form also checks the literal list against the file, so a proof     *)
(* states the bytes it is about and fails if the artifact differs.           *)
(*                                                                           *)
(* The function is chosen by export name (a function export, unique) or by   *)
(* "#<function index>".  The function index space starts with the imported   *)
(* functions, so code entry = function index - number of imported functions; *)
(* imported functions have no code and are refused.  The artifact path is    *)
(* the second argument, as for the ELF loaders, so the Hearth runtime can    *)
(* observe and hash the file into receipts (ocaml/hearth.ml).  Relative      *)
(* paths are read from the current directory, as for the ELF loaders.        *)
(*                                                                           *)
(* wasm/artifacts/wasm_dump.py is the independent Python reader of the same  *)
(* bytes: `wasm_dump.py FILE --func SEL --hol` prints the list to assert.     *)
(* ========================================================================= *)

(* Self-contained, loads no file: it requires Library/words.ml (byte type)   *)
(* loaded first, as every s2n-style base does; wasm/proofs/base.ml does.      *)

let wasm_load_file (file:string) : bytes =
  let ic = open_in_bin file in
  let n = in_channel_length ic in
  let bs = Bytes.create n in
  (try really_input ic bs 0 n with e -> close_in ic; raise e);
  close_in ic; bs;;

(* The byte list term [word b0; word b1; ...], as term_of_bytes in elf.ml. *)
let wasm_term_of_bytes =
  let word = `word:num->byte`
  and nil = `NIL:byte list`
  and cons = `CONS:byte->byte list->byte list` in
  fun (bs:bytes) ->
    let rec go i acc =
      if i < 0 then acc else
      let b = mk_comb (word, mk_small_numeral (Char.code (Bytes.get bs i))) in
      go (i - 1) (mk_comb (mk_comb (cons, b), acc)) in
    go (Bytes.length bs - 1) nil;;

(* ------------------------------------------------------------------------- *)
(* A bounds-checked reader over the file bytes.                              *)
(* ------------------------------------------------------------------------- *)

let wasm_byte (bs:bytes) (pos:int ref) (limit:int) : int =
  if !pos >= limit then failwith "wasm: unexpected end of section or file" else
  let b = Char.code (Bytes.get bs !pos) in
  pos := !pos + 1; b;;

(* Unsigned LEB128 of at most ceil(bits/7) bytes, as the binary format requires. *)
let wasm_uleb (bits:int) (bs:bytes) (pos:int ref) (limit:int) : int =
  let rec go acc shift count =
    if count = 0 then failwith "wasm: LEB128 too long" else
    let b = wasm_byte bs pos limit in
    let acc = acc lor ((b land 0x7f) lsl shift) in
    if b land 0x80 = 0 then
      (if shift + 7 > bits && (b lsr (bits - shift)) <> 0
       then failwith "wasm: LEB128 out of range" else acc)
    else go acc (shift + 7) (count - 1) in
  go 0 0 ((bits + 6) / 7);;

let wasm_u32 = wasm_uleb 32;;

let wasm_skip (n:int) (pos:int ref) (limit:int) : unit =
  if n < 0 || !pos + n > limit then failwith "wasm: truncated" else pos := !pos + n;;

let wasm_name (bs:bytes) (pos:int ref) (limit:int) : string =
  let n = wasm_u32 bs pos limit in
  let start = !pos in
  wasm_skip n pos limit;
  Bytes.sub_string bs start n;;

let wasm_limits (bs:bytes) (pos:int ref) (limit:int) : unit =
  let flags = wasm_byte bs pos limit in
  let bits = if flags land 4 <> 0 then 64 else 32 in
  ignore (wasm_uleb bits bs pos limit);
  if flags land 1 <> 0 then ignore (wasm_uleb bits bs pos limit);;

(* ------------------------------------------------------------------------- *)
(* Module structure: imported function count, function exports, code bodies. *)
(* Returns (imported functions, [(export name, function index)],             *)
(* [(body offset, body length)] in code-entry order).                        *)
(* ------------------------------------------------------------------------- *)

let wasm_module_index (bs:bytes) =
  let size = Bytes.length bs in
  if size < 8 || Bytes.sub_string bs 0 4 <> "\000asm" then
    failwith "wasm: not a WebAssembly binary (bad magic)" else
  if Bytes.sub_string bs 4 4 <> "\001\000\000\000" then
    failwith "wasm: unsupported binary version" else
  let pos = ref 8 in
  let imports = ref 0 and exports = ref [] and code = ref []
  and nfuncs = ref (-1) in
  while !pos < size do
    let id = wasm_byte bs pos size in
    let len = wasm_u32 bs pos size in
    let start = !pos in
    let limit = start + len in
    if limit > size then failwith "wasm: section runs past end of file" else
    (match id with
     | 2 ->
        for item = 1 to wasm_u32 bs pos limit do
          ignore (wasm_name bs pos limit); ignore (wasm_name bs pos limit);
          (match wasm_byte bs pos limit with
           | 0 -> ignore (wasm_u32 bs pos limit); imports := !imports + 1
           | 1 -> ignore (wasm_byte bs pos limit); wasm_limits bs pos limit
           | 2 -> wasm_limits bs pos limit
           | 3 -> wasm_skip 2 pos limit
           | 4 -> ignore (wasm_byte bs pos limit); ignore (wasm_u32 bs pos limit)
           | k -> failwith ("wasm: unknown import kind " ^ string_of_int k))
        done
     | 3 -> nfuncs := wasm_u32 bs pos limit
     | 7 ->
        for item = 1 to wasm_u32 bs pos limit do
          let name = wasm_name bs pos limit in
          let kind = wasm_byte bs pos limit in
          let index = wasm_u32 bs pos limit in
          if kind = 0 then exports := (name,index) :: !exports
        done
     | 10 ->
        for item = 1 to wasm_u32 bs pos limit do
          let n = wasm_u32 bs pos limit in
          code := (!pos,n) :: !code;
          wasm_skip n pos limit
        done
     | _ -> ());
    pos := limit
  done;
  let code = rev !code in
  if !nfuncs >= 0 && !nfuncs <> length code then
    failwith "wasm: function and code section counts differ" else
  !imports, rev !exports, code;;

(* ------------------------------------------------------------------------- *)
(* The body bytes of the selected function: export name or "#<index>".       *)
(* ------------------------------------------------------------------------- *)

let wasm_function_bytes_of (bs:bytes) (selector:string) : bytes =
  let imports,exports,code = wasm_module_index bs in
  let findex =
    if String.length selector > 1 && selector.[0] = '#' then
      (try int_of_string (String.sub selector 1 (String.length selector - 1))
       with Failure _ -> failwith ("wasm: bad function index " ^ selector))
    else
      match filter (fun (name,_) -> name = selector) exports with
      | [_,index] -> index
      | [] -> failwith ("wasm: no function export named " ^ selector)
      | _ -> failwith ("wasm: function export name not unique: " ^ selector) in
  if findex < imports then
    failwith ("wasm: function " ^ string_of_int findex ^ " is imported and has no code")
  else
    let entry = findex - imports in
    if entry >= length code then
      failwith ("wasm: function index " ^ string_of_int findex ^ " out of range")
    else
      let offset,len = el entry code in
      Bytes.sub bs offset len;;

let wasm_function_bytes (file:string) (selector:string) : bytes =
  wasm_function_bytes_of (wasm_load_file file) selector;;

(* ------------------------------------------------------------------------- *)
(* Definitions, as define_word_list / assert_word_list in the ISA decoders   *)
(* (not loaded in a WASM base, so restated here under wasm_ names).          *)
(* ------------------------------------------------------------------------- *)

let wasm_assert_byte_list =
  let rec go i = function
    | [], Const("NIL",_) -> ()
    | n::ls, Comb(Comb(Const("CONS",_),Comb(Const("word",_),a)),tm)
        when 0 <= n && n <= 255 && dest_numeral a = num n -> go (i + 1) (ls, tm)
    | n::_, Comb(Comb(Const("CONS",_),Comb(Const("word",_),a)),_) ->
        failwith (Printf.sprintf
          "define_assert_from_wasm: byte %d is %s in the file but 0x%02x in the literal"
          i (string_of_num (dest_numeral a)) n)
    | [], _ -> failwith (Printf.sprintf
          "define_assert_from_wasm: the file has more than %d bytes" i)
    | _ -> failwith (Printf.sprintf
          "define_assert_from_wasm: the file has only %d bytes" i) in
  fun tm ls ->
    if type_of tm = `:byte list` then go 0 (ls, tm)
    else failwith "define_assert_from_wasm: not a byte list";
    tm;;

let wasm_define_byte_list name tm =
  try new_definition (mk_eq (mk_var (name, `:byte list`), tm))
  with Failure _ -> new_definition (mk_eq (mk_mconst (name, `:byte list`), tm));;

let define_from_wasm name file selector =
  wasm_define_byte_list name (wasm_term_of_bytes (wasm_function_bytes file selector));;

let define_assert_from_wasm name file selector ls =
  wasm_define_byte_list name
    (wasm_assert_byte_list (wasm_term_of_bytes (wasm_function_bytes file selector)) ls);;

(* The literal to paste into define_assert_from_wasm. *)
let print_literal_from_wasm file selector =
  let bs = wasm_function_bytes file selector in
  let items = map (fun i -> Printf.sprintf "0x%02x" (Char.code (Bytes.get bs i)))
                  (0 -- (Bytes.length bs - 1)) in
  print_string ("[" ^ String.concat "; " items ^ "]\n");;
