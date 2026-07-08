(*- E_COMPCERT_DEACTIVATED_CODE_kv_parser_001 *)
(*- #Condition "Code is not compiled into CompCert." *)
(*- #Justification "Code is not part of CompCert" *)

(*- E_COMPCERT_CODE_kv_parser_001 *)
(*- #Justify_Derived "Module kv_parser.ml is an external helper tool. It is part of the build system and is not part of CompCert." *)

open Printf

(* Module to parse config files. *)

type config = (string * string) list

let get key config =
  match List.assoc_opt key config with
  | None -> eprintf "Config key '%s' not found!\n" key; raise Not_found
  | Some v -> v

let re_kv_line = Str.regexp {|\([^=]*\)=\(.*\)|}

(* Parse a single line into an optional key-value pair.
 A line in the config format can be one of:
 1. empty
 2. # a comment
 3. key=value (extra whitespace around both key and value allowed)
 *)
let parse_line line =
  (* Comments and empty lines are skipped. *)
  if line = "" || String.starts_with ~prefix:"#" line then
    None
  else begin
    if not (Str.string_match re_kv_line line 0) then begin
      raise (Invalid_argument ("Invalid configuration line: '"^line^"'"))
    end else
      (* Strip whitespace around key and value. *)
      let key = String.trim (Str.matched_group 1 line) in
      let value = String.trim (Str.matched_group 2 line) in 
      Some (key, value)
  end

let parse_file f = 
  let ic = open_in f in 
  let res = ref [] in
  try 
    while true do 
      let line = input_line ic in
      match parse_line line with
      | None -> ()
      | Some kv -> res := kv :: !res
    done
  with End_of_file -> 
    close_in ic;
    !res

(*- #End *)

(*- #End_DEACTIVATED_CODE *)
