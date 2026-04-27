(*- E_COMPCERT_DEACTIVATED_CODE_version_creator_001 *)
(*- #Condition "Code is not compiled into CompCert." *)
(*- #Justification "Code is not part of CompCert" *)

(*- E_COMPCERT_CODE_version_creator_001 *)
(*- #Justify_Derived "Module version_creator.ml is an external helper tool. It is part of the build system and is not part of CompCert." *)

open Printf

(* Module to create version.ml module from VERSION config file. *)

let re_quote_end = Str.regexp ".*|generated}"

(* `print_ocaml_let oc id value` prints a line of the form `let id = {generated|value|generated}` into `oc`.
  
  We generate a let-binding to a quoted string literal, so that the value is not accidentally changed 
  from what is written in the parsed config file by interpreting escape sequences.
  The docs mention that multiple newline sequences in a quoted string literal are still normalized, 
  but this does not affect us because we parsed the config file line by line. *)
let print_ocaml_let id value =
  (* Check that value does not accidentally contain the quoted string literal end sequence. *)
  assert (not (Str.string_match re_quote_end value 0)); 
  printf "let %s = {generated|%s|generated}\n" id value

let _ =
  let config = Kv_parser.parse_file "VERSION" in
  print_ocaml_let "version" (Kv_parser.get "version" config);
  print_ocaml_let "buildnr" (Kv_parser.get "buildnr" config);
  print_ocaml_let "tag" (Kv_parser.get "tag" config);
  print_ocaml_let "branch" (Kv_parser.get "branch" config)

(*- #End *)

(*- #End_DEACTIVATED_CODE *)
