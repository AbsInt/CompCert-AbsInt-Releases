(* Tool to generate documentation using coq2html from .v files compiled to compcert theory.

   Dune always uses forward slashes as path separators when computing e.g. rule dependencies.
   We pass those paths as arguments to coq2html which uses the generic Filename module, so we rewrite the paths to use the OS specific directory separator. *)

(*- E_COMPCERT_DEACTIVATED_CODE_gen_documentation_001 *)
(*- #Condition "Code is not compiled into CompCert." *)
(*- #Justification "Code is not part of CompCert" *)

(*- E_COMPCERT_CODE_gen_documentation_001 *)
(*- #Justify_Derived "Module gen_documentation.ml is an external helper tool. It is not part of CompCert." *)

let to_os_dir_sep filepath =
  String.(concat Filename.dir_sep (split_on_char '/' filepath))

(* Implement behavior as in Makefile to prevent doc generation for Parser.v. *)
let no_parser filepath =
  not (String.ends_with ~suffix:"cparser/Parser.v" filepath)

let _ =
  if Array.length Sys.argv < 2 then 
    invalid_arg "expected .glob & .v filenames"
  else 
    let filepaths = List.tl (Array.to_list Sys.argv) in
    let filepaths_modified = List.map to_os_dir_sep (List.filter no_parser filepaths) in
    let outdir = Filename.(concat parent_dir_name (concat "doc" "html")) in
    let command = Printf.sprintf "coq2html -d %s -base compcert -short-names %s" outdir (String.concat " " filepaths_modified) in
    Printf.printf "Running command:\n%s" command;
    Sys.command command

(*- #End *)

(*- #End_DEACTIVATED_CODE *)
