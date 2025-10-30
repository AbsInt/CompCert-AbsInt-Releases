(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*      Bernhard Schommer, AbsInt Angewandte Informatik GmbH           *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open Printf
open Clflags
open Diagnostics

(* Safe removal of files *)
(*- E_COMPCERT_CODE_Driveraux_safe_remove_001 *)
(*- #Justify_Derived "Utility function" *)
let safe_remove file =
  try Sys.remove file with Sys_error _ -> ()
(*- #End *)

(*- E_COMPCERT_CODE_Driveraux_tmp_file_001 *)
(*- #Justify_Derived "Utility function" *)
let tmp_file suff =
  let tmpfile = Filename.temp_file "compcert" suff in
  at_exit (fun () -> safe_remove tmpfile);
  tmpfile
(*- #End *)

(* Invocation of external tools *)

(*- E_COMPCERT_CODE_Driveraux_waitpid_no_intr_001 *)
(*- #Justify_Derived "Utility function" *)
let rec waitpid_no_intr pid =
  try Unix.waitpid [] pid
  with Unix.Unix_error (Unix.EINTR, _, _) -> waitpid_no_intr pid
(*- #End *)

(*- E_COMPCERT_CODE_Driveraux_command_result_001 *)
(*- #Justify_Derived "Type definition" *)
type command_result =
  | Success
  | Failure of int
  | ExitKilled of int
  | ExitError of (Unix.error * string * string)
(*- #End *)

(*- E_COMPCERT_CODE_Driveraux_command_001 *)
(*- #Link_to E_COMPCERT_TR_Function_PREPROCESSING_001 *)
(*- #Link_to E_COMPCERT_TR_Function_ASSEMBLING_001 *)
(*- #Link_to E_COMPCERT_TR_Function_LINKING_001 *)
let command stdout args =
  let argv = Array.of_list args in
  assert (Array.length argv > 0);
  try
    let fd_out = match stdout with
      | None ->
          Unix.stdout
      | Some f ->
          Unix.openfile f [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC] 0o666 in
    let pid =
      Unix.create_process argv.(0) argv Unix.stdin fd_out Unix.stderr in
    let (_, status) = waitpid_no_intr pid in
    if stdout <> None then Unix.close fd_out;
    match status with
    | Unix.WEXITED 0 -> Success
    | Unix.WEXITED rc -> Failure rc
    | Unix.WSIGNALED n | Unix.WSTOPPED n -> ExitKilled n
  with Unix.Unix_error(err, fn, param) ->
    ExitError(err, fn, param)
(*- #End *)

(*- E_COMPCERT_CODE_Driveraux_command_002 *)
(*- #Justify_Derived "Utility function" *)
let command ?stdout args =
  if !option_v then begin
    eprintf "+ %s" (String.concat " " args);
    begin match stdout with
    | None -> ()
    | Some f -> eprintf " > %s" f
    end;
    prerr_endline ""
  end;
  let resp = Sys.win32 && Configuration.response_file_style <> Configuration.Unsupported in
  if resp && List.fold_left (fun len arg -> len + String.length arg + 1) 0 args > 7000 then
    let quote,prefix = match Configuration.response_file_style with
    | Configuration.Unsupported -> assert false
    | Configuration.Gnu -> Responsefile.gnu_quote,"@"
    | Configuration.Diab -> Responsefile.diab_quote,"-@" in
    let file,oc = Filename.open_temp_file "compcert" "" in
    let cmd,args = match args with
    | cmd::args -> cmd,args
    | [] -> assert false (* Should never happen *) in
    List.iter (fun a -> Printf.fprintf oc "%s " (quote a)) args;
    close_out oc;
    let arg = prefix^file in
    let ret = command stdout [cmd;arg] in
    safe_remove file;
    ret
  else
    command stdout args
(*- #End *)

(*- E_COMPCERT_CODE_Driveraux_command_error_001 *)
(*- #Link_to E_COMPCERT_TR_Robustness_DRIVER_009 *)
let command_error n err =
  let msg = match err with
    | Success -> assert false (* Should never happen *)
    | Failure rc -> sprintf " with exit code %d (use -v to see invocation)\n" rc
    | ExitKilled _ -> sprintf ": killed by a signal\n"
    | ExitError (err, fn, param) -> sprintf " in '%s': %s '%s'\n" fn (Unix.error_message err) param
  in
    fatal_error no_loc "executing %s command failed%s" n msg
(*- #End *)

(* Determine names for output files.  We use -o option if specified
   and if this is the final destination file (not a dump file).
   Otherwise, we generate a file in the current directory. *)

(*- E_COMPCERT_CODE_Driveraux_output_filename_001 *)
(*- #Justify_Derived "Utility function" *)
let output_filename ?(final = false) source_file ~suffix =
  match !option_o with
  | Some file when final -> file
  | _ ->
    Filename.basename (Filename.remove_extension source_file)
    ^ suffix
(*- #End *)

(* A variant of [output_filename] where the default output name is fixed *)

(*- E_COMPCERT_CODE_Driveraux_output_filename_default_001 *)
(*- #Justify_Derived "Utility function" *)
let output_filename_default default_file =
  match !option_o with
  | Some file -> file
  | None -> default_file
(*- #End *)

(* All input files should exist *)

(*- E_COMPCERT_CODE_Driveraux_ensure_inputfile_exists_001 *)
(*- #Link_to E_COMPCERT_TR_Robustness_DRIVER_013 *)
let ensure_inputfile_exists name =
  if not (Sys.file_exists name) then
    fatal_error no_loc "no such file or directory: '%s'" name
(*- #End *)

(* Printing of error messages *)

(*- E_COMPCERT_CODE_Driveraux_loc_of_error_001 *)
(*- #Justify_Derived "Utility function" *)
let loc_of_error file msg =
  let file_loc = Diagnostics.file_loc file in
  let rec location = function
    | Errors.CTX i :: _ ->
      let loc = (C2C.atom_location i) in
      if loc <> Cutil.no_loc then
        loc
      else
        file_loc
    | _ :: r -> location r
    | [] -> file_loc in
  location msg
(*- #End *)

(*- E_COMPCERT_CODE_Driveraux_print_error_001 *)
(*- #Justify_Derived "Utility function" *)
let print_error pp msg =
  let print_one_error = function
  | Errors.MSG s -> Format.pp_print_string pp (Camlcoq.camlstring_of_coqstring s)
  | Errors.CTX i -> Format.pp_print_string pp (Camlcoq.extern_atom i)
  | Errors.POS i -> Format.fprintf pp "%ld" (Camlcoq.P.to_int32 i)
  in
  List.iter print_one_error msg
(*- #End *)

(* Command-line parsing *)
(*- E_COMPCERT_CODE_Driveraux_explode_comma_option_001 *)
(*- #Justify_Derived "Utility function" *)
let explode_comma_option s =
  match Str.split (Str.regexp ",") s with
  | [] -> assert false
  | _ :: tl -> tl
(*- #End *)

(* Record actions to be performed after parsing the command line *)

(*- E_COMPCERT_CODE_Driveraux_actions_001 *)
(*- #Justify_Derived "Utility function" *)
let actions : ((string -> string) * string) list ref = ref []

let push_action fn arg =
  actions := (fn, arg) :: !actions
(*- #End *)

(*- E_COMPCERT_CODE_Driveraux_push_linker_arg_001 *)
(*- #Justify_Derived "Utility function" *)
let push_linker_arg arg =
  push_action (fun s -> s) arg
(*- #End *)

(*- E_COMPCERT_CODE_Driveraux_perform_actions_001 *)
(*- #Justify_Derived "Utility function" *)
let perform_actions () =
  let rec perform = function
  | [] -> []
  | (fn, arg) :: rem -> let res = fn arg in res :: perform rem
  in perform (List.rev !actions)
(*- #End *)
