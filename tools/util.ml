(*- E_COMPCERT_DEACTIVATED_CODE_util_001 *)
(*- #Condition "Code is not compiled into CompCert." *)
(*- #Justification "Code is not part of CompCert" *)

(*- E_COMPCERT_CODE_util_001 *)
(*- #Justify_Derived "Module util.ml is an external helper tool. It is part of the build system and is not part of CompCert." *)

(* Utility functions *)

(** [file_delete f] deletes the file at path [f]. *)
let file_delete filename =
  try Sys.remove filename with Sys_error _ -> ()

(** [file_read f] returns the content of the file at path [f] as a string. *)
let file_read filename =
  let ic = open_in_bin filename in
  really_input_string ic (in_channel_length ic)

(** [grepi re str] returns true iff the pattern described by [re] occurs in string [str] (case-insensitively). *)
let grepi re str =
  let re = Str.regexp_case_fold re in
  try let _ = Str.search_forward re str 0 in true
  with Not_found -> false

type run_result = {
  exit_code: int;
  stdout: string;
  stderr: string;
}

let tmp_file prefix suffix =
  let tmpfile = Filename.temp_file prefix suffix in
  at_exit (fun () -> file_delete tmpfile);
  tmpfile

let open_tmp_file prefix suffix =
  let tmpfile, oc = Filename.open_temp_file prefix suffix in
  at_exit (fun () -> file_delete tmpfile);
  tmpfile, oc

(** [run_command cmd args] runs [cmd args] in the system shell, quoting all arguments.
  It captures exit code, standard out and standard error in a [run_result]. *)
let run_command cmd args =
    let tmp_stdout = tmp_file "stdout-" "" in
    let tmp_stderr = tmp_file "stderr-" "" in
    let command_line = Printf.sprintf "%s %s >%s 2>%s"
                                      cmd (String.concat " " (List.map Filename.quote args))
                                      tmp_stdout tmp_stderr in
    let exit_code = Sys.command command_line in
    let stdout = file_read tmp_stdout in
    let stderr = file_read tmp_stderr in
    { exit_code; stdout; stderr }

(*- #End *)

(*- #End_DEACTIVATED_CODE *)
