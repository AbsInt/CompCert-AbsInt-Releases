(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  AbsInt Angewandte Informatik GmbH. All rights reserved. This file  *)
(*  is distributed under the terms of the INRIA Non-Commercial         *)
(*  License Agreement.                                                 *)
(*                                                                     *)
(* *********************************************************************)

open Printf

(*- E_COMPCERT_CODE_Configuration_search_argv_001 *)
(*- #Justify_Derived "Utility function" *)
let search_argv key =
  let len = Array.length Commandline.argv in
  let res: string option ref = ref None in
  for i = 1 to len - 2 do
    if Commandline.argv.(i) = key then
      res := Some Commandline.argv.(i + 1);
  done;
  !res
(*- #End *)

(*- E_COMPCERT_CODE_Configuration_absolute_path_001 *)
(*- #Justify_Derived "Utility function" *)
let absolute_path base file =
  if Filename.is_relative file then
    Filename.concat base file
  else
    file
(*- #End *)

(* Locate the .ini file, which is either in the same directory as
  the executable or in the directory ../share *)

(*- E_COMPCERT_CODE_Configuration_ini_file_name_001 *)
(*- #Justify_Derived "Utility constant" *)
let ini_file_name =
  match search_argv "-conf" with
  | Some s -> absolute_path (Sys.getcwd ()) s
  | None ->
      try
        Sys.getenv "COMPCERT_CONFIG"
      with Not_found ->
        let ini_name = match search_argv "-target" with
        | Some s -> s^".ini"
        | None -> "compcert.ini" in
        let exe_dir = Filename.dirname Sys.executable_name in
        let share_dir =
          Filename.concat (Filename.concat exe_dir Filename.parent_dir_name)
            "share" in
        let share_compcert_dir =
          Filename.concat share_dir "compcert" in
        let search_path = [exe_dir;share_dir;share_compcert_dir] in
        let files = List.map (fun s -> Filename.concat s ini_name) search_path in
        try
          List.find  Sys.file_exists files
        with Not_found ->
          begin
            eprintf "Cannot find compcert.ini configuration file.\n";
            exit 2
          end
(*- #End *)

(*- E_COMPCERT_CODE_Configuration_ini_dir_001 *)
(*- #Justify_Derived "Utility constant" *)
let ini_dir = Filename.dirname ini_file_name
(*- #End *)

(* Read in the .ini file *)

(*- E_COMPCERT_CODE_Configuration_Readconfig_001 *)
(*- #Justify_Derived "Initializer" *)
let _ =
  try
    Readconfig.read_config_file ini_file_name
  with
  | Readconfig.Error(file, lineno, msg) ->
      eprintf "Error reading configuration file %s.\n" ini_file_name;
      eprintf "%s:%d:%s\n" file lineno msg;
      exit 2
  | Sys_error msg ->
      eprintf "Error reading configuration file %s.\n" ini_file_name;
      eprintf "%s\n" msg;
      exit 2
(*- #End *)

(*- E_COMPCERT_CODE_Configuration_re_ini_var_001 *)
(*- #Justify_Derived "Utility constant" *)
(* The ini var is not a valid file name at least under windows *)
let re_ini_var = Str.regexp_string "%<compcert_ini_dir>%"
(*- #End *)

(*- E_COMPCERT_CODE_Configuration_replace_ini_var_001 *)
(*- #Link_to E_COMPCERT_TR_Function_DRIVER_017 *)
let replace_ini_var vars =
  List.map (fun s -> Str.global_replace re_ini_var ini_dir s) vars
(*- #End *)

(*- E_COMPCERT_CODE_Configuration_get_config_001 *)
(*- #Justify_Derived "Utility function" *)
let get_config key =
  match Readconfig.key_val key with
  | Some v -> v
  | None -> eprintf "Configuration option `%s' is not set\n" key; exit 2
(*- #End *)

(*- E_COMPCERT_CODE_Configuration_bad_config_001 *)
(*- #Justify_Derived "Utility function" *)
let bad_config key vl =
  eprintf "Invalid value `%s' for configuration option `%s'\n"
          (String.concat " " vl) key;
  exit 2
(*- #End *)

(*- E_COMPCERT_CODE_Configuration_get_config_string_001 *)
(*- #Justify_Derived "Utility function" *)
let get_config_string key =
  match get_config key with
  | [v] -> v
  | vl -> bad_config key vl
(*- #End *)

(*- E_COMPCERT_CODE_Configuration_get_config_list_001 *)
(*- #Justify_Derived "Utility function" *)
let get_config_list key =
  match get_config key with
  | [] -> bad_config key []
  | vl -> vl
(*- #End *)

(*- E_COMPCERT_CODE_Configuration_tool_absolute_path_001 *)
(*- #Justify_Derived "Utility function" *)
let tool_absolute_path tools =
  match tools with
  | [] -> []
  | tool::args ->
    let tool =
      if Filename.is_implicit tool && Filename.dirname tool = Filename.current_dir_name then
        tool
      else
        absolute_path ini_dir tool in
    tool :: args
(*- #End *)

(*- E_COMPCERT_CODE_Configuration_opt_config_list_001 *)
(*- #Justify_Derived "Utility function" *)
let opt_config_list key =
  match Readconfig.key_val key with
  | Some v -> replace_ini_var v
  | None -> []
(*- #End *)

(*- E_COMPCERT_CODE_Configuration_prepro_001 *)
(*- #Link_to E_COMPCERT_TR_Function_PREPROCESSING_001 *)
(*- #Link_to E_COMPCERT_TR_Function_PREPROCESSING_002 *)
(*- #Link_to E_COMPCERT_TR_Function_DRIVER_017 *)
let prepro =
  tool_absolute_path (get_config_list "prepro")@(opt_config_list "prepro_options")
(*- #End *)

(*- E_COMPCERT_CODE_Configuration_asm_001 *)
(*- #Link_to E_COMPCERT_TR_Function_ASSEMBLING_001 *)
(*- #Link_to E_COMPCERT_TR_Function_ASSEMBLING_002 *)
(*- #Link_to E_COMPCERT_TR_Function_DRIVER_017 *)
let asm =
  tool_absolute_path (get_config_list "asm")@(opt_config_list "asm_options")
(*- #End *)

(*- E_COMPCERT_CODE_Configuration_linker_001 *)
(*- #Link_to E_COMPCERT_TR_Function_LINKING_001 *)
(*- #Link_to E_COMPCERT_TR_Function_LINKING_002 *)
(*- #Link_to E_COMPCERT_TR_Function_DRIVER_017 *)
let linker =
  tool_absolute_path (get_config_list "linker")@(opt_config_list "linker_options")
(*- #End *)

(*- E_COMPCERT_CODE_Configuration_get_bool_config_001 *)
(*- #Justify_Derived "Utility function" *)
let get_bool_config key =
  match get_config_string key with
  | "true" -> true
  | "false" -> false
  | v -> bad_config key [v]
(*- #End *)

(*- E_COMPCERT_CODE_Configuration_arch_001 *)
(*- #Justify_Derived "Configuration constant" *)
let arch =
  match get_config_string "arch" with
  | "powerpc"|"arm"|"x86"|"riscV"|"aarch64" as a -> a
  | v -> bad_config "arch" [v]
(*- #End *)

(*- E_COMPCERT_CODE_Configuration_model_001 *)
(*- #Justify_Derived "Configuration constant" *)
let model = get_config_string "model"
(*- #End *)

(*- E_COMPCERT_CODE_Configuration_abi_001 *)
(*- #Justify_Derived "Configuration constant" *)
let abi = get_config_string "abi"
(*- #End *)

(*- E_COMPCERT_CODE_Configuration_is_big_endian_001 *)
(*- #Justify_Derived "Configuration constant" *)
let is_big_endian =
  match get_config_string "endianness" with
  | "big" -> true
  | "little" -> false
  | v -> bad_config "endianness" [v]
(*- #End *)

(*- E_COMPCERT_CODE_Configuration_system_001 *)
(*- #Justify_Derived "Configuration constant" *)
let system = get_config_string "system"
(*- #End *)

(*- E_COMPCERT_CODE_Configuration_has_runtime_lib_001 *)
(*- #Justify_Derived "Configuration constant" *)
let has_runtime_lib = get_bool_config "has_runtime_lib"
(*- #End *)

(*- E_COMPCERT_CODE_Configuration_has_standard_headers_001 *)
(*- #Justify_Derived "Configuration constant" *)
let has_standard_headers = get_bool_config "has_standard_headers"
(*- #End *)

(*- E_COMPCERT_CODE_Configuration_stdlib_path_001 *)
(*- #Justify_Derived "Configuration constant" *)
let stdlib_path =
  if has_runtime_lib then
    let path = get_config_string "stdlib_path" in
    absolute_path ini_dir path
  else
    ""
(*- #End *)

(*- E_COMPCERT_CODE_Configuration_asm_supports_cfi_001 *)
(*- #Justify_Derived "Configuration constant" *)
let asm_supports_cfi = get_bool_config "asm_supports_cfi"
(*- #End *)

(*- E_COMPCERT_CODE_Configuration_response_file_style_001 *)
(*- #Justify_Derived "Configuration constant" *)
type response_file_style =
  | Gnu         (* responsefiles in gnu compatible syntax *)
  | Diab        (* responsefiles in diab compatible syntax *)
  | Unsupported (* responsefiles are not supported *)
(*- #End *)

(*- E_COMPCERT_CODE_Configuration_response_file_style_002 *)
(*- #Justify_Derived "Configuration constant" *)
let response_file_style =
  match get_config_string "response_file_style" with
  | "unsupported" -> Unsupported
  | "gnu" -> Gnu
  | "diab" -> Diab
  | v -> bad_config "response_file_style" [v]
(*- #End *)

(*- E_COMPCERT_CODE_Configuration_gnu_toolchain_001 *)
(*- #Justify_Derived "Configuration constant" *)
let gnu_toolchain = system <> "diab"
(*- #End *)

(*- E_COMPCERT_CODE_Configuration_elf_target_001 *)
(*- #Justify_Derived "Configuration constant" *)
let elf_target = system <> "macos" && system <> "cygwin"
(*- #End *)
