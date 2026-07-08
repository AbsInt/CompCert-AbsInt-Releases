(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open Printf
open Clflags
open Commandline

(* The version string for [tool_name] *)
(*- E_COMPCERT_CODE_version_string_001 *)
(*- #Justify_Derived "Utility function" *)
let version_string tool_name =
  if Version.buildnr <> "" && Version.tag <> "" && Version.branch <> "" then
    sprintf "The CompCert %s, Release: %s, Build: %s, Tag: %s, Branch: %s\n"
      tool_name Version.version Version.buildnr Version.tag Version.branch
  else
    sprintf "The CompCert %s, version %s\n" tool_name Version.version
(*- #End *)

(* Print the version string and exit the program *)
(*- E_COMPCERT_CODE_print_version_and_exit_001 *)
(*- #Justify_Derived "Utility function" *)
let print_version_and_exit tool_name () =
  printf "%s" (version_string tool_name); exit 0
(*- #End *)

(*- E_COMPCERT_CODE_version_file_string_001 *)
(*- #Justify_Derived "Utility function" *)
let version_file_string tool_name =
  if Version.buildnr <> "" && Version.tag <> "" then
    Printf.sprintf "This is CompCert %s\nVersion: %s\nBuild: %s\nTag: %s\nBranch: %s\n"
      tool_name Version.version Version.buildnr Version.tag Version.branch
  else
    Printf.sprintf "The CompCert %s,\nversion %s\n" tool_name Version.version
(*- #End *)

(* Print the version string to a file and exit the program *)
(*- E_COMPCERT_CODE_print_version_file_and_exit_001 *)
(*- #Justify_Derived "Utility function" *)
let print_version_file_and_exit tool_name file =
  let oc = open_out_bin file in
  output_string oc (version_file_string tool_name);
  close_out_noerr oc;
  exit 0
(*- #End *)

(* Print some additional configuation information in verbose mode *)
(*- E_COMPCERT_CODE_print_info_001 *)
(*- #Justify_Derived "Utility function" *)
let print_info tool_name =
  if !option_v then begin
    eprintf "+ Using configuration file: %s\n" Configuration.ini_file_name;
    eprintf "+ Target: %s\n" Configuration.arch;
    eprintf "+ Model: %s\n" Configuration.model;
    eprintf "+ ABI: %s\n" Configuration.abi;
    eprintf "+ System: %s\n" Configuration.system;
    eprintf "+ %s" (version_string tool_name)
  end
(*- #End *)

(*- E_COMPCERT_CODE_version_options_001 *)
(*- #Justify_Derived "Utility function" *)
let version_options tool_name =
  [ Exact "-version", Unit (print_version_and_exit tool_name);
    Exact "--version", Unit (print_version_and_exit tool_name);
    Exact "-version-file", String (print_version_file_and_exit tool_name);
    Exact "--version-file", String (print_version_file_and_exit tool_name);
  ]
(*- #End *)

(* Language support options *)

(*- E_COMPCERT_CODE_all_language_support_options_001 *)
(*- #Link_to E_COMPCERT_TR_Function_DRIVER_001 *)
let all_language_support_options = [
  option_flongdouble;
  option_fstruct_passing; option_fvararg_calls; option_funprototyped;
  option_fpacked_structs; option_finline_asm; option_funstructured_switch
]
(*- #End *)

(*- E_COMPCERT_CODE_f_opt_001 *)
(*- #Justify_Derived "Utility function" *)
let f_opt name ref =
    [Exact("-f" ^ name), Set ref; Exact("-fno-" ^ name), Unset ref]
(*- #End *)

(*- E_COMPCERT_CODE_f_set_char_signedness_001 *)
(*- #Justify_Derived "Utility function" *)
let f_set_char_signedness name sgn =
  [Exact("-f" ^ name), Unit (fun () -> Machine.(config := {!config with char_signed = sgn}));
   Exact("-fno-" ^ name), Unit (fun () -> Machine.(config := {!config with char_signed = not sgn}))]
(*- #End *)

(* Check that the size of the new integer kind is the same as the old one *)
(*- E_COMPCERT_CODE_ikind_check_001 *)
(*- #Link_to E_COMPCERT_TR_Robustness_DRIVER_020 *)
let ikind_check typ_name exp_name new_ikind exp_ikind =
  if Cutil.sizeof_ikind new_ikind <> Cutil.sizeof_ikind exp_ikind then
    raise (CmdError (sprintf "'%s' is not supported as type for '%s'"
      typ_name exp_name))
(*- #End *)

(*- E_COMPCERT_CODE_f_set_size_t_001 *)
(*- #Justify_Derived "Utility function" *)
let f_set_size_t name typ_name ikind =
  [Exact("-f" ^ name), Unit (fun () ->
       ikind_check typ_name "size_t" ikind (Cutil.size_t_ikind ());
       Machine.(config := {!config with size_t_ikind = ikind}))]
(*- #End *)

(*- E_COMPCERT_CODE_f_set_ptrdiff_t_001 *)
(*- #Justify_Derived "Utility function" *)
let f_set_ptrdiff_t name typ_name ikind =
  [Exact("-f" ^ name), Unit (fun () ->
       ikind_check typ_name "ptrdiff_t" ikind (Cutil.ptrdiff_t_ikind ());
       Machine.(config := {!config with ptrdiff_t_ikind = ikind}))]
(*- #End *)

(*- E_COMPCERT_CODE_set_all_001 *)
(*- #Justify_Derived "Utility function" *)
let set_all opts () = List.iter (fun r -> r := true) opts
(*- #End *)

(*- E_COMPCERT_CODE_unset_all_001 *)
(*- #Justify_Derived "Utility function" *)
let unset_all opts () = List.iter (fun r -> r := false) opts
(*- #End *)

(*- E_COMPCERT_CODE_set_std_001 *)
(*- #Link_to E_COMPCERT_TR_Robustness_DRIVER_019 *)
let set_std s =
  let s = String.lowercase_ascii s in
  option_std := s;
  match s with
  | "c99" ->
      Diagnostics.(activate_warning Celeven_extension ())
  | "c11" | "c18" ->
      Diagnostics.(deactivate_warning Celeven_extension ())
  | _ ->
      raise (CmdError (sprintf
                         "wrong -std option: unknown standard '%s'" s))
(*- #End *)

(*- E_COMPCERT_CODE_language_support_options_001 *)
(*- #Justify_Derived "Utility constant" *)
let language_support_options =
  [ longopt "-std" set_std;
    Exact "-fall", Unit (set_all all_language_support_options);
    Exact "-fnone", Unit (unset_all all_language_support_options);
    Exact "-fbitfields", Unit (fun () -> ()); ]
  @ f_opt "longdouble" option_flongdouble
  @ f_opt "struct-passing" option_fstruct_passing
  @ f_opt "vararg-calls" option_fvararg_calls
  @ f_opt "unprototyped" option_funprototyped
  @ f_opt "unstructured-switch" option_funstructured_switch
  @ f_opt "packed-structs" option_fpacked_structs
  @ f_opt "inline-asm" option_finline_asm
  @ f_set_char_signedness "signed-char" true
  @ f_set_char_signedness "unsigned-char" false
  @ f_set_size_t "size_t-int" "unsigned int" C.IUInt
  @ f_set_size_t "size_t-long" "unsigned long" C.IULong
  @ f_set_size_t "size_t-long-long" "unsigned long long" C.IULongLong
  @ f_set_ptrdiff_t "ptrdiff_t-int" "signed int" C.IInt
  @ f_set_ptrdiff_t "ptrdiff_t-long" "signed long" C.ILong
  @ f_set_ptrdiff_t "ptrdiff_t-long-long" "signed long long" C.ILongLong
(*- #End *)

(*- E_COMPCERT_CODE_language_support_help_001 *)
(*- #Justify_Derived "Utility constant" *)
let language_support_help =
  {|Language support options (use -fno-<opt> to turn off -f<opt>) :
  -std=c99  or  -std=c11  or  -std=c18
                 Choose the ISO C language standard used: C99, C11, or C18.
  -flongdouble   Treat 'long double' as 'double' [off]
  -fstruct-passing  Support passing structs and unions by value as function
                    results or function arguments [off]
  -fvararg-calls Support calls to variable-argument functions [on]
  -funprototyped Support calls to old-style functions without prototypes [on]
  -funstructured-switch Support non-structured 'switch' statements [off]
  -fpacked-structs  Emulate packed structs [off]
  -finline-asm   Support inline 'asm' statements [off]
  -fall          Activate all language support options above
  -fnone         Turn off all language support options above
  -fbitfields    Ignored (bit fields are now implemented natively)
  -fsigned-char  Make 'char' signed by default
  -funsigned-char Make 'char' unsigned by default
  -fsize_t-int   Use 'unsigned int' as type for 'size_t'
  -fsize_t-long  Use 'unsigned long' as type for 'size_t'
  -fsize_t-long-long Use 'unsigned long long' as type for 'size_t'
  -fptrdiff_t-int   Use 'signed int' as type for 'ptrdiff_t'
  -fptrdiff_t-long  Use 'signed long' as type for 'ptrdiff_t'
  -fptrdiff_t-long-long Use 'signed long long' as type for 'ptrdiff_t'
|}
(*- #End *)


(* General options *)

(*- E_COMPCERT_CODE_general_help_001 *)
(*- #Justify_Derived "Utility constant" *)
let general_help =
  {|General options:
  -stdlib <dir>  Set the path of the Compcert run-time library
  -v             Print external commands before invoking them
  -timings       Show the time spent in various compiler passes
  -version       Print the version string and exit
  -version-file <file> Print version inforation to <file> and exit
  -target <value> Generate code for the given target
  -conf <file>   Read configuration from file
  @<file>        Read command line options from <file>
|}
(*- #End *)

(*- E_COMPCERT_CODE_general_options_001 *)
(*- #Justify_Derived "Utility constant" *)
let general_options =
  [ Exact "-conf", Ignore; (* Ignore option since it is already handled *)
    Exact "-target", Ignore;(* Ignore option since it is already handled *)
    Exact "-v", Set option_v;
    Exact "-stdlib", String(fun s -> stdlib_path := s);
    Exact "-timings", Set option_timings;]
(*- #End *)
