(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Management of errors and warnings *)

open Format
open Commandline

(* Ensure that the error formatter is flushed at exit *)
(*- E_COMPCERT_CODE_Diagnostics_err_formatter_flush_001 *)
(*- #Justify_Derived "Initializer" *)
let _ =
  at_exit (pp_print_flush err_formatter)
(*- #End *)

(* Should errors be treated as fatal *)
(*- E_COMPCERT_CODE_Diagnostics_error_fatal_001 *)
(*- #Justify_Derived "Variable for global state" *)
let error_fatal = ref false
(*- #End *)

(* Maximum number of errors, 0 means unlimited *)
(*- E_COMPCERT_CODE_Diagnostics_max_error_001 *)
(*- #Justify_Derived "Variable for global state" *)
let max_error = ref 0
(*- #End *)

(* Whether [-Woption] should be printed *)
(*- E_COMPCERT_CODE_Diagnostics_diagnostics_show_option_001 *)
(*- #Justify_Derived "Variable for global state" *)
let diagnostics_show_option = ref true
(*- #End *)

(* Test if color diagnostics are available by testing if stderr is a tty
   and if the environment variable TERM is set
*)
(*- E_COMPCERT_CODE_Diagnostics_color_diagnostics_001 *)
(*- #Justify_Derived "Variable for global state" *)
let color_diagnostics =
  let term = try Sys.getenv "TERM" with Not_found -> "" in
  let activate = try
      (Unix.isatty Unix.stderr && term <> "dumb" && term <>"")
    with _ -> false in
  ref activate
(*- #End *)

(*- E_COMPCERT_CODE_Diagnostics_num_errors_001 *)
(*- #Justify_Derived "Variable for global state" *)
let num_errors = ref 0
(*- #End *)

(*- E_COMPCERT_CODE_Diagnostics_num_warnings_001 *)
(*- #Justify_Derived "Variable for global state" *)
let num_warnings = ref 0
(*- #End *)

(*- E_COMPCERT_CODE_Diagnostics_error_limit_reached_001 *)
(*- #Justify_Derived "Utility function" *)
let error_limit_reached  () =
  let max_err = !max_error in
  max_err <> 0 && !num_errors >= max_err - 1
(*- #End *)

(*- E_COMPCERT_CODE_Diagnostics_reset_001 *)
(*- #Justify_Derived "Utility function" *)
let reset () = num_errors := 0; num_warnings := 0
(*- #End *)

exception Abort

(* [fatal_error_raw] is identical to [fatal_error], except it uses [Printf]
   to print its message, as opposed to [Format], and does not automatically
   introduce indentation and a final dot into the message. This is useful
   for multi-line messages. *)

(*- E_COMPCERT_CODE_Diagnostics_fatal_error_raw_001 *)
(*- #Justify_Derived "Utility function" *)
let fatal_error_raw fmt =
  incr num_errors;
  Printf.kfprintf
    (fun _ -> raise Abort)
    stderr
    (fmt ^^ "Fatal error; compilation aborted.\n%!")
(*- #End *)

(*- E_COMPCERT_CODE_Diagnostics_msg_class_001 *)
(*- #Justify_Derived "Type definition" *)
type msg_class =
  | WarningMsg
  | ErrorMsg
  | FatalErrorMsg
  | SuppressedMsg
(*- #End *)

(*- E_COMPCERT_CODE_Diagnostics_warning_type_001 *)
(*- #Justify_Derived "Type definition" *)
type warning_type =
  | Unnamed
  | Unknown_attribute
  | Zero_length_array
  | Celeven_extension
  | Gnu_empty_struct
  | Missing_declarations
  | Constant_conversion
  | Int_conversion
  | Varargs
  | Implicit_function_declaration
  | Pointer_type_mismatch
  | Compare_distinct_pointer_types
  | Implicit_int
  | Main_return_type
  | Invalid_noreturn
  | Return_type
  | Literal_range
  | Unknown_pragmas
  | CompCert_conformance
  | Inline_asm_sdump
  | Unused_variable
  | Unused_parameter
  | Wrong_ais_parameter
  | Unused_ais_parameter
  | Ignored_attributes
  | Extern_after_definition
  | Static_in_inline
  | Flexible_array_extensions
  | Tentative_incomplete_static
  | Reduced_alignment
  | Non_linear_cond_expr
(*- #End *)

(* List of all warnings with default status.
   "true" means the warning is active by default.
   "false" means the warning is off by default. *)
(*- E_COMPCERT_CODE_Diagnostics_all_warnings_001 *)
(*- #Justify_Derived "Utility constant" *)
let all_warnings =
  [ (Unnamed, true);
    (Unknown_attribute, true);
    (Zero_length_array, false);
    (Celeven_extension, false);
    (Gnu_empty_struct, true);
    (Missing_declarations, true);
    (Constant_conversion, true);
    (Int_conversion, true);
    (Varargs, true);
    (Implicit_function_declaration, true);
    (Pointer_type_mismatch, true);
    (Compare_distinct_pointer_types, true);
    (Implicit_int, true);
    (Main_return_type, true);
    (Invalid_noreturn, true);
    (Return_type, true);
    (Literal_range, true);
    (Unknown_pragmas, false);
    (CompCert_conformance, false);
    (Inline_asm_sdump, true);
    (Unused_variable, false);
    (Unused_parameter, false);
    (Wrong_ais_parameter, true);
    (Unused_ais_parameter, true);
    (Ignored_attributes, true);
    (Extern_after_definition, true);
    (Static_in_inline, true);
    (Flexible_array_extensions, false);
    (Tentative_incomplete_static, false);
    (Reduced_alignment, false);
    (Non_linear_cond_expr, false);
  ]
(*- #End *)

(* List of active warnings *)
(*- E_COMPCERT_CODE_Diagnostics_active_warnings_001 *)
(*- #Justify_Derived "Utility constant" *)
let active_warnings: warning_type list ref =
  ref (List.map fst (List.filter snd all_warnings))
(*- #End *)

(* List of errors treated as warning *)
(*- E_COMPCERT_CODE_Diagnostics_error_warnings_001 *)
(*- #Justify_Derived "Utility constant" *)
let error_warnings: warning_type list ref = ref []
(*- #End *)

(* Conversion from warning type to string *)
(*- E_COMPCERT_CODE_Diagnostics_string_of_warning_001 *)
(*- #Justify_Derived "Utility function" *)
let string_of_warning = function
  | Unnamed -> ""
  | Unknown_attribute -> "unknown-attributes"
  | Zero_length_array -> "zero-length-array"
  | Celeven_extension -> "c11-extensions"
  | Gnu_empty_struct -> "gnu-empty-struct"
  | Missing_declarations -> "missing-declarations"
  | Constant_conversion -> "constant-conversion"
  | Int_conversion -> "int-conversion"
  | Varargs -> "varargs"
  | Implicit_function_declaration -> "implicit-function-declaration"
  | Pointer_type_mismatch -> "pointer-type-mismatch"
  | Compare_distinct_pointer_types -> "compare-distinct-pointer-types"
  | Implicit_int -> "implicit-int"
  | Main_return_type -> "main-return-type"
  | Invalid_noreturn -> "invalid-noreturn"
  | Return_type -> "return-type"
  | Literal_range -> "literal-range"
  | Unknown_pragmas -> "unknown-pragmas"
  | CompCert_conformance -> "compcert-conformance"
  | Inline_asm_sdump -> "inline-asm-sdump"
  | Unused_variable -> "unused-variable"
  | Unused_parameter -> "unused-parameter"
  | Wrong_ais_parameter -> "wrong-ais-parameter"
  | Unused_ais_parameter -> "unused-ais-parameter"
  | Ignored_attributes -> "ignored-attributes"
  | Extern_after_definition -> "extern-after-definition"
  | Static_in_inline -> "static-in-inline"
  | Flexible_array_extensions -> "flexible-array-extensions"
  | Tentative_incomplete_static -> "tentative-incomplete-static"
  | Reduced_alignment -> "reduced-alignment"
  | Non_linear_cond_expr -> "non-linear-cond-expr"
(*- #End *)

(* Activate the given warning *)
(*- E_COMPCERT_CODE_Diagnostics_activate_warning_001 *)
(*- #Justify_Derived "Utility function" *)
let activate_warning w () =
  if not (List.mem w !active_warnings) then
    active_warnings:=w::!active_warnings
(*- #End *)

(* Deactivate the given warning*)
(*- E_COMPCERT_CODE_Diagnostics_deactivate_warning_001 *)
(*- #Justify_Derived "Utility function" *)
let deactivate_warning w  () =
  active_warnings:=List.filter ((<>) w) !active_warnings;
  error_warnings:= List.filter ((<>) w) !error_warnings
(*- #End *)

(* Activate error for warning *)
(*- E_COMPCERT_CODE_Diagnostics_warning_as_error_001 *)
(*- #Justify_Derived "Utility function" *)
let warning_as_error w ()=
  activate_warning w ();
  if not (List.mem w !error_warnings) then
    error_warnings := w::!error_warnings
(*- #End *)

(* Deactivate error for warning *)
(*- E_COMPCERT_CODE_Diagnostics_warning_not_as_error_001 *)
(*- #Justify_Derived "Utility function" *)
let warning_not_as_error w () =
  error_warnings:= List.filter ((<>) w) !error_warnings
(*- #End *)

(* Activate all warnings *)
(*- E_COMPCERT_CODE_Diagnostics_wall_001 *)
(*- #Justify_Derived "Utility function" *)
let wall () =
  active_warnings:= List.map fst all_warnings
(*- #End *)

(*- E_COMPCERT_CODE_Diagnostics_wnothing_001 *)
(*- #Justify_Derived "Utility function" *)
let wnothing () =
  active_warnings :=[]
(*- #End *)

(* Make all warnings an error *)
(*- E_COMPCERT_CODE_Diagnostics_werror_001 *)
(*- #Justify_Derived "Utility function" *)
let werror () =
  error_warnings:= List.map fst all_warnings
(*- #End *)

(* Generate the warning key for the message *)
(*- E_COMPCERT_CODE_Diagnostics_key_of_warning_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let key_of_warning w =
  match w with
  | Unnamed -> None
  | _ -> if !diagnostics_show_option then
      Some ("-W"^(string_of_warning w))
    else
      None
(*- #End *)

(* Add -Werror to the printed keys *)
(*- E_COMPCERT_CODE_Diagnostics_key_add_werror_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let key_add_werror w =
  if !diagnostics_show_option then
    match w with
    | None -> Some ("-Werror")
    | Some s -> Some ("-Werror,"^s)
  else
    None
(*- #End *)

(* Lookup how to print the warning *)
(*- E_COMPCERT_CODE_Diagnostics_classify_warning_001 *)
(*- #Justify_Derived "Utility function" *)
let classify_warning w =
  let key = key_of_warning w in
  if List.mem w !active_warnings then
    if List.mem w !error_warnings then
      let key = key_add_werror key in
      if !error_fatal then
        FatalErrorMsg,key
      else
        ErrorMsg,key
    else
      WarningMsg,key
  else
    SuppressedMsg,None
(*- #End *)

(* Print color codes if color_diagnostics are enabled *)
(*- E_COMPCERT_CODE_Diagnostics_cprintf_001 *)
(*- #Justify_Derived "Utility function" *)
let cprintf fmt c =
  if !color_diagnostics then
    fprintf fmt c
  else
    ifprintf fmt c
(*- #End *)

(* Reset color codes *)
(*- E_COMPCERT_CODE_Diagnostics_color_rsc_001 *)
(*- #Justify_Derived "Utility function" *)
let rsc fmt =
  cprintf fmt "\x1b[0m"
(*- #End *)

(* BOLD *)
(*- E_COMPCERT_CODE_Diagnostics_color_bc_001 *)
(*- #Justify_Derived "Utility function" *)
let bc fmt =
  cprintf fmt "\x1b[1m"
(*- #End *)

(* RED *)
(*- E_COMPCERT_CODE_Diagnostics_color_rc_001 *)
(*- #Justify_Derived "Utility function" *)
let rc fmt =
  cprintf fmt "\x1b[31;1m"
(*- #End *)

(* MAGENTA *)
(*- E_COMPCERT_CODE_Diagnostics_color_mc_001 *)
(*- #Justify_Derived "Utility function" *)
let mc fmt  =
  cprintf fmt "\x1b[35;1m"
(*- #End *)

(* Print key (if available) and flush the formatter *)
(*- E_COMPCERT_CODE_Diagnostics_pp_key_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_key key fmt =
  let key = match key with
  | None -> ""
  | Some s -> " ["^s^"]" in
  fprintf fmt "%s%t@." key rsc
(*- #End *)

(* Different loc output formats *)
(*- E_COMPCERT_CODE_Diagnostics_loc_format_001 *)
(*- #Justify_Derived "Type definition" *)
type loc_format =
  | Default
  | MSVC
  | Vi
(*- #End *)

(*- E_COMPCERT_CODE_Diagnostics_diagnostics_format_001 *)
(*- #Justify_Derived "Variable for global state" *)
let diagnostics_format : loc_format ref = ref Default
(*- #End *)

(* Parse the option string *)
(*- E_COMPCERT_CODE_Diagnostics_parse_loc_format_001 *)
(*- #Justify_Derived "Utility function" *)
let parse_loc_format s =
  let s = String.sub s 21 ((String.length s) - 21) in
  let loc_fmt = match s with
  | "ccomp" -> Default
  | "msvc" -> MSVC
  | "vi" -> Vi
  | s -> Printf.eprintf "Invalid value '%s' in '-fdiagnostics-format=%s'\n" s s; exit 2 in
  diagnostics_format := loc_fmt
(*- #End *)

(* Print the location or ccomp for the case of unknown loc *)
(*- E_COMPCERT_CODE_Diagnostics_pp_loc_001 *)
(*- #Link_to E_COMPCERT_TR_Function_DIAGNOSTICS_FORMAT_001 *)
let pp_loc fmt (filename,lineno) =
  let lineno = if lineno = -10 then "" else
    match !diagnostics_format with
      | Default -> sprintf ":%d" lineno
      | MSVC -> sprintf "(%d)" lineno
      | Vi -> sprintf " +%d" lineno in
  if filename <> "" && filename <> "cabs loc unknown" then
    fprintf fmt "%t%s%s:%t " bc filename lineno rsc
  else
    fprintf fmt "%tccomp:%t " bc rsc
(*- #End *)

(*- E_COMPCERT_CODE_Diagnostics_error_001 *)
(*- #Link_to E_COMPCERT_TR_Function_DIAGNOSTICS_FORMAT_001 *)
let error key loc fmt =
  incr num_errors;
  kfprintf (pp_key key)
    err_formatter ("%a%terror:%t %t" ^^ fmt) pp_loc loc rc rsc bc
(*- #End *)

(*- E_COMPCERT_CODE_Diagnostics_fatal_error_001 *)
(*- #Link_to E_COMPCERT_TR_Function_DIAGNOSTICS_FORMAT_001 *)
let fatal_error key loc fmt =
  incr num_errors;
  kfprintf
    (fun fmt -> pp_key key fmt;raise Abort)
    err_formatter ("%a%terror:%t %t" ^^ fmt) pp_loc loc rc rsc bc
(*- #End *)

(*- E_COMPCERT_CODE_Diagnostics_warning_001 *)
(*- #Link_to E_COMPCERT_TR_Function_DIAGNOSTICS_FORMAT_001 *)
let warning loc ty fmt =
  let kind,key = classify_warning ty in
  match kind with
  | ErrorMsg ->
      error key loc fmt
  | FatalErrorMsg ->
      fatal_error key loc fmt
  | WarningMsg ->
      incr num_warnings;
      kfprintf (pp_key key)
        err_formatter ("%a%twarning:%t %t" ^^ fmt) pp_loc loc mc rsc bc
  | SuppressedMsg -> ifprintf err_formatter fmt
(*- #End *)

(*- E_COMPCERT_CODE_Diagnostics_error_002 *)
(*- #Justify_Derived "Utility function" *)
let error loc fmt =
  if !error_fatal || error_limit_reached ()then
    fatal_error None loc fmt
  else
    error None loc fmt
(*- #End *)

(*- E_COMPCERT_CODE_Diagnostics_fatal_error_002 *)
(*- #Justify_Derived "Utility function" *)
let fatal_error loc fmt =
  fatal_error None loc fmt
(*- #End *)

(*- E_COMPCERT_CODE_Diagnostics_error_summary_001 *)
(*- #Justify_Derived "Utility function" *)
let error_summary () =
 if !num_errors > 0 then begin
    eprintf "@[<hov 0>%d error%s detected.@]@."
            !num_errors
            (if !num_errors = 1 then "" else "s");
    num_errors := 0;
  end
(*- #End *)

(*- E_COMPCERT_CODE_Diagnostics_check_errors_001 *)
(*- #Justify_Derived "Utility function" *)
let check_errors () =
  if !num_errors > 0 then begin
    eprintf "@[<hov 0>%d error%s detected.@]@."
            !num_errors
            (if !num_errors = 1 then "" else "s");
    num_errors := 0;
    raise Abort
  end
(*- #End *)

(*- E_COMPCERT_CODE_Diagnostics_error_option_001 *)
(*- #Justify_Derived "Utility function" *)
let error_option w =
  let key = string_of_warning w in
  [Exact ("-W"^key), Unit (activate_warning w);
   Exact ("-Wno-"^key), Unit (deactivate_warning w);
   Exact ("-Werror="^key), Unit (warning_as_error w);
   Exact ("-Wno-error="^key), Unit ( warning_not_as_error w)]
(*- #End *)

(*- E_COMPCERT_CODE_Diagnostics_warning_options_001 *)
(*- #Justify_Derived "Utility constant" *)
let warning_options =
  List.concat (List.map (fun (w, active) -> error_option w) all_warnings) @
  [Exact ("-Wfatal-errors"), Set error_fatal;
   Exact ("-fdiagnostics-color"), Ignore; (* Either output supports it or no color *)
   Exact ("-fno-diagnostics-color"), Unset color_diagnostics;
   Exact ("-Werror"), Unit werror;
   Exact ("-Wall"), Unit wall;
   Exact ("-w"), Unit wnothing;
   longopt_int ("-fmax-errors") ((:=) max_error);
   Exact("-fno-diagnostics-show-option"),Unset diagnostics_show_option;
   Exact("-fdiagnostics-show-option"),Set diagnostics_show_option;
   _Regexp("-fdiagnostics-format=\\(ccomp\\|msvc\\|vi\\)"),Self parse_loc_format;
  ]
(*- #End *)

(*- E_COMPCERT_CODE_Diagnostics_warning_help_001 *)
(*- #Justify_Derived "Utility constant" *)
let warning_help = {|Diagnostic options:
  -Wall              Enable all warnings
  -W<warning>        Enable the specific <warning>
  -Wno-<warning>     Disable the specific <warning>
  -Werror            Make all warnings into errors
  -Werror=<warning>  Turn <warning> into an error
  -Wno-error=<warning> Turn <warning> into a warning even if -Werror is
                       specified
  -Wfatal-errors     Turn all errors into fatal errors aborting the compilation
  -fdiagnostics-color Turn on colored diagnostics
  -fno-diagnostics-color Turn of colored diagnostics
  -fmax-errors=<n>   Maximum number of errors to report
  -fdiagnostics-show-option Print the option name with mappable diagnostics
  -fno-diagnostics-show-option Turn of printing of options with mappable
                               diagnostics
|}
(*- #End *)

(*- E_COMPCERT_CODE_Diagnostics_raise_on_errors_001 *)
(*- #Justify_Derived "Utility function" *)
let raise_on_errors () =
  if !num_errors > 0 then
    raise Abort
(*- #End *)

(*- E_COMPCERT_CODE_Diagnostics_crash_001 *)
(*- #Justify_Derived "Utility function" *)
let crash exn =
  if Version.buildnr <> "" && Version.tag <> "" && Version.branch <> "" then begin
    let backtrace = Printexc.get_backtrace () in
    eprintf "%tThis is CompCert, Release %s, Build:%s, Tag:%s, Branch:%s%t\n"
      bc Version.version Version.buildnr Version.tag Version.branch rsc;
    eprintf "Backtrace (please include this in your support request):\n%s"
      backtrace;
    eprintf "%tUncaught exception: %s.\n\
\    Please report this problem to our support.\n\
\    Error occurred in Build: %s, Tag: %s, Branch %s.\n%t"
      rc (Printexc.to_string exn) Version.buildnr Version.tag Version.branch rsc;
    exit 2
  end else begin
    let backtrace = Printexc.get_backtrace ()
    and exc = Printexc.to_string exn in
    eprintf "Fatal error: uncaught exception %s\n%s" exc backtrace;
    exit 2
  end
(*- #End *)

(*- E_COMPCERT_CODE_Diagnostics_no_loc_001 *)
(*- #Justify_Derived "Utility constant" *)
let no_loc = ("", -1)
(*- #End *)

(*- E_COMPCERT_CODE_Diagnostics_file_loc_001 *)
(*- #Justify_Derived "Utility function" *)
let file_loc file = (file,-10)
(*- #End *)

(*- E_COMPCERT_CODE_Diagnostics_active_warning_001 *)
(*- #Justify_Derived "Utility function" *)
let active_warning ty =
  fst (classify_warning ty) <> SuppressedMsg
(*- #End *)
