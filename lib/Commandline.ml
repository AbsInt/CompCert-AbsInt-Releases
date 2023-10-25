(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(* Parsing of command-line flags and arguments *)

open Printf

(*- E_COMPCERT_CODE_Commandline_pattern_001 *)
(*- #Justify_Derived "Type definition" *)
type pattern =
  | Exact of string
  | Prefix of string
  | Suffix of string
  | Regexp of Str.regexp
(*- #End *)

(*- E_COMPCERT_CODE_Commandline_Regexp_001 *)
(*- #Justify_Derived "Utility function" *)
let _Regexp re = Regexp (Str.regexp re)
(*- #End *)

(*- E_COMPCERT_CODE_Commandline_action_001 *)
(*- #Justify_Derived "Type definition" *)
type action =
  | Set of bool ref
  | Unset of bool ref
  | Self of (string -> unit)
  | String of (string -> unit)
  | Integer of (int -> unit)
  | Ignore
  | Unit of (unit -> unit)
(*- #End *)

exception CmdError of string

(*- E_COMPCERT_CODE_Commandline_match_pattern_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let match_pattern text = function
  | Exact s ->
      text = s
  | Prefix pref ->
      let lpref = String.length pref and ltext = String.length text in
      lpref < ltext && String.sub text 0 lpref = pref
      (* strict prefix: no match if pref = text. See below. *)
  | Suffix suff ->
      let lsuff = String.length suff and ltext = String.length text in
      lsuff < ltext && String.sub text (ltext - lsuff) lsuff = suff
      (* strict suffix: no match if suff = text, so that e.g. ".c"
         causes an error rather than being treated as a C source file. *)
  | Regexp re ->
      Str.string_match re text 0
(*- #End *)

(*- E_COMPCERT_CODE_Commandline_find_action_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let rec find_action text = function
  | [] -> None
  | (pat, act) :: rem ->
      if match_pattern text pat then Some act else find_action text rem
(*- #End *)

(*- E_COMPCERT_CODE_Commandline_parse_array_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let parse_array spec argv first last =
  (* Parse the vector of arguments *)
  let rec parse i =
    if i <= last then begin
      let s = argv.(i) in
      match find_action s spec with
      | None ->
        (*- #Link_to E_COMPCERT_TR_Robustness_DRIVER_004 *)
        let msg = sprintf "unknown argument `%s'" s in
        raise (CmdError msg)
      | Some(Set r) ->
          r := true; parse (i+1)
      | Some(Unset r) ->
          r := false; parse (i+1)
      | Some(Self fn) ->
          fn s; parse (i+1)
      | Some(String fn) ->
          if i + 1 <= last then begin
            fn argv.(i+1); parse (i+2)
          end else begin
            (*- #Link_to E_COMPCERT_TR_Robustness_DRIVER_003 *)
            let msg = sprintf "option `%s' expects an argument" s in
            raise (CmdError msg)
          end
      | Some(Integer fn) ->
          if i + 1 <= last then begin
            match int_of_string_opt argv.(i+1) with
            | Some n -> fn n; parse (i+2)
            | None ->
                (*- #Link_to E_COMPCERT_TR_Robustness_DRIVER_002 *)
                let msg = sprintf "argument to option `%s' must be an integer" s in
                raise (CmdError msg)
          end else begin
            (*- #Link_to E_COMPCERT_TR_Robustness_DRIVER_003 *)
            let msg = sprintf  "option `%s' expects an argument" s in
            raise (CmdError msg)
          end
      | Some (Ignore) ->
          if i + 1 <= last then begin
            parse (i+2)
          end else begin
            (*- #Link_to E_COMPCERT_TR_Robustness_DRIVER_003 *)
            let msg = sprintf "option `%s' expects an argument" s in
            raise (CmdError msg)
          end
      | Some (Unit f) -> f (); parse (i+1)
    end
  in parse first
(*- #End *)

(*- E_COMPCERT_CODE_Commandline_argv_001 *)
(*- #Justify_Derived "Variable for global state" *)
let argv =
  try
    Responsefile.expandargv Sys.argv
  with Responsefile.Error msg | Sys_error msg ->
    eprintf "Error while processing the command line: %s\n" msg;
    exit 2
(*- #End *)

(*- E_COMPCERT_CODE_Commandline_parse_cmdline_001 *)
(*- #Justify_Derived "Utility function" *)
let parse_cmdline spec =
  (* Exact patterns have precedence over inexact patterns *)
  let is_exact = function (Exact _, _) -> true | _ -> false in
  let (exact_cases, inexact_cases) = List.partition is_exact spec in
  let sorted_spec = exact_cases @ inexact_cases in
  parse_array sorted_spec argv 1 (Array.length argv - 1)
(*- #End *)

(*- E_COMPCERT_CODE_Commandline_longopt_001 *)
(*- #Justify_Derived "Utility function" *)
let longopt key f =
  let lkey = String.length key + 1 in
  let act s = f (String.sub s lkey (String.length s - lkey)) in
  (Prefix (key ^ "="), Self act)
(*- #End *)

(*- E_COMPCERT_CODE_Commandline_longopt_int_001 *)
(*- #Justify_Derived "Utility function" *)
let longopt_int key f =
  longopt key (fun s ->
    match int_of_string_opt s with
    | Some n -> f n
    | None ->
        (*- #Link_to E_COMPCERT_TR_Robustness_DRIVER_002 *)
        let msg =  sprintf "argument to option `%s' must be an integer" key in
        raise (CmdError msg))
(*- #End *)
