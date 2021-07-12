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

(* Handling of pragmas *)

open Camlcoq

(* #pragma section *)

(*- E_COMPCERT_CODE_CPragmas_process_section_pragma_001 *)
(*- #Link_to E_COMPCERT_TR_Function_CPRAGMAS_002 *)
let process_section_pragma classname istring ustring addrmode accmode =
  Sections.define_section classname
    ?iname: (if istring = "" then None else Some istring)
    ?uname: (if ustring = "" then None else Some ustring)
    ?writable:
      (if accmode = "" then None else Some(String.contains accmode 'W'))
    ?executable:
      (if accmode = "" then None else Some(String.contains accmode 'X'))
    ?access:
      (match addrmode with
       | "" -> None
       | "near-data" -> Some Sections.Access_near
       | "far-data" -> Some Sections.Access_far
       | _ -> Some Sections.Access_default)
    ()
(*- #End *)

(* #pragma use_section *)

(*- E_COMPCERT_CODE_CPragmas_re_c_ident_001 *)
(*- #Justify_Derived "Utility constant" *)
let re_c_ident = Str.regexp "[A-Za-z_][A-Za-z_0-9]*$"
(*- #End *)

(*- E_COMPCERT_CODE_CPragmas_process_use_section_pragma_001 *)
(*- #Link_to E_COMPCERT_TR_Function_CPRAGMAS_003 *)
let process_use_section_pragma classname id =
  if id = "," || id = ";" then () else begin
    if not (Str.string_match re_c_ident id 0) then
      (*- #Link_to E_COMPCERT_TR_Robustness_CPRAGMAS_006 *)
      C2C.error "bad identifier `%s' in #pragma use_section" id;
    if not (Sections.use_section_for (intern_string id) classname) then
      (*- #Link_to E_COMPCERT_TR_Robustness_CPRAGMAS_007 *)
      C2C.error "unknown section name `%s'" classname
  end
(*- #End *)

(* #pragma reserve_register *)

(*- E_COMPCERT_CODE_CPragmas_process_reserve_registers_001 *)
(*- #Justify_Derived "Variable for local state" *)
let reserved_registers = ref ([]: Machregs.mreg list)
(*- #End *)

(*- E_COMPCERT_CODE_CPragmas_process_reserve_register_pragma_001 *)
(*- #Link_to E_COMPCERT_TR_Function_CPRAGMAS_001 *)
let process_reserve_register_pragma name =
  match Machregsnames.register_by_name name with
  | None ->
      (*- #Link_to E_COMPCERT_TR_Robustness_CPRAGMAS_005 *)
      C2C.error "unknown register in `reserve_register' pragma"
  | Some r ->
      if Conventions1.is_callee_save r then
        reserved_registers := r :: !reserved_registers
      else
        (*- #Link_to E_COMPCERT_TR_Robustness_CPRAGMAS_005 *)
        C2C.error "cannot reserve this register (not a callee-save)"
(*- #End *)

(* Parsing of pragmas *)

(*- E_COMPCERT_CODE_CPragmas_process_pragma_001 *)
let process_pragma name =
  match Tokenize.string name with
  | ["section"; classname; istring; ustring; addrmode; accmode] ->
      process_section_pragma classname istring ustring addrmode accmode;
      true
  | ["section"; classname; istring; ustring; accmode] ->
      process_section_pragma classname istring ustring "" accmode;
      true
  | "section" :: _ ->
      (*- #Link_to E_COMPCERT_TR_Robustness_CPRAGMAS_004 *)
      C2C.error "ill-formed `section' pragma"; true
  | "use_section" :: classname :: identlist ->
      (*- #Link_to E_COMPCERT_TR_Function_CPRAGMAS_008 *)
      if identlist = [] then C2C.warning Diagnostics.Unnamed "empty `use_section' pragma";
      List.iter (process_use_section_pragma classname) identlist;
      true
  | "use_section" :: _ ->
      (*- #Link_to E_COMPCERT_TR_Robustness_CPRAGMAS_004 *)
      C2C.error "ill-formed `use_section' pragma"; true
  | ["reserve_register"; reg] ->
      process_reserve_register_pragma reg; true
  | "reserve_register" :: _ ->
      (*- #Link_to E_COMPCERT_TR_Robustness_CPRAGMAS_004 *)
      C2C.error "ill-formed `reserve_register' pragma"; true
  | _ ->
      false
(*- #End *)

(*- E_COMPCERT_CODE_CPragmas_reset_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let reset () =
  reserved_registers := []
(*- #End *)

(*- E_COMPCERT_CODE_CPragmas_initialize_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let initialize () =
  C2C.process_pragma_hook := process_pragma
(*- #End *)
