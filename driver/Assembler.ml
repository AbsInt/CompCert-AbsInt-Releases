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

open Clflags
open Commandline
open Driveraux

(* From asm to object file *)

(*- E_COMPCERT_CODE_Assembler_assemble_001 *)
(*- #Link_to E_COMPCERT_TR_Function_ASSEMBLING_001 *)
(*- #Link_to E_COMPCERT_TR_Function_ASSEMBLING_002 *)
let assemble ifile ofile =
  Diagnostics.raise_on_errors ();
  let cmd = List.concat [
    Configuration.asm;
    ["-o"; ofile];
    List.rev !assembler_options;
    [ifile]
  ] in
  let exc = command cmd in
  if exc <> 0 then begin
    safe_remove ofile;
    command_error "assembler" exc
  end
(*- #End *)

(*- E_COMPCERT_CODE_Assembler_assembler_actions_001 *)
(*- #Link_to E_COMPCERT_TR_Function_ASSEMBLING_003 *)
(*- #Link_to E_COMPCERT_TR_Function_DRIVER_001 *)
let assembler_actions =
 [ Prefix "-Wa,", Self (fun s -> if Configuration.gnu_toolchain then
    assembler_options := s :: !assembler_options
  else
    assembler_options := List.rev_append (explode_comma_option s) !assembler_options);
  Exact "-Xassembler", String (fun s -> if Configuration.gnu_toolchain then
    assembler_options := s::"-Xassembler":: !assembler_options
  else
    assembler_options := s::!assembler_options );]
(*- #End *)

(*- E_COMPCERT_CODE_Assembler_assembler_help_001 *)
(*- #Justify_Derived "Utility constant" *)
let assembler_help =
{|Assembling options:
  -Wa,<opt>      Pass option <opt> to the assembler
  -Xassembler <opt> Pass <opt> as an option to the assembler
|}
(*- #End *)
