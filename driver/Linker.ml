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


(* Linking *)

(*- E_COMPCERT_CODE_Linker_001 *)
(*- #Justify_Derived "Utility function" *)
let linker exe_name files =
  Diagnostics.raise_on_errors ();
  let cmd = List.concat [
    (*- #Link_to E_COMPCERT_TR_Function_LINKING_001 *)
    Configuration.linker;
    ["-o"; exe_name];
    files;
    (*- #Link_to E_COMPCERT_TR_Function_LINKING_005 *)
    (if Configuration.has_runtime_lib
     then ["-L" ^ !stdlib_path; "-lcompcert"]
     else [])
  ] in
  let exc = command cmd in
  if exc <> 0 then begin
    command_error "linker" exc
  end
(*- #End *)

let gnu_linker_help =
{|  -nodefaultlibs Do not use the standard system libraries when
                 linking
  -nostdlib      Do not use the standard system startup files or
                 libraries when linking
|}

let linker_help =
{|Linking options:
  -l<lib>        Link library <lib>
  -L<dir>        Add <dir> to search path for libraries
  -nostartfiles  Do not use the standard system startup files when
                 linking
|} ^
 (if Configuration.gnu_toolchain then gnu_linker_help else "") ^
{|  -s             Remove all symbol table and relocation information from the
                 executable
  -static        Prevent linking with the shared libraries
  -T <file>      Use <file> as linker command file
  -Wl,<opt>      Pass option <opt> to the linker
  -WUl,<opt>     Pass option <opt> to the gcc or dcc used for linking
  -Xlinker <opt> Pass <opt> as an option to the linker
  -u <symb>      Pretend the symbol <symb> is undefined to force linking of
                 library modules to define it.
|}

(*- E_COMPCERT_CODE_Linker_actions_001 *)
(*- #Link_to E_COMPCERT_TR_Function_LINKING_003 *)
(*- #Link_to E_COMPCERT_TR_Function_LINKING_004 *)
(*- #Link_to E_COMPCERT_TR_Function_LINKING_006 *)
(*- #Link_to E_COMPCERT_TR_Function_DRIVER_001 *)
let linker_actions =
  [ Prefix "-l", Self push_linker_arg;
    Prefix "-L", Self push_linker_arg;
    Exact "-nostartfiles", Self (fun s  ->
        if Configuration.gnu_toolchain then
          push_linker_arg s
        else
          push_linker_arg "-Ws")
  ] @
  (if Configuration.gnu_toolchain then
    [ Exact "-nodefaultlibs", Self push_linker_arg;
      Exact "-nostdlib", Self push_linker_arg;]
  else []) @
  [ Exact "-s", Self push_linker_arg;
    Exact "-static", Self push_linker_arg;
    Exact "-T", String (fun s -> if Configuration.gnu_toolchain then begin
      push_linker_arg ("-T");
      push_linker_arg(s)
    end else
      push_linker_arg ("-Wm"^s));
    Exact "-Xlinker", String (fun s -> if Configuration.system = "diab" then
      push_linker_arg ("-Wl,"^s)
    else
      push_linker_arg s);
    Prefix "-Wl,", Self push_linker_arg;
    Prefix "-WUl,", Self (fun s -> List.iter push_linker_arg (explode_comma_option s));
    Exact "-u", String (fun s -> push_linker_arg "-u"; push_linker_arg s);]
(*- #End *)
