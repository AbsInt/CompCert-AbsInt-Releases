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

(* Processor-dependent builtin C functions *)

open C

let builtins = {
  builtin_typedefs = [
    "__builtin_va_list", TPtr(TVoid [], [])
  ];
  builtin_functions = [
    "__builtin_cadd",
      (TInt (IInt, []),[TInt(IInt, []);TInt(IInt, []);TInt(IInt, [])],false);
    "__builtin_csub",
      (TInt (IInt, []),[TInt(IInt, []);TInt(IInt, []);TInt(IInt, [])],false);
  ]
}

let va_list_type = TPtr(TVoid [], [])  (* to check! *)
let size_va_list = 4
let va_list_scalar = true

let asm_mem_argument arg = Printf.sprintf "0(%s)" arg

let asm_float_reg_cstr = None
