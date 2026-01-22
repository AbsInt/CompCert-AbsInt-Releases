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

(*- E_COMPCERT_CODE_CBuiltins_builtins_001 *)
(*- #Justify_Derived "Utility constant" *)
let builtins = {
  builtin_typedefs = [
    "__builtin_va_list", TPtr(TVoid [], [])
  ];
  builtin_functions = [
    (* Memory accesses *)
    "__builtin_read16_reversed",
      (TInt(IUShort, []), [TPtr(TInt(IUShort, [AConst]), [])], false);
    "__builtin_read32_reversed",
      (TInt(IUInt, []), [TPtr(TInt(IUInt, [AConst]), [])], false);
    "__builtin_write16_reversed",
      (TVoid [], [TPtr(TInt(IUShort, []), []); TInt(IUShort, [])], false);
    "__builtin_write32_reversed",
      (TVoid [], [TPtr(TInt(IUInt, []), []); TInt(IUInt, [])], false);
    (* Synchronization *)
    "__builtin_dmb",
      (TVoid [], [], false);
    "__builtin_dsb",
      (TVoid [], [], false);
    "__builtin_isb",
      (TVoid [], [], false);
    "__builtin_copysignf",
      (TFloat(FFloat, []), [TFloat(FFloat, []);TFloat(FFloat, [])], false);
    "__builtin_dtob",
      (TInt(IULongLong, []), [TFloat(FDouble, [])], false);
  ]
}
(*- #End *)

(*- E_COMPCERT_CODE_CBuiltins_valist_configuration_001 *)
(*- #Justify_Derived "Utility constants" *)
let size_va_list = 4
let va_list_scalar = true
(*- #End *)

(* Expand memory references inside extended asm statements.  Used in C2C. *)

(*- E_COMPCERT_CODE_CBuiltins_asm_mem_argument_001 *)
(*- #Justify_Derived "Utility function" *)
let asm_mem_argument arg = Printf.sprintf "[%s, #0]" arg
(*- #End *)

(*- E_COMPCERT_CODE_CBuiltins_asm_float_reg_cstr_001 *)
(*- #Justify_Derived "Utility constant" *)
let asm_float_reg_cstr = None
(*- #End *)
