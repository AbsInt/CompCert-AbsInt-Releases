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
    "__builtin_va_list",
    TArray(TInt(IUInt, []), Some 3L, [])
  ];
  builtin_functions = [
    (* Integer arithmetic *)
    "__builtin_mulhw",
      (TInt(IInt, []), [TInt(IInt, []); TInt(IInt, [])], false);
    "__builtin_mulhwu",
      (TInt(IUInt, []), [TInt(IUInt, []); TInt(IUInt, [])], false);
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
    "__builtin_sync",
      (TVoid [], [], false);
    "__builtin_isync",
      (TVoid [], [], false);
    (* Cache instructions *)
    "__builtin_dcbf",
      (TVoid [],[TPtr(TVoid [], [])],false);
    "__builtin_dcbi",
      (TVoid [],[TPtr(TVoid [], [])],false);
    "__builtin_icbi",
      (TVoid [],[TPtr(TVoid [], [])],false);
    "__builtin_prefetch",
      (TVoid [], [TPtr (TVoid [],[]);TInt (IInt, []);TInt (IInt,[])],false);
    "__builtin_dcbtls",
      (TVoid[], [TPtr (TVoid [],[]);TInt (IInt,[])],false);
    "__builtin_icbtls",
      (TVoid[], [TPtr (TVoid [],[]);TInt (IInt,[])],false);
    "__builtin_dcbz",
      (TVoid[], [TPtr (TVoid [],[])],false);
    (* Access to special registers *)
    "__builtin_get_spr",
      (TInt(IUInt, []), [TInt(IInt, [])], false);
    "__builtin_set_spr",
      (TVoid [], [TInt(IInt, []); TInt(IUInt, [])], false);
    (* Move register *)
    "__builtin_mr",
      (TVoid [], [TInt(IInt, []); TInt(IInt, [])], false);
    (* Frame and return address *)
    "__builtin_call_frame",
      (TPtr (TVoid [],[]),[],false);
    "__builtin_return_address",
      (TPtr (TVoid [],[]),[],false);
    (* isel *)
    "__builtin_isel",
      (TInt (IInt, []),[TInt(IBool, []);TInt(IInt, []);TInt(IInt, [])],false);
    (* uisel *)
    "__builtin_uisel",
      (TInt (IUInt, []),[TInt(IBool, []);TInt(IUInt, []);TInt(IUInt, [])],false);
    (* bsel *)
    "__builtin_bsel",
      (TInt (IBool, []),[TInt(IBool, []);TInt(IBool, []);TInt(IBool, [])],false);
  ]
}
(*- #End *)

(*- E_COMPCERT_CODE_CBuiltins_valist_configuration_001 *)
(*- #Justify_Derived "Utility constants" *)
let size_va_list = 12
let va_list_scalar = false
(*- #End *)

(* Expand memory references inside extended asm statements.  Used in C2C. *)

(*- E_COMPCERT_CODE_CBuiltins_asm_mem_argument_001 *)
(*- #Justify_Derived "Utility function" *)
let asm_mem_argument arg = Printf.sprintf "0(%s)" arg
(*- #End *)

let asm_float_reg_cstr = Some 'f'
