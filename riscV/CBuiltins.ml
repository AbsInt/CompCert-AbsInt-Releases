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

let reg_t =
  if Archi.ptr64 then
    TInt (ILongLong, [])
  else
    TInt (IInt, [])

let builtins = {
  builtin_typedefs = [
    "__builtin_va_list", TPtr(TVoid [], [])
  ];
  builtin_functions = [
    (* Synchronization *)
    "__builtin_fence",
      (TVoid [], [], false);
    (* Float arithmetic *)
    "__builtin_fmadd",
      (TFloat(FDouble, []),
       [TFloat(FDouble, []); TFloat(FDouble, []); TFloat(FDouble, [])],
       false);
    "__builtin_fmsub",
      (TFloat(FDouble, []),
       [TFloat(FDouble, []); TFloat(FDouble, []); TFloat(FDouble, [])],
       false);
    "__builtin_fnmadd",
      (TFloat(FDouble, []),
       [TFloat(FDouble, []); TFloat(FDouble, []); TFloat(FDouble, [])],
       false);
    "__builtin_fnmsub",
      (TFloat(FDouble, []),
       [TFloat(FDouble, []); TFloat(FDouble, []); TFloat(FDouble, [])],
       false);
    "__builtin_fmax",
      (TFloat(FDouble, []), [TFloat(FDouble, []); TFloat(FDouble, [])], false);
    "__builtin_fmin",
      (TFloat(FDouble, []), [TFloat(FDouble, []); TFloat(FDouble, [])], false);
    "__builtin_dtob",
      (TInt(IULongLong, []), [TFloat(FDouble, [])], false);
    "__builtin_czero_eqz",
      (TInt (IInt, []),[TInt(IInt, []);TInt(IInt, [])],false);
    "__builtin_czero_nez",
      (TInt (IInt, []),[TInt(IInt, []);TInt(IInt, [])],false);
    (* CSR read/write builds *)
    "__builtin_csr_read",
      (reg_t,[TInt(IUInt,[])],false);
    "__builtin_csr_write",
      (TVoid [], [TInt (IUInt, []); reg_t], false);
    "__builtin_csr_readwrite",
      (reg_t, [TInt (IUInt, []); reg_t], false);
    "__builtin_csr_clear_bits",
      (reg_t, [TInt (IUInt, []); reg_t], false);
    "__builtin_csr_set_bits",
      (reg_t, [TInt (IUInt, []); reg_t], false);
  ]
}

let va_list_type = TPtr(TVoid [], [])  (* to check! *)
let size_va_list = if Archi.ptr64 then 8 else 4
let va_list_scalar = true

(* Expand memory references inside extended asm statements.  Used in C2C. *)

let asm_mem_argument arg = Printf.sprintf "0(%s)" arg

let asm_float_reg_cstr = Some 'f'
