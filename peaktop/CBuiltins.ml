(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  AbsInt Angewandte Informatik GmbH. All rights reserved. This file  *)
(*  is distributed under the terms of the INRIA Non-Commercial         *)
(*  License Agreement.                                                 *)
(*                                                                     *)
(* *********************************************************************)

(* Processor-dependent builtin C functions *)

open C

let builtins = {
  builtin_typedefs = [
    "__builtin_va_list", TPtr(TVoid [], [])
  ];
  builtin_functions = [
    (* Synchronization *)
    "__builtin_fence",
    (TVoid [], [], false);
    (* Integer arithmetic *)
    "__builtin_madd",
    (TInt(IUInt, []),
     [TInt(IUInt, []); TInt(IUInt, []); TInt(IUInt, [])],
     false);
    "__builtin_msub",
    (TInt(IUInt, []),
     [TInt(IUInt, []); TInt(IUInt, []); TInt(IUInt, [])],
     false);
    (* Float arithmetic *)
    "__builtin_fmaddf",
    (TFloat(FFloat, []),
     [TFloat(FFloat, []); TFloat(FFloat, []); TFloat(FFloat, [])],
     false);
    "__builtin_fmsubf",
    (TFloat(FFloat, []),
     [TFloat(FFloat, []); TFloat(FFloat, []); TFloat(FFloat, [])],
     false);
    (* Varg functions *)
    "__builtin_va_int32",
    (TInt(IUInt, []),
     [TPtr(TVoid [], [])],
     false);
    "__builtin_va_int64",
    (TInt(IULongLong, []),
     [TPtr(TVoid [], [])],
     false);
    "__builtin_va_float32",
    (TFloat(FFloat, []),
     [TPtr(TVoid [], [])],
     false);
    "__builtin_va_composite",
    (TPtr(TVoid [], []),
     [TPtr(TVoid [], []); TInt(IULong, [])],
     false);
  ]
}

let va_list_type = TPtr(TVoid [], [])
let size_va_list = 4
let va_list_scalar = true

(* Expand memory references inside extended asm statements.  Used in C2C. *)

let asm_mem_argument arg = Printf.sprintf "[%s]" arg

let asm_float_reg_cstr = Some 'f'
