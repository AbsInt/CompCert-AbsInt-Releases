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

(* Machine-dependent aspects *)

(*- E_COMPCERT_CODE_Machine_struct_passing_style_001 *)
(*- #Justify_Derived "Type definition" *)
type struct_passing_style =
  | SP_ref_callee                       (* by reference, callee takes copy *)
  | SP_ref_caller                       (* by reference, caller takes copy *)
  | SP_split_args                       (* by value, as a sequence of ints *)
(*- #End *)

(*- E_COMPCERT_CODE_Machine_struct_return_style_001 *)
(*- #Justify_Derived "Type definition" *)
type struct_return_style =
  | SR_int1248      (* return by content if size is 1, 2, 4 or 8 bytes *)
  | SR_int1to4      (* return by content if size is <= 4 *)
  | SR_int1to8      (* return by content if size is <= 8 *)
  | SR_ref          (* always return by assignment to a reference
                       given as extra argument *)
(*- #End *)

(*- E_COMPCERT_CODE_Machine_t_001 *)
(*- #Justify_Derived "Type definition" *)
type t = {
  name: string;
  char_signed: bool;
  sizeof_ptr: int;
  sizeof_short: int;
  sizeof_int: int;
  sizeof_long: int;
  sizeof_longlong: int;
  sizeof_float: int;
  sizeof_double: int;
  sizeof_longdouble: int;
  sizeof_void: int option;
  sizeof_fun: int option;
  sizeof_wchar: int;
  wchar_signed: bool;
  sizeof_size_t: int;
  sizeof_ptrdiff_t: int;
  sizeof_intreg: int;
  alignof_ptr: int;
  alignof_short: int;
  alignof_int: int;
  alignof_long: int;
  alignof_longlong: int;
  alignof_float: int;
  alignof_double: int;
  alignof_longdouble: int;
  alignof_void: int option;
  alignof_fun: int option;
  bigendian: bool;
  bitfields_msb_first: bool;
  supports_unaligned_accesses: bool;
  supports_double: bool;
  struct_passing_style: struct_passing_style;
  struct_return_style : struct_return_style;
}
(*- #End *)

(*- E_COMPCERT_CODE_Machine_ilp32ll64_001 *)
(*- #Justify_Derived "Utility constant" *)
let ilp32ll64 = {
  name = "ilp32ll64";
  char_signed = false;
  sizeof_ptr = 4;
  sizeof_short = 2;
  sizeof_int = 4;
  sizeof_long = 4;
  sizeof_longlong = 8;
  sizeof_float = 4;
  sizeof_double = 8;
  sizeof_longdouble = 8;
  sizeof_void = None;
  sizeof_fun = None;
  sizeof_wchar = 4;
  wchar_signed = true;
  sizeof_size_t = 4;
  sizeof_ptrdiff_t = 4;
  sizeof_intreg = 4;
  alignof_ptr = 4;
  alignof_short = 2;
  alignof_int = 4;
  alignof_long = 4;
  alignof_longlong = 8;
  alignof_float = 4;
  alignof_double = 8;
  alignof_longdouble = 8;
  alignof_void = None;
  alignof_fun = None;
  bigendian = false;
  bitfields_msb_first = false;
  supports_unaligned_accesses = false;
  supports_double = true;
  struct_passing_style = SP_ref_callee;
  struct_return_style = SR_ref;
}
(*- #End *)

(*- E_COMPCERT_CODE_Machine_i32lpll64_001 *)
(*- #Justify_Derived "Utility constant" *)
let i32lpll64 = {
  name = "i32lpll64";
  char_signed = false;
  sizeof_ptr = 8;
  sizeof_short = 2;
  sizeof_int = 4;
  sizeof_long = 8;
  sizeof_longlong = 8;
  sizeof_float = 4;
  sizeof_double = 8;
  sizeof_longdouble = 8;
  sizeof_void = None;
  sizeof_fun = None;
  sizeof_wchar = 4;
  wchar_signed = true;
  sizeof_size_t = 8;
  sizeof_ptrdiff_t = 8;
  sizeof_intreg = 8;
  alignof_ptr = 8;
  alignof_short = 2;
  alignof_int = 4;
  alignof_long = 8;
  alignof_longlong = 8;
  alignof_float = 4;
  alignof_double = 8;
  alignof_longdouble = 8;
  alignof_void = None;
  alignof_fun = None;
  bigendian = false;
  bitfields_msb_first = false;
  supports_unaligned_accesses = false;
  supports_double = true;
  struct_passing_style = SP_ref_callee;
  struct_return_style = SR_ref;
}
(*- #End *)

(*- E_COMPCERT_CODE_Machine_il32pll64_001 *)
(*- #Justify_Derived "Utility constant" *)
let il32pll64 = {
  name = "il32pll64";
  char_signed = false;
  sizeof_ptr = 8;
  sizeof_short = 2;
  sizeof_int = 4;
  sizeof_long = 4;
  sizeof_longlong = 8;
  sizeof_float = 4;
  sizeof_double = 8;
  sizeof_longdouble = 8;
  sizeof_void = None;
  sizeof_fun = None;
  sizeof_wchar = 4;
  wchar_signed = true;
  sizeof_size_t = 8;
  sizeof_ptrdiff_t = 8;
  sizeof_intreg = 8;
  alignof_ptr = 8;
  alignof_short = 2;
  alignof_int = 4;
  alignof_long = 4;
  alignof_longlong = 8;
  alignof_float = 4;
  alignof_double = 8;
  alignof_longdouble = 8;
  alignof_void = None;
  alignof_fun = None;
  bigendian = false;
  bitfields_msb_first = false;
  supports_unaligned_accesses = false;
  supports_double = true;
  struct_passing_style = SP_ref_callee;
  struct_return_style = SR_ref;
}
(*- #End *)

(*- E_COMPCERT_CODE_Machine_deactivate_double_001 *)
(*- #Justify_Derived "Utility function" *)
let deactivate_double conf =
  { conf with supports_double = false;
              sizeof_double = conf.sizeof_float;
              sizeof_longdouble = conf.sizeof_float;
              alignof_double = conf.alignof_float;
              alignof_longdouble = conf.alignof_float; }
(*- #End *)

(* Canned configurations for some ABIs *)

(*- E_COMPCERT_CODE_Machine_x86_001 *)
(*- #Justify_Derived "Utility constant" *)
let x86_32 =
  { ilp32ll64 with name = "x86_32";
                   char_signed = true;
                   alignof_longlong = 4; alignof_double = 4;
                   alignof_longdouble = 4;
                   supports_unaligned_accesses = true;
                   struct_passing_style = SP_split_args;
                   struct_return_style = SR_ref}

let x86_32_macos =
  {x86_32 with struct_passing_style = SP_split_args;
               struct_return_style = SR_int1248 }

let x86_32_bsd =
  x86_32_macos

let x86_64 =
  { i32lpll64 with name = "x86_64"; char_signed = true;
                   struct_passing_style = SP_ref_callee; (* wrong *)
                   struct_return_style = SR_ref } (* to check *)

let win32 =
  { ilp32ll64 with name = "win32"; char_signed = true;
                   sizeof_wchar = 2; wchar_signed = false;
                   struct_passing_style = SP_split_args;
                   struct_return_style = SR_ref }
let win64 =
  { il32pll64 with name = "win64"; char_signed = true;
                   sizeof_wchar = 2; wchar_signed = false }
(*- #End *)

(*- E_COMPCERT_CODE_Machine_powerpc_001 *)
(*- #Justify_Derived "Utility constant" *)
let ppc_32_bigendian =
  { ilp32ll64 with name = "powerpc";
                   bigendian = true;
                   bitfields_msb_first = true;
                   supports_unaligned_accesses = true;
                   struct_passing_style = SP_ref_caller;
                   struct_return_style =  SR_int1to8; }
(*- #End *)

(*- E_COMPCERT_CODE_Machine_powerpc_002 *)
(*- #Justify_Derived "Utility constant" *)
let ppc_32_r64_bigendian =
  { ppc_32_bigendian with sizeof_intreg = 8;}
(*- #End *)

(*- E_COMPCERT_CODE_Machine_powerpc_003 *)
(*- #Justify_Derived "Utility constant" *)
let ppc_32_diab_bigendian =
  { ppc_32_bigendian with sizeof_wchar = 2; wchar_signed = false }
(*- #End *)

(*- E_COMPCERT_CODE_Machine_powerpc_vle_001 *)
(*- #Justify_Derived "Utility constant" *)
let ppcvle_32_bigendian =
  deactivate_double ppc_32_bigendian
(*- #End *)

(*- E_COMPCERT_CODE_Machine_powerpc_vle_002 *)
(*- #Justify_Derived "Utility constant" *)
let ppcvle_32_diab_bigendian =
  deactivate_double ppc_32_diab_bigendian
(*- #End *)

(*- E_COMPCERT_CODE_Machine_powerpc_004 *)
(*- #Justify_Derived "Utility constant" *)
let ppc_32_r64_diab_bigendian =
  { ppc_32_diab_bigendian with sizeof_intreg = 8;}
(*- #End *)

(*- E_COMPCERT_CODE_Machine_powerpc_005 *)
(*- #Justify_Derived "Utility constant" *)
let ppc_32_linux_bigendian = {ppc_32_bigendian with struct_return_style = SR_ref;}
(*- #End *)

(*- E_COMPCERT_CODE_Machine_powerpc_006 *)
(*- #Justify_Derived "Utility constant" *)
let ppc_32_r64_linux_bigendian =
  { ppc_32_linux_bigendian with sizeof_intreg = 8;}
(*- #End *)

(*- E_COMPCERT_CODE_Machine_arm_001 *)
(*- #Justify_Derived "Utility constant" *)
let arm_littleendian =
  { ilp32ll64 with name = "arm"; struct_passing_style = SP_split_args;
                   struct_return_style = SR_int1to4;}

let arm_bigendian =
  { arm_littleendian with bigendian = true;
                          bitfields_msb_first = true }
(*- #End *)

(*- E_COMPCERT_CODE_Machine_riscv_001 *)
(*- #Justify_Derived "Utility constant" *)
let rv32 =
  { ilp32ll64 with name = "rv32";
                   struct_passing_style = SP_ref_callee; (* Wrong *)
                   struct_return_style = SR_ref } (* to check *)
let rv64 =
  { i32lpll64 with name = "rv64";
                   struct_passing_style = SP_ref_callee; (* Wrong *)
                   struct_return_style = SR_ref } (* to check *)
(*- #End *)

(*- E_COMPCERT_CODE_Machine_aarch64_001 *)
(*- #Justify_Derived "Utility constant" *)
let aarch64 =
  { i32lpll64 with name = "aarch64";
                   struct_passing_style = SP_ref_callee; (* Wrong *)
                   struct_return_style = SR_ref } (* Wrong *)

let aarch64_apple =
  { aarch64 with char_signed = true }
(*- #End *)

(*- E_COMPCERT_CODE_Machine_peaktop_001 *)
(*- #Justify_Derived "Utility constant" *)
let peaktop =
  deactivate_double ilp32ll64
(*- #End *)

(* Add GCC extensions re: sizeof and alignof *)

(*- E_COMPCERT_CODE_Machine_gcc_001 *)
(*- #Justify_Derived "Utility constant" *)
let gcc_extensions c =
  { c with sizeof_void = Some 1; sizeof_fun = Some 1;
           alignof_void = Some 1; alignof_fun = Some 1 }
(*- #End *)

(* Normalize configuration for use with the CompCert reference interpreter *)

(*- E_COMPCERT_CODE_Machine_name_001 *)
(*- #Justify_Derived "Utility constant" *)
let compcert_interpreter c =
  { c with supports_unaligned_accesses = false }
(*- #End *)

(* Undefined configuration *)

(*- E_COMPCERT_CODE_Machine_undef_001 *)
(*- #Justify_Derived "Utility constant" *)
let undef = {
  name = "UNDEFINED";
  char_signed = false;
  sizeof_ptr = 0;
  sizeof_short = 0;
  sizeof_int = 0;
  sizeof_long = 0;
  sizeof_longlong = 0;
  sizeof_float = 0;
  sizeof_double = 0;
  sizeof_longdouble = 0;
  sizeof_void = None;
  sizeof_fun = None;
  sizeof_wchar = 0;
  wchar_signed = true;
  sizeof_size_t = 0;
  sizeof_ptrdiff_t = 0;
  sizeof_intreg = 0;
  alignof_ptr = 0;
  alignof_short = 0;
  alignof_int = 0;
  alignof_long = 0;
  alignof_longlong = 0;
  alignof_float = 0;
  alignof_double = 0;
  alignof_longdouble = 0;
  alignof_void = None;
  alignof_fun = None;
  bigendian = false;
  bitfields_msb_first = false;
  supports_unaligned_accesses = false;
  supports_double = false;
  struct_passing_style = SP_ref_callee;
  struct_return_style = SR_ref;
}
(*- #End *)

(* The current configuration.  Must be initialized before use. *)

(*- E_COMPCERT_CODE_Machine_config_001 *)
(*- #Justify_Derived "Variable for global state" *)
let config = ref undef
(*- #End *)
