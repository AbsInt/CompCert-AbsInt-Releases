(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open AST

(* Function to get the target specific register class for AST types.
   We have two main register classes:
     0 for integer registers
     1 for floating-point registers
   plus a third pseudo-class 2 that has no registers and forces
   stack allocation. *)

(*- E_COMPCERT_CODE_Machregsaux_class_of_type_001 *)
(*- #Justify_Derived "Utility function" *)
let class_of_type = function
  | Tint | Tlong -> 0
  | Tfloat | Tsingle -> 1
  | Tany32 -> 0
  | Tany64 -> 1
(*- #End *)

let class_of_ptype ty = class_of_type (proj_ptype_typ ty)

(* [interferes_caller_save tv mr] returns true iff the register [mr] may be used to hold the value [tv] across a function call.
   If the register is caller-save, we always deny using the register.

   The PowerPC 64-bit architecture is backwards compatible with 32-bit code, but for GPR registers only the lower 32-bit are preserved across a function call.
   We check via subtyping whether the value fits into the preserved part of the register. 
   If the value fits, the value is preserved and the register may be used.
   If the value does not fit, part of the value would be destroyed so we deny using the register. *)
let interferes_caller_save tv mr =
  Conventions1.is_caller_save mr || not (subtype (proj_ptype_typ tv) (Conventions1.callee_save_type mr))

include ArchitectureInterface
