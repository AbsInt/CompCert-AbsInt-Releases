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


let interferes_caller_save tv mr =
  not (Conventions1.is_callee_save mr && subtype tv (Conventions1.callee_save_type mr))

include ArchitectureInterface
