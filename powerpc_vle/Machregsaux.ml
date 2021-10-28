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

(** Auxiliary functions on machine registers *)

(*- E_COMPCERT_CODE_Machregsaux_is_scratch_register_001 *)
(*- #Justify_Derived "Utility function" *)
let is_scratch_register s = s = "R0" || s = "r0"
(*- #End *)

(* Function to get the target specific register class for AST types.
   We have two main register classes:
     0 for integer registers
     1 for special floating-point registers
   plus a third pseudo-class 2 that has no registers and forces
   stack allocation. *)

let class_of_type = function
  | Tint | Tlong -> 0
  | Tfloat | Tsingle -> 0
  | Tany32 -> 0
  | Tany64 -> 1
