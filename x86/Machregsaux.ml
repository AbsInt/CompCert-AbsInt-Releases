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

let is_scratch_register r = false

(* Function to get the target specific register class for AST types.
   We have two main register classes:
     0 for integer registers
     1 for floating-point registers
   plus a third pseudo-class 2 that has no registers and forces
   stack allocation. *)

let class_of_type = function
  | Tint | Tlong -> 0
  | Tfloat | Tsingle -> 1
  | Tany32 -> 0
  | Tany64 -> if Archi.ptr64 then 0 else 1
