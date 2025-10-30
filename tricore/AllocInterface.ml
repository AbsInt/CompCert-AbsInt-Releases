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

include ArchitectureInterface

let default_ptype_of_class n =
  match n with
  | 0 -> Ptyp Tint
  | 1 -> Pptr
  | _ -> assert false

let class_of_reg r =
  if Conventions1.is_addr_reg r then 1 else 0

let worst r1 r2 =
  match r1, r2 with
  | 0, 0 | 1, 1 -> 1
  | 0, 1 | 1, 0 -> 1
  | _, _ -> assert false

let class_of_type = function
  | Tint | Tlong -> 0
  | Tfloat | Tsingle -> 0
  | Tany32 -> 0
  | Tany64 -> assert false

let class_of_ptype = function
  | Pptr -> 1
  | Ptyp ty -> class_of_type ty

let interferes_caller_save tv mr = Conventions1.is_caller_save mr

