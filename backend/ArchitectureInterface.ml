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

let classes = [0; 1]

let default_ptype_of_class = function
  | 0 -> Ptyp Tint (* used in parallel moves only *)
  | 1 -> Ptyp Tfloat
  | _ -> assert false

let class_of_reg r =
  if Conventions1.is_float_reg r then 1 else 0

let no_spill_class = 2

let loc_result = Conventions1.loc_result

let loc_arguments = Conventions1.loc_arguments

let expand_mreg m = One m

let expand_loc l = One l

let aliasing_classes regclass = [regclass]

let worst r1 r2 =
  match r1, r2 with
  | 0, 0 | 1, 1 -> 1
  | _, _ -> assert false

let classes_alias class1 class2 = (class1 = class2)

let regs_alias r1 r2 = (r1 = r2)

let parallel_move_constraints srcs dsts = (Array.make 2 [], Array.make 2 [])

let parallel_move_interfs_tmps srcs dsts tmps = [|srcs@dsts; srcs@dsts|]
