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

open Machregs

(** Auxiliary functions on machine registers for Allocation Interface*)

val class_of_type: AST.typ -> int

val interferes_caller_save: AST.typ -> Machregs.mreg -> bool

val classes: int list

val default_type_of_class: int -> AST.typ

val class_of_reg: mreg -> int

val no_spill_class: int

val loc_result: AST.signature -> mreg AST.rpair

val loc_arguments: AST.signature -> Locations.loc AST.rpair list

val expand_mreg: mreg -> mreg AST.rpair

val expand_loc: Locations.loc -> Locations.loc AST.rpair

val worst: int -> int -> int

val aliasing_classes: int -> int list

val classes_alias: int -> int -> bool

val regs_alias: mreg -> mreg -> bool

val parallel_move_constraints: XTL.var list -> XTL.var list -> XTL.var list array * XTL.var list array

val parallel_move_interfs_tmps: XTL.var list -> XTL.var list -> XTL.var array -> XTL.var list array
