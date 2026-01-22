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

(*- E_COMPCERT_CODE_ArchitectureInterface_classes_001 *)
(*- #Justify_Derived "Utility constant" *)
let classes = [0; 1]
(*- #End *)

(*- E_COMPCERT_CODE_ArchitectureInterface_default_ptype_of_class_001 *)
(*- #Justify_Derived "Utility function" *)
let default_ptype_of_class = function
  | 0 -> Ptyp Tint (* used in parallel moves only *)
  | 1 -> Ptyp Tfloat
  | _ -> assert false
(*- #End *)

(*- E_COMPCERT_CODE_ArchitectureInterface_class_of_reg_001 *)
(*- #Justify_Derived "Utility function" *)
let class_of_reg r =
  if Conventions1.is_float_reg r then 1 else 0
(*- #End *)

(*- E_COMPCERT_CODE_ArchitectureInterface_no_spill_class_001 *)
(*- #Justify_Derived "Utility constant" *)
let no_spill_class = 2
(*- #End *)

(*- E_COMPCERT_CODE_ArchitectureInterface_loc_result_001 *)
(*- #Justify_Derived "Utility function" *)
let loc_result = Conventions1.loc_result
(*- #End *)

(*- E_COMPCERT_CODE_ArchitectureInterface_loc_arguments_001 *)
(*- #Justify_Derived "Utility function" *)
let loc_arguments = Conventions1.loc_arguments
(*- #End *)

(*- E_COMPCERT_CODE_ArchitectureInterface_expand_mreg_001 *)
(*- #Justify_Derived "Utility function" *)
let expand_mreg m = One m
(*- #End *)

(*- E_COMPCERT_CODE_ArchitectureInterface_expand_loc_001 *)
(*- #Justify_Derived "Utility function" *)
let expand_loc l = One l
(*- #End *)

(*- E_COMPCERT_CODE_ArchitectureInterface_aliasing_classes_001 *)
(*- #Justify_Derived "Utility function" *)
let aliasing_classes regclass = [regclass]
(*- #End *)

(*- E_COMPCERT_CODE_ArchitectureInterface_worst_001 *)
(*- #Justify_Derived "Utility function" *)
let worst r1 r2 =
  match r1, r2 with
  | 0, 0 | 1, 1 -> 1
  | _, _ -> assert false
(*- #End *)

(*- E_COMPCERT_CODE_ArchitectureInterface_classes_alias_001 *)
(*- #Justify_Derived "Utility function" *)
let classes_alias class1 class2 = (class1 = class2)
(*- #End *)

(*- E_COMPCERT_CODE_ArchitectureInterface_regs_alias_001 *)
(*- #Justify_Derived "Utility function" *)
let regs_alias r1 r2 = (r1 = r2)
(*- #End *)

(*- E_COMPCERT_CODE_ArchitectureInterface_parallel_move_constraints_001 *)
(*- #Justify_Derived "Utility function" *)
let parallel_move_constraints srcs dsts = (Array.make 2 [], Array.make 2 [])
(*- #End *)

(*- E_COMPCERT_CODE_ArchitectureInterface_parallel_move_interfs_tmps_001 *)
(*- #Justify_Derived "Utility function" *)
let parallel_move_interfs_tmps srcs dsts tmps = [|srcs@dsts; srcs@dsts|]
(*- #End *)
