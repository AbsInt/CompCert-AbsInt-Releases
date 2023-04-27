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

(** The XTL intermediate language for register allocation *)

open Datatypes
open Camlcoq
open Maps
open AST
open Registers
open Op
open Locations

(*- E_COMPCERT_CODE_XTL_var_001 *)
(*- #Justify_Derived "Type definition" *)
type var = V of reg * typ | L of loc
(*- #End *)

(*- E_COMPCERT_CODE_XTL_node_001 *)
(*- #Justify_Derived "Type definition" *)
type node = P.t
(*- #End *)

(*- E_COMPCERT_CODE_XTL_instruction_001 *)
(*- #Justify_Derived "Type definition" *)
type instruction =
  | Xmove of var * var
  | Xreload of var * var
  | Xspill of var * var
  | Xparmove of var list * var list * var * var
  | Xop of operation * var list * var
  | Xload of memory_chunk * addressing * var list * var
  | Xstore of memory_chunk * addressing * var list * var
  | Xcall of signature * (var, ident) sum * var list * var list
  | Xtailcall of signature * (var, ident) sum * var list
  | Xbuiltin of external_function * var builtin_arg list * var builtin_res
  | Xbranch of node
  | Xcond of condition * var list * node * node
  | Xjumptable of var * node list
  | Xreturn of var list
(*- #End *)

(*- E_COMPCERT_CODE_XTL_block_001 *)
(*- #Justify_Derived "Type definition" *)
type block = instruction list
  (* terminated by one of Xbranch, Xcond, Xjumptable, Xtailcall or Xreturn *)
(*- #End *)

(*- E_COMPCERT_CODE_XTL_code_001 *)
(*- #Justify_Derived "Type definition" *)
type code = block PTree.t
  (* mapping node -> block *)
(*- #End *)

(*- E_COMPCERT_CODE_XTL_xfunction_001 *)
(*- #Justify_Derived "Type definition" *)
type xfunction = {
  fn_sig: signature;
  fn_stacksize: Z.t;
  fn_code: code;
  fn_entrypoint: node
}
(*- #End *)


(* Type of a variable *)

(*- E_COMPCERT_CODE_XTL_typeof_001 *)
(*- #Justify_Derived "Utility function" *)
let typeof = function V(_, ty) -> ty | L l -> Loc.coq_type l
(*- #End *)


(* Constructors for type [var] *)

(*- E_COMPCERT_CODE_XTL_vloc_001 *)
(*- #Justify_Derived "Utility function" *)
let vloc l = L l
(*- #End *)

(*- E_COMPCERT_CODE_XTL_vlocs_001 *)
(*- #Justify_Derived "Utility function" *)
let vlocs ll = List.map vloc ll
(*- #End *)

(*- E_COMPCERT_CODE_XTL_vmreg_001 *)
(*- #Justify_Derived "Utility function" *)
let vmreg mr = L(R mr)
(*- #End *)

(*- E_COMPCERT_CODE_XTL_vmregs_001 *)
(*- #Justify_Derived "Utility function" *)
let vmregs mrl = List.map vmreg mrl
(*- #End *)

(*- E_COMPCERT_CODE_XTL_vlocpairs_001 *)
(*- #Justify_Derived "Utility function" *)
let rec vlocpairs = function
  | [] -> []
  | One l :: ll -> L l :: vlocpairs ll
  | Twolong(l1, l2) :: ll -> L l1 :: L l2 :: vlocpairs ll
(*- #End *)


(* Tests over variables *)

(*- E_COMPCERT_CODE_XTL_is_stack_reg_001 *)
(*- #Justify_Derived "Utility function" *)
let is_stack_reg = function
  | L(R r) -> Machregs.is_stack_reg r
  | _      -> false
(*- #End *)


(* Sets of variables *)

(*- E_COMPCERT_CODE_XTL_VSet_001 *)
(*- #Justify_Derived "Type definition" *)
module VSet = Set.Make(struct type t = var let compare = compare end)
(*- #End *)


(*** Generation of fresh registers and fresh register variables *)

(*- E_COMPCERT_CODE_XTL_next_temp_001 *)
(*- #Justify_Derived "Variable for local state" *)
let next_temp = ref P.one
(*- #End *)

(*- E_COMPCERT_CODE_XTL_twin_table_001 *)
(*- #Justify_Derived "Variable for local state" *)
let twin_table : (int32, P.t) Hashtbl.t = Hashtbl.create 27
(*- #End *)

(*- E_COMPCERT_CODE_XTL_reset_temps_001 *)
(*- #Justify_Derived "Utility function" *)
let reset_temps () =
  next_temp := P.one; Hashtbl.clear twin_table
(*- #End *)

(*- E_COMPCERT_CODE_XTL_new_reg_001 *)
(*- #Justify_Derived "Utility function" *)
let new_reg() =
  let r = !next_temp in next_temp := P.succ !next_temp; r
(*- #End *)

(*- E_COMPCERT_CODE_XTL_new_temp_001 *)
(*- #Justify_Derived "Utility function" *)
let new_temp ty = V (new_reg(), ty)
(*- #End *)

(*- E_COMPCERT_CODE_XTL_twin_reg_001 *)
(*- #Justify_Derived "Utility function" *)
let twin_reg r =
  let r = P.to_int32 r in
  try
    Hashtbl.find twin_table r
  with Not_found ->
    let t = new_reg() in Hashtbl.add twin_table r t; t
(*- #End *)


(*** Successors (for dataflow analysis) *)

(*- E_COMPCERT_CODE_XTL_successors_block_001 *)
(*- #Justify_Derived "Utility function" *)
let rec successors_block = function
  | Xbranch s :: _ -> [s]
  | Xtailcall(sg, vos, args) :: _ -> []
  | Xcond(cond, args, s1, s2) :: _ -> [s1; s2]
  | Xjumptable(arg, tbl) :: _ -> tbl
  | Xreturn  _:: _ -> []
  | instr :: blk -> successors_block blk
  | [] -> assert false
(*- #End *)


(**** Type checking for XTL *)

exception Type_error

exception Type_error_at of node

(*- E_COMPCERT_CODE_XTL_set_var_type_001 *)
(*- #Justify_Derived "Utility function" *)
let set_var_type v ty =
  if typeof v <> ty then raise Type_error
(*- #End *)

(*- E_COMPCERT_CODE_XTL_set_vars_type_001 *)
(*- #Justify_Derived "Utility function" *)
let rec set_vars_type vl tyl =
  match vl, tyl with
  | [], [] -> ()
  | v1 :: vl, ty1 :: tyl -> set_var_type v1 ty1; set_vars_type vl tyl
  | _, _ -> raise Type_error
(*- #End *)

(*- E_COMPCERT_CODE_XTL_unify_var_type_001 *)
(*- #Justify_Derived "Utility function" *)
let unify_var_type v1 v2 =
  if typeof v1 <> typeof v2 then raise Type_error
(*- #End *)

(*- E_COMPCERT_CODE_XTL_type_builtin_arg_001 *)
(*- #Justify_Derived "Utility function" *)
let rec type_builtin_arg a ty =
  match a with
  | BA v -> set_var_type v ty
  | BA_splitlong(a1, a2) -> type_builtin_arg a1 Tint; type_builtin_arg a2 Tint
  | BA_addptr(a1, a2) -> type_builtin_arg a1 coq_Tptr; type_builtin_arg a2 coq_Tptr
  | _ -> ()
(*- #End *)

(*- E_COMPCERT_CODE_XTL_type_builtin_args_001 *)
(*- #Justify_Derived "Utility function" *)
let rec type_builtin_args al tyl =
  match al, tyl with
  | [], [] -> ()
  | a :: al, ty :: tyl -> type_builtin_arg a ty; type_builtin_args al tyl
  | _, _ -> raise Type_error
(*- #End *)

(*- E_COMPCERT_CODE_XTL_type_builtin_res_001 *)
(*- #Justify_Derived "Utility function" *)
let rec type_builtin_res a ty =
  match a with
  | BR v -> set_var_type v ty
  | BR_splitlong(a1, a2) -> type_builtin_res a1 Tint; type_builtin_res a2 Tint
  | _ -> ()
(*- #End *)

(*- E_COMPCERT_CODE_XTL_type_instr_001 *)
(*- #Justify_Derived "Utility function" *)
let type_instr = function
  | Xmove(src, dst) | Xspill(src, dst) | Xreload(src, dst) ->
      unify_var_type src dst
  | Xparmove(srcs, dsts, itmp, ftmp) ->
      List.iter2 unify_var_type srcs dsts;
      set_var_type itmp Tint;
      set_var_type ftmp Tfloat
  | Xop(op, args, res) ->
      let (targs, tres) = type_of_operation op in
      set_vars_type args targs;
      set_var_type res tres
  | Xload(chunk, addr, args, dst) ->
      set_vars_type args (type_of_addressing addr);
      set_var_type dst (type_of_chunk chunk)
  | Xstore(chunk, addr, args, src) ->
      set_vars_type args (type_of_addressing addr);
      set_var_type src (type_of_chunk chunk)
  | Xcall(sg, Coq_inl v, args, res) ->
      set_var_type v Tint
  | Xcall(sg, Coq_inr id, args, res) ->
      ()
  | Xtailcall(sg, Coq_inl v, args) ->
      set_var_type v Tint
  | Xtailcall(sg, Coq_inr id, args) ->
      ()
  | Xbuiltin(ef, args, res) ->
      let sg = ef_sig ef in
      type_builtin_args args (proj_sig_args sg);
      type_builtin_res res (proj_sig_res sg)
  | Xbranch s ->
      ()
  | Xcond(cond, args, s1, s2) ->
      set_vars_type args (type_of_condition cond)
  | Xjumptable(arg, tbl) ->
      set_var_type arg Tint
  | Xreturn args ->
      ()
(*- #End *)

(*- E_COMPCERT_CODE_XTL_type_block_001 *)
(*- #Justify_Derived "Utility function" *)
let type_block blk =
  List.iter type_instr blk
(*- #End *)

(*- E_COMPCERT_CODE_XTL_type_function_001 *)
(*- #Justify_Derived "Utility function" *)
let type_function f =
  PTree.fold
    (fun () pc blk ->
       try
         type_block blk
       with Type_error ->
         raise (Type_error_at pc))
    f.fn_code ()
(*- #End *)


(*** A generic framework for transforming extended basic blocks *)

(* Determine instructions that start an extended basic block.
   These are instructions that have >= 2 predecessors. *)

(*- E_COMPCERT_CODE_XTL_basic_blocks_map_001 *)
(*- #Justify_Derived "Utility function" *)
let basic_blocks_map f = (* return mapping pc -> number of predecessors *)
  let add_successor map s =
    PMap.set s (1 + PMap.get s map) map in
  let add_successors_block map blk =
    List.fold_left add_successor map (successors_block blk) in
  PTree.fold1 add_successors_block f.fn_code
    (PMap.set f.fn_entrypoint 2 (PMap.init 0))
(*- #End *)

(*- E_COMPCERT_CODE_XTL_transform_basic_blocks_001 *)
(*- #Justify_Derived "Utility function" *)
let transform_basic_blocks
       (transf: node -> block -> 'state -> block * 'state)
       (top: 'state)
       f =
  let bbmap = basic_blocks_map f in
  let rec transform_block st newcode pc bb =
    assert (PTree.get pc newcode = None);
    let (bb', st') = transf pc bb st in
    (* Record new code after transformation *)
    let newcode' = PTree.set pc bb' newcode in
    (* Propagate outgoing state to all successors *)
    List.fold_left (transform_successor st') newcode' (successors_block bb)
  and transform_successor st newcode pc =
    if PMap.get pc bbmap <> 1 then newcode else begin
      match PTree.get pc f.fn_code with
      | None -> newcode
      | Some bb -> transform_block st newcode pc bb
    end in
  (* Iterate over all extended basic block heads *)
  let newcode =
    PTree.fold
      (fun newcode pc bb ->
        if PMap.get pc bbmap >= 2
        then transform_block top newcode pc bb
        else newcode)
      f.fn_code PTree.empty
  in {f with fn_code = newcode}
(*- #End *)
