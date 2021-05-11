(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Removing unused declarations *)

open C
open Cutil

(* The set of all identifiers referenced so far *)
(*- E_COMPCERT_CODE_Cleanup_referenced_001 *)
(*- #Link_to E_COMPCERT_TR_Function_CLEANUP_001 *)
let referenced = ref IdentSet.empty
(*- #End *)

(* Record that a new identifier was added to this set *)
(*- E_COMPCERT_CODE_Cleanup_ref_changed_001 *)
(*- #Link_to E_COMPCERT_TR_Function_CLEANUP_001 *)
let ref_changed = ref false
(*- #End *)

(* Record a reference to an identifier.  If seen for the first time,
   add it to worklist. *)

(*- E_COMPCERT_CODE_Cleanup_addref_001 *)
(*- #Link_to E_COMPCERT_TR_Function_CLEANUP_001 *)
let addref id =
  if not (IdentSet.mem id !referenced) then begin
(* Printf.printf "Referenced: %s$%d\n" id.name id.stamp; *)
    referenced := IdentSet.add id !referenced;
    ref_changed := true
  end
(*- #End *)

(*- E_COMPCERT_CODE_Cleanup_needed_001 *)
(*- #Justify_Derived "Utility function" *)
let needed id =
  IdentSet.mem id !referenced
(*- #End *)

(* Iterate [addref] on all syntactic categories. *)

(*- E_COMPCERT_CODE_Cleanup_add_typ_001 *)
(*- #Justify_Derived "Utility function" *)
let rec add_typ = function
  | TPtr(ty, _) -> add_typ ty
  | TArray(ty, _, _) -> add_typ ty
  | TFun(res, None, _, _) -> add_typ res
  | TFun(res, Some params, _, _) -> add_typ res; add_vars params
  | TNamed(id, _) -> addref id
  | TStruct(id, _) -> addref id
  | TUnion(id, _) -> addref id
  | TEnum(id, _) -> addref id
  | _ -> ()
(*- #End *)

(*- E_COMPCERT_CODE_Cleanup_add_vars_001 *)
(*- #Justify_Derived "Utility function" *)
and add_vars vl =
  List.iter (fun (id, ty) -> add_typ ty) vl
(*- #End *)

(*- E_COMPCERT_CODE_Cleanup_add_exp_001 *)
(*- #Justify_Derived "Utility function" *)
let rec add_exp e =
  add_typ e.etyp; (* perhaps not necessary but play it safe *)
  match e.edesc with
  | EConst (CEnum(id, v)) -> addref id
  | EConst _ -> ()
  | ESizeof ty -> add_typ ty
  | EAlignof ty -> add_typ ty
  | EVar id -> addref id
  | EUnop(op, e1) -> add_exp e1
  | EBinop(op, e1, e2, ty) -> add_exp e1; add_exp e2
  | EConditional(e1, e2, e3) -> add_exp e1; add_exp e2; add_exp e3
  | ECast(ty, e1) -> add_typ ty; add_exp e1
  | ECompound(ty, ie) -> add_typ ty; add_init ie
  | ECall(e1, el) -> add_exp e1; List.iter add_exp el
(*- #End *)

(*- E_COMPCERT_CODE_Cleanup_add_init_001 *)
(*- #Justify_Derived "Utility function" *)
and add_init = function
  | Init_single e -> add_exp e
  | Init_array il -> List.iter add_init il
  | Init_struct(id, il) -> addref id; List.iter (fun (_, i) -> add_init i) il
  | Init_union(id, _, i) -> addref id; add_init i
(*- #End *)

(*- E_COMPCERT_CODE_Cleanup_add_decl_001 *)
(*- #Justify_Derived "Utility function" *)
let add_decl (sto, id, ty, init) =
  add_typ ty;
  match init with None -> () | Some i -> add_init i
(*- #End *)

(*- E_COMPCERT_CODE_Cleanup_add_asm_operand_001 *)
(*- #Justify_Derived "Utility function" *)
let add_asm_operand (lbl, cstr, e) = add_exp e
(*- #End *)

(*- E_COMPCERT_CODE_Cleanup_add_stmt_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let rec add_stmt s =
  match s.sdesc with
  | Sskip -> ()
  | Sdo e -> add_exp e
  | Sseq(s1, s2) -> add_stmt s1; add_stmt s2
  | Sif(e, s1, s2) -> add_exp e; add_stmt s1; add_stmt s2
  | Swhile(e, s1) -> add_exp e; add_stmt s1
  | Sdowhile(s1, e) -> add_stmt s1; add_exp e
  | Sfor(e1, e2, e3, s1) -> add_stmt e1; add_exp e2; add_stmt e3; add_stmt s1
  | Sbreak -> ()
  | Scontinue -> ()
  | Sswitch(e, s1) -> add_exp e; add_stmt s1
  | Slabeled(lbl, s) ->
      begin match lbl with Scase(e, _) -> add_exp e | _ -> () end;
      add_stmt s
  | Sgoto lbl -> ()
  | Sreturn None -> ()
  | Sreturn(Some e) -> add_exp e
  | Sblock sl -> List.iter add_stmt sl
  | Sdecl d -> add_decl d
  | Sasm(attr, template, outputs, inputs, flags) ->
      List.iter add_asm_operand outputs;
      List.iter add_asm_operand inputs
(*- #End *)

(*- E_COMPCERT_CODE_Cleanup_add_fundef_001 *)
(*- #Justify_Derived "Utility function" *)
let add_fundef f =
  add_typ f.fd_ret;
  add_vars f.fd_params;
  List.iter add_decl f.fd_locals;
  add_stmt f.fd_body
(*- #End *)

(*- E_COMPCERT_CODE_Cleanup_add_field_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let add_field f = add_typ f.fld_typ
(*- #End *)

(*- E_COMPCERT_CODE_Cleanup_add_enum_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let add_enum e =
  List.iter
    (fun (id, v, opt_e) -> match opt_e with Some e -> add_exp e | None -> ())
    e
(*- #End *)

(* Saturate the set of referenced identifiers, starting with externally
   visible global declarations.

   Externally-visible globals include a minima:
   - Definitions of functions, unless "static" or "inline".
   - Declaration of variables with default storage.
   - Declarations of variables with the "used" attribute
*)
(*- E_COMPCERT_CODE_Cleanup_visible_decl_001 *)
(*- #Justify_Derived "Utility function" *)
let visible_decl (sto, id, ty, init) =
  let attr = attributes_of_type_no_expand ty in
  let used = has_used_attribute attr in
  used ||
  sto = Storage_default &&
  match ty with TFun _ -> false | _ -> true
(*- #End *)

(*- E_COMPCERT_CODE_Cleanup_visible_fundef_001 *)
(*- #Justify_Derived "Utility function" *)
let visible_fundef f =
  match f.fd_storage with
  | Storage_default -> not f.fd_inline
  | Storage_extern -> true
  (* We should keep functions using the attribute as used *)
  | Storage_static -> has_used_attribute f.fd_attrib
  | Storage_auto | Storage_register -> assert false
(*- #End *)

(*- E_COMPCERT_CODE_Cleanup_add_init_globdecls_001 *)
(*- #Link_to E_COMPCERT_TR_Function_CLEANUP_003 *)
let rec add_init_globdecls accu = function
  (*- #Link_to E_COMPCERT_TR_Function_CLEANUP_002 *)
  | [] -> accu
  | g :: rem ->
      match g.gdesc with
      | Gdecl decl when visible_decl decl ->
          add_decl decl; add_init_globdecls accu rem
      | Gfundef f when visible_fundef f ->
          add_fundef f; add_init_globdecls accu rem
      | Gdecl _ | Gfundef _ | Gcompositedef _ | Gtypedef _ | Genumdef _ ->
          (* Keep for later iterations *)
          add_init_globdecls (g :: accu) rem
      | Gcompositedecl _ | Gpragma _ ->
          (* Discard, since these cannot introduce more references later *)
          add_init_globdecls accu rem
(*- #End *)

(*- E_COMPCERT_CODE_Cleanup_add_needed_globdecls_001 *)
(*- #Link_to E_COMPCERT_TR_Function_CLEANUP_004 *)
let rec add_needed_globdecls accu = function
  (*- #Link_to E_COMPCERT_TR_Function_CLEANUP_002 *)
  | [] -> accu
  | g :: rem ->
      match g.gdesc with
      | Gdecl((sto, id, ty, init) as decl) ->
          if needed id
          then (add_decl decl; add_needed_globdecls accu rem)
          else add_needed_globdecls (g :: accu) rem
      | Gfundef f ->
          if needed f.fd_name
          then (add_fundef f; add_needed_globdecls accu rem)
          else add_needed_globdecls (g :: accu) rem
      | Gcompositedef(_, id, _, flds) ->
          if needed id
          then (List.iter add_field flds; add_needed_globdecls accu rem)
          else add_needed_globdecls (g :: accu) rem
      | Gtypedef(id, ty) ->
          if needed id
          then (add_typ ty; add_needed_globdecls accu rem)
          else add_needed_globdecls (g :: accu) rem
      | Genumdef(id, _, enu) ->
          if needed id || List.exists (fun (id, _, _) -> needed id) enu
          then (add_enum enu; add_needed_globdecls accu rem)
          else add_needed_globdecls (g :: accu) rem
      | _ ->
          assert false
(*- #End *)

(*- E_COMPCERT_CODE_Cleanup_saturate_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let saturate p =
  let rec loop p =
    if !ref_changed then begin
      ref_changed := false;
      loop (add_needed_globdecls [] p)
    end in
  ref_changed := false;
  loop (add_init_globdecls [] p)
(*- #End *)

(* Remove unreferenced definitions *)

(*- E_COMPCERT_CODE_Cleanup_remove_unused_debug_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let remove_unused_debug =  function
  | Gdecl (_,id,_,_) ->  Debug.remove_unused id
  | Gfundef f -> Debug.remove_unused_function f.fd_name
  | _ -> ()
(*- #End *)

(*- E_COMPCERT_CODE_Cleanup_simpl_globdecls_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let rec simpl_globdecls accu = function
  | [] -> accu
  | g :: rem ->
      let need =
        match g.gdesc with
        | Gdecl((sto, id, ty, init) as decl) -> visible_decl decl || needed id
        | Gfundef f -> visible_fundef f || needed f.fd_name
        | Gcompositedecl(_, id, _) -> needed id
        | Gcompositedef(_, id, _, flds) -> needed id
        | Gtypedef(id, ty) -> needed id
        | Genumdef(id, _, enu) ->
            needed id || List.exists (fun (id, _, _) -> needed id) enu
        | Gpragma s -> true in
      if need
      then simpl_globdecls (g :: accu) rem
      else begin remove_unused_debug g.gdesc; simpl_globdecls accu rem end
(*- #End *)

(*- E_COMPCERT_CODE_Cleanup_program_001 *)
let program p =
  (*- #Link_to E_COMPCERT_TR_Function_CLEANUP_005 *)
  referenced := IdentSet.empty;
  saturate p;
  (*- #Link_to E_COMPCERT_TR_Function_CLEANUP_006 *)
  let p' = simpl_globdecls [] p in
  referenced := IdentSet.empty;
  p'
(*- #End *)
