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

(* Renaming of identifiers *)

open C
open Cutil

module StringSet = Set.Make(String)
module StringMap = Map.Make(String)

(*- E_COMPCERT_CODE_Rename_rename_env_001 *)
(*- #Justify_Derived "Type definition" *)
type rename_env = {
  re_id: ident IdentMap.t;
  re_public: ident StringMap.t;
  re_used: StringSet.t
}
(*- #End *)

(*- E_COMPCERT_CODE_Rename_empty_env_001 *)
(*- #Link_to E_COMPCERT_TR_Function_RENAME_001 *)
let empty_env =
  { re_id = IdentMap.empty;
    re_public = StringMap.empty;
    re_used = StringSet.empty }
(*- #End *)

(* For public global identifiers, we must keep their names *)

(*- E_COMPCERT_CODE_Rename_enter_public_001 *)
(*- #Justify_Derived "Utility function" *)
let enter_public env id =
  try
    let id' = StringMap.find id.name env.re_public in
    { env with re_id = IdentMap.add id id' env.re_id }
  with Not_found ->
    { re_id = IdentMap.add id id env.re_id;
      re_public = StringMap.add id.name id env.re_public;
      re_used = StringSet.add id.name env.re_used }
(*- #End *)

(* For static or local identifiers, we make up a new name if needed *)
(* If the same identifier has already been declared,
   don't rename a second time *)

(*- E_COMPCERT_CODE_Rename_rename_001 *)
let rename env id =
  try
    (IdentMap.find id env.re_id, env)
  with Not_found ->
    (*- #Link_to E_COMPCERT_TR_Function_RENAME_006 *)
    let basename =
      if id.name = "" then Printf.sprintf "_%d" id.stamp else id.name in
    let newname =
      (*- #Link_to E_COMPCERT_TR_Function_RENAME_002 *)
      if not (StringSet.mem basename env.re_used) then basename else begin
        let rec find_name n =
          let s = Printf.sprintf "%s__%d" basename n in
          if StringSet.mem s env.re_used
          then find_name (n+1)
          else s
        in find_name 1
      end in
    let newid = {name = newname; stamp = id.stamp } in
    ( newid,
      { re_id = IdentMap.add id newid env.re_id;
        re_public = env.re_public;
        re_used = StringSet.add newname env.re_used } )
(*- #End *)

(* Monadic map to thread an environment *)

(*- E_COMPCERT_CODE_Rename_mmap_001 *)
(*- #Justify_Derived "Utility function" *)
let rec mmap (f: rename_env -> 'a -> 'b * rename_env) env = function
  | [] -> ([], env)
  | hd :: tl ->
      let (hd', env1) = f env hd in
      let (tl', env2) = mmap f env1 tl in
      (hd' :: tl', env2)
(*- #End *)

(* Renaming *)

(*- E_COMPCERT_CODE_Rename_ident_001 *)
(*- #Justify_Derived "Utility function" *)
let ident env id =
  try
    IdentMap.find id env.re_id
  with Not_found ->
    Diagnostics.fatal_error Diagnostics.no_loc "internal error: rename: %s__%d unbound"
      id.name id.stamp
(*- #End *)

(*- E_COMPCERT_CODE_Rename_typ_001 *)
(*- #Justify_Derived "Utility function" *)
let rec typ env = function
  | TPtr(ty, a) -> TPtr(typ env ty, a)
  | TArray(ty, sz, a) -> TArray(typ env ty, sz, a)
  | TFun(res, None, va, a) -> TFun(typ env res, None, va, a)
  | TFun(res, Some p, va, a) ->
      let (p', _) = mmap param env p in
      TFun(typ env res, Some p', va, a)
  | TNamed(id, a) -> TNamed(ident env id, a)
  | TStruct(id, a) -> TStruct(ident env id, a)
  | TUnion(id, a) -> TUnion(ident env id, a)
  | TEnum(id, a) -> TEnum(ident env id, a)
  | ty -> ty
(*- #End *)

(*- E_COMPCERT_CODE_Rename_param_001 *)
(*- #Justify_Derived "Utility function" *)
and param env (id, ty) =
  if id.name = "" then
    ((id, typ env ty), env)
  else
    let (id', env') = rename env id in ((id', typ env' ty), env')
(*- #End *)

(*- E_COMPCERT_CODE_Rename_field_001 *)
(*- #Justify_Derived "Utility function" *)
let field env f =
  { fld_name = f.fld_name;
    fld_typ = typ env f.fld_typ;
    fld_bitfield = f.fld_bitfield;
    fld_anonymous = f.fld_anonymous;  }
(*- #End *)

(*- E_COMPCERT_CODE_Rename_constant_001 *)
(*- #Justify_Derived "Utility function" *)
let constant env = function
  | CEnum(id, v) -> CEnum(ident env id, v)
  | cst -> cst
(*- #End *)

(*- E_COMPCERT_CODE_Rename_exp_001 *)
(*- #Justify_Derived "Utility function" *)
let rec exp env e =
  { edesc = exp_desc env e.edesc; etyp = typ env e.etyp }
(*- #End *)

(*- E_COMPCERT_CODE_Rename_exp_desc_001 *)
(*- #Justify_Derived "Utility function" *)
and exp_desc env = function
  | EConst cst -> EConst(constant env cst)
  | ESizeof ty -> ESizeof(typ env ty)
  | EAlignof ty -> EAlignof(typ env ty)
  | EVar id -> EVar(ident env id)
  | EUnop(op, a) -> EUnop(op, exp env a)
  | EBinop(op, a, b, ty) -> EBinop(op, exp env a, exp env b, typ env ty)
  | EConditional(a, b, c) -> EConditional(exp env a, exp env b, exp env c)
  | ECast(ty, a) -> ECast(typ env ty, exp env a)
  | ECompound(ty, ie) -> ECompound(typ env ty, init env ie)
  | ECall(a, al) -> ECall(exp env a, List.map (exp env) al)
(*- #End *)

(*- E_COMPCERT_CODE_Rename_init_001 *)
(*- #Justify_Derived "Utility function" *)
and init env = function
  | Init_single e -> Init_single(exp env e)
  | Init_array il -> Init_array (List.rev (List.rev_map (init env) il))
  | Init_struct(id, il) ->
      Init_struct(ident env id,
                  List.map (fun (f, i) -> (field env f, init env i)) il)
  | Init_union(id, f, i) ->
      Init_union(ident env id, field env f, init env i)
(*- #End *)

(*- E_COMPCERT_CODE_Rename_optexp_001 *)
(*- #Justify_Derived "Utility function" *)
let optexp env = function
  | None -> None
  | Some a -> Some (exp env a)
(*- #End *)

(*- E_COMPCERT_CODE_Rename_decl_001 *)
(*- #Justify_Derived "Utility function" *)
let decl env (sto, id, ty, int) =
  let (id', env') = rename env id in
  ((sto,
    id',
    typ env' ty,
    match int with None -> None | Some i -> Some(init env' i)),
   env')
(*- #End *)

(*- E_COMPCERT_CODE_Rename_asm_operand_001 *)
(*- #Justify_Derived "Utility function" *)
let asm_operand env (lbl, cstr, e) = (lbl, cstr, exp env e)
(*- #End *)

(*- E_COMPCERT_CODE_Rename_stmt_001 *)
(*- #Justify_Derived "Utility function" *)
let rec stmt env s =
  { sdesc = stmt_desc env s.sdesc; sloc = s.sloc }
(*- #End *)

(*- E_COMPCERT_CODE_Rename_stmt_desc_001 *)
(*- #Justify_Derived "Utility function" *)
and stmt_desc env = function
  | Sskip -> Sskip
  | Sdo a -> Sdo (exp env a)
  | Sseq(s1, s2) -> Sseq(stmt env s1, stmt env s2)
  | Sif(a, s1, s2) -> Sif(exp env a, stmt env s1, stmt env s2)
  | Swhile(a, s) -> Swhile(exp env a, stmt env s)
  | Sdowhile(s, a) -> Sdowhile(stmt env s, exp env a)
  | Sfor(a1, a2, a3, s) ->
      Sfor(stmt env a1, exp env a2, stmt env a3, stmt env s)
  | Sbreak -> Sbreak
  | Scontinue -> Scontinue
  | Sswitch(a, s) -> Sswitch(exp env a, stmt env s)
  | Slabeled(lbl, s) -> Slabeled(slabel env lbl, stmt env s)
  | Sgoto lbl -> Sgoto lbl
  | Sreturn a -> Sreturn (optexp env a)
  | Sblock sl -> let (sl', _) = mmap stmt_or_decl env sl in Sblock sl'
  | Sdecl d -> assert false
  | Sasm(attr, txt, outputs, inputs, flags) ->
       Sasm(attr, txt,
            List.map (asm_operand env) outputs,
            List.map (asm_operand env) inputs,
            flags)
(*- #End *)

(*- E_COMPCERT_CODE_Rename_stmt_or_decl_001 *)
(*- #Justify_Derived "Utility function" *)
and stmt_or_decl env s =
  match s.sdesc with
  | Sdecl d ->
      let (d', env') = decl env d in
      ({ sdesc = Sdecl d'; sloc = s.sloc}, env')
  | _ ->
      (stmt env s, env)
(*- #End *)

(*- E_COMPCERT_CODE_Rename_slabel_001 *)
(*- #Justify_Derived "Utility function" *)
and slabel env = function
  | Scase(e, n) -> Scase(exp env e, n)
  | sl -> sl
(*- #End *)

(*- E_COMPCERT_CODE_Rename_fundef_001 *)
(*- #Justify_Derived "Utility function" *)
let fundef env f =
  let (name', env0) = rename env f.fd_name in
  let (params', env1) = mmap param env0 f.fd_params in
  let (locals', env2) = mmap decl env1 f.fd_locals in
  ( { fd_storage = f.fd_storage;
      fd_inline = f.fd_inline;
      fd_name = name';
      fd_attrib = f.fd_attrib;
      fd_ret = typ env0 f.fd_ret;
      fd_params = params';
      fd_vararg = f.fd_vararg;
      fd_locals = locals';
      fd_body = stmt env2 f.fd_body },
    env0 )
(*- #End *)

(*- E_COMPCERT_CODE_Rename_enum_001 *)
(*- #Justify_Derived "Utility function" *)
let enum env (id, v, opte) =
  let (id', env') = rename env id in
  ((id', v, optexp env' opte), env')
(*- #End *)

(*- E_COMPCERT_CODE_Rename_globdecl_001 *)
(*- #Link_to E_COMPCERT_TR_Function_RENAME_005 *)
let rec globdecl env g =
  let (desc', env') = globdecl_desc env g.gdesc in
  ( { gdesc = desc'; gloc = g.gloc }, env' )
(*- #End *)

(*- E_COMPCERT_CODE_Rename_globdecl_desc_001 *)
(*- #Link_to E_COMPCERT_TR_Function_RENAME_005 *)
and globdecl_desc env = function
  | Gdecl d ->
      let (d', env') = decl env d in
      (Gdecl d', env')
  | Gfundef fd ->
      let (fd', env') = fundef env fd in
      (Gfundef fd', env')
  | Gcompositedecl(kind, id, attr) ->
      let (id', env') = rename env id in
      (Gcompositedecl(kind, id', attr), env')
  | Gcompositedef(kind, id, attr, members) ->
      (Gcompositedef(kind, ident env id, attr, List.map (field env) members),
       env)
  | Gtypedef(id, ty) ->
      let (id', env') = rename env id in
      (Gtypedef(id', typ env' ty), env')
  | Genumdef(id, attr, members) ->
      let (id', env') = rename env id in
      let (members', env'') = mmap enum env' members in
      (Genumdef(id', attr, members'), env'')
  | Gpragma s ->
      (Gpragma s, env)
(*- #End *)

(*- E_COMPCERT_CODE_Rename_globdecls_001 *)
(*- #Link_to E_COMPCERT_TR_Function_RENAME_005 *)
let rec globdecls env accu = function
  | [] -> List.rev accu
  | dcl :: rem ->
      let (dcl', env') = globdecl env dcl in
      globdecls env' (dcl' :: accu) rem
(*- #End *)

(* Reserve names of builtins *)

(*- E_COMPCERT_CODE_Rename_reserve_builtins_001 *)
(*- #Link_to E_COMPCERT_TR_Function_RENAME_003 *)
let reserve_builtins () =
  List.fold_left enter_public empty_env (Env.initial_identifiers())
(*- #End *)

(* Reserve global declarations with public visibility *)

(*- E_COMPCERT_CODE_Rename_reserve_public_001 *)
(*- #Link_to E_COMPCERT_TR_Function_RENAME_003 *)
let rec reserve_public env = function
  | [] -> env
  | dcl :: rem ->
      let env' =
        match dcl.gdesc with
        | Gdecl(sto, id, _, _) ->
            begin match sto with
            | Storage_default | Storage_extern -> enter_public env id
            | Storage_static -> env
            | _ -> assert false
            end
        | Gfundef f ->
            begin match f.fd_storage with
            | Storage_default | Storage_extern -> enter_public env f.fd_name
            | Storage_static -> env
            | _ -> assert false
            end
        | _ -> env in
      reserve_public env' rem
(*- #End *)

(* Rename the program *)

(*- E_COMPCERT_CODE_Rename_program_001 *)
let program p =
  globdecls
    (*- #Link_to E_COMPCERT_TR_Function_RENAME_004 *)
    (reserve_public (reserve_builtins()) p)
    [] p
(*- #End *)
