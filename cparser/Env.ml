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

(* Typing environment *)

open C

(*- E_COMPCERT_CODE_Env_error_001 *)
(*- #Link_to E_COMPCERT_TR_Robustness_ENV_004 *)
(*- #Link_to E_COMPCERT_TR_Robustness_ENV_005 *)
type error =
  | Unbound_identifier of string
  | Unbound_tag of string * string
  | Tag_mismatch of string * string * string
  | Unbound_typedef of string
  | No_member of string * string * string
(*- #End *)

exception Error of error

(* Maps over ident, accessible both by name or by name + stamp *)

(*- E_COMPCERT_CODE_Env_StringMap_001 *)
(*- #Justify_Derived "Type definition" *)
module StringMap = Map.Make(String)
(*- #End *)

(*- E_COMPCERT_CODE_Env_IdentMap_001 *)
(*- #Link_to E_COMPCERT_TR_Function_ENV_001 *)
module IdentMap = struct
  type 'a t = (ident * 'a) list StringMap.t
  let empty : 'a t = StringMap.empty

  (* Search by name and return topmost binding *)
  (*- #Link_to E_COMPCERT_TR_Function_ENV_002 *)
  let lookup s m =
    match StringMap.find s m with
    | id_data :: _ -> id_data
    | [] -> assert false

  (* Search by identifier and return associated binding *)
  let find id m =
    let rec lookup_in = function
    | [] -> raise Not_found
    | (id', data) :: rem ->
         if id'.stamp = id.stamp then data else lookup_in rem in
    lookup_in (StringMap.find id.name m)

  (* Insert by identifier *)
  let add id data m =
    let l = try StringMap.find id.name m with Not_found -> [] in
    StringMap.add id.name ((id, data) :: l) m
end
(*- #End *)

(*- E_COMPCERT_CODE_Env_gensym_001 *)
(*- #Justify_Derived "Variable for global state" *)
let gensym = ref 0
(*- #End *)

(*- E_COMPCERT_CODE_Env_fresh_ident_001 *)
(*- #Justify_Derived "Utility function" *)
let fresh_ident s = incr gensym; { name = s; stamp = !gensym }
(*- #End *)

(* Infos associated with structs or unions *)

(*- E_COMPCERT_CODE_Env_composite_info_001 *)
(*- #Justify_Derived "Type definition" *)
type composite_info = {
  ci_kind: struct_or_union;
  ci_members: field list;               (* members, in order *)
  ci_alignof: int option;               (* alignment; None if incomplete *)
  ci_sizeof: int option;                (* size; None if incomplete *)
  ci_attr: attributes                   (* attributes, if any *)
}
(*- #End *)

(* Infos associated with an ordinary identifier *)

(*- E_COMPCERT_CODE_Env_ident_info_001 *)
(*- #Justify_Derived "Type definition" *)
type ident_info =
  | II_ident of storage * typ
  | II_enum of int64  (* value of enumerator *)
(*- #End *)

(* Infos associated with a typedef *)

(*- E_COMPCERT_CODE_Env_typedef_info_001 *)
(*- #Justify_Derived "Type definition" *)
type typedef_info = typ
(*- #End *)

(* Infos associated with an enum *)

(*- E_COMPCERT_CODE_Env_enum_info_001 *)
(*- #Justify_Derived "Type definition" *)
type enum_info = {
  ei_members: enumerator list; (* list of all members *)
  ei_attr: attributes          (* attributes, if any *)
}
(*- #End *)

(* Environments *)

(*- E_COMPCERT_CODE_Env_t_001 *)
(*- #Link_to E_COMPCERT_TR_Function_ENV_003 *)
type t = {
  env_scope: int;
  env_ident: ident_info IdentMap.t;
  env_tag: composite_info IdentMap.t;
  env_typedef: typedef_info IdentMap.t;
  env_enum: enum_info IdentMap.t
}
(*- #End *)

(*- E_COMPCERT_CODE_Env_empty_001 *)
(*- #Justify_Derived "Type definition" *)
let empty = {
  env_scope = 0;
  env_ident = IdentMap.empty;
  env_tag = IdentMap.empty;
  env_typedef = IdentMap.empty;
  env_enum = IdentMap.empty
}
(*- #End *)

(* Enter a new scope. *)

(*- E_COMPCERT_CODE_Env_new_scope_001 *)
(*- #Justify_Derived "Utility function" *)
let new_scope env =
  { env with env_scope = !gensym + 1 }
(*- #End *)

(*- E_COMPCERT_CODE_Env_in_current_scope_001 *)
(*- #Justify_Derived "Utility function" *)
let in_current_scope env id = id.stamp >= env.env_scope
(*- #End *)

(* Looking up things by source name *)

(*- E_COMPCERT_CODE_Env_lookup_ident_001 *)
(*- #Justify_Derived "Utility function" *)
let lookup_ident env s =
  try
    IdentMap.lookup s env.env_ident
  with Not_found ->
    (*- #Link_to E_COMPCERT_TR_Robustness_ENV_004 *)
    raise(Error(Unbound_identifier s))
(*- #End *)

(*- E_COMPCERT_CODE_Env_lookup_struct_001 *)
(*- #Justify_Derived "Utility function" *)
let lookup_struct env s =
  try
    let (id, ci as res) = IdentMap.lookup s env.env_tag in
    if ci.ci_kind <> Struct then
      raise(Error(Tag_mismatch(s, "struct", "union")));
    res
  with Not_found ->
    raise(Error(Unbound_tag(s, "struct")))
(*- #End *)

(*- E_COMPCERT_CODE_Env_lookup_union_001 *)
(*- #Justify_Derived "Utility function" *)
let lookup_union env s =
  try
    let (id, ci as res) = IdentMap.lookup s env.env_tag in
    if ci.ci_kind <> Union then
      raise(Error(Tag_mismatch(s, "union", "struct")));
    res
  with Not_found ->
    raise(Error(Unbound_tag(s, "union")))
(*- #End *)

(*- E_COMPCERT_CODE_Env_lookup_composite_001 *)
(*- #Justify_Derived "Utility function" *)
let lookup_composite env s =
  try Some (IdentMap.lookup s env.env_tag)
  with Not_found -> None
(*- #End *)

(*- E_COMPCERT_CODE_Env_lookup_typedef_001 *)
(*- #Justify_Derived "Utility function" *)
let lookup_typedef env s =
  try
    IdentMap.lookup s env.env_typedef
  with Not_found ->
    raise(Error(Unbound_typedef s))
(*- #End *)

(*- E_COMPCERT_CODE_Env_lookup_enum_001 *)
(*- #Justify_Derived "Utility function" *)
let lookup_enum env s =
  try
    IdentMap.lookup s env.env_enum
  with Not_found ->
    raise(Error(Unbound_tag(s, "enum")))
(*- #End *)

(* Checking if a source name is bound *)

(*- E_COMPCERT_CODE_Env_ident_is_bound_001 *)
(*- #Justify_Derived "Utility function" *)
let ident_is_bound env s = StringMap.mem s env.env_ident
(*- #End *)

(* Finding things by translated identifier *)

(*- E_COMPCERT_CODE_Env_find_ident_001 *)
let find_ident env id =
  try IdentMap.find id env.env_ident
  with Not_found ->
    (*- #Link_to E_COMPCERT_TR_Robustness_ENV_004 *)
    raise(Error(Unbound_identifier(id.name)))
(*- #End *)

(*- E_COMPCERT_CODE_Env_find_struct_001 *)
(*- #Justify_Derived "Utility function" *)
let find_struct env id =
  try
    let ci = IdentMap.find id env.env_tag in
    if ci.ci_kind <> Struct then
      raise(Error(Tag_mismatch(id.name, "struct", "union")));
    ci
  with Not_found ->
    raise(Error(Unbound_tag(id.name, "struct")))
(*- #End *)

(*- E_COMPCERT_CODE_Env_find_union_001 *)
(*- #Justify_Derived "Utility function" *)
let find_union env id =
  try
    let ci = IdentMap.find id env.env_tag in
    if ci.ci_kind <> Union then
      raise(Error(Tag_mismatch(id.name, "union", "struct")));
    ci
  with Not_found ->
    raise(Error(Unbound_tag(id.name, "union")))
(*- #End *)

(*- E_COMPCERT_CODE_Env_tag_id_001 *)
(*- #Justify_Derived "Utility function" *)
let tag_id = function
  | TStruct (id,_)
  | TUnion (id,_) -> id
  | _ -> assert false (* should be checked before *)
(*- #End *)

(*- E_COMPCERT_CODE_Env_find_member_001 *)
(*- #Justify_Derived "Utility function" *)
let find_member env ci m =
  let rec member acc = function
    | [] -> raise Not_found
    | f::rest -> if f.fld_name = m then
        f::acc
      else if f.fld_anonymous then
        try
          tag acc f
         with Not_found ->
           member acc rest
       else
         member acc rest
   and tag acc fld =
     let id = tag_id fld.fld_typ in
     let ci = IdentMap.find id env.env_tag in
     member (fld::acc) ci.ci_members
   in
   member [] ci
(*- #End *)

(*- E_COMPCERT_CODE_Env_find_struct_member_001 *)
let find_struct_member env (id, m) =
  try
    let ci = find_struct env id in
    find_member env ci.ci_members m
  with Not_found ->
    (*- #Link_to E_COMPCERT_TR_Robustness_ENV_005 *)
    raise(Error(No_member(id.name, "struct", m)))
(*- #End *)

(*- E_COMPCERT_CODE_Env_find_union_member_001 *)
let find_union_member env (id, m) =
  try
    let ci = find_union env id in
    find_member env ci.ci_members m
  with Not_found ->
    (*- #Link_to E_COMPCERT_TR_Robustness_ENV_005 *)
    raise(Error(No_member(id.name, "union", m)))
(*- #End *)

(*- E_COMPCERT_CODE_Env_find_typedef_001 *)
(*- #Justify_Derived "Utility function" *)
let find_typedef env id =
  try
    IdentMap.find id env.env_typedef
  with Not_found ->
    raise(Error(Unbound_typedef(id.name)))
(*- #End *)

(*- E_COMPCERT_CODE_Env_find_enum_001 *)
(*- #Justify_Derived "Utility function" *)
let find_enum env id =
  try
    IdentMap.find id env.env_enum
  with Not_found ->
    raise(Error(Unbound_tag(id.name, "enum")))
(*- #End *)

(* Inserting things by source name, with generation of a translated name *)

(*- E_COMPCERT_CODE_Env_enter_ident_001 *)
(*- #Justify_Derived "Utility function" *)
let enter_ident env s sto ty =
  let id = fresh_ident s in
  (id,
   { env with env_ident = IdentMap.add id (II_ident(sto, ty)) env.env_ident })
(*- #End *)

(*- E_COMPCERT_CODE_Env_enter_composite_001 *)
(*- #Justify_Derived "Utility function" *)
let enter_composite env s ci =
  let id = fresh_ident s in
  (id, { env with env_tag = IdentMap.add id ci env.env_tag })
(*- #End *)

(*- E_COMPCERT_CODE_Env_enter_enum_item_001 *)
(*- #Justify_Derived "Utility function" *)
let enter_enum_item env s v =
  let id = fresh_ident s in
  (id, { env with env_ident = IdentMap.add id (II_enum v) env.env_ident })
(*- #End *)

(*- E_COMPCERT_CODE_Env_enter_typedef_001 *)
(*- #Justify_Derived "Utility function" *)
let enter_typedef env s info =
  let id = fresh_ident s in
  (id, { env with env_typedef = IdentMap.add id info env.env_typedef })
(*- #End *)

(*- E_COMPCERT_CODE_Env_enter_enum_001 *)
(*- #Justify_Derived "Utility function" *)
let enter_enum env s info =
  let id = fresh_ident s in
  (id, { env with env_enum = IdentMap.add id info env.env_enum })
(*- #End *)

(* Inserting things by translated name *)

(*- E_COMPCERT_CODE_Env_add_ident_001 *)
(*- #Justify_Derived "Utility function" *)
let add_ident env id sto ty =
  { env with env_ident = IdentMap.add id (II_ident(sto, ty)) env.env_ident }
(*- #End *)

(*- E_COMPCERT_CODE_Env_add_composite_001 *)
(*- #Justify_Derived "Utility function" *)
let add_composite env id ci =
  { env with env_tag = IdentMap.add id ci env.env_tag }
(*- #End *)

(*- E_COMPCERT_CODE_Env_add_typedef_001 *)
(*- #Justify_Derived "Utility function" *)
let add_typedef env id info =
  { env with env_typedef = IdentMap.add id info env.env_typedef }
(*- #End *)

(*- E_COMPCERT_CODE_Env_add_enum_001 *)
(*- #Justify_Derived "Utility function" *)
let add_enum env id info =
  let add_enum_item env (id, v, exp) =
    { env with env_ident = IdentMap.add id (II_enum v) env.env_ident } in
  List.fold_left add_enum_item
    { env with env_enum = IdentMap.add id info env.env_enum }
    info.ei_members
(*- #End *)

(*- E_COMPCERT_CODE_Env_add_types_001 *)
(*- #Justify_Derived "Utility function" *)
let add_types env_old env_new =
  { env_new with env_ident = env_old.env_ident;env_scope = env_old.env_scope;}
(*- #End *)

(* Initial environment describing the built-in types and functions *)

module Init = struct

(*- E_COMPCERT_CODE_Env_Init_env_001 *)
(*- #Justify_Derived "Utility constant" *)
let env = ref empty
(*- #End *)
(*- E_COMPCERT_CODE_Env_Init_idents_001 *)
(*- #Justify_Derived "Utility constant" *)
let idents = ref []
(*- #End *)
(*- E_COMPCERT_CODE_Env_Init_decls_001 *)
(*- #Justify_Derived "Utility constant" *)
let decls = ref []
(*- #End *)

(*- E_COMPCERT_CODE_Env_Init_no_loc_001 *)
(*- #Justify_Derived "Utility constant" *)
let no_loc = ("", -1)
(*- #End *)

(*- E_COMPCERT_CODE_Env_Init_add_typedef_001 *)
(*- #Justify_Derived "Utility function" *)
let add_typedef (s, ty) =
  let (id, env') = enter_typedef !env s ty in
  env := env';
  idents := id :: !idents;
  decls := {gdesc = Gtypedef(id, ty); gloc = no_loc} :: !decls
(*- #End *)

(*- E_COMPCERT_CODE_Env_Init_add_function_001 *)
(*- #Justify_Derived "Utility function" *)
let add_function (s, (res, args, va)) =
  let ty =
    TFun(res,
         Some (List.map (fun ty -> (fresh_ident "", ty)) args),
         va, []) in
  let (id, env') = enter_ident !env s Storage_extern ty in
  env := env';
  idents := id :: !idents;
  decls :=
    {gdesc = Gdecl(Storage_extern, id, ty, None); gloc = no_loc} :: !decls
(*- #End *)

end

(*- E_COMPCERT_CODE_Env_initial_001 *)
(*- #Justify_Derived "Utility function" *)
let initial () = !Init.env
(*- #End *)
(*- E_COMPCERT_CODE_Env_initial_identifiers_001 *)
(*- #Justify_Derived "Utility function" *)
let initial_identifiers () = !Init.idents
(*- #End *)
(*- E_COMPCERT_CODE_Env_initial_declarations_001 *)
(*- #Justify_Derived "Utility function" *)
let initial_declarations () = List.rev !Init.decls
(*- #End *)

(*- E_COMPCERT_CODE_Env_set_builtins_001 *)
(*- #Justify_Derived "Utility function" *)
let set_builtins blt =
  Init.env := empty;
  Init.idents := [];
  Init.decls := [];
  List.iter Init.add_typedef blt.builtin_typedefs;
  List.iter Init.add_function blt.builtin_functions
(*- #End *)

(*- E_COMPCERT_CODE_Env_is_builtin_001 *)
(*- #Justify_Derived "Utility function" *)
let is_builtin name =
  ident_is_bound !Init.env name
(*- #End *)

(* Error reporting *)

open Printf

(*- E_COMPCERT_CODE_Env_composite_tag_name_001 *)
(*- #Justify_Derived "Utility function" *)
let composite_tag_name name =
  if name = "" then "<anonymous>" else name
(*- #End *)

(*- E_COMPCERT_CODE_Env_error_message_001 *)
(*- #Justify_Derived "Utility function" *)
let error_message = function
  | Unbound_identifier name ->
      (*- #Link_to E_COMPCERT_TR_Robustness_ENV_004 *)
      sprintf "use of undeclared identifier '%s'" name
  | Unbound_tag(name, kind) ->
      (*- #Link_to E_COMPCERT_TR_Robustness_ENV_006 *)
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_171 *)
      sprintf "unbound %s '%s'" kind (composite_tag_name name)
  | Tag_mismatch(name, expected, actual) ->
      sprintf "'%s' was declared as a %s but is used as a %s"
              (composite_tag_name name) actual expected
  | Unbound_typedef name ->
      sprintf "unbound typedef '%s'" name
  | No_member(compname, compkind, memname) ->
      (*- #Link_to E_COMPCERT_TR_Robustness_ENV_005 *)
      sprintf "no member named '%s' in '%s %s'"
        memname compkind (composite_tag_name compname) 
(*- #End *)

(*- E_COMPCERT_CODE_Env_init_001 *)
(*- #Justify_Derived "Initializer" *)
let _ =
  Printexc.register_printer
    (function Error e -> Some (sprintf "Env.Error \"%s\"" (error_message e))
            | _ -> None)
(*- #End *)
