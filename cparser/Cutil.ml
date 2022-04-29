(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(* Operations on C types and abstract syntax *)

open Diagnostics
open C
open Env
open Machine


(* Empty location *)

(*- E_COMPCERT_CODE_Cutil_no_loc_001 *)
(*- #Justify_Derived "Utility constant" *)
let no_loc = ("", -1)
(*- #End *)

(* Set and Map structures over identifiers *)

(*- E_COMPCERT_CODE_Cutil_Ident_001 *)
(*- #Justify_Derived "Type definition" *)
module Ident = struct
  type t = ident
  let compare id1 id2 = compare id1.stamp id2.stamp
end
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_IdentSet_001 *)
(*- #Justify_Derived "Type definition" *)
module IdentSet = Set.Make(Ident)
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_IdentMap_001 *)
(*- #Justify_Derived "Type definition" *)
module IdentMap = Map.Make(Ident)
(*- #End *)

(* Operations on attributes *)

(* Normalize the name of an attribute, removing starting and trailing '__' *)

(*- E_COMPCERT_CODE_Cutil_re_normalize_attrname_001 *)
(*- #Justify_Derived "Utility constant" *)
let re_normalize_attrname = Str.regexp "^__\\(.*\\)__$"
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_normalize_attrname_001 *)
(*- #Justify_Derived "Utility function" *)
let normalize_attrname a =
  if Str.string_match re_normalize_attrname a 0
  then Str.matched_group 1 a
  else a
(*- #End *)

(* Lists of attributes are kept sorted in increasing order *)

(*- E_COMPCERT_CODE_Cutil_add_attributes_001 *)
(*- #Justify_Derived "Utility function" *)
let rec add_attributes (al1: attributes) (al2: attributes) =
  match al1, al2 with
  | [], _ -> al2
  | _, [] -> al1
  | a1 :: al1', a2 :: al2' ->
      if a1 < a2 then a1 :: add_attributes al1' al2
      else if a1 > a2 then a2 :: add_attributes al1 al2'
      else a1 :: add_attributes al1' al2'
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_remove_attributes_001 *)
(*- #Justify_Derived "Utility function" *)
let rec remove_attributes (al1: attributes) (al2: attributes) =
  (* viewed as sets: al1 \ al2 *)
  match al1, al2 with
  | [], _ -> []
  | _, [] -> al1
  | a1 :: al1', a2 :: al2' ->
      if a1 < a2 then a1 :: remove_attributes al1' al2
      else if a1 > a2 then remove_attributes al1 al2'
      else remove_attributes al1' al2'
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_incl_attributes_001 *)
(*- #Justify_Derived "Utility function" *)
let rec incl_attributes (al1: attributes) (al2: attributes) =
  match al1, al2 with
  | [], _ -> true
  | _ :: _, [] -> false
  | a1 :: al1', a2 :: al2' ->
      if a1 < a2 then false
      else if a1 > a2 then incl_attributes al1 al2'
      else incl_attributes al1' al2'
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_find_custom_attributes_001 *)
(*- #Justify_Derived "Utility function" *)
let rec find_custom_attributes (names: string list)  (al: attributes) =
  match al with
  | [] -> []
  | Attr(name, args) :: tl when List.mem name names ->
      args :: find_custom_attributes names tl
  | _ :: tl ->
      find_custom_attributes names tl
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_remove_custom_attributes_001 *)
(*- #Justify_Derived "Utility function" *)
let rec remove_custom_attributes (names: string list)  (al: attributes) =
  match al with
  | [] -> []
  | Attr(name, args) :: tl when List.mem name names ->
      remove_custom_attributes names tl
  | a :: tl ->
      a :: remove_custom_attributes names tl
(*- #End *)

(* Classification of attributes *)

(*- E_COMPCERT_CODE_Cutil_attribute_class_001 *)
(*- #Justify_Derived "Type definition" *)
type attribute_class =
  | Attr_object         (* Attribute applies to the object being declared
                           (function, global variable, local variable)  *)
  | Attr_name           (* Attribute applies to the name being declared
                          (object, struct/union member, struct/union/enum tag *)
  | Attr_type           (* Attribute applies to types *)
  | Attr_struct         (* Attribute applies to struct, union and enum *)
  | Attr_function       (* Attribute applies to function types and decls *)
  | Attr_unknown        (* Unknown attribute *)
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_attr_class_001 *)
(*- #Justify_Derived "Variables for local state" *)
let attr_class : (string, attribute_class) Hashtbl.t = Hashtbl.create 32
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_declare_attribute_001 *)
(*- #Justify_Derived "Utility function" *)
let declare_attribute name cls =
  Hashtbl.replace attr_class (normalize_attrname name) cls
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_declare_attributes_001 *)
(*- #Justify_Derived "Utility function" *)
let declare_attributes l =
  List.iter (fun (n,c) -> declare_attribute n c) l
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_class_of_attribute_001 *)
(*- #Justify_Derived "Utility function" *)
let class_of_attribute = function
  | AConst | AVolatile | ARestrict -> Attr_type
  | AAlignas _ -> Attr_object
  | Attr(name, args) ->
      try Hashtbl.find attr_class (normalize_attrname name)
      with Not_found -> Attr_unknown
(*- #End *)

(* Name for printing an attribute *)

(*- E_COMPCERT_CODE_Cutil_name_of_attribute_001 *)
(*- #Justify_Derived "Utility function" *)
let name_of_attribute = function
  | AConst -> "const"
  | AVolatile -> "volatile"
  | ARestrict -> "restrict"
  | AAlignas n -> "_Alignas"
  | Attr(name, _) ->  name
(*- #End *)

(* Is an attribute a ISO C standard attribute? *)

(*- E_COMPCERT_CODE_Cutil_attr_is_standard_001 *)
(*- #Justify_Derived "Utility function" *)
let attr_is_standard = function
  | AConst | AVolatile | ARestrict -> true
  | AAlignas _ | Attr _ -> false
(*- #End *)

(* Is an attribute applicable to a whole array (true) or only to
   array elements (false)? *)

(*- E_COMPCERT_CODE_Cutil_attr_array_applicable_001 *)
(*- #Justify_Derived "Utility function" *)
let attr_array_applicable a =
  class_of_attribute a <> Attr_type
(*- #End *)

(* Is an attribute of a composite type applicable to members of this type
  when they are accessed? *)

(*- E_COMPCERT_CODE_Cutil_attr_inherited_by_members_001 *)
(*- #Justify_Derived "Utility function" *)
let attr_inherited_by_members = function
  | AConst | AVolatile | ARestrict -> true
  | AAlignas _ | Attr _ -> false
(*- #End *)

(* Adding top-level attributes to a type.  Doesn't need to unroll defns. *)
(* For array types, standard attrs are pushed to the element type. *)

(*- E_COMPCERT_CODE_Cutil_add_attributes_type_001 *)
(*- #Justify_Derived "Utility function" *)
let rec add_attributes_type attr t =
  match t with
  | TVoid a -> TVoid (add_attributes attr a)
  | TInt(ik, a) -> TInt(ik, add_attributes attr a)
  | TFloat(fk, a) -> TFloat(fk, add_attributes attr a)
  | TPtr(ty, a) -> TPtr(ty, add_attributes attr a)
  | TArray(ty, sz, a) ->
      let (attr_arr, attr_elt) = List.partition attr_array_applicable attr in
      TArray(add_attributes_type attr_elt ty, sz, add_attributes attr_arr a)
  | TFun(ty, params, vararg, a) -> TFun(ty, params, vararg, add_attributes attr
a)
  | TNamed(s, a) -> TNamed(s, add_attributes attr a)
  | TStruct(s, a) -> TStruct(s, add_attributes attr a)
  | TUnion(s, a) -> TUnion(s, add_attributes attr a)
  | TEnum(s, a) -> TEnum(s, add_attributes attr a)
(*- #End *)

(* Unrolling of typedef *)

(*- E_COMPCERT_CODE_Cutil_unroll_001 *)
(*- #Justify_Derived "Utility function" *)
let rec unroll env t =
  match t with
  | TNamed(name, attr) ->
      let ty = Env.find_typedef env name in
      unroll env (add_attributes_type attr ty)
  | _ -> t
(*- #End *)

(* Extracting the attributes of a type, including the attributes
   attached to typedefs, structs and unions.  In other words,
   typedefs are unrolled and composite definitions expanded
   before extracting the attributes.  *)

(*- E_COMPCERT_CODE_Cutil_attributes_of_type_001 *)
(*- #Justify_Derived "Utility function" *)
let rec attributes_of_type env t =
  match t with
  | TVoid a -> a
  | TInt(ik, a) -> a
  | TFloat(fk, a) -> a
  | TPtr(ty, a) -> a
  | TArray(ty, sz, a) -> add_attributes a (attributes_of_type env ty)
  | TFun(ty, params, vararg, a) -> a
  | TNamed(s, a) -> attributes_of_type env (unroll env t)
  | TStruct(s, a) ->
      begin match Env.find_struct env s with
      | ci -> add_attributes ci.ci_attr a
      | exception Env.Error(Env.Unbound_tag _) -> a
      end
  | TUnion(s, a) ->
      begin match Env.find_union env s with
      | ci -> add_attributes ci.ci_attr a
      | exception Env.Error(Env.Unbound_tag _) -> a
      end
  | TEnum(s, a) ->
      begin match Env.find_enum env s with
      | ei -> add_attributes ei.ei_attr a
      | exception Env.Error(Env.Unbound_tag _) -> a
      end
(*- #End *)

(* Extracting the attributes of a type, excluding the attributes
   attached to typedefs, structs and unions.  In other words,
   typedefs are not unrolled and composite definitions are not expanded. *)

(*- E_COMPCERT_CODE_Cutil_attributes_of_type_no_expand_001 *)
(*- #Justify_Derived "Utility function" *)
let rec attributes_of_type_no_expand t =
  match t with
  | TVoid a -> a
  | TInt(ik, a) -> a
  | TFloat(fk, a) -> a
  | TPtr(ty, a) -> a
  | TArray(ty, sz, a) -> add_attributes a (attributes_of_type_no_expand ty)
  | TFun(ty, params, vararg, a) -> a
  | TNamed(s, a) -> a
  | TStruct(s, a) -> a
  | TUnion(s, a) -> a
  | TEnum(s, a) -> a
(*- #End *)

(* Changing the attributes of a type (at top-level) *)
(* Same hack as above for array types. *)

(*- E_COMPCERT_CODE_Cutil_change_attributes_type_001 *)
(*- #Justify_Derived "Utility function" *)
let rec change_attributes_type env (f: attributes -> attributes) t =
  match t with
  | TVoid a -> TVoid (f a)
  | TInt(ik, a) -> TInt(ik, f a)
  | TFloat(fk, a) -> TFloat(fk, f a)
  | TPtr(ty, a) -> TPtr(ty, f a)
  | TArray(ty, sz, a) ->
      TArray(change_attributes_type env f ty, sz, f a)
  | TFun(ty, params, vararg, a) -> TFun(ty, params, vararg, f a)
  | TNamed(s, a) ->
      let t1 = unroll env t in
      let t2 = change_attributes_type env f t1 in
      if t2 = t1 then t else t2         (* avoid useless expansion *)
  | TStruct(s, a) -> TStruct(s, f a)
  | TUnion(s, a) -> TUnion(s, f a)
  | TEnum(s, a) -> TEnum(s, f a)
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_remove_attributes_type_001 *)
(*- #Justify_Derived "Utility function" *)
let remove_attributes_type env attr t =
  change_attributes_type env (fun a -> remove_attributes a attr) t
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_erase_attributes_type_001 *)
(*- #Justify_Derived "Utility function" *)
let erase_attributes_type env t =
  change_attributes_type env (fun a -> []) t
(*- #End *)

(* Remove all attributes from type that are not contained in attr *)
(*- E_COMPCERT_CODE_Cutil_strip_attributes_type_001 *)
(*- #Justify_Derived "Utility function" *)
let strip_attributes_type t attr =
  let strip =  List.filter (fun a -> List.mem a attr) in
  match t with
  | TVoid at -> TVoid (strip at)
  | TInt (k,at) ->  TInt (k,strip at)
  | TFloat (k,at) -> TFloat(k,strip at)
  | TPtr (t,at) -> TPtr(t,strip at)
  | TArray (t,s,at) -> TArray(t,s,strip at)
  | TFun (t,arg,v,at) -> TFun(t,arg,v,strip at)
  | TNamed (n,at) -> TNamed(n,strip at)
  | TStruct (n,at) -> TStruct(n,strip at)
  | TUnion (n,at) -> TUnion(n,strip at)
  | TEnum (n,at) -> TEnum(n,strip at)
(*- #End *)

(* Remove the last attribute from the toplevel and return the changed type *)
(*- E_COMPCERT_CODE_Cutil_strip_last_attribute_001 *)
(*- #Justify_Derived "Utility function" *)
let strip_last_attribute typ  =
  let hd_opt l = match l with
    [] -> None,[]
  | a::rest -> Some a,rest in
  match typ with
  | TVoid at -> let l,r = hd_opt at in
    l,TVoid r
  | TInt (k,at) -> let l,r = hd_opt at in
    l,TInt (k,r)
  | TFloat (k,at) -> let l,r = hd_opt at in
    l,TFloat (k,r)
  | TPtr (t,at) -> let l,r = hd_opt at in
    l,TPtr(t,r)
  | TArray (t,s,at) -> let l,r = hd_opt at in
    l,TArray(t,s,r)
  | TFun (t,arg,v,at) -> let l,r = hd_opt at in
    l,TFun(t,arg,v,r)
  | TNamed (n,at) -> let l,r = hd_opt at in
    l,TNamed(n,r)
  | TStruct (n,at) -> let l,r = hd_opt at in
    l,TStruct(n,r)
  | TUnion (n,at) -> let l,r = hd_opt at in
    l,TUnion(n,r)
  | TEnum (n,at) -> let l,r = hd_opt at in
    l,TEnum(n,r)
(*- #End *)

(* Check whether the attributes contain _Alignas attribute *)
(*- E_COMPCERT_CODE_Cutil_has_std_alignas_001 *)
(*- #Justify_Derived "Utility function" *)
let has_std_alignas env typ  =
  List.exists (function | AAlignas _ -> true | _ -> false) (attributes_of_type env typ)
(*- #End *)

(* Extracting alignment value from a set of attributes.  Return 0 if none. *)

(*- E_COMPCERT_CODE_Cutil_alignas_attribute_001 *)
(*- #Justify_Derived "Utility function" *)
let alignas_attribute al =
  let rec alignas_attr accu = function
  | [] -> accu
  | AAlignas n :: al -> alignas_attr (max n accu) al
  | Attr(("aligned" | "__aligned__"), [AInt n]) :: al ->
                        alignas_attr (max (Int64.to_int n) accu) al
  | a :: al -> alignas_attr accu al
  in alignas_attr 0 al
(*- #End *)

(* Extracting struct packing parameters from a set of attributes.
   Assume the parameters were checked earlier, e.g. alignments are
   either 0 or powers of two. *)

(*- E_COMPCERT_CODE_Cutil_packing_parameters_001 *)
(*- #Justify_Derived "Utility function" *)
let packing_parameters al =
  match find_custom_attributes ["packed";"__packed__"] al with
  | [[]] -> (1, 0, false)
  | [[AInt n]] -> (Int64.to_int n, 0, false)
  | [[AInt n; AInt p]] -> (Int64.to_int n, Int64.to_int p, false)
  | [[AInt n; AInt p; AInt q]] -> (Int64.to_int n, Int64.to_int p, q = 1L)
  | _ -> (0, 0, false)
(*- #End *)

(* Type compatibility *)

exception Incompat

(*- E_COMPCERT_CODE_Cutil_attr_handling_001 *)
(*- #Justify_Derived "Type definition" *)
type attr_handling =
  | AttrCompat
  | AttrIgnoreTop
  | AttrIgnoreAll
(*- #End *)

(* Check that [t1] and [t2] are compatible and produce a type that
   combines the information in [t1] and [t2].  For example,
   if [t1] is a prototyped function type and [t2] an unprototyped
   function type, the combined type takes the prototype from [t1]. *)

let combine_types mode env t1 t2 =

(*- E_COMPCERT_CODE_Cutil_comp_attr_001 *)
(*- #Justify_Derived "Functional decomposition" *)
  let comp_attr m a1 a2 =
    if a1 = a2 then a2 else match m with
    | AttrCompat ->
        let (a1std, a1other) = List.partition attr_is_standard a1
        and (a2std, a2other) = List.partition attr_is_standard a2 in
        if a1std = a2std
        then add_attributes a1std (add_attributes a1other a2other)
        else raise Incompat
    | AttrIgnoreTop | AttrIgnoreAll ->
        add_attributes a1 a2
  and comp_base x1 x2 =
    if x1 = x2 then x2 else raise Incompat
  and comp_array_size sz1 sz2 =
    match sz1, sz2 with
    | None, _ -> sz2
    | _, None -> sz1
    | Some n1, Some n2 -> if n1 = n2 then Some n2 else raise Incompat
  and comp_conv (id, ty) =
    match unroll env ty with
    | TInt(kind, attr) ->
        begin match kind with
        | IBool | IChar | ISChar | IUChar | IShort | IUShort -> raise Incompat
        | _ -> ()
        end
    | TFloat(kind, attr) ->
        begin match kind with
        | FFloat -> raise Incompat
        | _ -> ()
        end
    | _ -> () in
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_comp_001 *)
(*- #Justify_Derived "Functional decomposition" *)
  let rec comp m t1 t2 =
    match t1, t2 with
    | TVoid a1, TVoid a2 ->
        TVoid(comp_attr m a1 a2)
    | TInt(ik1, a1), TInt(ik2, a2) ->
        TInt(comp_base ik1 ik2, comp_attr m a1 a2)
    | TFloat(fk1, a1), TFloat(fk2, a2) ->
        TFloat(comp_base fk1 fk2, comp_attr m a1 a2)
    | TPtr(ty1, a1), TPtr(ty2, a2) ->
        let m' = if m = AttrIgnoreTop then AttrCompat else m in
        TPtr(comp m' ty1 ty2, comp_attr m a1 a2)
    | TArray(ty1, sz1, a1), TArray(ty2, sz2, a2) ->
        TArray(comp m ty1 ty2, comp_array_size sz1 sz2, comp_attr m a1 a2)
    | TFun(ty1, params1, vararg1, a1), TFun(ty2, params2, vararg2, a2) ->
        let (params, vararg) =
          match params1, params2 with
          | None, None -> None, false
          | None, Some l2 -> List.iter comp_conv l2; (params2, vararg2)
          | Some l1, None -> List.iter comp_conv l1; (params1, vararg1)
          | Some l1, Some l2 ->
              if List.length l1 <> List.length l2 then raise Incompat;
              let comp_param (id1, ty1) (id2, ty2) =
                (id2, comp AttrIgnoreTop ty1 ty2) in
              (Some(List.map2 comp_param l1 l2), comp_base vararg1 vararg2)
        in
        let m' = if m = AttrIgnoreTop then AttrCompat else m in
        TFun(comp m' ty1 ty2, params, vararg, comp_attr m a1 a2)
    | TNamed _, _ -> comp m (unroll env t1) t2
    | _, TNamed _ -> comp m t1 (unroll env t2)
    | TStruct(s1, a1), TStruct(s2, a2) ->
        TStruct(comp_base s1 s2, comp_attr m a1 a2)
    | TUnion(s1, a1), TUnion(s2, a2) ->
        TUnion(comp_base s1 s2, comp_attr m a1 a2)
    | TEnum(s1, a1), TEnum(s2, a2) ->
        TEnum(comp_base s1 s2, comp_attr m a1 a2)
    | TEnum(s,a1), TInt(enum_ikind,a2)
    | TInt(enum_ikind,a2), TEnum (s,a1) ->
        TEnum(s,comp_attr m a1 a2)
    | _, _ ->
        raise Incompat
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_combine_types_001 *)
(*- #Justify_Derived "Utility function" *)
  in try Some(comp mode t1 t2) with Incompat -> None
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_equal_types_001 *)
(*- #Justify_Derived "Utility function" *)
let rec equal_types env t1 t2 =
  match t1, t2 with
  | TVoid a1, TVoid a2 ->
     a1=a2
  | TInt(ik1, a1), TInt(ik2, a2) ->
      ik1 = ik2 && a1 = a2
  | TFloat(fk1, a1), TFloat(fk2, a2) ->
     fk1 = fk2 && a1 = a2
  | TPtr(ty1, a1), TPtr(ty2, a2) ->
      a1 = a2 && equal_types env ty1 ty2
  | TArray(ty1, sz1, a1), TArray(ty2, sz2, a2) ->
      let size = begin match sz1,sz2 with
      | None, None -> true
      | Some s1, Some s2 -> s1 = s2
      | _ -> false end in
      size && a1 = a2 && equal_types env ty1 ty2
  | TFun(ty1, params1, vararg1, a1), TFun(ty2, params2, vararg2, a2) ->
      let params =
        match params1, params2 with
        | None, None -> true
        | None, Some _
        | Some _, None -> false
        | Some l1, Some l2 ->
            try
              List.for_all2 (fun (_,t1) (_,t2) -> equal_types env t1 t2) l1 l2
            with _ -> false
      in params && a1 = a2 && vararg1 = vararg2 && equal_types env ty1 ty2
  | TNamed _, _ -> equal_types env (unroll env t1) t2
  | _, TNamed _ -> equal_types env t1 (unroll env t2)
  | TStruct(s1, a1), TStruct(s2, a2)
  | TUnion(s1, a1), TUnion(s2, a2)
  | TEnum(s1, a1), TEnum(s2, a2) ->
      s1 = s2 && a1 = a2
  | _, _ ->
      false
(*- #End *)

(** Check whether two types are compatible. *)

(*- E_COMPCERT_CODE_Cutil_compatible_types_001 *)
(*- #Justify_Derived "Utility function" *)
let compatible_types mode env t1 t2 =
  match combine_types mode env t1 t2 with Some _ -> true | None -> false
(*- #End *)

(* Natural alignment, in bytes *)

(*- E_COMPCERT_CODE_Cutil_alignof_ikind_001 *)
(*- #Justify_Derived "Utility function" *)
let alignof_ikind = function
  | IBool | IChar | ISChar | IUChar -> 1
  | IInt | IUInt -> !config.alignof_int
  | IShort | IUShort -> !config.alignof_short
  | ILong | IULong -> !config.alignof_long
  | ILongLong | IULongLong -> !config.alignof_longlong
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_alignof_fkind_001 *)
(*- #Justify_Derived "Utility function" *)
let alignof_fkind = function
  | FFloat -> !config.alignof_float
  | FDouble -> !config.alignof_double
  | FLongDouble -> !config.alignof_longdouble
(*- #End *)

(* Return natural alignment of given type, or None if the type is incomplete *)

(*- E_COMPCERT_CODE_Cutil_enum_ikind_001 *)
(*- #Justify_Derived "Utility constant" *)
let enum_ikind = IInt
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_alignof_001 *)
(*- #Justify_Derived "Utility function" *)
let rec alignof env t =
  let a = alignas_attribute (attributes_of_type env t) in
  if a > 0 then Some a else
  match t with
  | TVoid _ -> !config.alignof_void
  | TInt(ik, _) -> Some(alignof_ikind ik)
  | TFloat(fk, _) -> Some(alignof_fkind fk)
  | TPtr(_, _) -> Some(!config.alignof_ptr)
  | TArray(ty, _, _) -> alignof env ty
  | TFun(_, _, _, _) -> !config.alignof_fun
  | TNamed(_, _) -> alignof env (unroll env t)
  | TStruct(name, _) ->
    let ci = Env.find_struct env name in ci.ci_alignof
  | TUnion(name, _) ->
    let ci = Env.find_union env name in ci.ci_alignof
  | TEnum(_, _) -> Some(alignof_ikind enum_ikind)
(*- #End *)

(* Compute the natural alignment of a struct or union.
   Not done here but in composite_info_decl: taking into account
   the packing parameters (max-field-alignment, min-struct-alignment)
   and the alignas attributes. *)

(*- E_COMPCERT_CODE_Cutil_alignof_struct_union_001 *)
(*- #Justify_Derived "Utility function" *)
let alignof_struct_union env members =
  let rec align_rec al = function
  | [] -> Some al
  | m :: rem ->
      if m.fld_name = "" then
        align_rec al rem
      else
        match alignof env m.fld_typ with
        | None -> None
        | Some a -> align_rec (max a al) rem
  in align_rec 1 members
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_align_001 *)
(*- #Justify_Derived "Utility function" *)
let align x boundary =
  (* boundary must be a power of 2 *)
  (x + boundary - 1) land (lnot (boundary - 1))
(*- #End *)

(* Size of, in bytes *)

(*- E_COMPCERT_CODE_Cutil_sizeof_ikind_001 *)
(*- #Justify_Derived "Utility function" *)
let sizeof_ikind = function
  | IBool | IChar | ISChar | IUChar -> 1
  | IInt | IUInt -> !config.sizeof_int
  | IShort | IUShort -> !config.sizeof_short
  | ILong | IULong -> !config.sizeof_long
  | ILongLong | IULongLong -> !config.sizeof_longlong
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_sizeof_fkind_001 *)
(*- #Justify_Derived "Utility function" *)
let sizeof_fkind = function
  | FFloat -> !config.sizeof_float
  | FDouble -> !config.sizeof_double
  | FLongDouble -> !config.sizeof_longdouble
(*- #End *)

(* Overflow-avoiding multiplication of an int64 and an int, with
   result in type int. *)

(*- E_COMPCERT_CODE_Cutil_cautious_mul_001 *)
(*- #Justify_Derived "Utility function" *)
let cautious_mul (a: int64) (b: int) =
  if b = 0 || a <= Int64.of_int (max_int / b)
  then Some(Int64.to_int a * b)
  else None
(*- #End *)

(* Return size of type, in bytes, or [None] if the type is incomplete *)

(*- E_COMPCERT_CODE_Cutil_sizeof_001 *)
(*- #Justify_Derived "Utility function" *)
let rec sizeof env t =
  match t with
  | TVoid _ -> !config.sizeof_void
  | TInt(ik, _) -> Some(sizeof_ikind ik)
  | TFloat(fk, _) -> Some(sizeof_fkind fk)
  | TPtr(_, _) -> Some(!config.sizeof_ptr)
  | TArray(ty, None, _) -> None
  | TArray(ty, Some n, _) as t' ->
      begin match sizeof env ty with
      | None -> None
      | Some s ->
          match cautious_mul n s with
          | Some sz -> Some sz
          (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_089 *)
          | None -> error no_loc "sizeof(%a) overflows" Cprint.typ t'; Some 1
      end
  | TFun(_, _, _, _) -> !config.sizeof_fun
  | TNamed(_, _) -> sizeof env (unroll env t)
  | TStruct(name, _) ->
      let ci = Env.find_struct env name in ci.ci_sizeof
  | TUnion(name, _) ->
      let ci = Env.find_union env name in ci.ci_sizeof
  | TEnum(_, _) -> Some(sizeof_ikind enum_ikind)
(*- #End *)

(* Compute the size of a union.
   It is the size is the max of the sizes of fields.
   Not done here but in composite_info_def: rounding size to alignment. *)

(*- E_COMPCERT_CODE_Cutil_sizeof_union_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let sizeof_union env members =
  let rec sizeof_rec sz = function
  | [] ->
      Some sz
  | m :: rem ->
      begin match sizeof env m.fld_typ with
      | None -> None
      | Some s -> sizeof_rec (max sz s) rem
      end
  in sizeof_rec 0 members
(*- #End *)

(* Compute the size of a struct and the byte offset of the members.
   We lay out fields consecutively, inserting padding to preserve
   their alignment.
   The [ma] parameter is the maximal alignment for each member.
   It is used for packed structs.  If [ma = 0], it is ignored.
   Bitfields are taken into account for the size and offset computations
   but not given an offset.
   Not done here but in composite_info_def: rounding size to alignment. *)

(*- E_COMPCERT_CODE_Cutil_sizeof_layout_struct_001 *)
(*- #Link_to E_COMPCERT_TR_Function_PACKED_STRUCT_016 *)
let sizeof_layout_struct env members ma =

  let align_bit_offset pos a =
    align pos (8 * (if ma > 0 && a > ma then ma else a)) in

  let record_field name pos =
    assert (pos mod 8 = 0);
    (name, pos / 8) in

  (* pos is the current position in bits *)
  let rec sizeof_rec pos accu = function
  | [] ->
      Some (pos, accu)
  | [ { fld_typ = TArray(_, None, _) } as m ] ->
      (* C99: ty[] allowed as last field *)
      begin match alignof env m.fld_typ with
      | Some a ->
          let pos = align_bit_offset pos a in
          Some (pos, record_field m.fld_name pos :: accu)
      | None -> None
      end
  | m :: rem ->
      begin match alignof env m.fld_typ, sizeof env m.fld_typ with
      | Some a, Some s ->
          begin match m.fld_bitfield with
          | None ->
              let pos = align_bit_offset pos a in
              sizeof_rec (pos + s * 8)
                         (record_field m.fld_name pos :: accu)
                         rem
          | Some width ->
              (* curr = beginning of storage unit, in bits
                 next = one past end of storage unit, in bits *)
              let curr = pos / (a * 8) * (a * 8) in
              let next = curr + s * 8 in
              let pos' =
                if width <= 0 then align pos (a * 8)
                else if pos + width <= next then pos + width
                else next + width in
              sizeof_rec pos' accu rem
          end
      | _, _ ->
          None
      end
  in sizeof_rec 0 [] members
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_sizeof_struct_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let sizeof_struct env members ma =
  match sizeof_layout_struct env members ma with
  | None -> None
  | Some(bitsize, offsets) -> Some ((bitsize + 7) / 8)
(*- #End *)

(* Compute the offsets of all non-bitfield members of a struct. *)
(*- E_COMPCERT_CODE_Cutil_struct_layout_001 *)
(*- #Link_to E_COMPCERT_TR_Function_PACKED_STRUCT_016 *)
let struct_layout env attrs members =
  let (ma, _, _) = packing_parameters attrs in
  match sizeof_layout_struct env members ma with
  | Some(bitsize, offsets) -> offsets
  | None -> []
(*- #End *)

(* Compute the offset of a struct member *)
(*- E_COMPCERT_CODE_Cutil_offsetof_001 *)
(*- #Justify_Derived "Utility function" *)
let offsetof env ty field =
  match unroll env ty with
  | TStruct (id, _) ->
      let str = Env.find_struct env id in
      let offsets = struct_layout env str.ci_attr str.ci_members in
      begin try
        List.assoc field.fld_name offsets
      with Not_found ->
        raise (Env.Error(No_member(id.C.name, "struct", field.fld_name)))
      end
  | TUnion _ -> 0
  | _ -> assert false
(*- #End *)

(* Determine whether a type is incomplete *)

(*- E_COMPCERT_CODE_Cutil_incomplete_type_001 *)
(*- #Justify_Derived "Utility function" *)
let incomplete_type env t =
  match unroll env t with
  | TVoid _ -> true (* Void is always incomplete *)
  | _ -> begin match sizeof env t with
    | None -> true
    | Some _ -> false
  end
(*- #End *)

(* Computing composite_info records *)

(*- E_COMPCERT_CODE_Cutil_composite_info_decl_001 *)
(*- #Justify_Derived "Utility function" *)
let composite_info_decl su attr =
  { ci_kind = su; ci_members = [];
    ci_alignof = None; ci_sizeof = None;
    ci_attr = attr }
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_composite_info_def_001 *)
(*- #Justify_Derived "Utility function" *)
let composite_info_def env su attr m =
  let (max_field_align, min_struct_align, swapped) = packing_parameters attr in
  let attr_align = alignas_attribute attr in
  let natural_align = alignof_struct_union env m in
  let al =
    (* alignas takes precedence over packing *)
    if attr_align > 0 then Some attr_align
    (* ignore packing on unions for compatibility with earlier versions *)
    else if su = Union then natural_align
    else begin
      match natural_align with
      | None -> None
      | Some a ->
          (* If max_field_align is given, reduce natural alignment a
             to be at most max_field_align *)
          let a =
            if max_field_align > 0 && a > max_field_align
            then max_field_align
            else a in
          (* If min_struct_align is given, increase alignment a
             to be at least min_struct_align *)
          let a =
            if min_struct_align > 0 && a < min_struct_align
            then min_struct_align
            else a in
          Some a
      end in
  let sz =
    match su with
    | Struct -> sizeof_struct env m max_field_align
    | Union -> sizeof_union env m
  in
  { ci_kind = su; ci_members = m;
    ci_alignof = al;
    ci_sizeof =
      begin match sz, al with
      | Some s, Some a -> Some (align s a)
      | _, _ -> None
      end;
    ci_attr = attr }
(*- #End *)

(* Is an integer [v] representable in [n] bits, signed or unsigned? *)

(*- E_COMPCERT_CODE_Cutil_int_representable_001 *)
(*- #Justify_Derived "Utility function" *)
let int_representable v nbits sgn =
  if nbits >= 64 then true else
  if sgn then
    let p = Int64.shift_left 1L (nbits - 1) in Int64.neg p <= v && v < p
  else
    0L <= v && v < Int64.shift_left 1L nbits
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_valid_array_size_001 *)
(*- #Justify_Derived "Utility function" *)
let valid_array_size env ty v =
  match sizeof env ty with
  | None -> true (* Incomplete type should be caught later *)
  | Some sz ->
    let sz = Int64.of_int sz in
    let ptr_bits = !Machine.config.sizeof_ptr * 8 - 1 in
    if sz = 0L || v <= (Int64.div Int64.max_int sz) then
      int_representable (Int64.mul sz v) ptr_bits true
    else
      false
(*- #End *)

(* Type of a function definition *)

(*- E_COMPCERT_CODE_Cutil_fundef_typ_001 *)
(*- #Justify_Derived "Utility function" *)
let fundef_typ fd =
  TFun(fd.fd_ret, Some fd.fd_params, fd.fd_vararg, fd.fd_attrib)
(*- #End *)

(* Signedness of integer kinds *)

(*- E_COMPCERT_CODE_Cutil_is_signed_ikind_001 *)
(*- #Justify_Derived "Utility function" *)
let is_signed_ikind = function
  | IBool -> false
  | IChar -> !config.char_signed
  | ISChar -> true
  | IUChar -> false
  | IInt -> true
  | IUInt -> false
  | IShort -> true
  | IUShort -> false
  | ILong -> true
  | IULong -> false
  | ILongLong -> true
  | IULongLong -> false
(*- #End *)

(* Conversion to unsigned ikind *)

(*- E_COMPCERT_CODE_Cutil_unsigned_ikind_of_001 *)
(*- #Justify_Derived "Utility function" *)
let unsigned_ikind_of = function
  | IBool -> IBool
  | IChar | ISChar | IUChar -> IUChar
  | IInt | IUInt -> IUInt
  | IShort | IUShort -> IUShort
  | ILong | IULong -> IULong
  | ILongLong | IULongLong -> IULongLong
(*- #End *)

(* Conversion to signed ikind *)

(*- E_COMPCERT_CODE_Cutil_signed_ikind_of_001 *)
(*- #Justify_Derived "Utility function" *)
let signed_ikind_of = function
  | IBool -> IBool
  | IChar | ISChar | IUChar -> ISChar
  | IInt | IUInt -> IInt
  | IShort | IUShort -> IShort
  | ILong | IULong -> ILong
  | ILongLong | IULongLong -> ILongLong
(*- #End *)

(* Some classification functions over types *)

(*- E_COMPCERT_CODE_Cutil_is_void_type_001 *)
(*- #Justify_Derived "Utility function" *)
let is_void_type env t =
  match unroll env t with
  | TVoid _ -> true
  | _ -> false
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_is_integer_type_001 *)
(*- #Justify_Derived "Utility function" *)
let is_integer_type env t =
  match unroll env t with
  | TInt(_, _) -> true
  | TEnum(_, _) -> true
  | _ -> false
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_is_float_type_001 *)
(*- #Justify_Derived "Utility function" *)
let is_float_type env t =
  match unroll env t with
  | TFloat (_, _) -> true
  | _ -> false
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_is_arith_type_001 *)
(*- #Justify_Derived "Utility function" *)
let is_arith_type env t =
  match unroll env t with
  | TInt(_, _) -> true
  | TFloat(_, _) -> true
  | TEnum(_, _) -> true
  | _ -> false
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_is_pointer_type_001 *)
(*- #Justify_Derived "Utility function" *)
let is_pointer_type env t =
  match unroll env t with
  | TPtr _ -> true
  | _ -> false
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_is_scalar_type_001 *)
(*- #Justify_Derived "Utility function" *)
let is_scalar_type env t =
  match unroll env t with
  | TInt(_, _) -> true
  | TFloat(_, _) -> true
  | TPtr _ -> true
  | TArray _ -> true                    (* assume implicit decay *)
  | TFun _ -> true                      (* assume implicit decay *)
  | TEnum(_, _) -> true
  | _ -> false
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_is_composite_type_001 *)
(*- #Justify_Derived "Utility function" *)
let is_composite_type env t =
  match unroll env t with
  | TStruct _ | TUnion _ -> true
  | _ -> false
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_is_array_type_001 *)
(*- #Justify_Derived "Utility function" *)
let is_array_type env t =
  match unroll env t with
  | TArray _ -> true
  | _ -> false
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_is_function_type_001 *)
(*- #Justify_Derived "Utility function" *)
let is_function_type env t =
  match unroll env t with
  | TFun _ -> true
  | _ -> false
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_is_anonymous_composite_001 *)
(*- #Justify_Derived "Utility function" *)
let is_anonymous_composite = function
  | TStruct (id,_)
  | TUnion (id,_) -> id.C.name = ""
  | _ -> false
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_is_anonymous_type_001 *)
(*- #Justify_Derived "Utility function" *)
let is_anonymous_type = function
  | TEnum (id,_)
  | TStruct (id,_)
  | TUnion (id,_) -> id.C.name = ""
  | _ -> false
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_is_function_pointer_type_001 *)
(*- #Justify_Derived "Utility function" *)
let is_function_pointer_type env t =
  match unroll env t with
  | TPtr (ty, _) -> is_function_type env ty
  | _ -> false
(*- #End *)

(* Find the info for a field access *)

(*- E_COMPCERT_CODE_Cutil_field_of_dot_access_001 *)
(*- #Justify_Derived "Utility function" *)
let field_of_dot_access env t m =
 let m = match unroll env t with
   | TStruct(id, _) -> Env.find_struct_member env (id, m)
   | TUnion(id, _) -> Env.find_union_member env (id, m)
   | _ -> assert false in
 List.hd (List.rev m)
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_field_of_arrow_access_001 *)
(*- #Justify_Derived "Utility function" *)
let field_of_arrow_access env t m =
  match unroll env t with
  | TPtr(t, _) | TArray(t, _, _) -> field_of_dot_access env t m
  | _ -> assert false
(*- #End *)

(* Ranking of integer kinds *)

(*- E_COMPCERT_CODE_Cutil_integer_rank_001 *)
(*- #Link_to E_COMPCERT_TR_Function_ELAB_177 *)
let integer_rank = function
  | IBool -> 1
  | IChar | ISChar | IUChar -> 2
  | IShort | IUShort -> 3
  | IInt | IUInt -> 4
  | ILong | IULong -> 5
  | ILongLong | IULongLong -> 6
(*- #End *)

(* Ranking of float kinds *)

(*- E_COMPCERT_CODE_Cutil_float_rank_001 *)
(*- #Justify_Derived "Utility function" *)
let float_rank = function
  | FFloat -> 1
  | FDouble -> 2
  | FLongDouble -> 3
(*- #End *)

(* Test for qualified array types *)

(*- E_COMPCERT_CODE_Cutil_is_qualified_array_001 *)
(*- #Justify_Derived "Utility function" *)
let rec is_qualified_array = function
  | TArray (ty, _, attr) ->
    List.exists attr_is_standard attr || is_qualified_array ty
  | TPtr (ty, _) -> is_qualified_array ty
  | TFun(ty_ret, _, _, _) -> is_qualified_array ty_ret
  | _ -> false
(*- #End *)

(* Array and function types "decay" to pointer types in many cases *)

(*- E_COMPCERT_CODE_Cutil_pointer_decay_001 *)
(*- #Justify_Derived "Utility function" *)
let pointer_decay env t =
  match unroll env t with
  | TArray(ty, _, _) -> TPtr(ty, [])
  | TFun _ as ty -> TPtr(ty, [])
  | t -> t
(*- #End *)

(* The usual unary conversions (H&S 6.3.3) *)

(*- E_COMPCERT_CODE_Cutil_unary_conversion_001 *)
(*- #Justify_Derived "Utility function" *)
let unary_conversion env t =
  match unroll env t with
  (* Promotion of small integer types *)
  | TInt(kind, attr) ->
      begin match kind with
      | IBool | IChar | ISChar | IUChar | IShort | IUShort ->
          TInt(IInt, [])
      | IInt | IUInt | ILong | IULong | ILongLong | IULongLong ->
          TInt(kind, [])
      end
  (* Enums are like signed ints *)
  | TEnum(id, attr) -> TInt(enum_ikind, [])
  (* Arrays and functions decay automatically to pointers *)
  | TArray(ty, _, _) -> TPtr(ty, [])
  | TFun _ as ty -> TPtr(ty, [])
  (* Float types and pointer types lose their attributes *)
  | TFloat(kind, attr) -> TFloat(kind, [])
  | TPtr(ty, attr) -> TPtr(ty, [])
  (* Other types should not occur, but in doubt... *)
  | _ -> t
(*- #End *)

(* The usual binary conversions  (H&S 6.3.4).
   Applies only to arithmetic types.
   Return the type to which both sides are to be converted. *)

(*- E_COMPCERT_CODE_Cutil_binary_conversion_001 *)
(*- #Justify_Derived "Utility function" *)
let binary_conversion env t1 t2 =
  let t1 = unary_conversion env t1 in
  let t2 = unary_conversion env t2 in
  match unroll env t1, unroll env t2 with
  | TFloat(FLongDouble, _), (TInt _ | TFloat _) -> t1
  | (TInt _ | TFloat _), TFloat(FLongDouble, _) -> t2
  | TFloat(FDouble, _), (TInt _ | TFloat _)     -> t1
  | (TInt _ | TFloat _), TFloat(FDouble, _)     -> t2
  | TFloat(FFloat, _), (TInt _ | TFloat _)      -> t1
  | (TInt _), TFloat(FFloat, _)      -> t2
  | TInt(k1, _), TInt(k2, _)  ->
      if k1 = k2 then t1 else begin
        (*- #Link_to E_COMPCERT_TR_Function_ELAB_177 *)
        match is_signed_ikind k1, is_signed_ikind k2 with
        | true, true | false, false ->
            (* take the bigger of the two types *)
            if integer_rank k1 >= integer_rank k2 then t1 else t2
        | false, true ->
            (* if rank (unsigned type) >= rank (signed type),
               take the unsigned type *)
            if integer_rank k1 >= integer_rank k2 then t1
            (* if rank (unsigned type) < rank (signed type)
               and all values of the unsigned type can be represented
               in the signed type, take the signed type *)
            else if sizeof_ikind k2 > sizeof_ikind k1 then t2
            (* if rank (unsigned type) < rank (signed type)
               and some values of the unsigned type cannot be represented
               in the signed type,
               take the unsigned type corresponding to the signed type *)
            else TInt(unsigned_ikind_of k2, [])
        | true, false ->
            if integer_rank k2 >= integer_rank k1 then t2
            else if sizeof_ikind k1 > sizeof_ikind k2 then t1
            else TInt(unsigned_ikind_of k1, [])
      end
  | _, _ -> assert false
(*- #End *)

(* Conversion on function arguments (with prototypes) *)

(*- E_COMPCERT_CODE_Cutil_argument_conversion_001 *)
(*- #Justify_Derived "Utility function" *)
let argument_conversion env t =
  (* Arrays and functions degrade automatically to pointers *)
  (* Other types are not changed *)
  match unroll env t with
  | TArray(ty, _, attr) -> TPtr(ty, attr)
  | TFun _ as ty -> TPtr(ty, [])
  | _ -> t (* preserve typedefs *)
(*- #End *)

(* Conversion on function arguments (old-style unprototyped, or vararg *)
(* H&S 6.3.5 *)

(*- E_COMPCERT_CODE_Cutil_default_argument_conversion_001 *)
(*- #Justify_Derived "Utility function" *)
let default_argument_conversion env t =
  match unary_conversion env t with
  | TFloat(FFloat, attr) -> TFloat(FDouble, attr)
  | t' -> t'
(*- #End *)

(** Is the type Tptr(ty, a) appropriate for pointer arithmetic? *)

(*- E_COMPCERT_CODE_Cutil_pointer_arithmetic_ok_001 *)
(*- #Justify_Derived "Utility function" *)
let pointer_arithmetic_ok env ty =
  match unroll env ty with
  | TVoid _ | TFun _ -> false
  | _ -> not (incomplete_type env ty)
(*- #End *)

(** The type of [x.fld].  Normally, it's the type of the field [fld],
  but if it is an unsigned bitfield of size < length of its type,
  its type is the corresponding signed int. *)

(*- E_COMPCERT_CODE_Cutil_type_of_member_001 *)
(*- #Justify_Derived "Utility function" *)
let type_of_member env fld =
  match fld.fld_bitfield with
  | None -> fld.fld_typ
  | Some w ->
      let (ik, attr) =
        match unroll env fld.fld_typ with
        | TInt(ik, attr) -> (ik, attr)
        | TEnum(_, attr) -> (enum_ikind, attr)
        | _ -> assert false in
      if w < sizeof_ikind ik * 8
      then TInt(signed_ikind_of ik, attr)
      else fld.fld_typ
(*- #End *)

(** Special types *)

(*- E_COMPCERT_CODE_Cutil_find_matching_unsigned_ikind_001 *)
(*- #Justify_Derived "Utility function" *)
let find_matching_unsigned_ikind sz =
  assert (sz > 0);
  if sz = !config.sizeof_short then IUShort
  else if sz = !config.sizeof_int then IUInt
  else if sz = !config.sizeof_long then IULong
  else if sz = !config.sizeof_longlong then IULongLong
  else assert false
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_find_matching_signed_ikind_001 *)
(*- #Justify_Derived "Utility function" *)
let find_matching_signed_ikind sz =
  assert (sz > 0);
  if sz = !config.sizeof_int then IInt
  else if sz = !config.sizeof_long then ILong
  else if sz = !config.sizeof_longlong then ILongLong
  else assert false
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_type_ikind_001 *)
(*- #Justify_Derived "Utility function" *)
let wchar_ikind () =
  if !config.wchar_signed
  then find_matching_signed_ikind !config.sizeof_wchar
  else find_matching_unsigned_ikind !config.sizeof_wchar
(*- #End *)
(*- E_COMPCERT_CODE_Cutil_type_ikind_002 *)
(*- #Justify_Derived "Utility function" *)
let size_t_ikind () = find_matching_unsigned_ikind !config.sizeof_size_t
(*- #End *)
(*- E_COMPCERT_CODE_Cutil_type_ikind_003 *)
(*- #Justify_Derived "Utility function" *)
let ptr_t_ikind () = find_matching_unsigned_ikind !config.sizeof_ptr
(*- #End *)
(*- E_COMPCERT_CODE_Cutil_type_ikind_004 *)
(*- #Justify_Derived "Utility function" *)
let ptrdiff_t_ikind () = find_matching_signed_ikind !config.sizeof_ptrdiff_t
(*- #End *)

(** The type of a constant *)

(*- E_COMPCERT_CODE_Cutil_type_of_constant_001 *)
(*- #Justify_Derived "Utility function" *)
let type_of_constant = function
  | CInt(_, ik, _) -> TInt(ik, [])
  | CFloat(_, fk) -> TFloat(fk, [])
  | CStr s ->
    let size = Int64.of_int (String.length s + 1) in
    TArray(TInt(IChar,[]), Some size, [])
  | CWStr s ->
    let size = Int64.of_int (List.length s + 1) in
    TArray(TInt(wchar_ikind(), []), Some size, [])
  | CEnum(_, _) -> TInt(IInt, [])
(*- #End *)

(* Check that a C expression is a lvalue *)

(*- E_COMPCERT_CODE_Cutil_is_lvalue_001 *)
(*- #Justify_Derived "Utility function" *)
let rec is_lvalue e =
  match e.edesc with
  | EVar id -> true
  | EConst (CStr _)
  | EConst (CWStr _) -> true
  | EUnop((Oderef | Oarrow _), _) -> true
  | EUnop(Odot _, e') -> is_lvalue e'
  | EBinop(Oindex, _, _, _) -> true
  | ECompound _ -> true
  | _ -> false
(*- #End *)

(* Check that a C expression is a modifiable l-value: an l-value
   whose type is not const, neither an array type, nor a function type,
   nor an incomplete type. *)

(*- E_COMPCERT_CODE_Cutil_is_const_type_001 *)
(*- #Justify_Derived "Utility function" *)
let rec is_const_type env ty =
  List.mem AConst (attributes_of_type env ty) ||
  begin match unroll env ty with
  | TStruct(s, a) ->
      let ci = Env.find_struct env s in
      List.exists (fun m -> is_const_type env m.fld_typ) ci.ci_members
  | TUnion(s, a) ->
      let ci = Env.find_union env s in
      List.exists (fun m -> is_const_type env m.fld_typ) ci.ci_members
  | _ ->
      false
  end
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_is_modifiable_lvalue_001 *)
(*- #Justify_Derived "Utility function" *)
let is_modifiable_lvalue env e =
  is_lvalue e
  && not (incomplete_type env e.etyp)
  && not (is_const_type env e.etyp)
  && begin match unroll env e.etyp with
     | TFun _ | TArray _ -> false
     | _ -> true
     end
(*- #End *)

(* Check that a C expression is the literal "0", which can be used
   as a pointer. *)

(*- E_COMPCERT_CODE_Cutil_is_literal_0_001 *)
(*- #Justify_Derived "Utility function" *)
let is_literal_0 e =
  match e.edesc with
  | EConst(CInt(0L, _, _)) -> true
  | _ -> false
(*- #End *)

(* Check that a C statement is a debug annotation *)

(*- E_COMPCERT_CODE_Cutil_is_debug_stmt_001 *)
(*- #Justify_Derived "Utility function" *)
let is_debug_stmt s =
  let is_debug_call = function
    | (ECall ({edesc = EVar id; _},_)) -> id.C.name = "__builtin_debug"
    | _ -> false in
  match s.sdesc with
  | Sdo {edesc = e;_} ->
      is_debug_call e
  | _ -> false
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_is_call_to_fun_001 *)
(*- #Justify_Derived "Utility function" *)
let is_call_to_fun e s =
  match e.edesc with
  | EVar id -> id.C.name = s
  | _ -> false
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_is_bitfield_001 *)
(*- #Justify_Derived "Utility function" *)
let is_bitfield env e =
  match e.edesc with
  | EUnop(Odot f,b) ->
    let fld = field_of_dot_access env b.etyp f in
    fld.fld_bitfield <> None
  | EUnop(Oarrow f,b) ->
    let fld = field_of_arrow_access env b.etyp f in
    fld.fld_bitfield <> None
  | _ -> false
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_find_flex_array_mem_001 *)
(*- #Justify_Derived "Utility function" *)
let find_flex_array_mem env id =
  let ci = Env.find_struct env id in
  let rec find_mem = function
    | [] -> None
    | [ { fld_typ = TArray (ty_elf, None, _); fld_name = name} ] ->
      Some name
    | _ :: rem -> find_mem rem in
  find_mem ci.ci_members
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_contains_flex_array_mem_001 *)
(*- #Justify_Derived "Utility function" *)
let contains_flex_array_mem env ty =
  match unroll env ty with
  | TStruct (id,_) ->
    find_flex_array_mem env id <> None
  | _ -> false
(*- #End *)

(* Assignment compatibility check over attributes.
   Standard attributes ("const", "volatile", "restrict") can safely
   be added (to the rhs type to get the lhs type) but must not be dropped.
   Custom attributes can safely be dropped or added. *)

(*- E_COMPCERT_CODE_Cutil_valid_assignment_attr_001 *)
(*- #Justify_Derived "Utility function" *)
let valid_assignment_attr afrom ato =
  let (afromstd, afromcustom) = List.partition attr_is_standard afrom
  and (atostd, atocustom) = List.partition attr_is_standard ato in
  incl_attributes afromstd atostd
(*- #End *)

(* Check that an assignment is allowed *)

(*- E_COMPCERT_CODE_Cutil_valid_assignment_001 *)
(*- #Justify_Derived "Utility function" *)
let valid_assignment env from tto =
  match pointer_decay env from.etyp, pointer_decay env tto with
  | (TInt _ | TFloat _ | TEnum _), (TInt _ | TFloat _ | TEnum _) -> true
  | TInt _, TPtr _ -> is_literal_0 from
  | TPtr(ty, _), TPtr(ty', _) ->
      valid_assignment_attr (attributes_of_type env ty)
                            (attributes_of_type env ty')
      && (is_void_type env ty || is_void_type env ty'
          || compatible_types AttrIgnoreTop env ty ty')
  | TStruct(s, _), TStruct(s', _) -> s = s'
  | TUnion(s, _), TUnion(s', _) -> s = s'
  | _, _ -> false
(*- #End *)

(* Check that a cast is allowed *)

(*- E_COMPCERT_CODE_Cutil_valid_cast_001 *)
(*- #Justify_Derived "Utility function" *)
let valid_cast env tfrom tto =
  match unroll env tfrom, unroll env tto with
  (* from any type to void *)
  | _, TVoid _ -> true
  (* from any int-or-pointer (with array and functions decaying to pointers)
     to any int-or-pointer *)
  | (TInt _ | TPtr _ | TArray _ | TFun _ | TEnum _),
    (TInt _ | TPtr _ | TEnum _) -> true
  (* between int and float types *)
  | (TInt _ | TFloat _ | TEnum _), (TInt _ | TFloat _ | TEnum _) -> true
  | _, _ -> false
(*- #End *)

(* Check that the cast from tfrom to tto is an integer to pointer conversion *)

(*- E_COMPCERT_CODE_Cutil_int_pointer_conversion_001 *)
(*- #Justify_Derived "Utility function" *)
let int_pointer_conversion env tfrom tto =
  match unroll env tfrom, unroll env tto with
  | (TInt _ | TEnum _),(TPtr _)
  | (TPtr _),(TInt _ | TEnum _) -> true
  | _,_ -> false
(*- #End *)

(* Construct an integer constant *)

(*- E_COMPCERT_CODE_Cutil_intconst_001 *)
(*- #Justify_Derived "Utility function" *)
let intconst v ik =
  { edesc = EConst(CInt(v, ik, "")); etyp = TInt(ik, []) }
(*- #End *)

(* Construct the 0 float constant of double type *)

(*- E_COMPCERT_CODE_Cutil_floatconst0_001 *)
(*- #Justify_Derived "Utility function" *)
let floatconst0 =
  { edesc = EConst(CFloat(FConstant {hex=false; intPart="0"; fracPart="0"; exp="0"}, FDouble));
    etyp = TFloat(FDouble, []) }
(*- #End *)

(* Construct a cast expression *)

(*- E_COMPCERT_CODE_Cutil_ecast_001 *)
(*- #Justify_Derived "Utility function" *)
let ecast ty e = { edesc = ECast(ty, e); etyp = ty }
(*- #End *)

(* Construct the literal "0" with void * type *)

(*- E_COMPCERT_CODE_Cutil_nullconst_001 *)
(*- #Justify_Derived "Utility constant" *)
let nullconst = ecast (TPtr(TVoid [], [])) (intconst 0L IInt)
(*- #End *)

(* Construct an assignment expression *)

(*- E_COMPCERT_CODE_Cutil_eassign_001 *)
(*- #Justify_Derived "Utility function" *)
let eassign e1 e2 = { edesc = EBinop(Oassign, e1, e2, e1.etyp); etyp = e1.etyp }
(*- #End *)

(* Construct a "," expression.  Reassociate to the left so that
   it prints more nicely. *)

(*- E_COMPCERT_CODE_Cutil_ecomma_001 *)
(*- #Justify_Derived "Utility function" *)
let rec ecomma e1 e2 =
  match e2.edesc with
  | EBinop(Ocomma, e2', e2'', _) ->
     ecomma (ecomma e1 e2') e2''
  | _ ->
     { edesc = EBinop(Ocomma, e1, e2, e2.etyp); etyp = e2.etyp }
(*- #End *)

(* Construct a cascade of "," expressions.
   Associate to the left so that it prints more nicely. *)

(*- E_COMPCERT_CODE_Cutil_ecommalist_001 *)
(*- #Justify_Derived "Utility function" *)
let ecommalist el e =
  match el with
  | [] -> e
  | e1 :: el -> ecomma (List.fold_left ecomma e1 el) e
(*- #End *)

(* Construct an address-of expression.  Can be applied not just to
   an l-value but also to a sequence or a conditional of l-values. *)

(*- E_COMPCERT_CODE_Cutil_eaddrof_001 *)
(*- #Justify_Derived "Utility function" *)
let rec eaddrof e =
  match e.edesc with
  | EUnop(Oderef, e1) -> e1
  | EBinop(Ocomma, e1, e2, _) -> ecomma e1 (eaddrof e2)
  | EConditional(e1, e2, e3) ->
      { edesc = EConditional(e1, eaddrof e2, eaddrof e3); etyp = TPtr(e.etyp, []) }
  | _ -> { edesc = EUnop(Oaddrof, e); etyp = TPtr(e.etyp, []) }
(*- #End *)

(* Construct a sequence *)

(*- E_COMPCERT_CODE_Cutil_sseq_001 *)
(*- #Justify_Derived "Utility function" *)
let sseq loc s1 s2 =
  match s1.sdesc, s2.sdesc with
  | Sskip, _ -> s2
  | _, Sskip -> s1
  | _, Sblock sl -> { sdesc = Sblock(s1 :: sl); sloc = loc }
  | _, _ -> { sdesc = Sseq(s1, s2); sloc = loc }
(*- #End *)

(* Construct an assignment statement *)

(*- E_COMPCERT_CODE_Cutil_sassign_001 *)
(*- #Justify_Derived "Utility function" *)
let sassign loc lv rv =
  { sdesc = Sdo (eassign lv rv); sloc = loc }
(*- #End *)

(* Dummy skip statement *)

(*- E_COMPCERT_CODE_Cutil_sskip_001 *)
(*- #Justify_Derived "Utility constant" *)
let sskip = { sdesc = Sskip; sloc = no_loc }
(*- #End *)

(* Print a location *)

(*- E_COMPCERT_CODE_Cutil_printloc_001 *)
(*- #Justify_Derived "Utility function" *)
let printloc oc (filename, lineno) =
  if filename <> "" then Printf.fprintf oc "%s:%d: " filename lineno
(*- #End *)

(* Format a location *)

(*- E_COMPCERT_CODE_Cutil_formatloc_001 *)
(*- #Justify_Derived "Utility function" *)
let formatloc pp (filename, lineno) =
  if filename <> "" then Format.fprintf pp "%s:%d: " filename lineno
(*- #End *)

(* Generate the default initializer for the given type *)
exception No_default_init

(*- E_COMPCERT_CODE_Cutil_default_init_001 *)
(*- #Justify_Derived "Utility function" *)
let rec default_init env ty =
  match unroll env ty with
  | TInt _ | TEnum _ ->
      Init_single (intconst 0L IInt)
  | TFloat(fk, _) ->
      Init_single floatconst0
  | TPtr(ty, _) ->
      Init_single nullconst
  | TArray(ty, sz, _) ->
      Init_array []
  | TStruct(id, _) ->
      let rec default_init_fields = function
      | [] -> []
      | f1 :: fl ->
          if f1.fld_name = ""
          then default_init_fields fl
          else (f1, default_init env f1.fld_typ) :: default_init_fields fl in
      let ci = Env.find_struct env id in
      Init_struct(id, default_init_fields ci.ci_members)
  | TUnion(id, _) ->
      let ci = Env.find_union env id in
      begin match ci.ci_members with
      | [] -> raise No_default_init
      | fld :: _ -> Init_union(id, fld, default_init env fld.fld_typ)
      end
  | _ ->
      raise No_default_init
(*- #End *)

(* Substitution of variables by expressions *)

(*- E_COMPCERT_CODE_Cutil_subst_expr_001 *)
(*- #Justify_Derived "Utility function" *)
let rec subst_expr phi e =
  match e.edesc with
  | EConst _ | ESizeof _ | EAlignof _ -> e
  | EVar x ->
      begin try IdentMap.find x phi with Not_found -> e end
  | EUnop(op, e1) ->
      { e with edesc = EUnop(op, subst_expr phi e1) }
  | EBinop(op, e1, e2, ty) ->
      { e with edesc = EBinop(op, subst_expr phi e1, subst_expr phi e2, ty) }
  | EConditional(e1, e2, e3) ->
      { e with edesc =
          EConditional(subst_expr phi e1, subst_expr phi e2, subst_expr phi e3) }
  | ECast(ty, e1) ->
      { e with edesc = ECast(ty, subst_expr phi e1) }
  | ECompound(ty, i) ->
      { e with edesc = ECompound(ty, subst_init phi i) }
  | ECall(e1, el) ->
      { e with edesc = ECall(subst_expr phi e1, List.map (subst_expr phi) el) }
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_subst_init_001 *)
(*- #Justify_Derived "Utility function" *)
and subst_init phi = function
  | Init_single e -> Init_single (subst_expr phi e)
  | Init_array il -> Init_array (List.map (subst_init phi) il)
  | Init_struct(name, fl) ->
      Init_struct(name, List.map (fun (f,i) -> (f, subst_init phi i)) fl)
  | Init_union(name, f, i) ->
      Init_union(name, f, subst_init phi i)
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_subst_decl_001 *)
(*- #Justify_Derived "Utility function" *)
let subst_decl phi (sto, name, ty, optinit) =
  (sto, name, ty,
   match optinit with None -> None | Some i -> Some (subst_init phi i))
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_subst_stmt_001 *)
(*- #Justify_Derived "Utility function" *)
let rec subst_stmt phi s =
  { s with sdesc =
      match s.sdesc with
      | Sskip
      | Sbreak
      | Scontinue
      | Sgoto _ -> s.sdesc
      | Sdo e -> Sdo (subst_expr phi e)
      | Sseq(s1, s2) -> Sseq (subst_stmt phi s1, subst_stmt phi s2)
      | Sif(e, s1, s2) ->
          Sif (subst_expr phi e, subst_stmt phi s1, subst_stmt phi s2)
      | Swhile(e, s1) -> Swhile (subst_expr phi e, subst_stmt phi s1)
      | Sdowhile(s1, e) -> Sdowhile (subst_stmt phi s1, subst_expr phi e)
      | Sfor(s1, e, s2, s3) ->
          Sfor (subst_stmt phi s1, subst_expr phi e,
                subst_stmt phi s2, subst_stmt phi s3)
      | Sswitch(e, s1) -> Sswitch (subst_expr phi e, subst_stmt phi s1)
      | Slabeled(l, s1) -> Slabeled (l, subst_stmt phi s1)
      | Sreturn None -> s.sdesc
      | Sreturn (Some e) -> Sreturn (Some (subst_expr phi e))
      | Sblock sl -> Sblock (List.map (subst_stmt phi) sl)
      | Sdecl d -> Sdecl (subst_decl phi d)
      | Sasm(attr, template, outputs, inputs, clob) ->
          let subst_asm_operand (lbl, cstr, e) =
            (lbl, cstr, subst_expr phi e) in
          Sasm(attr, template,
               List.map subst_asm_operand outputs,
               List.map subst_asm_operand inputs,
               clob)
  }
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_is_volatile_variable_001 *)
(*- #Justify_Derived "Utility function" *)
let is_volatile_variable env exp =
  match exp.edesc with
  |  EVar x -> List.mem AVolatile (attributes_of_type env exp.etyp)
  | _ -> false
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_has_used_attribute_001 *)
(*- #Justify_Derived "Utility function" *)
let has_used_attribute attr =
  find_custom_attributes ["used"; "__used__"] attr <> []
(*- #End *)

(*- E_COMPCERT_CODE_Cutil_has_weaka_attribute_001 *)
(*- #Justify_Derived "Utility function" *)
let has_weak_attribute attr =
  find_custom_attributes ["weak"; "__weak__"] attr <> []
(*- #End *)
