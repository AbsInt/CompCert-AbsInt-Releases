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

(* Emulation of #pragma pack (experimental) *)

(* Assumes: unblocked code.
   Preserves: unblocked code. *)

open Printf
open Machine
open C
open Cutil
open Env
open Diagnostics
open Transform

(* The set of struct fields that are byte-swapped.
   A field is identified by a pair (struct name, field name). *)

(*- E_COMPCERT_CODE_PackedStructs_byteswapped_fields_001 *)
(*- #Justify_Derived "Variable for local state" *)
let byteswapped_fields : (ident * string, unit) Hashtbl.t
                       = Hashtbl.create 57
(*- #End *)

(* What are the types that can be byte-swapped? *)

(*- E_COMPCERT_CODE_PackedStructs_can_byte_swap_001 *)
(*- #Justify_Derived "Utility function" *)
let rec can_byte_swap env ty =
  match unroll env ty with
  | TInt(ik, _) -> (sizeof_ikind ik <= !config.sizeof_intreg, sizeof_ikind ik > 1)
  | TEnum(_, _) -> (true, sizeof_ikind enum_ikind > 1)
  | TPtr(_, _) -> (true, true)          (* tolerance? *)
  | TArray(ty_elt, _, _) -> can_byte_swap env ty_elt
  | _ -> (false, false)
(*- #End *)

(* "Safe" [alignof] function, with detection of incomplete types. *)

(*- E_COMPCERT_CODE_PackedStructs_safe_alignof_001 *)
(*- #Justify_Derived "Utility function" *)
let safe_alignof loc env ty =
  match alignof env ty with
  | Some al -> al
  | None ->
      error loc "incomplete type for a struct field"; 1
(*- #End *)

(* Remove existing [_Alignas] attributes and add the given [_Alignas] attr. *)

(*- E_COMPCERT_CODE_PackedStructs_remove_alignas_attr_001 *)
(*- #Justify_Derived "Utility function" *)
let remove_alignas_attr attrs =
  List.filter (function AAlignas _ -> false | _ -> true) attrs
(*- #End *)

(*- E_COMPCERT_CODE_PackedStructs_set_alignas_attr_001 *)
(*- #Justify_Derived "Utility function" *)
let set_alignas_attr al attrs =
  add_attributes [AAlignas al] (remove_alignas_attr attrs)
(*- #End *)

(* Rewriting field declarations *)

(*- E_COMPCERT_CODE_PackedStructs_transf_field_decl_001 *)
let transf_field_decl mfa swapped loc env struct_id f =
  if f.fld_bitfield <> None then
    (*- #Link_to E_COMPCERT_TR_Robustness_PACKED_STRUCT_008 *)
    error loc "bitfields in packed structs not allowed";
  (* Register as byte-swapped if needed *)
  if swapped then begin
    let (can_swap, must_swap) = can_byte_swap env f.fld_typ in
    if not can_swap then
      (*- #Link_to E_COMPCERT_TR_Robustness_PACKED_STRUCT_010 *)
      fatal_error loc "cannot byte-swap field of type '%a'"
        Cprint.typ f.fld_typ;
    if must_swap then
      Hashtbl.add byteswapped_fields (struct_id, f.fld_name) ()
  end;
  (* Reduce alignment if requested *)
  if mfa = 0 then f else begin
    let al = safe_alignof loc env f.fld_typ in
    (*- #Link_to E_COMPCERT_TR_Function_PACKED_STRUCT_006 *)
    { f with fld_typ =
         change_attributes_type env (set_alignas_attr (min mfa al)) f.fld_typ }
  end
(*- #End *)

(* Rewriting struct declarations *)

(*- E_COMPCERT_CODE_PackedStructs_transf_struct_decl_001 *)
let transf_struct_decl mfa msa swapped loc env struct_id attrs ml =
  let attrs' =
    (*- #Link_to E_COMPCERT_TR_Function_PACKED_STRUCT_004 *)
    remove_custom_attributes  ["packed";"__packed__"] attrs in
  let ml' =
    List.map (transf_field_decl mfa swapped loc env struct_id) ml in
  if msa = 0 then (attrs', ml') else begin
    (* [Cutil.composite_info_def] takes packing parameters into account.
       Hence the alignment it returns is the correct alignment for
       the transformed struct. *)
    let ci = Cutil.composite_info_def env Struct attrs ml in
    match ci.ci_alignof with
    | None -> error loc "incomplete struct"; (attrs', ml')
    | Some al -> (set_alignas_attr al attrs', ml')
  end
(*- #End *)

(* Rewriting composite declarations *)

(*- E_COMPCERT_CODE_PackedStructs_transf_composite_001 *)
let transf_composite loc env su id attrs ml =
  match su with
  | Union -> (attrs, ml)
  | Struct ->
      let (mfa, msa, swapped) =
        match find_custom_attributes ["packed";"__packed__"] attrs with
        | []  -> (0, 0, false)
        (*- #Link_to E_COMPCERT_TR_Function_PACKED_STRUCT_002 *)
        | [_] -> Cutil.packing_parameters attrs
        (*- #Link_to E_COMPCERT_TR_Robustness_PACKED_STRUCT_014 *)
        | _   -> error loc "multiple __packed__ attributes";
                 (0, 0, false) in
      transf_struct_decl mfa msa swapped loc env id attrs ml
(*- #End *)

(* Accessor functions *)

(*- E_COMPCERT_CODE_PackedStructs_lookup_function_001 *)
(*- #Justify_Derived "Utility function" *)
let lookup_function env name =
  match Env.lookup_ident env name with
  | (id, II_ident(sto, ty)) -> (id, ty)
  | (id, II_enum _) -> raise (Env.Error(Env.Unbound_identifier name))
(*- #End *)

(* Type for the access *)

(*- E_COMPCERT_CODE_PackedStructs_accessor_type_001 *)
(*- #Justify_Derived "Utility function" *)
let accessor_type loc env ty =
  match unroll env ty with
  | TInt(ik,_) -> (8 * sizeof_ikind ik, TInt(unsigned_ikind_of ik,[]))
  | TEnum(_,_) -> (8 * sizeof_ikind enum_ikind, TInt(unsigned_ikind_of enum_ikind,[]))
  | TPtr _     -> (8 * !config.sizeof_ptr, TInt(ptr_t_ikind(),[]))
  | _ ->
     error loc "unsupported type for byte-swapped field access";
     (32, TVoid [])
(*- #End *)

(*  (ty) e *)
(*- E_COMPCERT_CODE_PackedStructs_ecast_001 *)
(*- #Justify_Derived "Utility function" *)
let ecast ty e = {edesc = ECast(ty, e); etyp = ty}
(*- #End *)

(*- E_COMPCERT_CODE_PackedStructs_ecast_opt_001 *)
(*- #Justify_Derived "Utility function" *)
let ecast_opt env ty e =
  if compatible_types AttrCompat env ty e.etyp then e else ecast ty e
(*- #End *)

(*  (ty) __builtin_readNN_reversed(&lval)
 or (ty) __builtin_bswapNN(lval) *)

(*- E_COMPCERT_CODE_PackedStructs_use_reversed_001 *)
(*- #Justify_Derived "Variable for global state" *)
let use_reversed = ref false
(*- #End *)

(*- E_COMPCERT_CODE_PackedStructs_bswap_read_001 *)
(*- #Link_to E_COMPCERT_TR_Function_PACKED_STRUCT_005 *)
let bswap_read loc env lval =
  let ty = lval.etyp in
  let (bsize, aty) = accessor_type loc env ty in
  assert (bsize = 16 || bsize = 32 || (bsize = 64 && !config.sizeof_intreg = 8));
  try
    if !use_reversed then begin
      let (id, fty) =
        lookup_function env (sprintf "__builtin_read%d_reversed" bsize) in
      let fn = {edesc = EVar id; etyp = fty} in
      let args = [ecast_opt env (TPtr(aty,[])) (eaddrof lval)] in
      let call = {edesc = ECall(fn, args); etyp = aty} in
      ecast_opt env ty call
    end else begin
      let (id, fty) =
        lookup_function env (sprintf "__builtin_bswap%d" bsize) in
      let fn = {edesc = EVar id; etyp = fty} in
      let args = [ecast_opt env aty lval] in
      let call = {edesc = ECall(fn, args); etyp = aty} in
      ecast_opt env ty call
    end
  with Env.Error msg ->
    fatal_error loc "%s" (Env.error_message msg)
(*- #End *)

(*  __builtin_write_intNN_reversed(&lhs,rhs)
  or  lhs = __builtin_bswapNN(rhs) *)

(*- E_COMPCERT_CODE_PackedStructs_bswap_write_001 *)
(*- #Link_to E_COMPCERT_TR_Function_PACKED_STRUCT_005 *)
let bswap_write loc env lhs rhs =
  let ty = lhs.etyp in
  let (bsize, aty) =
    accessor_type loc env ty in
  assert (bsize = 16 || bsize = 32 || (bsize = 64 && !config.sizeof_intreg = 8));
  try
    if !use_reversed then begin
      let (id, fty) =
        lookup_function env (sprintf "__builtin_write%d_reversed" bsize) in
      let fn = {edesc = EVar id; etyp = fty} in
      let args = [ecast_opt env (TPtr(aty,[])) (eaddrof lhs);
                  ecast_opt env aty rhs] in
      {edesc = ECall(fn, args); etyp = TVoid[]}
    end else begin
      let (id, fty) =
        lookup_function env (sprintf "__builtin_bswap%d" bsize) in
      let fn = {edesc = EVar id; etyp = fty} in
      let args = [ecast_opt env aty rhs] in
      let call = {edesc = ECall(fn, args); etyp = aty} in
      eassign lhs (ecast_opt env ty call)
    end
  with Env.Error msg ->
    fatal_error loc "%s" (Env.error_message msg)
(*- #End *)

(* Expressions *)

let transf_expr loc env ctx e =

  (*- E_COMPCERT_CODE_PackedStructs_is_byteswapped_001 *)
  (*- #Justify_Derived "Utility function" *)
  let is_byteswapped ty fieldname =
    match unroll env ty with
    | TStruct(id, _) -> Hashtbl.mem byteswapped_fields (id, fieldname)
    | _ -> false in
  (*- #End *)

  (*- E_COMPCERT_CODE_PackedStructs_is_byteswapped_ptr_001 *)
  (*- #Justify_Derived "Utility function" *)
  let is_byteswapped_ptr ty fieldname =
    match unroll env ty with
    | TPtr(ty', _) -> is_byteswapped ty' fieldname
    | _ -> false in
  (*- #End *)

  (* Transformation of l-values.  Return transformed expr plus
     [true] if l-value is a byte-swapped field and [false] otherwise. *)

  (*- E_COMPCERT_CODE_PackedStructs_lvalue_001 *)
  (*- #Justify_Derived "Utility function" *)
  let rec lvalue e =
    match e.edesc with
    | EUnop(Odot fieldname, e1) ->
        ({edesc = EUnop(Odot fieldname, texp Val e1); etyp = e.etyp},
         is_byteswapped e1.etyp fieldname)
    | EUnop(Oarrow fieldname, e1) ->
        ({edesc = EUnop(Oarrow fieldname, texp Val e1); etyp = e.etyp},
         is_byteswapped_ptr e1.etyp fieldname)
    | EBinop(Oindex, e1, e2, tyres) ->
        let (e1', swap) = lvalue e1 in
        ({edesc = EBinop(Oindex, e1', e2, tyres); etyp = e.etyp}, swap)
    | _ ->
        (texp Val e, false)
  (*- #End *)

  (*- E_COMPCERT_CODE_PackedStructs_texp_001 *)
  and texp ctx e =
    match e.edesc with
    | EConst _ -> e
    | ESizeof _ -> e
    | EAlignof _ -> e
    | EVar _ -> e

    | EUnop(Odot _, _) | EUnop(Oarrow _, _) | EBinop(Oindex, _, _, _) ->
        let (e', swap) = lvalue e in
        if swap then bswap_read loc env e' else e'

    | EUnop(Oaddrof, e1) ->
        let (e1', swap) = lvalue e1 in
        if swap then
          (*- #Link_to E_COMPCERT_TR_Robustness_PACKED_STRUCT_009 *)
          error loc "& over byte-swapped field";
        {edesc = EUnop(Oaddrof, e1'); etyp = e.etyp}

    | EUnop((Opreincr|Opredecr) as op, e1) ->
        let (e1', swap) = lvalue e1 in
        if swap then
          expand_preincrdecr
            ~read:(bswap_read loc env) ~write:(bswap_write loc env)
            env ctx op e1'
        else
          {edesc = EUnop(op, e1'); etyp = e.etyp}

    | EUnop((Opostincr|Opostdecr as op), e1) ->
        let (e1', swap) = lvalue e1 in
        if swap then
          expand_postincrdecr
            ~read:(bswap_read loc env) ~write:(bswap_write loc env)
            env ctx op e1'
        else
          {edesc = EUnop(op, e1'); etyp = e.etyp}

    | EUnop(op, e1) ->
        {edesc = EUnop(op, texp Val e1); etyp = e.etyp}

    | EBinop(Oassign, e1, e2, ty) ->
        let (e1', swap) = lvalue e1 in
        let e2' = texp Val e2 in
        if swap then
          expand_assign ~write:(bswap_write loc env) env ctx e1' e2'
        else
          {edesc = EBinop(Oassign, e1', e2', ty); etyp = e.etyp}

    | EBinop((Oadd_assign|Osub_assign|Omul_assign|Odiv_assign|Omod_assign|
              Oand_assign|Oor_assign|Oxor_assign|Oshl_assign|Oshr_assign as op),
              e1, e2, ty) ->
        let (e1', swap) = lvalue e1 in
        let e2' = texp Val e2 in
        if swap then
          expand_assignop
            ~read:(bswap_read loc env) ~write:(bswap_write loc env)
            env ctx op e1' e2' ty
        else
          {edesc = EBinop(op, e1', e2', ty); etyp = e.etyp}

    | EBinop(Ocomma, e1, e2, ty) ->
        {edesc = EBinop(Ocomma, texp Effects e1, texp Val e2, ty);
         etyp = e.etyp}

    | EBinop(op, e1, e2, ty) ->
        {edesc = EBinop(op, texp Val e1, texp Val e2, ty); etyp = e.etyp}

    | EConditional(e1, e2, e3) ->
        {edesc = EConditional(texp Val e1, texp ctx e2, texp ctx e3);
         etyp = e.etyp}

    | ECast(ty, e1) ->
        {edesc = ECast(ty, texp Val e1); etyp = e.etyp}

    | ECompound _ ->
        assert false    (* does not occur in unblocked code *)

    | ECall(e1, el) ->
        {edesc = ECall(texp Val e1, List.map (texp Val) el); etyp = e.etyp}
  (*- #End *)

  (*- E_COMPCERT_CODE_PackedStructs_transf_expr_001 *)
  (*- #Justify_Derived "Utility function" *)
  in texp ctx e
  (*- #End *)

(* Statements *)

(*- E_COMPCERT_CODE_PackedStructs_transf_stmt_001 *)
(*- #Justify_Derived "Utility function" *)
let transf_stmt env s =
  Transform.stmt ~expr:transf_expr env s
(*- #End *)

(* Functions *)

(*- E_COMPCERT_CODE_PackedStructs_transf_fundef_001 *)
(*- #Justify_Derived "Utility function" *)
let transf_fundef env f =
  Transform.fundef transf_stmt env f
(*- #End *)

(* Initializers *)

(*- E_COMPCERT_CODE_PackedStructs_extract_byte_001 *)
(*- #Justify_Derived "Utility function" *)
let extract_byte n i =
  Int64.(logand (shift_right_logical n (i * 8)) 0xFFL)
(*- #End *)

(*- E_COMPCERT_CODE_PackedStructs_byteswap_int_001 *)
(*- #Justify_Derived "Utility function" *)
let byteswap_int nbytes n =
  let res = ref 0L in
  for i = 0 to nbytes - 1 do
    res := Int64.(logor (shift_left !res 8) (extract_byte n i))
  done;
  !res
(*- #End *)

(*- E_COMPCERT_CODE_PackedStructs_transf_init_001 *)
let transf_init loc env i =
  (* [swap] is [None] if no byte swapping needed, [Some ty] if
     byte-swapping is needed, with target type [ty] *)
  let rec trinit swap = function
  | Init_single e as i ->
      begin match swap with
      | None -> i
      | Some ty ->
          match Ceval.constant_expr env ty e with
          | Some(CInt(n, ik, _)) ->
              let n' = byteswap_int (sizeof_ikind ik) n in
              Init_single {edesc = EConst(CInt(n', ik, "")); etyp = e.etyp}
          | _ ->
              (*- #Link_to E_COMPCERT_TR_Robustness_PACKED_STRUCT_015 *)
              error loc "initializer for byte-swapped field is not \
                         a compile-time integer constant"; i
      end

  | Init_array il ->
      let swap_elt =
        match swap with
        | None -> None
        | Some ty ->
            match unroll env ty with
            | TArray(ty_elt, _, _) -> Some ty_elt
            | _ -> assert false in
      Init_array (List.rev (List.rev_map (trinit swap_elt) il))

  | Init_struct(id, fld_init_list) ->
      let trinit_field (f, i) =
        let swap_f =
          if Hashtbl.mem byteswapped_fields (id, f.fld_name)
          then Some f.fld_typ
          else None in
        (f, trinit swap_f i) in
      Init_struct(id, List.map trinit_field fld_init_list)

  | Init_union(id, fld, i) ->
      Init_union(id, fld, trinit None i)

  in trinit None i
(*- #End *)

(* Declarations *)

(*- E_COMPCERT_CODE_PackedStructs_transf_decl_001 *)
let transf_decl loc env (sto, id, ty, init_opt) =
  (sto, id, ty,
   match init_opt with
   | None -> None
   (*- #Link_to E_COMPCERT_TR_Function_PACKED_STRUCT_003 *)
   | Some i -> Some (transf_init loc env i))
(*- #End *)

(* Global declarations *)

(*- E_COMPCERT_CODE_PackedStructs_transf_globdecls_001 *)
let rec transf_globdecls env accu = function
  | [] -> List.rev accu
  | g :: gl ->
      match g.gdesc with
      | Gdecl((sto, id, ty, init) as d) ->
          transf_globdecls
            (Env.add_ident env id sto ty)
            ({g with gdesc = Gdecl(transf_decl g.gloc env d)} :: accu)
            gl
      | Gfundef f ->
          transf_globdecls
            (Env.add_ident env f.fd_name f.fd_storage (fundef_typ f))
            ({g with gdesc = Gfundef(transf_fundef env f)} :: accu)
            gl
      | Gcompositedecl(su, id, attr) ->
          let attr' =
            match su with
            | Union -> attr
            (*- #Link_to E_COMPCERT_TR_Function_PACKED_STRUCT_004 *)
            | Struct -> remove_custom_attributes  ["packed";"__packed__"] attr in
          transf_globdecls
            (Env.add_composite env id (composite_info_decl su attr'))
            ({g with gdesc = Gcompositedecl(su, id, attr')} :: accu)
            gl
      | Gcompositedef(su, id, attr, fl) ->
          let (attr', fl') = transf_composite g.gloc env su id attr fl in
          transf_globdecls
            (Env.add_composite env id (composite_info_def env su attr' fl'))
            ({g with gdesc = Gcompositedef(su, id, attr', fl')} :: accu)
            gl
      | Gtypedef(id, ty) ->
          transf_globdecls
            (Env.add_typedef env id ty)
            (g :: accu)
            gl
      | Genumdef(id, attr, el) ->
          transf_globdecls
            (Env.add_enum env id {ei_members =  el; ei_attr = attr})
            (g :: accu)
            gl
      | Gpragma p ->
          transf_globdecls env (g :: accu) gl
(*- #End *)

(* Program *)

(*- E_COMPCERT_CODE_PackedStructs_program_001 *)
(*- #Link_to E_COMPCERT_TR_Function_PACKED_STRUCT_001 *)
let program p =
  use_reversed :=
    begin match !Machine.config.Machine.name with
    | "powerpc" -> true
    | _ -> false
    end;
  Hashtbl.clear byteswapped_fields;
  transf_globdecls (Env.initial()) [] p
(*- #End *)
