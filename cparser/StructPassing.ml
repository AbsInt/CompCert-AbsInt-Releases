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

(* Eliminate structs and unions that are
   - returned by value as function results
   - passed by value as function parameters. *)

open Machine
open C
open Cutil
open Transform

(*- E_COMPCERT_CODE_StructPassing_struct_return_style_001 *)
(*- #Justify_Derived "Variable for global state" *)
let struct_return_style = ref SR_ref
(*- #End *)
(*- E_COMPCERT_CODE_StructPassing_struct_passing_style_001 *)
(*- #Justify_Derived "Variable for global state" *)
let struct_passing_style = ref SP_ref_callee
(*- #End *)

(* Classification of function return types. *)

(*- E_COMPCERT_CODE_StructPassing_return_kind_001 *)
(*- #Justify_Derived "Type definition" *)
type return_kind =
  | Ret_scalar    (**r a scalar type, returned as usual *)
  | Ret_ref       (**r a composite type, returned by reference *)
  | Ret_value of typ * int * int
                  (**r a small composite type, returned as an integer
                       (type, size, alignment) *)
(*- #End *)

(*- E_COMPCERT_CODE_StructPassing_classify_return_001 *)
(*- #Justify_Derived "Utility function" *)
let classify_return env ty =
  if is_composite_type env ty then begin
    match sizeof env ty, alignof env ty with
    | Some sz, Some al ->
        begin match !struct_return_style with
        | SR_int1248 when sz = 1 || sz = 2 || sz = 4 ->
            Ret_value (TInt(IUInt, []), sz, al)
        | SR_int1248 when sz = 8 ->
            Ret_value (TInt(IULongLong, []), sz, al)
        | (SR_int1to4 | SR_int1to8) when sz <= 4 ->
            Ret_value (TInt(IUInt, []), sz, al)
        | SR_int1to8 when sz > 4 && sz <= 8 ->
            Ret_value (TInt(IULongLong, []), sz, al)
        | _ ->
            Ret_ref
        end
    | _, _ ->
        Ret_ref  (* should not happen *)
  end else
    Ret_scalar
(*- #End *)

(* Classification of function parameter types. *)

(*- E_COMPCERT_CODE_StructPassing_param_kind_001 *)
(*- #Justify_Derived "Type definition" *)
type param_kind =
  | Param_unchanged     (**r passed as is *)
  | Param_ref_caller    (**r passed by reference to a copy taken by the caller *)
  | Param_flattened of int * int * int (**r passed as N integer arguments
                          (N, size, alignment) *)
  | Param_int of int * int (**r passed as single integer argument
                          (size, alignment) *)
(*- #End *)

(*- E_COMPCERT_CODE_StructPassing_classify_param_001 *)
(*- #Justify_Derived "Utility function" *)
let classify_param env ty =
  if is_composite_type env ty then begin
    match !struct_passing_style with
    | SP_ref_callee -> Param_unchanged
    | SP_ref_caller -> Param_ref_caller
    | SP_split_args ->
      begin match sizeof env ty, alignof env ty with
      | Some sz, Some al ->
          Param_flattened ((sz + 3) / 4, sz, al)
      | _, _ ->
          Param_unchanged  (* should not happen *)
      end
    | SP_int1to8 ->
      begin match sizeof env ty, alignof env ty with
        | Some sz, Some al when sz <= 8 ->
          Param_int (sz, al)
        | _, _ -> Param_ref_caller
      end
  end else
    Param_unchanged
(*- #End *)

(* Return the list [f 0; f 1; ...; f (n-1)] *)

(*- E_COMPCERT_CODE_StructPassing_list_map_n_001 *)
(*- #Justify_Derived "Utility function" *)
let list_map_n f n =
  let rec map i = if i >= n then [] else f i :: map (i + 1)
  in map 0
(*- #End *)

(* Declaring and accessing buffers (arrays of int) *)

(*- E_COMPCERT_CODE_StructPassing_basic_types_001 *)
(*- #Justify_Derived "Utility constant" *)
let uchar = TInt(IUChar, [])
(*- #End *)
(*- E_COMPCERT_CODE_StructPassing_basic_types_002 *)
(*- #Justify_Derived "Utility constant" *)
let ushort = TInt(IUShort, [])
(*- #End *)
(*- E_COMPCERT_CODE_StructPassing_basic_types_003 *)
(*- #Justify_Derived "Utility constant" *)
let uint = TInt(IUInt, [])
(*- #End *)
(*- E_COMPCERT_CODE_StructPassing_basic_types_004 *)
(*- #Justify_Derived "Utility constant" *)
let ulonglong = TInt(IULongLong, [])
(*- #End *)
(*- E_COMPCERT_CODE_StructPassing_basic_types_005 *)
(*- #Justify_Derived "Utility constant" *)
let ucharptr = TPtr(uchar, [])
(*- #End *)
(*- E_COMPCERT_CODE_StructPassing_basic_types_006 *)
(*- #Justify_Derived "Utility constant" *)
let ushortptr = TPtr(ushort, [])
(*- #End *)
(*- E_COMPCERT_CODE_StructPassing_basic_types_007 *)
(*- #Justify_Derived "Utility constant" *)
let uintptr = TPtr(uint, [])
(*- #End *)
(*- E_COMPCERT_CODE_StructPassing_basic_types_008 *)
(*- #Justify_Derived "Utility constant" *)
let ulonglongptr = TPtr(ulonglong, [])
(*- #End *)

(*- E_COMPCERT_CODE_StructPassing_basic_types_009 *)
(*- #Justify_Derived "Utility function" *)
let ty_buffer n =
  TArray(uint, Some (Int64.of_int n), [])
(*- #End *)

(*- E_COMPCERT_CODE_StructPassing_ebuffer_index_001 *)
(*- #Justify_Derived "Utility function" *)
let ebuffer_index base idx =
  { edesc = EBinop(Oindex, base, intconst (Int64.of_int idx) IInt, uintptr);
    etyp = uint }
(*- #End *)

(*- E_COMPCERT_CODE_StructPassing_attr_structret_001 *)
(*- #Justify_Derived "Utility constant" *)
let attr_structret = [Attr("__structreturn", [])]
(*- #End *)

(* Expression constructor functions *)

(*- E_COMPCERT_CODE_StructPassing_ereinterpret_001 *)
(*- #Justify_Derived "Utility function" *)
let ereinterpret ty e =
  { edesc = EUnop(Oderef, ecast (TPtr(ty, [])) (eaddrof e)); etyp = ty }
(*- #End *)

(*- E_COMPCERT_CODE_StructPassing_compose_or_001 *)
(*- #Justify_Derived "Utility function" *)
let or2 a b = { edesc = EBinop(Oor, a, b, uint); etyp = uint }
(*- #End *)
(*- E_COMPCERT_CODE_StructPassing_compose_or_002 *)
(*- #Justify_Derived "Utility function" *)
let or3 a b c = or2 (or2 a b) c
(*- #End *)
(*- E_COMPCERT_CODE_StructPassing_compose_or_003 *)
(*- #Justify_Derived "Utility function" *)
let or4 a b c d = or2 (or2 (or2 a b) c) d
(*- #End *)

(*- E_COMPCERT_CODE_StructPassing_lshift_001 *)
(*- #Justify_Derived "Utility function" *)
let lshift a nbytes =
  if nbytes = 0 then a else
    { edesc = EBinop(Oshl, a, intconst (Int64.of_int (nbytes * 8)) IInt, uint);
      etyp = uint }
(*- #End *)

(*- E_COMPCERT_CODE_StructPassing_offsetptr_001 *)
(*- #Justify_Derived "Utility function" *)
let offsetptr base ofs =
  if ofs = 0 then base else
  { edesc = EBinop(Oadd, base, intconst (Int64.of_int ofs) IInt, ucharptr);
    etyp = ucharptr }
(*- #End *)

(*- E_COMPCERT_CODE_StructPassing_load1_001 *)
(*- #Justify_Derived "Utility function" *)
let load1 base ofs shift_le shift_be =
  let shift = if (!config).bigendian then shift_be else shift_le in
  let a = offsetptr base ofs in
  lshift { edesc = EUnop(Oderef, a); etyp = uchar } shift
(*- #End *)

(*- E_COMPCERT_CODE_StructPassing_load2_001 *)
(*- #Justify_Derived "Utility function" *)
let load2 base ofs shift_le shift_be =
  let shift = if (!config).bigendian then shift_be else shift_le in
  let a = ecast ushortptr (offsetptr base ofs) in
  lshift { edesc = EUnop(Oderef, a); etyp = ushort } shift
(*- #End *)

(*- E_COMPCERT_CODE_StructPassing_load4_001 *)
(*- #Justify_Derived "Utility function" *)
let load4 base ofs =
  let a = ecast uintptr (offsetptr base ofs) in
  { edesc = EUnop(Oderef, a); etyp = uint }
(*- #End *)

(*- E_COMPCERT_CODE_StructPassing_load8_001 *)
(*- #Justify_Derived "Utility function" *)
let load8 base ofs =
  let a = ecast ulonglongptr (offsetptr base ofs) in
  { edesc = EUnop(Oderef, a); etyp = ulonglong }
(*- #End *)

(*- E_COMPCERT_CODE_StructPassing_lshift_ll_001 *)
(*- #Justify_Derived "Utility function" *)
let lshift_ll a nbytes =
  let a = ecast ulonglong a in
  if nbytes = 0 then a else
    { edesc = EBinop(Oshl, a, intconst (Int64.of_int (nbytes * 8)) IInt, ulonglong);
      etyp = ulonglong }
(*- #End *)

(*- E_COMPCERT_CODE_StructPassing_or2_ll_001 *)
(*- #Justify_Derived "Utility function" *)
let or2_ll a b = { edesc = EBinop(Oor, a, b, uint); etyp = ulonglong }
(*- #End *)

(* Loading a memory area as one or several integers. *)

(*- E_COMPCERT_CODE_StructPassing_load_word_001 *)
(*- #Justify_Derived "Utility function" *)
let load_word base ofs sz al =
  match sz with
  | 0 -> intconst 0L IInt
  | 1 -> load1 base ofs 0 3
  | 2 -> if al >= 2 || (!config).supports_unaligned_accesses then
           load2 base ofs 0 2
         else
           or2 (load1 base ofs 0 3)
               (load1 base (ofs + 1) 1 2)
  | 3 -> if al >= 2 || (!config).supports_unaligned_accesses then
           or2 (load2 base ofs 0 2)
               (load1 base (ofs + 2) 2 1)
         else
           or3 (load1 base ofs 0 3)
               (load1 base (ofs + 1) 1 2)
               (load1 base (ofs + 2) 2 1)
  | 4 -> if al >= 4 || (!config).supports_unaligned_accesses then
           load4 base ofs
         else if al >= 2 then
           or2 (load2 base ofs 0 2)
               (load2 base (ofs + 2) 2 0)
         else
           or4 (load1 base ofs 0 3)
               (load1 base (ofs + 1) 1 2)
               (load1 base (ofs + 2) 2 1)
               (load1 base (ofs + 3) 3 0)
  | _ -> assert false
(*- #End *)

(*- E_COMPCERT_CODE_StructPassing_load_words_001 *)
(*- #Justify_Derived "Utility function" *)
let rec load_words base ofs sz al =
  if ofs >= sz then []
  else if ofs + 4 >= sz then [load_word base ofs (sz - ofs) al]
  else load_word base ofs 4 al :: load_words base (ofs + 4) sz al
(*- #End *)

(*- E_COMPCERT_CODE_StructPassing_load_result_001 *)
(*- #Justify_Derived "Utility function" *)
let load_result base sz al =
  assert (sz <= 8);
  if sz <= 4 then
    load_word base 0 sz al
  else if sz = 8 && (al >= 8 || (!config).supports_unaligned_accesses) then
    load8 base 0
  else begin
    let (shift1, shift2) = if (!config).bigendian then (4, 0) else (0, 4) in
    or2_ll (lshift_ll (load_word base 0 4 al) shift1)
           (lshift_ll (load_word base 4 (sz - 4) al) shift2)
  end
(*- #End *)

(* Rewriting of function types.  For the return type:
      return kind scalar   -> no change
      return kind ref      -> return type void + add 1st parameter struct s *
      return kind value(t) -> return type t.
   For the parameters:
      param unchanged      -> no change
      param_ref_caller     -> turn into a pointer
      param_flattened N    -> turn into N parameters of type "int"
      param_int            -> turn into one parameter of type "int" or "long long"
   Try to preserve original typedef names when no change.
*)

(*- E_COMPCERT_CODE_StructPassing_transf_type_001 *)
(*- #Link_to E_COMPCERT_TR_Function_STRUCT_PASSING_002 *)
let rec transf_type env t =
  match unroll env t with
  | TFun(tres, None, vararg, attr) ->
      let tres' = transf_type env tres in
      begin match classify_return env tres with
      | Ret_scalar ->
          TFun(tres', None, vararg, attr)
      | Ret_ref ->
          TFun(TVoid [], None, vararg, add_attributes attr attr_structret)
      | Ret_value(ty, sz, al) ->
          TFun(ty, None, vararg, attr)
      end
  | TFun(tres, Some args, vararg, attr) ->
      let args' = transf_funargs env args in
      let tres' = transf_type env tres in
      begin match classify_return env tres with
      | Ret_scalar ->
          TFun(tres', Some args', vararg, attr)
      | Ret_ref ->
          let res = Env.fresh_ident "_res" in
          TFun(TVoid [], Some((res, TPtr(tres', [])) :: args'), vararg,
               add_attributes attr attr_structret)
      | Ret_value(ty, sz, al) ->
          TFun(ty, Some args', vararg, attr)
      end
  | TPtr(t1, attr) ->
      let t1' = transf_type env t1 in
      if t1' = t1 then t else TPtr(transf_type env t1, attr)
  | TArray(t1, sz, attr) ->
      let t1' = transf_type env t1 in
      if t1' = t1 then t else TArray(transf_type env t1, sz, attr)
  | _ -> t
(*- #End *)

(*- E_COMPCERT_CODE_StructPassing_transf_funargs_001 *)
(*- #Link_to E_COMPCERT_TR_Function_STRUCT_PASSING_003 *)
and transf_funargs env = function
  | [] -> []
  | (id, t) :: args ->
      let t' = transf_type env t in
      let args' = transf_funargs env args in
      match classify_param env t with
      | Param_unchanged ->
          (id, t') :: args'
      | Param_ref_caller ->
          (id, TPtr(t', [])) :: args'
      | Param_flattened(n, sz, al) ->
          list_map_n (fun _ -> (Env.fresh_ident id.C.name, uint)) n
          @ args'
      | Param_int (sz, al) ->
        let typ = if sz <= 4 then uint else ulonglong in
        (Env.fresh_ident id.C.name, typ) :: args'
(*- #End *)

(* Expressions: transform calls + rewrite the types *)

(*- E_COMPCERT_CODE_StructPassing_translates_to_extended_lvalue_001 *)
(*- #Justify_Derived "Utility function" *)
let rec translates_to_extended_lvalue arg =
  is_lvalue arg ||
  (match arg.edesc with
   | ECall _ -> true
   | EBinop(Ocomma, a, b, _) -> translates_to_extended_lvalue b
   | _ -> false)
(*- #End *)

(*- E_COMPCERT_CODE_StructPassing_transf_expr_001 *)
(*- #Justify_Derived "Utility function" *)
let rec transf_expr env ctx e =
  let newty = transf_type env e.etyp in
  match e.edesc with
  | EConst c ->
      {edesc = EConst c; etyp = newty}
  | ESizeof ty ->
      {edesc = ESizeof (transf_type env ty); etyp = newty}
  | EAlignof ty ->
      {edesc = EAlignof (transf_type env ty); etyp = newty}
  | EVar x ->
      {edesc = EVar x; etyp = newty}
  | EUnop(op, e1) ->
      {edesc = EUnop(op, transf_expr env Val e1); etyp = newty}
  | EBinop(Oassign, lhs, {edesc = ECall(fn, args); etyp = ty}, _) ->
      transf_call env ctx (Some (transf_expr env Val lhs)) fn args ty
  | EBinop(Ocomma, e1, e2, ty) ->
      ecomma (transf_expr env Effects e1) (transf_expr env ctx e2)
  | EBinop(op, e1, e2, ty) ->
      {edesc = EBinop(op, transf_expr env Val e1,
                          transf_expr env Val e2,
                          transf_type env ty);
       etyp = newty}
  | EConditional(e1, e2, e3) ->
      {edesc = EConditional(transf_expr env Val e1,
                            transf_expr env ctx e2,
                            transf_expr env ctx e3);
       etyp = newty}
  | ECast(ty, e1) ->
      {edesc = ECast(transf_type env ty, transf_expr env Val e1); etyp = newty}
  | ECompound(ty, ie) ->
      {edesc = ECompound(transf_type env ty, transf_init env ie); etyp = newty}
  | ECall(fn, args) ->
      transf_call env ctx None fn args e.etyp
(*- #End *)

(* Function calls returning a composite by reference: add first argument.
    ctx = Effects:   lv = f(...)     -> f(&newtemp, ...), lv = newtemp
                     f(...)          -> f(&newtemp, ...)
    ctx = Val:       lv = f(...)     -> f(&newtemp, ...), lv = newtemp
                     f(...)          -> f(&newtemp, ...), newtemp

   We used to do a copy optimization:
     ctx = Effects:   lv = f(...)     -> f(&lv, ...)
   but it is not correct in case of overlap (see test/regression/struct12.c)

   Function calls returning a composite by value:
    ctx = Effects:   lv = f(...)     -> newtemp = f(...), lv = newtemp
                     f(...)          -> f(...)
    ctx = Val:       lv = f(...)     -> newtemp = f(...), lv = newtemp
                     f(...)          -> newtemp = f(...), newtemp
*)

(*- E_COMPCERT_CODE_StructPassing_transf_call_001 *)
(*- #Link_to E_COMPCERT_TR_Function_STRUCT_PASSING_008 *)
and transf_call env ctx opt_lhs fn args ty =
  let ty' = transf_type env ty in
  let fn' = transf_expr env Val fn in
  let opt_eassign e =
    match opt_lhs with
    | None -> e
    | Some lhs -> eassign lhs e in
  match fn with
  | {edesc = EVar { C.name = "__builtin_va_arg"
                           | "__builtin_annot"
                           | "__builtin_annot_intval"
                           | "__builtin_ais_annot" } } ->
    (* Do not transform the call in this case, just use the default
       pass-by-reference mode for struct/union arguments. *)
    let args' = List.map (fun arg -> transf_expr env Val arg) args in
    opt_eassign {edesc = ECall(fn, args'); etyp = ty}
  | _ ->
    let (assignments, args') = transf_arguments env args in
    let call =
      match classify_return env ty with
      | Ret_scalar ->
          opt_eassign {edesc = ECall(fn', args'); etyp = ty'}
      | Ret_ref ->
          begin match ctx, opt_lhs with
          | Effects, None ->
              let tmp = new_temp ~name:"_res" ty in
              {edesc = ECall(fn', eaddrof tmp :: args'); etyp = TVoid []}
          (* Copy optimization, turned off as explained above *)
       (* | Effects, Some lhs ->
              {edesc = ECall(fn', eaddrof lhs :: args'); etyp = TVoid []} *)
          | Val, None ->
              let tmp = new_temp ~name:"_res" ty in
              ecomma {edesc = ECall(fn', eaddrof tmp :: args'); etyp = TVoid []}
                     tmp
          | _, Some lhs ->
              let tmp = new_temp ~name:"_res" ty in
              ecomma {edesc = ECall(fn', eaddrof tmp :: args'); etyp = TVoid []}
                     (eassign lhs tmp)
          end
      | Ret_value(ty_ret, sz, al) ->
          let ecall = {edesc = ECall(fn', args'); etyp = ty_ret} in
          begin match ctx, opt_lhs with
          | Effects, None ->
              ecall
          | _, _ ->
              let tmp = new_temp ~name:"_res" ty_ret in
              opt_eassign
                (ecomma (eassign tmp ecall)
                        (ereinterpret ty' tmp))
          end
    in ecommalist assignments call
(*- #End *)

(* Function argument of ref_caller kind: take a copy and pass pointer to copy
        arg      --->   newtemp = arg  ...   &newtemp
   Function argument of flattened(N) kind: load and pass as integers
   either using an intermediate array
        arg      --->   ( * ((ty * ) temparray) = arg ...
                        temparray[0], ...,, temparray[N-1]
   or by using loadwords:
        arg      --->   addr = &(arg) ... loadwords addr ...
   Function argument of int kind: load and pass as integer
   either using an intermediate variable
        arg      --->   ( * ((ty * ) temp) = arg ...
                        temp
   or by using load_result:
        arg      --->   addr = &(arg) ... load_result addr ...
*)

(*- E_COMPCERT_CODE_StructPassing_transf_arguments_001 *)
(*- #Link_to E_COMPCERT_TR_Function_STRUCT_PASSING_005 *)
and transf_arguments env args =
  match args with
  | [] -> ([], [])
  | arg :: args ->
      let (assignments, args') = transf_arguments env args in
      match classify_param env arg.etyp with
      | Param_unchanged ->
          let arg' = transf_expr env Val arg in
          (assignments, arg' :: args')
      | Param_ref_caller ->
          let ty' = transf_type env arg.etyp in
          let tmp = new_temp ~name:"_arg" ty' in
          (transf_assign env tmp arg :: assignments,
           eaddrof tmp :: args')
      | Param_flattened(n, sz, al) ->
          let ty' = transf_type env arg.etyp in
          if translates_to_extended_lvalue arg then begin
            let tmp = new_temp ~name:"_arg" ucharptr in
            (eassign tmp (ecast ucharptr (eaddrof (transf_expr env Val arg)))
             :: assignments,
             load_words tmp 0 sz al @ args')
          end else begin
            let tmp = new_temp ~name:"_arg" (ty_buffer n) in
            (transf_assign env (ereinterpret ty' tmp) arg :: assignments,
             list_map_n (ebuffer_index tmp) n @ args')
          end
      | Param_int (sz, al) ->
        let ty' = transf_type env arg.etyp in
        if translates_to_extended_lvalue arg then begin
          let tmp = new_temp ~name:"_arg" ucharptr in
          (eassign tmp (ecast ucharptr (eaddrof (transf_expr env Val arg)))
           :: assignments,
           (load_result tmp sz al) :: args')
        end else begin
          let base_ty = if sz <= 4 then uint else ulonglong in
          let tmp = new_temp ~name:"_arg" base_ty in
          (transf_assign env (ereinterpret ty' tmp) arg :: assignments, tmp :: args')
        end
(*- #End *)

(*- E_COMPCERT_CODE_StructPassing_transf_assign_001 *)
(*- #Justify_Derived "Utility function" *)
and transf_assign env lhs e =
  match e.edesc with
  | ECall(fn, args) ->
      transf_call env Effects (Some lhs) fn args e.etyp
  | _ ->
      eassign lhs (transf_expr env Val e)
(*- #End *)

(* Initializers *)

(*- E_COMPCERT_CODE_StructPassing_transf_init_001 *)
(*- #Justify_Derived "Utility function" *)
and transf_init env = function
  | Init_single e ->
      Init_single (transf_expr env Val e)
  | Init_array il ->
      Init_array (List.rev (List.rev_map (transf_init env) il))
  | Init_struct(id, fil) ->
      Init_struct (id, List.map (fun (fld, i) -> (fld, transf_init env i)) fil)
  | Init_union(id, fld, i) ->
      Init_union(id, fld, transf_init env i)
(*- #End *)

(* Declarations *)

(*- E_COMPCERT_CODE_StructPassing_transf_decl_001 *)
(*- #Link_to E_COMPCERT_TR_Function_STRUCT_PASSING_004 *)
let transf_decl env loc (sto, id, ty, init) =
  (sto, id, transf_type env ty,
   match init with None -> None | Some i -> Some (transf_init env i))
(*- #End *)

(* Transformation of statements and function bodies *)

(*- E_COMPCERT_CODE_StructPassing_transf_funbody_001 *)
let transf_funbody env body optres =

let transf_expr ctx e = transf_expr env ctx e in
let transf_asm_operand (lbl, cstr, e) = (lbl, cstr, transf_expr Val e) in

(* Function returns:
     return kind scalar    -> return e
     return kind ref       -> _res = x; return
     return kind value ty  -> *((struct s * )_res) = x; return _res
                           or addr = &x; return loadresult(addr)
*)

let rec transf_stmt s =
  match s.sdesc with
  | Sskip -> s
  | Sdo e ->
      {s with sdesc = Sdo(transf_expr Effects e)}
  | Sseq(s1, s2) ->
      {s with sdesc = Sseq(transf_stmt s1, transf_stmt s2)}
  | Sif(e, s1, s2) ->
      {s with sdesc = Sif(transf_expr Val e,
                          transf_stmt s1, transf_stmt s2)}
  | Swhile(e, s1) ->
      {s with sdesc = Swhile(transf_expr Val e, transf_stmt s1)}
  | Sdowhile(s1, e) ->
      {s with sdesc = Sdowhile(transf_stmt s1, transf_expr Val e)}
  | Sfor(s1, e, s2, s3) ->
      {s with sdesc = Sfor(transf_stmt s1, transf_expr Val e,
                           transf_stmt s2, transf_stmt s3)}
  | Sbreak -> s
  | Scontinue -> s
  | Sswitch(e, s1) ->
      {s with sdesc = Sswitch(transf_expr Val e, transf_stmt s1)}
  | Slabeled(lbl, s1) ->
      {s with sdesc = Slabeled(lbl, transf_stmt s1)}
  | Sgoto lbl -> s
  | Sreturn None -> s
  | Sreturn(Some e) ->
      (*- #Link_to E_COMPCERT_TR_Function_STRUCT_PASSING_007 *)
      let e' = transf_expr Val e in
      begin match classify_return env e'.etyp, optres with
      | Ret_scalar, None ->
          {s with sdesc = Sreturn(Some e')}
      | Ret_ref, Some dst ->
          sseq s.sloc
            (sassign s.sloc dst e')
            {sdesc = Sreturn None; sloc = s.sloc}
      | Ret_value(ty, sz, al), None ->
          if translates_to_extended_lvalue e then begin
            let tmp = new_temp ~name:"_res" ucharptr in
            sseq s.sloc
              (sassign s.sloc tmp (ecast ucharptr (eaddrof e')))
              {sdesc = Sreturn (Some (load_result tmp sz al)); sloc = s.sloc}
          end else begin
            let dst = new_temp ~name:"_res" ty in
            sseq s.sloc
              (sassign s.sloc (ereinterpret e'.etyp dst) e')
              {sdesc = Sreturn (Some dst); sloc = s.sloc}
          end
      | _, _ ->
          assert false
      end
  | Sblock sl ->
      {s with sdesc = Sblock(List.map transf_stmt sl)}
  | Sdecl d ->
      {s with sdesc = Sdecl(transf_decl env s.sloc d)}
  | Sasm(attr, template, outputs, inputs, clob) ->
      {s with sdesc = Sasm(attr, template,
                           List.map transf_asm_operand outputs,
                           List.map transf_asm_operand inputs, clob)}

in
  transf_stmt body
(*- #End *)

(* Binding arguments to parameters.  Returns a triple:
    - parameter list
    - actions to perform at the beginning of the function
    - substitution to apply to the function body
*)

(*- E_COMPCERT_CODE_StructPassing_transf_funparams_001 *)
(*- #Link_to E_COMPCERT_TR_Function_STRUCT_PASSING_006 *)
let rec transf_funparams loc env params =
  match params with
  | [] ->
      ([], sskip, IdentMap.empty)
  | (x, tx) :: params ->
      let tx' = transf_type env tx in
      let (params', actions, subst) = transf_funparams loc env params in
      match classify_param env tx with
      | Param_unchanged ->
          ((x, tx') :: params',
           actions,
           subst)
      | Param_ref_caller ->
          let tpx = TPtr(tx', []) in
          let ex = { edesc = EVar x; etyp = tpx } in
          let estarx = { edesc = EUnop(Oderef, ex); etyp = tx' } in
          ((x, tpx) :: params',
           actions,
           IdentMap.add x estarx subst)
      | Param_flattened(n, sz, al) ->
          let y = new_temp ~name:x.C.name (ty_buffer n) in
          let yparts = list_map_n (fun _ -> Env.fresh_ident x.C.name) n in
          let assign_part e p act =
            sseq loc (sassign loc e {edesc = EVar p; etyp = uint}) act in
          (List.map (fun p -> (p, uint)) yparts @ params',
           List.fold_right2 assign_part
                            (list_map_n (ebuffer_index y) n)
                            yparts
                            actions,
           IdentMap.add x (ereinterpret tx' y) subst)
      | Param_int(sz, al) ->
          let ty_base = if sz <= 4 then uint else ulonglong in
          let y = new_temp ~name:x.C.name ty_base in
          let yparts = Env.fresh_ident x.C.name in
          ((yparts, ty_base) ::  params',
           sseq loc (sassign loc y {edesc = EVar yparts; etyp = ty_base}) actions,
           IdentMap.add x (ereinterpret tx' y) subst)
 (*- #End *)

(*- E_COMPCERT_CODE_StructPassing_transf_fundef_001 *)
(*- #Justify_Derived "Utility function" *)
let transf_fundef env loc f =
  reset_temps();
  let ret = transf_type env f.fd_ret in
  let (params, actions, subst) =
    transf_funparams f.fd_body.sloc env f.fd_params in
  let locals =
    List.map (fun d -> transf_decl env loc (subst_decl subst d)) f.fd_locals in
  let (attr1, ret1, params1, body1) =
    match classify_return env f.fd_ret with
    | Ret_scalar ->
        (f.fd_attrib,
         ret,
         params,
         transf_funbody env (subst_stmt subst f.fd_body) None)
    | Ret_ref ->
        let vres = Env.fresh_ident "_res" in
        let tres = TPtr(ret, []) in
        let eres = {edesc = EVar vres; etyp = tres} in
        let eeres = {edesc = EUnop(Oderef, eres); etyp = ret} in
        (add_attributes f.fd_attrib attr_structret,
         TVoid [],
         (vres, tres) :: params,
         transf_funbody env (subst_stmt subst f.fd_body) (Some eeres))
    | Ret_value(ty, sz, al) ->
        (f.fd_attrib,
         ty,
         params,
         transf_funbody env (subst_stmt subst f.fd_body) None) in
  let temps = get_temps() in
  {f with fd_attrib = attr1;
          fd_ret = ret1;
          fd_params = params1;
          fd_locals = locals @ temps;
          fd_body = sseq f.fd_body.sloc actions body1}
(*- #End *)

(* Composites *)

(*- E_COMPCERT_CODE_StructPassing_transf_composite_001 *)
(*- #Justify_Derived "Utility function" *)
let transf_composite env loc su id attr fl =
  (attr, List.map (fun f -> {f with fld_typ = transf_type env f.fld_typ}) fl)
(*- #End *)

(* Entry point *)

(*- E_COMPCERT_CODE_StructPassing_program_001 *)
(*- #Justify_Derived "Utility function" *)
let program p =
  struct_passing_style :=
    if !Clflags.option_interp
    then SP_ref_callee
    else !Machine.config.struct_passing_style;
  struct_return_style :=
    if !Clflags.option_interp
    then SR_ref
    else !Machine.config.struct_return_style;
  Transform.program
    ~decl:transf_decl
    ~fundef:transf_fundef
    ~composite:transf_composite
    ~typedef:(fun env loc id ty -> transf_type env ty)
    p
(*- #End *)
