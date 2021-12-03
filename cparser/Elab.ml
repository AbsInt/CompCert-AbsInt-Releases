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

(* Elaboration from Cabs parse tree to C simplified, typed syntax tree *)

(* Numbered references are to sections of the ISO C99 standard *)

open Machine
open Cabs
open C
open Diagnostics
open! Cutil

(** * Utility functions *)

(* Error reporting  *)

(*- E_COMPCERT_CODE_Elab_fatal_error_001 *)
(*- #Justify_Derived "Utility function" *)
let fatal_error loc fmt =
  fatal_error (loc.filename,loc.lineno) fmt
(*- #End *)

(*- E_COMPCERT_CODE_Elab_error_001 *)
(*- #Justify_Derived "Utility function" *)
let error loc fmt =
  error (loc.filename,loc.lineno) fmt
(*- #End *)

(*- E_COMPCERT_CODE_Elab_warning_001 *)
(*- #Justify_Derived "Utility function" *)
let warning loc =
  warning (loc.filename,loc.lineno)
(*- #End *)

(*- E_COMPCERT_CODE_Elab_print_typ_001 *)
(*- #Justify_Derived "Utility function" *)
let print_typ env fmt ty =
  match ty with
  | TNamed _  ->
    Format.fprintf fmt "'%a'" Cprint.typ_raw ty;
    let ty' = unroll env ty in
    if not (is_anonymous_type ty')
    then Format.fprintf fmt " (aka '%a')" Cprint.typ_raw ty'
  | TStruct (id,_) when id.C.name = "" ->
    Format.fprintf fmt "'struct <anonymous>'"
  | TUnion (id,_) when id.C.name = "" ->
    Format.fprintf fmt "'union <anonymous>'"
  | TEnum (id,_) when id.C.name = "" ->
    Format.fprintf fmt "'enum <anonymous>'"
  | _ -> Format.fprintf fmt "'%a'" Cprint.typ_raw ty
(*- #End *)

(*- E_COMPCERT_CODE_Elab_pp_field_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_field fmt id =
 Format.fprintf fmt "%s" (if id <> "" then id else "<anonymous>")
(*- #End *)


(* Error reporting for Env functions *)

(*- E_COMPCERT_CODE_Elab_wrap_env_error_001 *)
(*- #Justify_Derived "Utility function" *)
let wrap fn loc env arg =
  try fn env arg
  with Env.Error msg -> fatal_error loc "%s" (Env.error_message msg)
(*- #End *)

(*- E_COMPCERT_CODE_Elab_wrap_env_error_002 *)
(*- #Justify_Derived "Utility function" *)
let wrap2 fn loc env arg1 arg2 =
  try fn env arg1 arg2
  with Env.Error msg -> fatal_error loc "%s" (Env.error_message msg)
(*- #End *)


(* Translation of locations *)

(*- E_COMPCERT_CODE_Elab_elab_loc_001 *)
(*- #Justify_Derived "Utility function" *)
let elab_loc l = (l.filename, l.lineno)
(*- #End *)


(* Buffering of the result (a list of topdecl *)

(*- E_COMPCERT_CODE_Elab_top_declaration_001 *)
(*- #Justify_Derived "Variable for global state" *)
let top_declarations = ref ([] : globdecl list)
(*- #End *)


(* Environment that records the top declarations of functions and
   variables with external or internal linkage.  Used for
   analyzing "extern" declarations. *)

(*- E_COMPCERT_CODE_Elab_top_environment_001 *)
(*- #Justify_Derived "Variable for global state" *)
let top_environment = ref Env.empty
(*- #End *)


(* Set of all globals with a definitions *)

module StringSet = Set.Make(String)

(*- E_COMPCERT_CODE_Elab_global_defines_001 *)
(*- #Justify_Derived "Variable for global state" *)
let global_defines = ref StringSet.empty
(*- #End *)

(*- E_COMPCERT_CODE_Elab_add_global_define_001 *)
(*- #Link_to E_COMPCERT_TR_Robustness_ELAB_017 *)
let add_global_define loc name =
  if StringSet.mem name !global_defines then
    error loc "redefinition of '%s'" name;
  global_defines := StringSet.add name !global_defines
(*- #End *)

(*- E_COMPCERT_CODE_Elab_is_global_defined_001 *)
(*- #Justify_Derived "Utility function" *)
let is_global_defined name =
  StringSet.mem name !global_defines
(*- #End *)

(*- E_COMPCERT_CODE_Elab_emit_elab_001 *)
(*- #Justify_Derived "Utility function" *)
let emit_elab ?(debuginfo = true) ?(linkage = false) env loc td =
  let loc = elab_loc loc in
  let dec ={ gdesc = td; gloc = loc } in
  if debuginfo then Debug.insert_global_declaration env dec;
  top_declarations := dec :: !top_declarations;
  if linkage then begin
    match td with
    | Gdecl(sto, id, ty, init) ->
        top_environment := Env.add_ident !top_environment id sto ty
    | Gfundef f ->
        top_environment :=
          Env.add_ident !top_environment f.fd_name f.fd_storage (fundef_typ f)
    | _ -> ()
  end
(*- #End *)

(*- E_COMPCERT_CODE_Elab_reset_001 *)
(*- #Justify_Derived "Utility function" *)
let reset() = top_declarations := []; top_environment := Env.empty; global_defines := StringSet.empty
(*- #End *)

(*- E_COMPCERT_CODE_Elab_elaborated_program_001 *)
(*- #Justify_Derived "Utility function" *)
let elaborated_program () =
  let p = !top_declarations in
  top_declarations := [];
  (* Reverse it and eliminate unreferenced declarations *)
  Cleanup.program p
(*- #End *)


(* Monadic map for functions env -> 'a -> 'b * env *)

(*- E_COMPCERT_CODE_Elab_monadic_map_001 *)
(*- #Justify_Derived "Utility function" *)
let rec mmap f env = function
  | [] -> ([], env)
  | hd :: tl ->
      let (hd', env1) = f env hd in
      let (tl', env2) = mmap f env1 tl in
      (hd' :: tl', env2)
(*- #End *)

(*- E_COMPCERT_CODE_Elab_mmap2_filter_001 *)
(*- #Justify_Derived "Utility function" *)
let rec mmap2_filter f env l1 l2 =
  match l1,l2 with
  | [], [] -> ([], env)
  | a1 :: l1, a2 :: l2 ->
      let (opt_hd, env1) = f env a1 a2 in
      let (tl, env2) = mmap2_filter f env1 l1 l2 in
      ((match opt_hd with Some hd -> hd :: tl | None -> tl), env2)
  | _, _ ->
      invalid_arg "mmap2_filter"
(*- #End *)

(* To detect redefinitions within the same scope *)

(*- E_COMPCERT_CODE_Elab_previous_def_001 *)
(*- #Justify_Derived "Utility function" *)
let previous_def fn env arg =
  try
    Some (fn env arg)
  with Env.Error _ ->
    None
(*- #End *)

(*- E_COMPCERT_CODE_Elab_redef_001 *)
(*- #Justify_Derived "Utility function" *)
let redef fn env arg =
  match previous_def fn env arg with
  | None -> false
  | Some(id, info) -> Env.in_current_scope env id
(*- #End *)


(* Auxiliaries for handling declarations and redeclarations *)

(*- E_COMPCERT_CODE_Elab_name_of_storage_class_001 *)
(*- #Justify_Derived "Utility function" *)
let name_of_storage_class = function
  | Storage_default -> "<default>"
  | Storage_extern -> "'extern'"
  | Storage_static -> "'static'"
  | Storage_auto -> "'auto'"
  | Storage_register -> "'register'"
(*- #End *)

(*- E_COMPCERT_CODE_Elab_combine_toplevel_definitions_001 *)
let combine_toplevel_definitions loc env s old_sto old_ty sto ty =
  let new_ty =
    match combine_types AttrCompat env old_ty ty with
    | Some new_ty ->
        new_ty
    | None ->
       (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_013 *)
        error loc
          "redefinition of '%s' with a different type: %a vs %a"
          s (print_typ env) old_ty (print_typ env) ty;
        ty in
  if is_global_defined s then begin
    let old_attrs = attributes_of_type env old_ty
    and new_attrs = attributes_of_type env ty in
    (*- #Link_to E_COMPCERT_TR_Function_ELAB_014 *)
    if not (Cutil.incl_attributes new_attrs old_attrs) then
      warning loc Ignored_attributes "attribute declaration must precede definition"
  end;
  let new_sto =
    (* The only case not allowed is removing static *)
    (*- #Link_to E_COMPCERT_TR_Function_ELAB_172 *)
    (*- #Link_to E_COMPCERT_TR_Function_ELAB_185 *)
    match old_sto,sto with
    | Storage_static,Storage_static
    | Storage_extern,Storage_extern
    | Storage_default,Storage_default -> sto
    | _,Storage_static ->
        (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_015 *)
	error loc "static declaration of '%s' follows non-static declaration" s;
        sto
    | Storage_static,_ -> Storage_static (* Static stays static *)
    | Storage_extern,_ -> if is_function_type env new_ty then Storage_extern else sto
    | Storage_default,Storage_extern ->
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_016 *)
      if is_global_defined s && is_function_type env ty then
        warning loc Extern_after_definition "this extern declaration follows a non-extern definition and is ignored";
      Storage_extern
    | _,Storage_extern -> old_sto
    (* "auto" and "register" don't appear in toplevel definitions.
       Normally this was checked earlier.  Generate error message
       instead of "assert false", just in case. *)
    | _,Storage_auto
    | Storage_auto,_
    | _,Storage_register
    | Storage_register,_ ->
	error loc "unexpected %s declaration of '%s'"
                  (name_of_storage_class sto) s;
        sto
  in
    (new_sto, new_ty)
(*- #End *)

(*- E_COMPCERT_CODE_Elab_enter_or_refine_ident_base_001 *)
let enter_or_refine_ident_base local loc env new_id sto ty =
  let s = new_id.C.name in
  (* Check for illegal redefinitions:
       - a name that was previously a typedef
       - a variable that was already declared in the same local scope
         (unless both old and new declarations are extern)
       - an enum that was already declared in the same scope.
     Redefinition of a variable at global scope (or extern) is treated below. *)
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_017 *)
  if redef Env.lookup_typedef env s then
    error loc "redefinition of '%s' as different kind of symbol" s;
  begin match previous_def Env.lookup_ident env s with
  | Some(old_id, Env.II_ident(old_sto, old_ty))
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_017 *)
    when local && Env.in_current_scope env old_id
               && not (sto = Storage_extern && old_sto = Storage_extern) ->
      error loc "redefinition of '%s'" s
  | Some(old_id, Env.II_enum _) when Env.in_current_scope env old_id ->
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_017 *)
      error loc "redefinition of '%s' as different kind of symbol" s;
  | _ ->
     ()
  end;
  (* For a block-scoped, "static" or "auto" or "register" variable,
     a new declaration is entered, and it has no linkage. *)
  if local
  && (sto = Storage_auto || sto = Storage_register || sto = Storage_static)
  then begin
    (new_id, sto, Env.add_ident env new_id sto ty, ty, false)
  end else begin
  (* For a file-scoped or "extern" variable, we need to check against
     prior declarations of this variable with internal or external linkage.
     The variable has linkage. *)
    match previous_def Env.lookup_ident !top_environment s with
    | Some(old_id, Env.II_ident(old_sto, old_ty)) ->
        let (new_sto, new_ty) =
          combine_toplevel_definitions loc env s old_sto old_ty sto ty in
        (old_id, new_sto, Env.add_ident env old_id new_sto new_ty, new_ty, true)
    | _ ->
        (new_id, sto, Env.add_ident env new_id sto ty, ty, true)
  end
(*- #End *)


(* We use two variants of [enter_or_refine]:

 - [enter_or_refine_ident] is to be used for all declarations,
   block-scoped ([local = true]) or top-level ([local = false]).
   The name of the declared thing is given as a string [s].  If a
   previous declaration with this name exists in the current scope,
   its unique identifier is returned.  Otherwise a fresh identifier
   named [s] is created in the current scope of [env] and returned.

 - [enter_or_refine_function] is to be used for function definitions.
   Such definitions are always global, hence the [local] parameter
   defaults to [false] and is omitted.  The function name is given
   as an identifier, created in advance by the caller.  This
   identifier is used if no previous declaration exists for the
   function.  Otherwise, the identifier of the previous declaration is
   used.  By creating the identifier in advance, [elab_fundef] makes
   sure that it is properly scoped to file scope and not to the local
   scope of function parameters.
*)

(*- E_COMPCERT_CODE_Elab_enter_or_refine_ident_001 *)
(*- #Justify_Derived "Utility function" *)
let enter_or_refine_ident local loc env s sto ty =
  enter_or_refine_ident_base local loc env (Env.fresh_ident s) sto ty
(*- #End *)

(*- E_COMPCERT_CODE_Elab_enter_or_refine_function_001 *)
(*- #Justify_Derived "Utility function" *)
let enter_or_refine_function loc env id sto ty =
  enter_or_refine_ident_base false loc env id sto ty
(*- #End *)


(* Forward declarations *)

let elab_expr_f : (Cabs.loc -> Env.t -> Cabs.expression -> C.exp * Env.t) ref
  = ref (fun _ _ _ -> assert false)

let elab_funbody_f : (C.typ -> bool -> bool -> Env.t -> statement -> C.stmt) ref
  = ref (fun _ _ _ _ _ -> assert false)



(** * Elaboration of constants - C99 section 6.4.4 *)

(*- E_COMPCERT_CODE_Elab_has_suffix_001 *)
(*- #Justify_Derived "Utility function" *)
let has_suffix s suff =
  let ls = String.length s and lsuff = String.length suff in
  ls >= lsuff && String.sub s (ls - lsuff) lsuff = suff
(*- #End *)

(*- E_COMPCERT_CODE_Elab_chop_last_001 *)
(*- #Justify_Derived "Utility function" *)
let chop_last s n =
  assert (String.length s >= n);
  String.sub s 0 (String.length s - n)
(*- #End *)

(*- E_COMPCERT_CODE_Elab_has_prefix_001 *)
(*- #Justify_Derived "Utility function" *)
let has_prefix s pref =
  let ls = String.length s and lpref = String.length pref in
  ls >= lpref && String.sub s 0 lpref = pref
(*- #End *)

(*- E_COMPCERT_CODE_Elab_chop_first_001 *)
(*- #Justify_Derived "Utility function" *)
let chop_first s n =
  assert (String.length s >= n);
  String.sub s n (String.length s - n)
(*- #End *)

exception Overflow
exception Bad_digit

(*- E_COMPCERT_CODE_Elab_parse_int_001 *)
(*- #Justify_Derived "Utility function" *)
let parse_int base s =
  let max_val = (* (2^64-1) / base, unsigned *)
    match base with
    |  8 -> 2305843009213693951L
    | 10 -> 1844674407370955161L
    | 16 -> 1152921504606846975L
    |  _ -> assert false in
  let v = ref 0L in
  for i = 0 to String.length s - 1 do
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_018 *)
    let c = s.[i] in
    let digit =
      if c >= '0' && c <= '9' then Char.code c - 48
      else if c >= 'A' && c <= 'F' then Char.code c - 55
      else raise Bad_digit in
    if digit >= base then raise Bad_digit;
    if !v < 0L || !v > max_val then raise Overflow;
    (* because (2^64 - 1) % 10 = 5, not 9 *)
    if base = 10 && !v = max_val && digit > 5 then raise Overflow;
    v := Int64.mul !v (Int64.of_int base);
    v := Int64.add !v (Int64.of_int digit)
  done;
  !v
(*- #End *)

(*- E_COMPCERT_CODE_Elab_integer_representable_001 *)
let integer_representable v ik =
  let bitsize = sizeof_ikind ik * 8
  and signed = is_signed_ikind ik in
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_019 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_163 *)
  if bitsize >= 64 then
    (not signed) || (v >= 0L && v <= 0x7FFF_FFFF_FFFF_FFFFL)
  else if not signed then
    v >= 0L && v < Int64.shift_left 1L bitsize
  else
    v >= 0L && v < Int64.shift_left 1L (bitsize - 1)
(*- #End *)

(*- E_COMPCERT_CODE_Elab_extract_kind_and_base_001 *)
(*- #Justify_Derived "Utility function" *)
let extract_kind_and_base s0 =
  let s = String.uppercase_ascii s0 in
  (* Determine possible types and chop type suffix *)
  let (s, dec_kinds, hex_kinds) =
    if has_suffix s "ULL" || has_suffix s "LLU" then
      (chop_last s 3, [IULongLong], [IULongLong])
    else if has_suffix s "LL" then
      (chop_last s 2, [ILongLong], [ILongLong; IULongLong])
    else if has_suffix s "UL" || has_suffix s "LU" then
      (chop_last s 2, [IULong; IULongLong], [IULong; IULongLong])
    else if has_suffix s "L" then
      (chop_last s 1, [ILong; ILongLong],
                      [ILong; IULong; ILongLong; IULongLong])
    else if has_suffix s "U" then
      (chop_last s 1, [IUInt; IULong; IULongLong],
                      [IUInt; IULong; IULongLong])
    else
      (s, [IInt; ILong; ILongLong],
          [IInt; IUInt; ILong; IULong; ILongLong; IULongLong])
  in
  (* Determine base *)
  let (s, base) =
    if has_prefix s "0X" then
      (chop_first s 2, 16)
    else if has_prefix s "0" then
      (chop_first s 1, 8)
    else
      (s, 10)
  in
  s, base, (if base = 10 then dec_kinds else hex_kinds)
(*- #End *)

(*- E_COMPCERT_CODE_Elab_elab_int_constant_001 *)
let elab_int_constant loc s0 =
  let s, base, kinds = extract_kind_and_base s0 in
  (* Parse digits *)
  let v =
    try parse_int base s
    with
    | Overflow ->
        (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_018 *)
        error loc "integer literal '%s' is too large to be represented in any integer type" s0;
        0L
    | Bad_digit ->
        (*error loc "bad digit in integer literal '%s'" s0;*) (* Is caught earlier *)
        0L
  in
  (* Find smallest allowable type that fits *)
  let ty =
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_019 *)
    try List.find (fun ty -> integer_representable v ty) kinds
    with Not_found ->
      error loc "integer literal '%s' cannot be represented" s0;
      IInt
  in
  (v, ty)
(*- #End *)

(*- E_COMPCERT_CODE_Elab_eval_int_of_string_literal_001 *)
(*- #Justify_Derived "Utility function" *)
let eval_int_of_string_literal env b =
  try
   begin match Ceval.constant_expr env b.etyp b with
    | Some (CStr s) ->
      let s = String.trim s in
      let s, base, _ = extract_kind_and_base s in
      Some (parse_int base s)
    | _ -> None
   end
  with _ -> None
(*- #End *)

(*- E_COMPCERT_CODE_Elab_elab_float_constant_001 *)
(*- #Justify_Derived "Utility function" *)
let elab_float_constant f =
  let ty = match f.suffix_FI with
    | Some ("l"|"L") -> FLongDouble
    | Some ("f"|"F") -> FFloat
    | None -> FDouble
    | _ -> assert false (* The lexer should not accept anything else. *)
  in
  let v = {
    hex=f.isHex_FI;
    intPart=begin match f.integer_FI with Some s -> s | None -> "0" end;
    fracPart=begin match f.fraction_FI with Some s -> s | None -> "0" end;
    exp=begin match f.exponent_FI with Some s -> s | None -> "0" end }
  in
  (FConstant v, ty)
(*- #End *)

(*- E_COMPCERT_CODE_Elab_elab_char_constant_001 *)
let elab_char_constant loc wide chars =
  let nbits = if wide then 8 * !config.sizeof_wchar else 8 in
  (* Treat multi-char constants as a number in base 2^nbits *)
  let max_digit = Int64.shift_left 1L nbits in
  let max_val = Int64.shift_left 1L (64 - nbits) in
  let v,_ =
    List.fold_left
      (fun (acc,err) d ->
        if not err then begin
          let overflow = acc < 0L || acc >= max_val
          and out_of_range = d < 0L || d >= max_digit in
          (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_019 *)
          if overflow then
            error loc "character constant too long for its type";
          (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_020 *)
          if out_of_range then
            error loc "escape sequence is out of range (code 0x%LX)" d;
          Int64.add (Int64.shift_left acc nbits) d,overflow || out_of_range
        end else
          Int64.add (Int64.shift_left acc nbits) d,true
      )
      (0L,false) chars in
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_163 *)
  if not (integer_representable v IInt) then
    warning loc Unnamed "character constant too long for its type";
  (* C99 6.4.4.4 item 10: single character -> represent at type char
     or wchar_t *)
  (*- #Link_to E_COMPCERT_TR_Function_CEVAL_007 *)
  Ceval.normalize_int v
    (if List.length chars = 1 then
       if wide then wchar_ikind() else IChar
     else
       IInt)
(*- #End *)

(*- E_COMPCERT_CODE_Elab_elab_string_literal_001 *)
(*- #Link_to E_COMPCERT_TR_Function_ELAB_179 *)
let elab_string_literal loc wide chars =
  let nbits = if wide then 8 * !config.sizeof_wchar else 8 in
  let char_max = Int64.shift_left 1L nbits in
  List.iter
    (fun c ->
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_020 *)
      if c < 0L || c >= char_max
      then error loc "escape sequence is out of range (code 0x%LX)" c)
    chars;
  if wide then
    CWStr chars
  else begin
    let res = Bytes.create (List.length chars) in
    List.iteri
      (fun i c -> Bytes.set res i (Char.unsafe_chr (Int64.to_int c)))
      chars;
    CStr (Bytes.to_string res)
  end
(*- #End *)

(*- E_COMPCERT_CODE_Elab_elab_constant_001 *)
(*- #Link_to E_COMPCERT_TR_Function_ELAB_008 *)
(*- #Link_to E_COMPCERT_TR_Function_ELAB_179 *)
let elab_constant loc = function
  | CONST_INT s ->
      let (v, ik) = elab_int_constant loc s in
      CInt(v, ik, s)
  | CONST_FLOAT f ->
      let (v, fk) = elab_float_constant f in
      CFloat(v, fk)
  | CONST_CHAR(wide, s) ->
      let ikind = if wide then wchar_ikind () else IInt in
      CInt(elab_char_constant loc wide s, ikind, "")
  | CONST_STRING(wide, s) ->
      elab_string_literal loc wide s
(*- #End *)

(*- E_COMPCERT_CODE_Elab_elab_simple_string_001 *)
let elab_simple_string loc wide chars =
  match elab_string_literal loc wide chars with
  | CStr s -> s
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_021 *)
  | _ -> error loc "cannot use wide string literal in 'asm'"; ""
(*- #End *)

(** Elaboration and checking of static assertions *)

(*- E_COMPCERT_CODE_Elab_elab_static_assert_001 *)
(*- #Link_to E_COMPCERT_TR_Robustness_ELAB_214 *)
let elab_static_assert env exp loc_exp msg loc_msg loc =
  let (exp, env) = !elab_expr_f loc_exp env exp in
  match Ceval.integer_expr env exp  with
  | None ->
      error loc_exp "expression in static assertion is not an integer constant"
  | Some n ->
      if n = 0L then begin
        match elab_constant loc_msg msg with
          | CStr s ->
              error loc "static assertion failed: \"%s\"" s
          | _ ->
              (* This can happen with a wide string literal *)
              error loc "static assertion failed (cannot display associated message)"
      end
(*- #End *)



(** * Elaboration of type expressions, type specifiers, name declarations *)

(* Elaboration of attributes *)

exception Wrong_attr_arg

(*- E_COMPCERT_CODE_Elab_elab_attr_arg_001 *)
let elab_attr_arg loc env a =
  match a with
  | VARIABLE s ->
      begin try
        match Env.lookup_ident env s with
        | (id, Env.II_ident(sto, ty)) ->  AIdent s
        | (id, Env.II_enum v) -> AInt v
      with Env.Error _ ->
        AIdent s
      end
  | _ ->
      let b,env = !elab_expr_f loc env a in
      (*- #Link_to E_COMPCERT_TR_Function_CEVAL_002 *)
      match Ceval.constant_expr env b.etyp b with
      | Some(CInt(n, _, _)) -> AInt n
      | Some(CStr s) -> AString s
      | _ -> raise Wrong_attr_arg
(*- #End *)

(*- E_COMPCERT_CODE_Elab_elab_gcc_attr_word_001 *)
(*- #Justify_Derived "Utility function" *)
let elab_gcc_attr_word = function
  | GCC_ATTR_IDENT s -> s
  | GCC_ATTR_CONST -> "const"
  | GCC_ATTR_PACKED -> "__packed__"
(*- #End *)

(*- E_COMPCERT_CODE_Elab_elab_gcc_attr_001 *)
(*- #Justify_Derived "Utility function" *)
let elab_gcc_attr loc env = function
  | GCC_ATTR_EMPTY -> []
  | GCC_ATTR_NOARGS w ->
      let v = elab_gcc_attr_word w in
      [Attr(v, [])]
  | GCC_ATTR_ARGS (w, args) ->
      let v = elab_gcc_attr_word w in
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_022 *)
      begin try
        [Attr(v, List.map (elab_attr_arg loc env) args)]
      with Wrong_attr_arg ->
        warning loc Unknown_attribute
          "unknown attribute '%s' ignored" v; []
      end
(*- #End *)

(*- E_COMPCERT_CODE_Elab_is_power_of_two_001 *)
(*- #Justify_Derived "Utility function" *)
let is_power_of_two n = n > 0L && Int64.logand n (Int64.pred n) = 0L
(*- #End *)

(* Check alignment parameter *)
(*- E_COMPCERT_CODE_Elab_check_alignment_001 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PACKED_STRUCT_012 *)
let check_alignment loc n =
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_023 *)
  if not (is_power_of_two n || n = 0L) then begin
    error loc "requested alignment %Ld is not a power of 2" n; false
  end else
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_023 *)
  if n <> Int64.of_int (Int64.to_int n) then begin
    error loc "requested alignment %Ld is too large" n; false
  end else
    true
(*- #End *)

(* Process GCC attributes that have special significance.  Currently we
   have two: "aligned" and "packed". *)
(*- E_COMPCERT_CODE_Elab_enter_gcc_attr_001 *)
let enter_gcc_attr loc a =
  match a with
  | Attr(("aligned"|"__aligned__"), args) ->
      begin match args with
      | [AInt n] -> if check_alignment loc n then [a] else []
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_023 *)
      | [_] -> error loc "requested alignment is not an integer constant"; []
      | [] -> [] (* Use default alignment, like gcc does *)
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_023 *)
      | _ -> error loc "'aligned' attribute takes no more than 1 argument"; []
      end
  | Attr(("packed"|"__packed__"), args) ->
      begin match args with
      | [] -> [a]
      | [AInt n] -> if check_alignment loc n then [a] else []
      | [AInt n; AInt p] ->
          if check_alignment loc n && check_alignment loc p then [a] else []
      | [AInt n; AInt p; AInt q] when q = 0L || q = 1L ->
          if check_alignment loc n && check_alignment loc p then [a] else []
      (*- #Link_to E_COMPCERT_TR_Robustness_PACKED_STRUCT_013 *)
      | _ -> error loc "ill-formed 'packed' attribute"; []
      end
  | _ -> [a]
(*- #End *)

(*- E_COMPCERT_CODE_Elab_elab_attribute_001 *)
(*- #Link_to E_COMPCERT_TR_Function_ELAB_009 *)
let elab_attribute env = function
  | GCC_ATTR (l, loc) ->
      List.fold_left add_attributes []
         (List.map (enter_gcc_attr loc)
            (List.flatten
               (List.map (elab_gcc_attr loc env) l)))
  | PACKED_ATTR (args, loc) ->
    begin try
      enter_gcc_attr loc
        (Attr("__packed__", List.map (elab_attr_arg loc env) args))
      (*- #Link_to E_COMPCERT_TR_Robustness_PACKED_STRUCT_011 *)
      with Wrong_attr_arg -> error loc "ill-formed 'packed' attribute"; []
    end
  | ALIGNAS_ATTR ([a], loc) ->
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_154 *)
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_159 *)
      warning loc Celeven_extension "'_Alignas' is a C11 extension";
      begin match elab_attr_arg loc env a with
      | AInt n ->
         if check_alignment loc n then [AAlignas (Int64.to_int n)] else []
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_023 *)
      | _ -> error loc "requested alignment is not an integer constant"; []
      | exception Wrong_attr_arg -> error loc "bad _Alignas value"; []
      end
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_023 *)
  | ALIGNAS_ATTR (_, loc) ->
      error loc "_Alignas takes no more than 1 argument"; []
(*- #End *)

(*- E_COMPCERT_CODE_Elab_elab_attributes_001 *)
(*- #Justify_Derived "Utility function" *)
let elab_attributes env al =
  List.fold_left add_attributes [] (List.map (elab_attribute env) al)
(*- #End *)

(* Warning for alignment requests that reduce the alignment below the
   natural alignment. *)

(*- E_COMPCERT_CODE_Elab_warn_if_reduced_alignment_001 *)
let warn_if_reduced_alignment loc ~actual ~natural =
  match actual, natural with
  | Some act, Some nat when act < nat ->
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_162 *)
      warning loc Reduced_alignment
         "requested alignment (%d) is less than natural alignment (%d)"
         act nat
  | _, _ -> ()
(*- #End *)

(*- E_COMPCERT_CODE_Elab_check_reduced_alignment_001 *)
(*- #Justify_Derived "Utility function" *)
let check_reduced_alignment loc env typ =
  warn_if_reduced_alignment loc
    ~actual: (wrap alignof loc env typ)
    ~natural: (wrap alignof loc env (erase_attributes_type env typ))
(*- #End *)


(* Auxiliary for typespec elaboration *)

(*- E_COMPCERT_CODE_Elab_typespec_rank_001 *)
(*- #Justify_Derived "Utility function" *)
let typespec_rank = function (* Don't change this *)
  | Cabs.Tvoid -> 0
  | Cabs.Tsigned -> 1
  | Cabs.Tunsigned -> 2
  | Cabs.Tchar -> 3
  | Cabs.Tshort -> 4
  | Cabs.Tlong -> 5
  | Cabs.Tint -> 6
  | Cabs.Tfloat -> 8
  | Cabs.Tdouble -> 9
  | Cabs.T_Bool -> 10
  | _ -> 11 (* There should be at most one of the others *)
(*- #End *)

(*- E_COMPCERT_CODE_Elab_typespec_order_001 *)
(*- #Justify_Derived "Utility function" *)
let typespec_order t1 t2 = compare (typespec_rank t1) (typespec_rank t2)
(*- #End *)

(* Auxiliary for type declarator elaboration.  Remove the non-type-related
   attributes from the given type and return those attributes separately.
   If the type is a function type, keep function-related attributes
   attached to the type. *)

(*- E_COMPCERT_CODE_Elab_get_nontype_attrs_001 *)
(*- #Justify_Derived "Utility function" *)
let get_nontype_attrs env ty =
  let to_be_removed a =
    match class_of_attribute a with
    | Attr_type -> false
    | Attr_function -> not (is_function_type env ty)
    | _ -> true in
  let nta = List.filter to_be_removed (attributes_of_type_no_expand ty) in
  (remove_attributes_type env nta ty, nta)
(*- #End *)


(* Elaboration of a type specifier.  Returns 6-tuple:
     (storage class, "inline" flag, "noreturn" flag, "typedef" flag,
      elaborated type, new env)
   Optional argument "only" is true if this is a standalone
   struct or union declaration, without variable names.
   C99 section 6.7.2.
*)

(*- E_COMPCERT_CODE_Elab_elab_specifier_001 *)
(*- #Link_to E_COMPCERT_TR_Function_ELAB_200 *)
let rec elab_specifier ?(only = false) loc env specifier =
  (* We first divide the parts of the specifier as follows:
       - a storage class
       - a set of attributes (const, volatile, restrict)
       - a list of type specifiers *)
  let sto = ref Storage_default
  and inline = ref false
  and noreturn = ref false
  and restrict = ref false
  and attr = ref []
  and tyspecs = ref []
  and typedef = ref false in

  let do_specifier = function
  | SpecCV cv ->
      restrict := cv = CV_RESTRICT;
      attr := add_attributes (elab_cvspec env cv) !attr
  | SpecStorage st ->
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_024 *)
      if !sto <> Storage_default && st <> TYPEDEF then
        error loc "multiple storage classes in declaration specifier";
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_172 *)
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_185 *)
      begin match st with
      | AUTO -> sto := Storage_auto
      | STATIC -> sto := Storage_static
      | EXTERN -> sto := Storage_extern
      | REGISTER -> sto := Storage_register
      | TYPEDEF ->
          if !typedef then
            error loc "multiple uses of 'typedef'";
          typedef := true
      end
  | SpecFunction INLINE -> inline := true
  | SpecFunction NORETURN -> noreturn := true
  | SpecType tys -> tyspecs := tys :: !tyspecs in

  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_164 *)
  let restrict_check ty =
    if !restrict then
      if not (is_pointer_type env ty) then
        error loc "restrict requires a pointer type (%a is invalid)" (print_typ env) ty
      else if is_function_pointer_type env ty then
        error loc "pointer to function type %a may not be 'restrict' qualified" (print_typ env) ty in

  List.iter do_specifier specifier;

  let simple ty =
    restrict_check ty;
    (!sto, !inline, !noreturn ,!typedef, add_attributes_type !attr ty, env) in

  (* Partition !attr into name- and struct-related attributes,
     which are returned, and other attributes, which are left in !attr.
     The returned name-or-struct-related attributes are applied to the
     struct/union/enum being defined.
     The leftover attributes (e.g. object attributes) will be applied
     to the variable being defined.
     If [optmembers] is [None], name-related attributes are not returned
     but left in !attr.  This corresponds to two use cases:
     - A use of an already-defined struct/union/enum.  In this case
       the name-related attributes should go to the name being declared.
       Sending them to the struct/union/enum would cause them to be ignored,
       with a warning.  The struct-related attributes go to the
       struct/union/enum, are ignored, and cause a warning.
     - An incomplete declaration of a struct/union.  In this case
       the name- and struct-related attributes are just ignored,
       like GCC does.
  *)
  let get_definition_attrs optmembers =
    let (ta, nta) =
      List.partition
        (fun a -> match class_of_attribute a with
                  | Attr_struct -> true
                  | Attr_name -> optmembers <> None
                  | _ -> false)
        !attr in
    attr := nta;
    ta in

  (* Now interpret the list of type specifiers.  Much of this code
     is stolen from CIL. *)
  match List.stable_sort typespec_order (List.rev !tyspecs) with
    | [Cabs.Tvoid] -> simple (TVoid [])

    | [Cabs.T_Bool] -> simple (TInt(IBool, []))
    | [Cabs.Tchar] -> simple (TInt(IChar, []))
    | [Cabs.Tsigned; Cabs.Tchar] -> simple (TInt(ISChar, []))
    | [Cabs.Tunsigned; Cabs.Tchar] -> simple (TInt(IUChar, []))

    | [Cabs.Tshort] -> simple (TInt(IShort, []))
    | [Cabs.Tsigned; Cabs.Tshort] -> simple (TInt(IShort, []))
    | [Cabs.Tshort; Cabs.Tint] -> simple (TInt(IShort, []))
    | [Cabs.Tsigned; Cabs.Tshort; Cabs.Tint] -> simple (TInt(IShort, []))

    | [Cabs.Tunsigned; Cabs.Tshort] -> simple (TInt(IUShort, []))
    | [Cabs.Tunsigned; Cabs.Tshort; Cabs.Tint] -> simple (TInt(IUShort, []))

    | [] -> simple (TInt(IInt, []))
    | [Cabs.Tint] -> simple (TInt(IInt, []))
    | [Cabs.Tsigned] -> simple (TInt(IInt, []))
    | [Cabs.Tsigned; Cabs.Tint] -> simple (TInt(IInt, []))

    | [Cabs.Tunsigned] -> simple (TInt(IUInt, []))
    | [Cabs.Tunsigned; Cabs.Tint] -> simple (TInt(IUInt, []))

    | [Cabs.Tlong] -> simple (TInt(ILong, []))
    | [Cabs.Tsigned; Cabs.Tlong] -> simple (TInt(ILong, []))
    | [Cabs.Tlong; Cabs.Tint] -> simple (TInt(ILong, []))
    | [Cabs.Tsigned; Cabs.Tlong; Cabs.Tint] -> simple (TInt(ILong, []))

    | [Cabs.Tunsigned; Cabs.Tlong] -> simple (TInt(IULong, []))
    | [Cabs.Tunsigned; Cabs.Tlong; Cabs.Tint] -> simple (TInt(IULong, []))

    | [Cabs.Tlong; Cabs.Tlong] -> simple (TInt(ILongLong, []))
    | [Cabs.Tsigned; Cabs.Tlong; Cabs.Tlong] -> simple (TInt(ILongLong, []))
    | [Cabs.Tlong; Cabs.Tlong; Cabs.Tint] -> simple (TInt(ILongLong, []))
    | [Cabs.Tsigned; Cabs.Tlong; Cabs.Tlong; Cabs.Tint] -> simple (TInt(ILongLong, []))

    | [Cabs.Tunsigned; Cabs.Tlong; Cabs.Tlong] -> simple (TInt(IULongLong, []))
    | [Cabs.Tunsigned; Cabs.Tlong; Cabs.Tlong; Cabs.Tint] -> simple (TInt(IULongLong, []))

    | [Cabs.Tfloat] -> simple (TFloat(FFloat, []))
    | [Cabs.Tdouble] -> simple (TFloat(FDouble, []))

    | [Cabs.Tlong; Cabs.Tdouble] -> simple (TFloat(FLongDouble, []))

    (* Now the other type specifiers *)

    | [Cabs.Tnamed id] ->
        let (id', info) = wrap Env.lookup_typedef loc env id in
        simple (TNamed(id', []))

    | [Cabs.Tstruct_union(STRUCT, id, optmembers, a)] ->
        let a' =
          add_attributes (get_definition_attrs optmembers)
                         (elab_attributes env a) in
        let (id', env') =
          elab_struct_or_union only Struct loc id optmembers a' env in
        let ty =  TStruct(id', !attr) in
        restrict_check ty;
        (!sto, !inline, !noreturn, !typedef, ty, env')

    | [Cabs.Tstruct_union(UNION, id, optmembers, a)] ->
        let a' =
          add_attributes (get_definition_attrs optmembers)
                         (elab_attributes env a) in
        let (id', env') =
          elab_struct_or_union only Union loc id optmembers a' env in
        let ty =  TUnion(id', !attr) in
        restrict_check ty;
        (!sto, !inline, !noreturn, !typedef, ty, env')

    | [Cabs.Tenum(id, optmembers, a)] ->
        let a' =
          add_attributes (get_definition_attrs optmembers)
                         (elab_attributes env a) in
        let (id', env') =
          elab_enum only loc id optmembers a' env in
        let ty = TEnum (id', !attr) in
        restrict_check ty;
        (!sto, !inline, !noreturn, !typedef, ty, env')

    (* Specifier doesn't make sense *)
    | _ ->
        (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_025 *)
        fatal_error loc "illegal combination of type specifiers"
(*- #End *)

(* Elaboration of a type qualifier. *)

(*- E_COMPCERT_CODE_Elab_elab_cvspec_001 *)
(*- #Justify_Derived "Utility function" *)
and elab_cvspec env = function
  | CV_CONST -> [AConst]
  | CV_VOLATILE -> [AVolatile]
  | CV_RESTRICT -> [ARestrict]
  | CV_ATTR attr -> elab_attribute env attr
(*- #End *)

(*- E_COMPCERT_CODE_Elab_elab_csspecs_001 *)
(*- #Justify_Derived "Utility function" *)
and elab_cvspecs env cv_specs =
  List.fold_left add_attributes [] (List.map (elab_cvspec env) cv_specs)
(*- #End *)

(* Elaboration of a type declarator.  C99 section 6.7.5. *)
(*- E_COMPCERT_CODE_Elab_elab_return_type_001 *)
and elab_return_type loc env ty =
  match unroll env ty with
  | TArray _ ->
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_026 *)
      error loc "function cannot return array type %a" (print_typ env) ty
  | TFun _ ->
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_026 *)
      error loc "function cannot return function type %a" (print_typ env) ty
  | _ -> ()
(*- #End *)

(* The [?fundef] parameter is true if we're elaborating a function definition
   and false otherwise.  When [fundef = true], K&R function declarators
   are allowed, and the returned environment includes bindings for the
   function parameters and the struct/unions they may define.
   When [fundef = false], K&R function declarators are rejected
   and declarations in parameters are not returned. *)

(*- E_COMPCERT_CODE_Elab_elab_type_declarator_001 *)
(*- #Link_to E_COMPCERT_TR_Function_ELAB_187 *)
and elab_type_declarator ?(fundef = false) loc env ty = function
  | Cabs.JUSTBASE ->
      ((ty, None), env)
  | Cabs.ARRAY(d, cv_specs, sz) ->
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_189 *)
      let (ty, a) = get_nontype_attrs env ty in
      let a = add_attributes a (elab_cvspecs env cv_specs) in
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_027 *)
      if wrap incomplete_type loc env ty then
        error loc "array type has incomplete element type %a" (print_typ env) ty;
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_165 *)
      if wrap contains_flex_array_mem loc env ty then
        warning loc Flexible_array_extensions "%a may not be used as an array element due to flexible array member" (print_typ env) ty;
      let sz' =
        match sz with
        | None ->
            None
        | Some sz ->
            let expr,env = (!elab_expr_f loc env sz) in
            (*- #Link_to E_COMPCERT_TR_Function_CEVAL_001 *)
            match Ceval.integer_expr env expr  with
            | Some n ->
                (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_028 *)
                if n < 0L then error loc "size of array is negative";
                (*- #Link_to E_COMPCERT_TR_Function_ELAB_029 *)
                if n = 0L then warning loc Zero_length_array
                    "zero size arrays are an extension";
                (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_028 *)
                if not (Cutil.valid_array_size env ty n) then error loc "size of array is too large";
                Some n
            | None ->
                (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_028 *)
                error loc "size of array is not a compile-time constant";
                Some 1L in (* produces better error messages later *)
       elab_type_declarator ~fundef loc env (TArray(ty, sz', a)) d
  | Cabs.PTR(cv_specs, d) ->
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_188 *)
      let (ty, a) = get_nontype_attrs env ty in
      let a = add_attributes a (elab_cvspecs env cv_specs) in
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_164 *)
      if is_function_type env ty && incl_attributes [ARestrict] a then
        error loc "pointer to function type %a may not be 'restrict' qualified" (print_typ env) ty;
      elab_type_declarator ~fundef loc env (TPtr(ty, a)) d
  | Cabs.PROTO(d, (params, vararg)) ->
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_190 *)
      elab_return_type loc env ty;
      let (ty, a) = get_nontype_attrs env ty in
      let (params', env') = elab_parameters loc env params in
      (* For a function declaration (fundef = false), the scope introduced
         to treat parameters ends here, so we discard the extended
         environment env' returned by elab_parameters.
         For a function definition (fundef = true) we return the
         extended environment env' so that it can serve as the basis
         to elaborating the function body. *)
      let env'' = if fundef then env' else env in
      elab_type_declarator ~fundef loc env'' (TFun(ty, Some params', vararg, a)) d
  | Cabs.PROTO_OLD(d, params) ->
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_190 *)
      elab_return_type loc env ty;
      let (ty, a) = get_nontype_attrs env ty in
      (* For consistency with the PROTO case above, for a function definition
         (fundef = true) we open a new scope, even though we do not
         add any bindings for the parameters. *)
      let env'' = if fundef then Env.new_scope env else env in
      match params with
      | [] ->
        elab_type_declarator ~fundef loc env'' (TFun(ty, None, false, a)) d
      | _ ->
        (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_030 *)
        if not fundef || d <> Cabs.JUSTBASE then
          fatal_error loc "illegal old-style K&R function definition";
        ((TFun(ty, None, false, a), Some params), env'')
(*- #End *)


(* Elaboration of parameters in a prototype *)

(*- E_COMPCERT_CODE_Elab_elab_prameters_001 *)
and elab_parameters loc env params =
  (* Prototype introduces a new scope *)
  let (vars, env) = mmap elab_parameter (Env.new_scope env) params in
  (* Catch special case f(t) where t is void or a typedef to void *)
  match vars with
    | [ ( {C.name=""}, t) ] when is_void_type env t -> [],env
    | _ -> if List.exists (fun (id, t) -> id.C.name = "" && is_void_type env t) vars then
        (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_203 *)
        error loc "'void' must be the only parameter";
      (vars, env)
(*- #End *)

(* Elaboration of a function parameter *)

(*- E_COMPCERT_CODE_Elab_elab_parameter_001 *)
and elab_parameter env (PARAM (spec, id, decl, attr, loc)) =
  let (sto, inl, noret, tydef, bty, env1) = elab_specifier loc env spec in
  if tydef then
    error loc "'typedef' used in function parameter";
  let ((ty, _), _) = elab_type_declarator loc env1 bty decl in
  let ty = add_attributes_type (elab_attributes env attr) ty in
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_031 *)
  if sto <> Storage_default && sto <> Storage_register then
    error loc                               (* NB: 'auto' not allowed *)
      "invalid storage class %s for function parameter"
      (name_of_storage_class sto);
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_031 *)
  if inl then
    error loc "'inline' can only appear on functions";
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_031 *)
  if noret then
    error loc "'_Noreturn' can only appear on functions";
  let id = match id with None -> "" | Some id -> id in
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_175 *)
  if id <> "" && is_void_type env1 ty then
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_031 *)
    error loc "argument '%s' may not have 'void' type" id;
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_032 *)
  if id <> "" && redef Env.lookup_ident env id then
    error loc "redefinition of parameter '%s'" id;
  (* replace array and function types by pointer types *)
  let ty1 = argument_conversion env1 ty in
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_170 *)
  if is_qualified_array ty1 then
    error loc "type qualifier used in non-outermost array type derivation";
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_161 *)
  if has_std_alignas env ty then begin
    if id <> "" then
      error loc "alignment specified for parameter '%s'" id
    else
      error loc "alignment specified for unnamed parameter"
  end;
  let (id', env2) = Env.enter_ident env1 id sto ty1 in
  ( (id', ty1) , env2)
(*- #End *)


(* Elaboration of a (specifier, Cabs "name") pair as found in a function
   definition.  Returns two environments: the first is [env]
   enriched with struct/union definitions from the return type,
   as usual; the second is like the first, plus a new scope.
   For a prototyped function ([kr_params = None]) the new scope
   includes bindings for the function parameters and the struct/unions
   they may define.  For a K&R function ([kr_params <> None]) the new
   scope is empty. *)

(*- E_COMPCERT_CODE_Elab_elab_fundef_name_001 *)
(*- #Justify_Derived "Utility function" *)
and elab_fundef_name env spec (Name (s, decl, attr, loc)) =
  let (sto, inl, noret, tydef, bty, env') = elab_specifier loc env spec in
  if tydef then
    error loc "'typedef' is forbidden here";
  let id = Env.fresh_ident s in
  let ((ty, kr_params), env'') =
    elab_type_declarator ~fundef:true loc env' bty decl in
  let a = elab_attributes env attr in
  (id, sto, inl, noret, add_attributes_type a ty, kr_params, env', env'')
(*- #End *)


(* Elaboration of a name group.  C99 section 6.7.6 *)

(*- E_COMPCERT_CODE_Elab_elab_name_group_001 *)
and elab_name_group loc env  (spec, namelist) =
  let (sto, inl, noret, tydef, bty, env') =
    elab_specifier loc env spec in
  if tydef then
    error loc "'typedef' is forbidden here";
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_034 *)
  if inl then
    error loc "'inline' is forbidden here";
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_034 *)
  if noret then
    error loc "'_Noreturn' is forbidden here";
  let elab_one_name env (Name (id, decl, attr, loc)) =
    let ((ty, _), env1) =
      elab_type_declarator loc env bty decl in
    let a = elab_attributes env attr in
    ((id, add_attributes_type a ty), env1) in
  (mmap elab_one_name env' namelist, sto)
(*- #End *)



(* Elaboration of a field group *)

(*- E_COMPCERT_CODE_Elab_elab_field_group_001 *)
and elab_field_group env = function

| Field_group (spec, fieldlist, loc) ->

  let fieldlist = List.map
    (function (None, x) -> (Name ("", JUSTBASE, [], loc), x)
            | (Some n, x) -> (n, x))
    fieldlist
  in

  let ((names, env'), sto) =
    elab_name_group loc env  (spec, List.map fst fieldlist) in

  if sto <> Storage_default then
    (* This should actually never be triggered, catched by pre-parser *)
    error loc "non-default storage in struct or union";
  if fieldlist = [] then
      (* This should actually never be triggered, empty structs are captured earlier *)
      warning loc Missing_declarations "declaration does not declare anything";

  let elab_bitfield env (Name (_, _, _, loc), optbitsize) (id, ty) =
    (*- #Link_to E_COMPCERT_TR_Function_ELAB_005 *)
    let optbitsize',env' =
      match optbitsize with
      | None -> None,env
      | Some sz ->
          let ik =
            match unroll env' ty with
            | TInt(ik, _) -> ik
            | TEnum(_, _) -> enum_ikind
            | _ -> ILongLong (* trigger next error message *) in
          (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_036 *)
          if sizeof_ikind ik > sizeof_ikind IInt then begin
            error loc
              "the type of bit-field '%a' must be an integer type no bigger than 'int'" pp_field id;
            None,env
          (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_037 *)
          end else if has_std_alignas env' ty then begin
            error loc "alignment specified for bit-field '%a'" pp_field id;
            None, env
          end else begin
            let expr,env' =(!elab_expr_f loc env sz) in
            (*- #Link_to E_COMPCERT_TR_Function_CEVAL_001 *)
            match Ceval.integer_expr env' expr with
            | Some n ->
                (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_037 *)
                if n < 0L then begin
                  error loc "bit-field '%a' has negative width (%Ld)" pp_field id n;
                  None,env
                end else
                  let max = Int64.of_int(sizeof_ikind ik * 8) in
                  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_037 *)
                  if n >  max then begin
                    error loc "size of bit-field '%a' (%Ld bits) exceeds its type (%Ld bits)" pp_field id n max;
                    None,env
                end else
                (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_037 *)
                if n = 0L && id <> "" then begin
                  error loc "named bit-field '%a' has zero width" pp_field id;
                  None,env
                end else
                  Some(Int64.to_int n),env'
            | None ->
                (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_037 *)
                error loc "bit-field '%a' width not an integer constant" pp_field id;
                None,env
          end in
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_169 *)
    if is_qualified_array ty then
      error loc "type qualifier used in array declarator outside of function prototype";
    let anon_composite = is_anonymous_composite ty in
    (*- #Link_to E_COMPCERT_TR_Function_ELAB_038 *)
    if id = "" && not anon_composite && optbitsize = None  then begin
      warning loc Missing_declarations "declaration does not declare anything";
      None, env'
    end else
      Some { fld_name = id; fld_typ = ty; fld_bitfield = optbitsize';
             fld_anonymous = id = "" && anon_composite},
      env'
  in
  (mmap2_filter elab_bitfield env' fieldlist names)


| Field_group_static_assert(exp, loc_exp, msg, loc_msg, loc) ->
    elab_static_assert env exp loc_exp msg loc_msg loc;
    (*- #Link_to E_COMPCERT_TR_Function_ELAB_213 *)
    ([], env)
(*- #End *)

(* Elaboration of a struct or union. C99 section 6.7.2.1 *)

(*- E_COMPCERT_CODE_Elab_elab_struct_or_union_info_001 *)
(*- #Link_to E_COMPCERT_TR_Function_ELAB_186 *)
and elab_struct_or_union_info kind loc env members attrs =
  let (m, env') = mmap elab_field_group env members in
  let m = List.flatten m in
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_004 *)
  let m,_ = mmap (fun c fld  ->
      if fld.fld_anonymous then
        let name = Printf.sprintf "<anon>_%d" c in
        {fld with fld_name = name},c+1
      else
        fld,c) 0 m in
  let rec duplicate acc = function
    | [] -> ()
    | fld::rest ->
       if fld.fld_anonymous then begin
         let rest = match unroll env fld.fld_typ with
           | TStruct (id,_) ->
             (*- #Link_to E_COMPCERT_TR_Function_ELAB_039 *)
             (*- #Link_to E_COMPCERT_TR_Function_ELAB_154 *)
             warning loc Celeven_extension "anonymous structs/unions are a C11 extension";
             let str = Env.find_struct env' id in
             str.Env.ci_members@rest
           | TUnion (id,_) ->
             (*- #Link_to E_COMPCERT_TR_Function_ELAB_039 *)
             (*- #Link_to E_COMPCERT_TR_Function_ELAB_154 *)
             warning loc Celeven_extension "anonymous structs/unions are a C11 extension";
             let union = Env.find_union env' id in
             union.Env.ci_members@rest
           | _ -> rest in
         duplicate acc rest
       end else if fld.fld_name <> "" then begin
         (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_040 *)
         if List.exists ((=) fld.fld_name) acc then
           error loc "duplicate member '%a'" pp_field fld.fld_name;
         duplicate (fld.fld_name::acc) rest
       end else
         duplicate acc rest in
  duplicate [] m;
  (* Check for incomplete types *)
  let rec check_incomplete only = function
  | [] -> ()
  | [ { fld_typ = TArray(ty_elt, None, _) as typ; fld_name = name } ] when kind = Struct ->
    (* C99: ty[] allowed as last field of a struct, provided this is not the only field *)
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_166 *)
      if only then
        error loc "flexible array member '%a' not allowed in otherwise empty struct" pp_field name;
      check_reduced_alignment loc env' typ
  | fld :: rem ->
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_041 *)
      if wrap incomplete_type loc env' fld.fld_typ then
        (* Must be fatal otherwise we get problems constructing the init *)
        fatal_error loc "member '%a' has incomplete type %a" pp_field fld.fld_name (print_typ env) fld.fld_typ;
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_165 *)
      if wrap contains_flex_array_mem loc env' fld.fld_typ && kind = Struct then
        warning loc Flexible_array_extensions "%a may not be used as a struct member due to flexible array member" (print_typ env) fld.fld_typ;
      check_reduced_alignment loc env' fld.fld_typ;
      check_incomplete false rem in
  check_incomplete true m;
  (* Warn for empty structs or unions *)
  if m = [] then
    if kind = Struct then begin
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_042 *)
      warning loc Gnu_empty_struct "empty struct is a GNU extension"
    end else begin
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_043 *)
      fatal_error loc "empty union is a GNU extension"
    end;
  let ci = composite_info_def env' kind attrs m in
  (* Warn for reduced alignment *)
  if attrs <> [] then begin
    let ci_nat = composite_info_def env' kind [] m in
    warn_if_reduced_alignment loc
           ~actual:ci.Env.ci_alignof ~natural:ci_nat.Env.ci_alignof
  end;
  (* Final result *)
  (composite_info_def env' kind attrs m, env')
(*- #End *)

(*- E_COMPCERT_CODE_Elab_elab_struct_or_union_001 *)
(*- #Link_to E_COMPCERT_TR_Function_ELAB_003 *)
(*- #Link_to E_COMPCERT_TR_Function_ELAB_186 *)
and elab_struct_or_union only kind loc tag optmembers attrs env =
  let warn_attrs () =
    (*- #Link_to E_COMPCERT_TR_Function_ELAB_044 *)
    if attrs <> [] then
      warning loc Ignored_attributes "attribute declaration must precede definition" in
  let optbinding, tag =
    match tag with
      | None -> None, ""
      | Some s ->
          (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_045 *)
          if redef Env.lookup_enum env s then
            error loc "'%s' redeclared as different kind of symbol" s;
          Env.lookup_composite env s, s
  in
  match optbinding, optmembers with
  | Some(tag', ci), None
    when (not only) || Env.in_current_scope env tag' ->
      (* Reference to an already declared struct or union.
         Special case: if this is an "only" declaration (without variable names)
         and the composite was bound in another scope,
         create a new incomplete composite instead via the case
         "_, None" below. *)
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_046 *)
      if ci.Env.ci_kind <> kind then
        fatal_error loc "use of '%s' with tag type that does not match previous declaration" tag;
      warn_attrs();
      (tag', env)
  | Some(tag', ({Env.ci_sizeof = None} as ci)), Some members
    when Env.in_current_scope env tag' ->
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_046 *)
      if ci.Env.ci_kind <> kind then
        fatal_error loc "use of '%s' with tag type that does not match previous declaration" tag;
      (* finishing the definition of an incomplete struct or union *)
      let (ci', env') = elab_struct_or_union_info kind loc env members attrs in
      (* Emit a global definition for it *)
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_001 *)
      emit_elab env' loc (Gcompositedef(kind, tag', attrs, ci'.Env.ci_members));
      (* Replace infos but keep same ident *)
      (tag', Env.add_composite env' tag' ci')
  | Some(tag', {Env.ci_sizeof = Some _}), Some _
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_047 *)
    when Env.in_current_scope env tag' ->
      fatal_error loc "redefinition of struct or union '%s'" tag
  | _, None ->
      (* declaration of an incomplete struct or union *)
      if tag = "" then
        error loc "anonymous, incomplete struct or union";
      let ci = composite_info_decl kind attrs in
      (* enter it with a new name *)
      let (tag', env') = Env.enter_composite env tag ci in
      (* emit it *)
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_001 *)
      emit_elab env' loc (Gcompositedecl(kind, tag', attrs));
      (tag', env')
  | _, Some members ->
      (* definition of a complete struct or union *)
      let ci1 = composite_info_decl kind attrs in
      (* enter it, incomplete, with a new name *)
      let (tag', env') = Env.enter_composite env tag ci1 in
      (* emit a declaration so that inner structs and unions can refer to it *)
      emit_elab env' loc (Gcompositedecl(kind, tag', attrs));
      (* elaborate the members *)
      let (ci2, env'') =
        elab_struct_or_union_info kind loc env' members attrs in
      (* emit a definition *)
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_001 *)
      emit_elab env'' loc (Gcompositedef(kind, tag', attrs, ci2.Env.ci_members));
      (* Replace infos but keep same ident *)
      (tag', Env.add_composite env'' tag' ci2)
(*- #End *)


(* Elaboration of an enum item.  C99 section 6.7.2.2 *)

(*- E_COMPCERT_CODE_Elab_elab_enum_item_001 *)
(*- #Link_to E_COMPCERT_TR_Function_ELAB_006 *)
and elab_enum_item env ((s, exp), loc) nextval =
  let (v, exp') =
    match exp with
    | None ->
        (nextval, None)
    | Some exp ->
        let exp',env = !elab_expr_f loc env exp in
        (*- #Link_to E_COMPCERT_TR_Function_CEVAL_001 *)
        match Ceval.integer_expr env exp' with
        | Some n -> (n, Some exp')
        | None ->
            (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_049 *)
            error loc
              "value of enumerator '%s' is not an integer constant" s;
            (nextval, Some exp') in
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_050 *)
  if redef Env.lookup_ident env s then
    error loc "'%s' redeclared as different kind of symbol" s;
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_050 *)
  if redef Env.lookup_typedef env s then
    error loc "'%s' redeclared as different kind of symbol" s;
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_051 *)
  if not (int_representable v (8 * sizeof_ikind enum_ikind) (is_signed_ikind enum_ikind)) then
    warning loc Constant_conversion "integer literal '%Ld' is too large to be represented in the enumeration integer type"
      v;
  let (id, env') = Env.enter_enum_item env s v in
  ((id, v, exp'), Int64.succ v, env')
(*- #End *)


(* Elaboration of an enumeration declaration.   C99 section 6.7.2.2  *)

(*- E_COMPCERT_CODE_Elab_elab_enum_001 *)
(*- #Link_to E_COMPCERT_TR_Function_ELAB_006 *)
and elab_enum only loc tag optmembers attrs env =
  let tag = match tag with
    | None -> ""
    | Some s ->
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_052 *)
      if redef Env.lookup_struct env s || redef Env.lookup_union env s then
        error loc "'%s' redeclared as different kind of symbol" s;
      s in
  match optmembers with
  | None ->
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_054 *)
    if only && not (redef Env.lookup_enum env tag) then
      fatal_error loc
         "forward declaration of 'enum %s' is not allowed in ISO C" tag;
      let (tag', info) = wrap Env.lookup_enum loc env tag in (tag', env)
  | Some members ->
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_053 *)
      if tag <> "" && redef Env.lookup_enum env tag then
        error loc "redefinition of 'enum %s'" tag;
      let rec elab_members env nextval = function
      | [] -> ([], env)
      | hd :: tl ->
          let (dcl1, nextval1, env1) = elab_enum_item env hd nextval in
          let (dcl2, env2) = elab_members env1 nextval1 tl in
          (dcl1 :: dcl2, env2) in
      let (dcls, env') = elab_members env 0L members in
      let info = { Env.ei_members = dcls; ei_attr = attrs } in
      let (tag', env'') = Env.enter_enum env' tag info in
      emit_elab env' loc (Genumdef(tag', attrs, dcls));
      (tag', env'')
(*- #End *)


(* Elaboration of a naked type, e.g. in a cast *)

(*- E_COMPCERT_CODE_Elab_elab_type_001 *)
(*- #Link_to E_COMPCERT_TR_Function_ELAB_173 *)
let elab_type loc env spec decl =
  let (sto, inl, noret, tydef, bty, env') = elab_specifier loc env spec in
  let ((ty, _), env'') = elab_type_declarator loc env' bty decl in
  (* NB: it seems the parser doesn't accept any of the specifiers below.
     We keep the error message as extra safety. *)
  if sto <> Storage_default || inl || noret || tydef then
    error loc "'typedef', 'extern', 'static', 'auto', 'register' and 'inline' are meaningless in cast";
  (ty, env'')
(*- #End *)



(* Elaboration of initializers. C99 section 6.7.8 *)

(*- E_COMPCERT_CODE_Elab_init_char_array_string_001 *)
(*- #Justify_Derived "Utility function" *)
let init_char_array_string opt_size s =
  let len = Int64.of_int (String.length s) in
  let size =
    match opt_size with
    | Some sz -> sz
    | None -> Int64.succ len  (* include final 0 character *) in
  let rec add_chars i init =
    if i < 0L then init else begin
      let c =
        if i < len then Int64.of_int (Char.code s.[Int64.to_int i]) else 0L in
      add_chars (Int64.pred i) (Init_single (intconst c IInt) :: init)
    end in
  Init_array (add_chars (Int64.pred size) [])
(*- #End *)

(*- E_COMPCERT_CODE_Elab_init_int_array_wstring_001 *)
(*- #Justify_Derived "Utility function" *)
let init_int_array_wstring opt_size s =
  let a = Array.of_list s in
  let len = Int64.of_int (Array.length a) in
  let size =
    match opt_size with
    | Some sz -> sz
    | None -> Int64.succ len  (* include final 0 character *) in
  let rec add_chars i init =
    if i < 0L then init else begin
      let c = if i < len then a.(Int64.to_int i) else 0L in
      add_chars (Int64.pred i) (Init_single (intconst c IInt) :: init)
    end in
  Init_array (add_chars (Int64.pred size) [])
(*- #End *)

(*- E_COMPCERT_CODE_Elab_check_init_type_001 *)
let check_init_type loc env a ty =
  if wrap2 valid_assignment loc env a ty then ()
  else if wrap2 valid_cast loc env a.etyp ty then
    (*- #Link_to E_COMPCERT_TR_Function_ELAB_176 *)
    if wrap2 int_pointer_conversion loc env a.etyp ty then
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_056 *)
      warning loc Int_conversion
        "incompatible integer-pointer conversion: initializer has type %a instead of the expected type %a"
         (print_typ env) a.etyp (print_typ env) ty
    else
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_056 *)
      warning loc Unnamed
        "incompatible conversion: initializer has type %a instead of the expected type %a"
        (print_typ env) a.etyp (print_typ env) ty
  else
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_057 *)
    error loc
      "initializer has type %a instead of the expected type %a"
      (print_typ env) a.etyp (print_typ env) ty
(*- #End *)


(* Representing initialization state using zippers *)

module I = struct

  (*- E_COMPCERT_CODE_Elab_zip_zipinit_001 *)
  (*- #Justify_Derived "Type definition" *)
  type zipinit =
    | Ztop of string * typ

    | Zarray of zipinit                 (* ancestor *)
              * typ                     (* type of elements *)
              * int64 option            (* size *)
              * init                    (* default initializer *)
              * init list               (* elements before point, reversed *)
              * int64                   (* position of point *)
              * init list               (* elements after point *)

    | Zstruct of zipinit                (* ancestor *)
               * ident                  (* struct type *)
               * (field * init) list    (* elements before current, reversed *)
               * field                  (* current field *)
               * (field * init) list    (* elements after current *)

    | Zunion of zipinit                 (* ancestor *)
              * ident                   (* union type *)
              * field                   (* current member *)
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_zip_result_001 *)
  (*- #Justify_Derived "Type definition" *)
  type 'a result =
    | OK of 'a
    | NotFound
    | Unsupported
  (*- #End *)

  (* The initial state: default initialization, current point at top *)
  (*- E_COMPCERT_CODE_Elab_zip_top_001 *)
  (*- #Justify_Derived "Utility function" *)
  let top env name ty = (Ztop(name, ty), default_init env ty)
  (*- #End *)

  (* Change the initializer for the current point *)
  (*- E_COMPCERT_CODE_Elab_zip_set_001 *)
  (*- #Justify_Derived "Utility function" *)
  let set (z, i) i' = (z, i')
  (*- #End *)

  (* Is the current point at top? *)
  (*- E_COMPCERT_CODE_Elab_zip_at_top_001 *)
  (*- #Justify_Derived "Utility function" *)
  let at_top = function Ztop(_, _), _ -> true | _, _ -> false
  (*- #End *)

  (* Put the current point back to the top *)
  (*- E_COMPCERT_CODE_Elab_zip_to_top_001 *)
  (*- #Justify_Derived "Utility function" *)
  let rec to_top = function
    | Ztop(name, ty), i as zi -> zi
    | Zarray(z, ty, sz, dfl, before, idx, after), i ->
        to_top (z, Init_array (List.rev_append before (i :: after)))
    | Zstruct(z, id, before, fld, after), i ->
        to_top (z, Init_struct(id, List.rev_append before ((fld, i) :: after)))
    | Zunion(z, id, fld), i ->
        to_top (z, Init_union(id, fld, i))
  (*- #End *)

  (* Extract the initializer corresponding to the current state *)
  (*- E_COMPCERT_CODE_Elab_zip_to_init_001 *)
  (*- #Justify_Derived "Utility function" *)
  let to_init zi = snd (to_top zi)
  (*- #End *)

  (* The type of the current point *)
  (*- E_COMPCERT_CODE_Elab_zip_typeof_001 *)
  (*- #Justify_Derived "Utility function" *)
  let typeof = function
    | Ztop(name, ty), i -> ty
    | Zarray(z, ty, sz, dfl, before, idx, after), i -> ty
    | Zstruct(z, id, before, fld, after), i -> fld.fld_typ
    | Zunion(z, id, fld), i -> fld.fld_typ
  (*- #End *)

  (* The name of the path leading to the current point, for error reporting *)
  (*- E_COMPCERT_CODE_Elab_zip_zipname_001 *)
  (*- #Justify_Derived "Utility function" *)
  let rec zipname = function
    | Ztop(name, ty) -> name
    | Zarray(z, ty, sz, dfl, before, idx, after) ->
        Printf.sprintf "%s[%Ld]" (zipname z) idx
    | Zstruct(z, id, before, fld, after) ->
        Printf.sprintf "%s.%s" (zipname z) fld.fld_name
    | Zunion(z, id, fld) ->
        Printf.sprintf "%s.%s" (zipname z) fld.fld_name
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_zip_name_001 *)
  (*- #Justify_Derived "Utility function" *)
  let name (z, i) = zipname z
  (*- #End *)

  (* Auxiliary functions to deal with arrays *)
  (*- E_COMPCERT_CODE_Elab_zip_index_below_001 *)
  (*- #Justify_Derived "Utility function" *)
  let index_below (idx: int64) (sz: int64 option) =
    match sz with None -> true | Some sz -> idx < sz
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_zip_il_head_001 *)
  (*- #Justify_Derived "Utility function" *)
  let il_head dfl = function [] -> dfl | i1 :: il -> i1
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_zip_il_tail_001 *)
  (*- #Justify_Derived "Utility function" *)
  let il_tail = function [] -> [] | i1 :: il -> il
  (*- #End *)

  (* Advance the current point to the next point in right-up order.
     Return NotFound if no next point, i.e. we are at top *)
  (*- E_COMPCERT_CODE_Elab_zip_next_001 *)
  (*- #Justify_Derived "Utility function" *)
  let rec next = function
    | Ztop(name, ty), i -> NotFound
    | Zarray(z, ty, sz, dfl, before, idx, after), i ->
        let idx' = Int64.succ idx in
        if index_below idx' sz
        then OK(Zarray(z, ty, sz, dfl, i :: before, idx', il_tail after),
                il_head dfl after)
        else next (z, Init_array (List.rev_append before (i :: after)))
    | Zstruct(z, id, before, fld, []), i ->
        next (z, Init_struct(id, List.rev_append before [(fld, i)]))
    | Zstruct(z, id, before, fld, (fld1, i1) :: after), i ->
        OK(Zstruct(z, id, (fld, i) :: before, fld1, after), i1)
    | Zunion(z, id, fld), i ->
        next (z, Init_union(id, fld, i))
  (*- #End *)

  (* Move the current point "down" to the first component of an array,
     struct, or union.  No effect if the current point is a scalar. *)
  (*- E_COMPCERT_CODE_Elab_zip_first_001 *)
  (*- #Justify_Derived "Utility function" *)
  let first env (z, i as zi) =
    let ty = typeof zi in
    match unroll env ty, i with
    | TArray(ty, sz, _), Init_array il ->
        if index_below 0L sz then begin
          let dfl = default_init env ty in
          OK(Zarray(z, ty, sz, dfl, [], 0L, il_tail il), il_head dfl il)
        end
        else NotFound
    | TStruct(id, _), Init_struct(id', []) ->
        NotFound
    | TStruct(id, _), Init_struct(id', (fld1, i1) :: flds) ->
        OK(Zstruct(z, id, [], fld1, flds), i1)
    | TUnion(id, _), Init_union(id', fld, i) ->
      let rec first_named = function
        | [] -> NotFound
        | fld1 :: fl ->
          if fld1.fld_name = "" then
            first_named fl
          else begin
            OK(Zunion(z, id, fld1),
               if fld.fld_name = fld1.fld_name
               then i
               else default_init env fld1.fld_typ)
          end in
      first_named (Env.find_union env id).Env.ci_members
    | (TStruct _ | TUnion _), Init_single a ->
        (* This is a previous whole-struct initialization that we
           are going to overwrite.  Hard to support correctly
           and without code duplication, so turn it into an error. *)
        Unsupported
    | _ ->
        OK (z, i)
  (*- #End *)

  (* Move to the [n]-th element of the current point, which must be
     an array. *)
  (*- E_COMPCERT_CODE_Elab_zip_index_001 *)
  (*- #Justify_Derived "Utility function" *)
  let index env (z, i as zi) n =
    match unroll env (typeof zi), i with
    | TArray(ty, sz, _), Init_array il ->
        if n >= 0L && index_below n sz then begin
          let dfl = default_init env ty in
          let rec loop p before after =
            if p = n then
              OK (Zarray(z, ty, sz, dfl, before, n, il_tail after),
                  il_head dfl after)
            else
              loop (Int64.succ p)
                   (il_head dfl after :: before)
                   (il_tail after)
          in loop 0L [] il
        end else
          NotFound
    | _, _ ->
      NotFound
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_zip_has_member_001 *)
  (*- #Justify_Derived "Utility function" *)
  let has_member env name ty =
    let mem f id =
      try
        ignore(f env (id,name)); true
      with Env.Error _ -> false in
    match ty with
    | TStruct (id,_) ->
      mem Env.find_struct_member id
    | TUnion (id,_) ->
      mem Env.find_union_member id
    | _ -> false
  (*- #End *)

  (* Move to the member named [name] of the current point, which must be
     a struct or a union. *)
  (*- E_COMPCERT_CODE_Elab_zip_member_001 *)
  (*- #Justify_Derived "Utility function" *)
  let rec member env (z, i as zi) name =
    let ty = typeof zi in
    match unroll env ty, i with
    | TStruct(id, _), Init_struct(id', flds) ->
        let rec find before = function
          | [] -> NotFound
          | (fld, i as f_i) :: after ->
              if fld.fld_name = name then
                OK(Zstruct(z, id, before, fld, after), i)
              else if fld.fld_anonymous && has_member env name fld.fld_typ then
                let zi = (Zstruct(z, id, before, fld, after), i) in
                member env zi name
              else
                find (f_i :: before) after
        in find [] flds
    | TUnion(id, _), Init_union(id', fld, i) ->
        if fld.fld_name = name then
          OK(Zunion(z, id, fld), i)
        else begin
          let rec find = function
            | [] -> NotFound
            | fld1 :: rem ->
                if fld1.fld_name = name then
                  OK(Zunion(z, id, fld1), default_init env fld1.fld_typ)
                else if fld.fld_anonymous && has_member env name fld.fld_typ then
                  let zi = (Zunion(z, id, fld1),i) in
                  member env zi name
                else
                  find rem
           in find (Env.find_union env id).Env.ci_members
         end
    | (TStruct _ | TUnion _), Init_single a ->
        (* This is a previous whole-struct initialization that we
           are going to overwrite.  Hard to support correctly
           and without code duplication, so turn it into an error. *)
        Unsupported
    | _, _ ->
        NotFound
  (*- #End *)
end


(* Interpret the given designator, moving the initialization state [zi]
   "down" accordingly. *)

(*- E_COMPCERT_CODE_Elab_elab_designator_001 *)
let rec elab_designator loc env zi desig =
  match desig with
  | [] ->
      zi
  | INFIELD_INIT name :: desig' ->
      begin match I.member env zi name with
      | I.OK zi' ->
          elab_designator loc env zi' desig'
      | I.NotFound ->
          (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_058 *)
          error loc "%s has no member named %s" (I.name zi) name;
          raise Exit
      | I.Unsupported ->
          (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_060 *)
          error loc "unsupported reinitialization of %s that was previously initialized as a whole" (I.name zi);
          raise Exit
      end
  | ATINDEX_INIT a :: desig' ->
      let expr,env = (!elab_expr_f loc env a) in
      (*- #Link_to E_COMPCERT_TR_Function_CEVAL_001 *)
      begin match Ceval.integer_expr env expr with
      | None ->
          (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_059 *)
          error loc "array element designator for %s is not an integer constant expression" (I.name zi);
          raise Exit
      | Some n ->
          match I.index env zi n with
          | I.OK zi' ->
              elab_designator loc env zi' desig'
          | I.NotFound ->
              (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_059 *)
              error loc "array index %Ld within %s exceeds array bounds" n (I.name zi);
            raise Exit
          | I.Unsupported -> assert false
      end
(*- #End *)

(* Elaboration of an initialization expression.  Return the corresponding
   initializer. *)

let elab_init loc env root ty_root ie =

(* Perform the initializations described by the list [il] over
   the initialization state [zi].  [first] is true if we are at the
   beginning of a braced initializer.  Returns the final initializer. *)

(*- E_COMPCERT_CODE_Elab_elab_list_001 *)
let rec elab_list zi il first =
  match il with
  | [] ->
      (* All initialization items consumed. *)
      I.to_init zi
  | (desig, item) :: il' ->
      if desig = [] then begin
        match (if first then I.first env zi else I.next zi)
        with
        | I.NotFound ->
            (*- #Link_to E_COMPCERT_TR_Function_ELAB_061 *)
            warning loc Unnamed "excess elements in initializer for %s"
                        (I.name zi);
            I.to_init zi
        | I.OK zi' ->
            elab_item zi' item il'
        | I.Unsupported ->
            error loc "unsupported reinitialization of %s that was previously initialized as a whole" (I.name zi);
            raise Exit
      end else
        elab_item (elab_designator loc env (I.to_top zi) desig) item il'
(*- #End *)


(* Perform the initialization described by [item] for the current
   subobject of state [zi].  Continue initializing with the list [il]. *)

(*- E_COMPCERT_CODE_Elab_elab_item_001 *)
and elab_item zi item il =
  let ty = I.typeof zi in
  match item, unroll env ty with
  (* Special case char array = "string literal"
               or wchar array = L"wide string literal" *)
  | (SINGLE_INIT (CONSTANT (CONST_STRING(w, s)))
     | COMPOUND_INIT [_, SINGLE_INIT(CONSTANT (CONST_STRING(w, s)))]),
    TArray(ty_elt, sz, _)
    when is_integer_type env ty_elt ->
      begin match elab_string_literal loc w s, unroll env ty_elt with
      | CStr s, TInt((IChar | ISChar | IUChar), _) ->
          (*- #Link_to E_COMPCERT_TR_Function_ELAB_063 *)
          if not (I.index_below (Int64.of_int(String.length s - 1)) sz) then
            warning loc Unnamed "initializer string for array of chars %s is too long" (I.name zi);
          elab_list (I.set zi (init_char_array_string sz s)) il false
      | CStr _, _ ->
          (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_064 *)
          error loc "initialization of an array of non-char elements with a string literal";
          elab_list zi il false
      | CWStr s, TInt(_, _) when compatible_types AttrIgnoreTop env ty_elt (TInt(wchar_ikind(), [])) ->
          (*- #Link_to E_COMPCERT_TR_Function_ELAB_063 *)
          if not (I.index_below (Int64.of_int(List.length s - 1)) sz) then
            warning loc Unnamed "initializer string for array of wide chars %s is too long" (I.name zi);
          elab_list (I.set zi (init_int_array_wstring sz s)) il false
      | CWStr _, _ ->
          (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_064 *)
          error loc "initialization of an array of non-wchar_t elements with a wide string literal";
          elab_list zi il false
      | _ -> assert false
      end
  (* Brace-enclosed compound initializer *)
  | COMPOUND_INIT il', _ ->
      (* Process the brace-enclosed stuff, obtaining its initializer *)
      let ini' = elab_list (I.top env (I.name zi) ty) il' true in
      (* Initialize current subobject with this state, and continue *)
      elab_list (I.set zi ini') il false
  (* Single expression *)
  | SINGLE_INIT a, _ ->
      let a',_ = !elab_expr_f loc env a in
      elab_single zi a' il
  (* No initializer: can this happen? *)
  | NO_INIT, _ ->
      elab_list zi il false
(*- #End *)

(* Perform initialization by a single expression [a] for the current
   subobject of state [zi],  Continue initializing with the list [il']. *)

(*- E_COMPCERT_CODE_Elab_elab_single_001 *)
and elab_single zi a il =
  let ty = I.typeof zi in
  match unroll env ty with
  | TInt _ | TEnum _ | TFloat _ | TPtr _ ->
      (* This is a scalar: do direct initialization and continue *)
      check_init_type loc env a ty;
      elab_list (I.set zi (Init_single a)) il false
  | TStruct _ | TUnion _ when compatible_types AttrIgnoreTop env ty a.etyp ->
      (* This is a composite that can be initialized directly
         from the expression: do as above *)
      elab_list (I.set zi (Init_single a)) il false
  | TStruct _ | TUnion _ | TArray _ ->
      (* This is an aggregate.
         At top, explicit { } are required. *)
      if I.at_top zi then begin
        (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_067 *)
        error loc "invalid initializer, an initializer list was expected";
        raise Exit
      end;
      (* Otherwise we need to drill into the aggregate, recursively *)
      begin match I.first env zi with
      | I.OK zi' ->
          elab_single zi' a il
      | I.NotFound ->
          (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_068 *)
          error loc "initializer for aggregate %s with no elements requires explicit braces"
                    (I.name zi);
          raise Exit
      | I.Unsupported ->
          (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_065 *)
          error loc "unsupported reinitialization of %s that was previously initialized as a whole" (I.name zi);
          raise Exit
      end
  | _ ->
      error loc "impossible to initialize %s of type %a"
                (I.name zi) (print_typ env) ty;
      raise Exit
(*- #End *)

(* Start with top-level object initialized to default *)

(*- E_COMPCERT_CODE_Elab_elab_init_001 *)
in
(*- #Link_to E_COMPCERT_TR_Robustness_ELAB_069 *)
if is_function_type env ty_root then begin
  error loc "illegal initializer (only variables can be initialized)";
  raise Exit
end;
(*- #Link_to E_COMPCERT_TR_Robustness_ELAB_070 *)
try
  elab_item (I.top env root ty_root) ie []
with No_default_init ->
  error loc "variable has incomplete type %a" (print_typ env) ty_root;
  raise Exit
(*- #End *)


(* Elaboration of a top-level initializer *)

(*- E_COMPCERT_CODE_Elab_elab_initial_001 *)
(*- #Link_to E_COMPCERT_TR_Function_ELAB_191 *)
let elab_initial loc env root ty ie =
  match ie with
  | NO_INIT -> None
  | _ ->
    try
      Some (elab_init loc env root ty ie)
    with
    | Exit -> None  (* error was already reported *)
    | Env.Error msg -> error loc "%s" (Env.error_message msg); None
(*- #End *)

(* Check struct initializers whether they contain a non-default
   initializer for flexible array members, also for structs recursively
   contained in unions *)

(*- E_COMPCERT_CODE_Elab_check_struct_init_001 *)
let check_struct_init loc env init =
  let rec aux = function
    | Init_struct (id, il) ->
      begin match find_flex_array_mem env id with
        | Some name ->
          (* Check whether the flexible array member has an initializer that is not
             the default initializer *)
          let has_init = List.exists
              (fun (fld, init) -> fld.fld_name = name && init <> Init_array []) il in
          if has_init then
            (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_222 *)
            error loc "initialization of flexible array member '%s' is not allowed" name
        | None -> ()
      end;
    | Init_union (_, _, init) -> aux init
    | _ -> () (* Structs with flexible array members are only allowed in toplevel structs *)
  in
  aux init
(*- #End *)

(* Complete an array type with the size obtained from the initializer:
   "int x[] = { 1, 2, 3 }" becomes "int x[3] = ..." *)

(*- E_COMPCERT_CODE_Elab_fixup_typ_001 *)
let fixup_typ loc env ty init =
  match unroll env ty, init with
  | TArray(ty_elt, None, attr), Init_array il ->
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_071 *)
      if il = [] then warning loc Zero_length_array "zero size arrays are an extension";
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_011 *)
      TArray(ty_elt, Some(Int64.of_int(List.length il)), attr)
  | _ -> ty
(*- #End *)


(* Entry point *)

(*- E_COMPCERT_CODE_Elab_elab_initializer_001 *)
let elab_initializer loc env root ty ie =
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_010 *)
  match elab_initial loc env root ty ie with
  | None ->
      (ty, None)
  | Some init ->
      check_struct_init loc env init;
      (fixup_typ loc env ty init, Some init)
(*- #End *)



(* Contexts for elaborating statements and expressions *)

type elab_context = {
  ctx_return_typ: typ;          (**r return type for the function *)
  ctx_labels: StringSet.t;      (**r all labels defined in the function *)
  ctx_break: bool;              (**r is 'break' allowed? *)
  ctx_continue: bool;           (**r is 'continue' allowed? *)
  ctx_in_switch: bool;          (**r are 'case' and 'default' allowed? *)
  ctx_vararg: bool;             (**r is this a vararg function? *)
  ctx_nonstatic_inline: bool    (**r is this a nonstatic inline function? *)
}

(* Context for evaluating compile-time constant expressions.
   Only the [ctx_vararg] and [ctx_nonstatic_inline] fields matter. *)
let ctx_constexp = {
  ctx_return_typ = TVoid [];
  ctx_labels = StringSet.empty;
  ctx_break = false; ctx_continue = false; ctx_in_switch = false;
  ctx_vararg = false; ctx_nonstatic_inline = false
}



(* Elaboration of expressions *)

let elab_expr ctx loc env a =

  let error fmt = error loc fmt in
  let fatal_error fmt = fatal_error loc fmt in
  let warning t fmt = warning loc t fmt in

  (*- E_COMPCERT_CODE_Elab_elab_expr_check_ptr_arith_001 *)
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_072 *)
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_094 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_175 *)
  let check_ptr_arith env ty s =
    match unroll env ty with
    | TVoid _ ->
        error "illegal arithmetic on a pointer to void in %s" s
    | TFun _ ->
        error "illegal arithmetic on a pointer to the function type %a in %s" (print_typ env) ty s
    | _ -> if incomplete_type env ty then
        error "arithmetic on a pointer to an incomplete type %a in %s" (print_typ env) ty s
  in
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_check_static_var_001 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_167 *)
  let check_static_var env id sto ty =
    if ctx.ctx_nonstatic_inline
    && sto = Storage_static
    && List.mem AConst (attributes_of_type env ty)
    then warning Static_in_inline "static variable '%s' is used in an inline function with external linkage" id.C.name
  in
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_check_builtin_fun_001 *)
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_220 *)
  let check_builtin_fun env called_fun id =
    if not called_fun && Env.is_builtin id.C.name then
      error "builtin function '%s' must be directly called" id.C.name;
  in
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_lookup_known_id_001 *)
  (*- #Justify_Derived "Utility function" *)
  let lookup_known_id env id =
    match wrap Env.lookup_ident loc env id with
    | (id, Env.II_ident(sto, ty)) -> { edesc = EVar id; etyp = ty }
    | _ -> assert false
  in
  (*- #End *)

  (* The optional parameter call indicates whether the expression is
     the called function in a function call *)
  let rec elab ?(called_fun=false) env = function

(* 6.5.1 Primary expressions *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_001 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_179 *)
  | VARIABLE s ->
      begin match wrap Env.lookup_ident loc env s with
        | (id, Env.II_ident(sto, ty)) ->
          check_builtin_fun env called_fun id;
          check_static_var env id sto ty;
          { edesc = EVar id; etyp = ty },env
      | (id, Env.II_enum v) ->
          { edesc = EConst(CEnum(id, v)); etyp = TInt(enum_ikind, []) },env
      end
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_002 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_179 *)
  | CONSTANT cst ->
      let cst' = elab_constant loc cst in
      { edesc = EConst cst'; etyp = type_of_constant cst' },env
  (*- #End *)

(* 6.5.2 Postfix expressions *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_003 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_180 *)
  | INDEX(a1, a2) ->            (* e1[e2] *)
      let b1,env = elab env a1 in
      let b2,env = elab env a2 in
      let tres =
        match (unroll env b1.etyp, unroll env b2.etyp) with
        | (TPtr(t, _) | TArray(t, _, _)), (TInt _ | TEnum _) -> t
        | (TInt _ | TEnum _), (TPtr(t, _) | TArray(t, _, _)) -> t
        (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_073 *)
        | t1, t2 -> fatal_error "subscripted value is neither an array nor pointer" in
      { edesc = EBinop(Oindex, b1, b2, TPtr(tres, [])); etyp = tres },env
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_004 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_182 *)
  | MEMBEROF(a1, fieldname) ->
      let b1,env = elab env a1 in
      let (fld, attrs) =
        match unroll env b1.etyp with
        | TStruct(id, attrs) ->
            (wrap Env.find_struct_member loc env (id, fieldname), attrs)
        | TUnion(id, attrs) ->
            (wrap Env.find_union_member loc env (id, fieldname), attrs)
        (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_074 *)
        | _ ->
            fatal_error "request for member '%s' in something not a structure or union" fieldname in
      (* A field of a const/volatile struct or union is itself const/volatile *)
      let rec access = function
         | [] -> b1
         | fld::rest ->
             let b1 = access rest in
             { edesc = EUnop(Odot fld.fld_name, b1);
               etyp = add_attributes_type (List.filter attr_inherited_by_members attrs)
                 (type_of_member env fld) } in
       access fld,env
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_005 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_182 *)
  | MEMBEROFPTR(a1, fieldname) ->
      let b1,env = elab env a1 in
      let (fld, attrs) =
        match unroll env b1.etyp with
        | TPtr(t, _) | TArray(t,_,_) ->
            begin match unroll env t with
            | TStruct(id, attrs) ->
                (wrap Env.find_struct_member loc env (id, fieldname), attrs)
            | TUnion(id, attrs) ->
                (wrap Env.find_union_member loc env (id, fieldname), attrs)
            (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_075 *)
            | _ ->
                fatal_error "request for member '%s' in something not a structure or union" fieldname
            end
        | _ ->
            (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_075 *)
            fatal_error "member reference type %a is not a pointer" (print_typ env) b1.etyp in
       let rec access =  function
         | [] -> assert false
         | [fld] ->
           { edesc = EUnop(Oarrow fld.fld_name, b1);
               etyp = add_attributes_type (List.filter attr_inherited_by_members attrs)
                (type_of_member env fld) }
         | fld::rest ->
             let b1 = access rest in
             { edesc = EUnop(Odot fld.fld_name, b1);
               etyp = add_attributes_type (List.filter attr_inherited_by_members attrs)
                (type_of_member env fld) } in
            access fld,env
  (*- #End *)

(* Hack to treat vararg.h functions the GCC way.  Helps with testing.
    va_start(ap,n)
      (preprocessing) --> __builtin_va_start(ap, arg)
      (elaboration)   --> __builtin_va_start(ap)
    va_arg(ap, ty)
      (preprocessing) --> __builtin_va_arg(ap, ty)
      (elaboration)   --> __builtin_va_arg(ap, sizeof(ty))
*)
  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_006 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_181 *)
  | CALL(VARIABLE "__builtin_va_start", args) ->
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_077 *)
      if not ctx.ctx_vararg then
        error "'va_start' used in function with fixed args";
      let b1 = lookup_known_id env "__builtin_va_start" in
      begin match args with
        | [a2; a3] ->
          let b2,env = elab env a2 in
          let _b3,env = elab env a3 in
          { edesc = ECall(b1, [b2]);
            etyp = TVoid [] },env
        (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_210 *)
        | _ -> fatal_error "'__builtin_va_start' expects 2 arguments"
      end
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_037 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_217 *)
  | CALL((VARIABLE ("__builtin_inff" | "__builtin_huge_valf" as id)), args) ->
      begin match args with
        | [] -> ()
        | _ -> fatal_error "'%s' expects no arguments" id
      end;
      {edesc = EConst (CFloat (FInfinity false, FFloat)); etyp = TFloat (FFloat, [])}, env
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_038 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_218 *)
  | CALL((VARIABLE ("__builtin_inf" | "__builtin_huge_val" as id)), args) ->
      begin match args with
        | [] -> ()
        | _ -> fatal_error "'%s' expects no arguments" id
      end;
      {edesc = EConst (CFloat (FInfinity false, FDouble)); etyp = TFloat (FDouble, [])}, env
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_039 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_215 *)
  | CALL (VARIABLE ("__builtin_nanf" as id), al) ->
      let conv i =
        let i = Int64.logand i 0x3FFFFFL in (* We only need the lower bits *)
         Int64.logor i 0x7FC00000L in (* Set exponent to all 1s and set quiet bit *)
      elab_nan_variants env conv "nanf" FFloat id al
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_040 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_216 *)
  | CALL (VARIABLE ("__builtin_nansf" as id), al) ->
      let conv i =
        let i = Int64.logand i 0x3FFFFFL in (* We only need the lower bits *)
        let i = if i = 0L then 0x200000L else i in (* Avoid all zeros by setting one bit *)
        Int64.logor i 0x7F800000L in (* Set exponent to all 1s *)
      elab_nan_variants env conv "nansf" FFloat id al
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_044 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_223 *)
  | CALL (VARIABLE ("__builtin_nan" as id), al) ->
    let conv i =
      let i = Int64.logand i 0x7FFFFFFFFFFFFL in (* We only need the lower bits *)
      Int64.logor i 0x7FF8000000000000L in (* Set exponent to all 1s and set quiet bit *)
    elab_nan_variants env conv "nan" FDouble id al
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_045 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_224 *)
  | CALL (VARIABLE ("__builtin_nans" as id), al) ->
    let conv i =
      let i = Int64.logand i 0x7FFFFFFFFFFFFL in (* We only need the lower bits *)
      let i = if i = 0L then 0x4000000000000L else i in (* Avoid all zeros by setting one bit *)
      Int64.logor i 0x7FF0000000000000L in (* Set exponent to all 1s *)
    elab_nan_variants env conv "nans" FDouble id al
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_007 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_181 *)
  | BUILTIN_VA_ARG (a2, a3) ->
      let ident = lookup_known_id env "__builtin_va_arg" in
      let b2,env = elab env a2 in
      let b3,env = elab env (TYPE_SIZEOF a3) in
      let ty = match b3.edesc with ESizeof ty -> ty | _ -> assert false in
      let ty' = default_argument_conversion env ty in
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_078 *)
      if not (compatible_types AttrIgnoreTop env ty ty') then
        warning Varargs "%a is promoted to %a when passed through '...'. You should pass %a, not %a, to 'va_arg'"
          (print_typ env) ty (print_typ env) ty'  (print_typ env) ty'  (print_typ env) ty;
      { edesc = ECall(ident, [b2; b3]); etyp = ty },env
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_036 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_212 *)
  | CALL(VARIABLE "__builtin_constant_p", al) ->
      begin match al with
      | [a1] ->
          let b1,env = elab env a1 in
          let v = if Ceval.is_constant_expr env b1 then 1L else 0L in
          intconst v IInt, env
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_211 *)
      | _ ->
          fatal_error "'__builtin_constant_p' expects one argument"
      end
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_041 *)
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_221 *)
  | CALL(VARIABLE ("__builtin_isnan" as id), al) when Env.is_builtin id ->
      let s_id = "__builtin_isnanf"
      and d_id = "__builtin_isnan" in
      elab_float_generic_builtin_one_arg env id d_id s_id al
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_042 *)
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_221 *)
  | CALL(VARIABLE ("__builtin_isinf" as id), al) when Env.is_builtin id ->
      let s_id = "__builtin_isinff"
      and d_id = "__builtin_isinf" in
      elab_float_generic_builtin_one_arg env id d_id s_id al
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_043 *)
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_221 *)
  | CALL(VARIABLE ("__builtin_isfinite" as id), al) when Env.is_builtin id ->
      let s_id = "__builtin_isfinitef"
      and d_id = "__builtin_isfinite" in
      elab_float_generic_builtin_one_arg env id d_id s_id al
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_035 *)
  | CALL(VARIABLE "__builtin_sel", al) ->
      begin match al with
      | [a1; a2; a3] ->
          let b0 = lookup_known_id env "__builtin_sel" in
          let b1,env = elab env a1 in
          let b2,env = elab env a2 in
          let b3,env = elab env a3 in
          if not (is_scalar_type env b1.etyp) then
            (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_205 *)
            error "first argument of '__builtin_sel' is not a scalar type (invalid %a)"
               (print_typ env) b1.etyp;
          let tyres =
            match pointer_decay env b2.etyp, pointer_decay env b3.etyp with
            | (TInt _ | TFloat _ | TEnum _), (TInt _ | TFloat _ | TEnum _) ->
                binary_conversion env b2.etyp b3.etyp
            | (TPtr(ty1, a1) as pty1), (TPtr(ty2, a2)  as pty2) ->
                if is_void_type env ty1 || is_void_type env ty2 then
                  TPtr(TVoid (add_attributes a1 a2), [])
                else begin
                  match combine_types AttrIgnoreAll env pty1 pty2 with
                  | None ->
                      (*- #Link_to E_COMPCERT_TR_Function_ELAB_204 *)
                      warning Pointer_type_mismatch "the second and third arguments of '__builtin_sel' have incompatible pointer types (%a and %a)"
                     (print_typ env) pty1  (print_typ env) pty2;
                     (* tolerance *)
                     TPtr(TVoid (add_attributes a1 a2), [])
                  | Some ty -> ty
                end
            | _, _ ->
                (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_206 *)
                fatal_error "wrong types (%a and %a) for the second and third arguments of '__builtin_sel'"
                  (print_typ env) b2.etyp (print_typ env) b3.etyp

            in
          { edesc = ECall(b0, [b1; b2; b3]); etyp = tyres }, env
      | _ ->
          (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_207 *)
          fatal_error "'__builtin_sel' expect 3 arguments"
      end
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_008 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_181 *)
  | CALL(a1, al) ->
      let b1,env =
        (* Catch the old-style usage of calling a function without
           having declared it *)
        match a1 with
        | VARIABLE n when not (Env.ident_is_bound env n) ->
            let is_builtin = String.length n > 10
                           && String.sub n 0 10 = "__builtin_" in
            if is_builtin then
              (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_208 *)
              (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_221 *)
              error "use of unknown builtin '%s'" n
            else
              (*- #Link_to E_COMPCERT_TR_Function_ELAB_079 *)
              warning Implicit_function_declaration "implicit declaration of function '%s' is invalid in C99" n;
            let ty = TFun(TInt(IInt, []), None, false, []) in
            (* Check against other definitions and enter in env *)
            let (id, sto, env, ty, linkage) =
              enter_or_refine_ident true loc env n Storage_extern ty in
            (* Emit an extern declaration for it *)
            emit_elab ~linkage env loc (Gdecl(sto, id, ty, None));
            { edesc = EVar id; etyp = ty },env
        | _ -> elab ~called_fun:true env a1 in
      let (bl, env) = mmap (fun env e -> elab env e) env al in
      (* Extract type information *)
      let (res, args, vararg) =
        match unroll env b1.etyp with
        | TFun(res, args, vararg, a) -> (res, args, vararg)
        | TPtr(ty, a) ->
            begin match unroll env ty with
            | TFun(res, args, vararg, a) -> (res, args, vararg)
            (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_080 *)
            | _ -> fatal_error "called object type %a is neither a function nor function pointer" (print_typ env) b1.etyp
            end
        (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_080 *)
        | _ -> fatal_error "called object type %a is neither a function nor function pointer" (print_typ env) b1.etyp
      in
      (* Type-check the arguments against the prototype *)
      let bl',env =
        match args with
        | None ->
          List.iter (fun arg ->
              let arg_typ = argument_conversion env arg.etyp in
              if incomplete_type env arg_typ then
                (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_202 *)
                error "argument type %a is incomplete" (print_typ env) arg.etyp;
            ) bl; (bl,env)
        | Some proto -> elab_arguments 1 (bl, env) proto vararg in
      { edesc = ECall(b1, bl'); etyp = res },env
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_009 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_184 *)
  | UNARY(POSINCR, a1) ->
      elab_pre_post_incr_decr env Opostincr "increment" a1
  | UNARY(POSDECR, a1) ->
      elab_pre_post_incr_decr env Opostdecr "decrement" a1
  (*- #End *)

(* 6.5.4 Cast operators *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_010 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_184 *)
  | CAST ((spec, dcl), SINGLE_INIT a1) ->
      let (ty, env) = elab_type loc env spec dcl in
      let b1,env = elab env a1 in
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_081 *)
      if not (wrap2 valid_cast loc env b1.etyp ty) then
        begin match unroll env b1.etyp, unroll env ty with
        | _, (TStruct _|TUnion _ | TVoid _) ->
            error "used type %a where arithmetic or pointer type is required"
              (print_typ env) ty
        | (TStruct _| TUnion _ | TVoid _),_ ->
            error "operand of type %a where arithmetic or pointer type is required"
              (print_typ env) b1.etyp
        | TFloat _, TPtr _  ->
            error "operand of type %a cannot be cast to a pointer type"
              (print_typ env) b1.etyp
        | TPtr _ , TFloat _ ->
            error "pointer cannot be cast to type %a" (print_typ env) ty
        | _ ->
            error "illegal cast from %a to %a" (print_typ env) b1.etyp (print_typ env) ty
        end;
      { edesc = ECast(ty, b1); etyp = ty },env
  (*- #End *)

(* 6.5.2.5 Compound literals *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_011 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_183 *)
  | CAST ((spec, dcl), ie) ->
      let (ty, env) = elab_type loc env spec dcl in
      if not (is_array_type env ty) && incomplete_type env ty then
        (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_082 *)
        fatal_error "ill-formed compound literal with incomplete type %a" (print_typ env) ty;
      begin match elab_initializer loc env "<compound literal>" ty ie with
      | (ty', Some i) -> { edesc = ECompound(ty', i); etyp = ty' },env
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_082 *)
      | (ty', None)   -> fatal_error "ill-formed compound literal"
      end
  (*- #End *)

(* 6.5.3 Unary expressions *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_012 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_184 *)
  | EXPR_SIZEOF a1 ->
      let b1,env = elab env a1 in
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_084 *)
      if wrap incomplete_type loc env b1.etyp then
        fatal_error "invalid application of 'sizeof' to an incomplete type %a" (print_typ env) b1.etyp;
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_084 *)
      if wrap is_bitfield loc env b1 then
        fatal_error "invalid application of 'sizeof' to a bit-field";
      { edesc = ESizeof b1.etyp; etyp = TInt(size_t_ikind(), []) },env
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_013 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_184 *)
  | TYPE_SIZEOF (spec, dcl) ->
      let (ty, env') = elab_type loc env spec dcl in
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_083 *)
      if wrap incomplete_type loc env' ty then
        fatal_error "invalid application of 'sizeof' to an incomplete type %a" (print_typ env) ty;
      { edesc = ESizeof ty; etyp = TInt(size_t_ikind(), []) },env'
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_014 *)
  | ALIGNOF (spec, dcl) ->
      let (ty, env') = elab_type loc env spec dcl in
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_154 *)
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_159 *)
      warning Celeven_extension "'_Alignof' is a C11 extension";
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_083 *)
      if wrap incomplete_type loc env' ty then
        fatal_error "invalid application of 'alignof' to an incomplete type %a" (print_typ env) ty;
      { edesc = EAlignof ty; etyp =  TInt(size_t_ikind(), []) },env'
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_015 *)
  | BUILTIN_OFFSETOF ((spec,dcl), mem) ->
    let (ty,env) = elab_type loc env spec dcl in
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_085 *)
    if  incomplete_type env ty then
      fatal_error "offsetof of incomplete type %a" (print_typ env) ty;
    let members env ty mem =
      match ty with
      | TStruct (id,_) -> wrap Env.find_struct_member loc env (id,mem)
      | TUnion (id,_) -> wrap Env.find_union_member loc env (id,mem)
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_086 *)
      | _ -> fatal_error "request for member '%s' in something not a structure or union" mem in
    let rec offset_of_list acc env ty = function
      | [] -> acc,ty
      | fld::rest ->
        if fld.fld_bitfield <> None then
          (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_155 *)
          fatal_error "cannot compute offset of bit-field '%s'" fld.fld_name;
        let off = offsetof env ty fld in
        offset_of_list (acc+off) env fld.fld_typ rest in
    let offset_of_member (env,off_accu,ty) mem =
      match mem,unroll env ty with
      | INFIELD_INIT mem,ty ->
        let flds = members env ty mem in
        let flds = List.rev flds in
        let off,ty = offset_of_list 0 env ty flds in
        env,off_accu + off,ty
      | ATINDEX_INIT e,TArray (sub_ty,_,_) ->
        let e,env = elab env e in
        (*- #Link_to E_COMPCERT_TR_Function_CEVAL_001 *)
        let e = match Ceval.integer_expr env e with
          (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_088 *)
          | None -> fatal_error "array element designator is not an integer constant expression"
          | Some n-> n in
        let size = match sizeof env sub_ty with
          | None -> assert false (* We expect only complete types *)
          | Some s -> s in
        let off_accu = match cautious_mul e size with
          (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_089 *)
          | None -> fatal_error "'offsetof' overflows"
          | Some s -> off_accu + s in
        env,off_accu,sub_ty
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_087 *)
      | ATINDEX_INIT _,_ -> fatal_error "subscripted value is not an array" in
    let env,offset,_ = List.fold_left offset_of_member (env,0,ty) mem in
    let size_t = size_t_ikind () in
    (*- #Link_to E_COMPCERT_TR_Function_CEVAL_007 *)
    let offset = Ceval.normalize_int (Int64.of_int offset) size_t in
    let offsetof_const = EConst (CInt(offset,size_t,"")) in
    { edesc = offsetof_const; etyp = TInt(size_t, []) },env
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_016 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_184 *)
  | UNARY(PLUS, a1) ->
      let b1,env = elab env a1 in
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_090 *)
      if not (is_arith_type env b1.etyp) then
        fatal_error "invalid argument type %a to unary '+'" (print_typ env) b1.etyp;
      { edesc = EUnop(Oplus, b1); etyp = unary_conversion env b1.etyp },env
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_017 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_184 *)
  | UNARY(MINUS, a1) ->
      let b1,env = elab env a1 in
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_090 *)
      if not (is_arith_type env b1.etyp) then
        fatal_error "invalid argument type %a to unary '-'" (print_typ env) b1.etyp;
      { edesc = EUnop(Ominus, b1); etyp = unary_conversion env b1.etyp },env
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_018 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_184 *)
  | UNARY(BNOT, a1) ->
      let b1,env = elab env a1 in
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_090 *)
      if not (is_integer_type env b1.etyp) then
        fatal_error "invalid argument type %a to unary '~'" (print_typ env) b1.etyp;
      { edesc = EUnop(Onot, b1); etyp = unary_conversion env b1.etyp },env
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_019 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_184 *)
  | UNARY(NOT, a1) ->
      let b1,env = elab env a1 in
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_090 *)
      if not (is_scalar_type env b1.etyp) then
        fatal_error "invalid argument type %a to unary '!'" (print_typ env) b1.etyp;
      { edesc = EUnop(Olognot, b1); etyp = TInt(IInt, []) },env
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_020 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_184 *)
  | UNARY(ADDROF, a1) ->
      let b1,env = elab env a1 in
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_091 *)
      if not (is_lvalue b1 || is_function_type env b1.etyp) then
        error "argument of '&' is not an lvalue (invalid %a)" (print_typ env) b1.etyp;
      begin match b1.edesc with
      | EVar id ->
          begin match wrap Env.find_ident loc env id with
          | Env.II_ident(Storage_register, _) ->
              (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_091 *)
              error "address of register variable '%s' requested" id.C.name
          | _ -> ()
          end
      | EUnop(Odot f, b2) ->
          let fld = wrap2 field_of_dot_access loc env b2.etyp f in
          (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_091 *)
          if fld.fld_bitfield <> None then
            error "address of bit-field '%s' requested" f
      | EUnop(Oarrow f, b2) ->
          let fld = wrap2 field_of_arrow_access loc env b2.etyp f in
          (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_091 *)
          if fld.fld_bitfield <> None then
            error "address of bit-field '%s' requested" f
      | _ -> ()
      end;
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_091 *)
      { edesc = EUnop(Oaddrof, b1); etyp = TPtr(b1.etyp, []) },env
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_021 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_184 *)
  | UNARY(MEMOF, a1) ->
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_090 *)
      let b1,env = elab env a1 in
      begin match unroll env b1.etyp with
      (* '*' applied to a function type has no effect *)
      | TFun _ -> b1,env
      | TPtr(ty, _) | TArray(ty, _, _) ->
          { edesc = EUnop(Oderef, b1); etyp = ty },env
      | _ ->
          fatal_error "argument of unary '*' is not a pointer (%a invalid)"
            (print_typ env) b1.etyp
      end
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_022 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_184 *)
  | UNARY(PREINCR, a1) ->
      elab_pre_post_incr_decr env Opreincr "increment" a1
  | UNARY(PREDECR, a1) ->
      elab_pre_post_incr_decr env Opredecr "decrement" a1
  (*- #End *)

(* 6.5.5 to 6.5.12  Binary operator expressions *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_023 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_184 *)
  | BINARY(MUL, a1, a2) ->
      elab_binary_arithmetic env "*" Omul a1 a2

  | BINARY(DIV, a1, a2) ->
      elab_binary_arithmetic env "/" Odiv a1 a2
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_024 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_184 *)
  | BINARY(MOD, a1, a2) ->
      elab_binary_integer env "%" Omod a1 a2
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_025 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_184 *)
  | BINARY(ADD, a1, a2) ->
      let b1,env = elab env a1 in
      let b2,env = elab env a2 in
      let tyres =
        if is_arith_type env b1.etyp && is_arith_type env b2.etyp then
          binary_conversion env b1.etyp b2.etyp
        else begin
          let ty =
            match unroll env b1.etyp, unroll env b2.etyp with
            | (TPtr(ty, a) | TArray(ty, _, a)), (TInt _ | TEnum _) -> ty
            | (TInt _ | TEnum _), (TPtr(ty, a) | TArray(ty, _, a)) -> ty
            (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_092 *)
            | _, _ -> fatal_error "invalid operands to binary '+' (%a and %a)"
                  (print_typ env) b1.etyp (print_typ env) b2.etyp
          in
          check_ptr_arith env ty "binary '+'";
          TPtr(ty, [])
        end in
      { edesc = EBinop(Oadd, b1, b2, tyres); etyp = tyres },env
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_026 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_184 *)
  | BINARY(SUB, a1, a2) ->
      let b1,env = elab env a1 in
      let b2,env = elab env a2 in
      let (tyop, tyres) =
        if is_arith_type env b1.etyp && is_arith_type env b2.etyp then begin
          let tyres = binary_conversion env b1.etyp b2.etyp in
          (tyres, tyres)
        end else begin
          match wrap unroll loc env b1.etyp, wrap  unroll loc env b2.etyp with
          | (TPtr(ty, a) | TArray(ty, _, a)), (TInt _ | TEnum _) ->
              check_ptr_arith env ty "binary '-'";
              (TPtr(ty, []), TPtr(ty, []))
          | (TPtr(ty1, a1) | TArray(ty1, _, a1)),
            (TPtr(ty2, a2) | TArray(ty2, _, a2)) ->
              (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_094 *)
              if not (compatible_types AttrIgnoreAll env ty1 ty2) then
                error "%a and %a are not pointers to compatible types"
                   (print_typ env) b1.etyp (print_typ env) b2.etyp;
              check_ptr_arith env ty1 "binary '-'";
              check_ptr_arith env ty2 "binary '-'";
              (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_094 *)
              if wrap sizeof loc env ty1 = Some 0 then
                error "subtraction between two pointers to zero-sized objects";
              (TPtr(ty1, []), TInt(ptrdiff_t_ikind(), []))
          (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_092 *)
          | _, _ -> fatal_error "invalid operands to binary '-' (%a and %a)"
                (print_typ env) b1.etyp (print_typ env) b2.etyp
        end in
      { edesc = EBinop(Osub, b1, b2, tyop); etyp = tyres },env
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_027 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_184 *)
  | BINARY(SHL, a1, a2) ->
      elab_shift env "<<" Oshl a1 a2

  | BINARY(SHR, a1, a2) ->
      elab_shift env ">>" Oshr a1 a2
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_028 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_184 *)
  | BINARY(EQ, a1, a2) ->
      elab_comparison env Oeq a1 a2
  | BINARY(NE, a1, a2) ->
      elab_comparison env One a1 a2
  | BINARY(LT, a1, a2) ->
      elab_comparison env Olt a1 a2
  | BINARY(GT, a1, a2) ->
      elab_comparison env Ogt a1 a2
  | BINARY(LE, a1, a2) ->
      elab_comparison env Ole a1 a2
  | BINARY(GE, a1, a2) ->
      elab_comparison env Oge a1 a2
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_029 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_184 *)
  | BINARY(BAND, a1, a2) ->
     elab_binary_integer env "&" Oand a1 a2
  | BINARY(BOR, a1, a2) ->
     elab_binary_integer env "|" Oor a1 a2
  | BINARY(XOR, a1, a2) ->
     elab_binary_integer env "^" Oxor a1 a2
  (*- #End *)

(* 6.5.13 and 6.5.14 Logical operator expressions *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_030 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_184 *)
  | BINARY(AND, a1, a2) ->
      elab_logical_operator env "&&" Ologand a1 a2
  | BINARY(OR, a1, a2) ->
      elab_logical_operator env "||" Ologor a1 a2
  (*- #End *)

(* 6.5.15 Conditional expressions *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_031 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_184 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_175 *)
  | QUESTION(a1, a2, a3) ->
      let b1,env = elab env a1 in
      let b2,env = elab env a2 in
      let b3,env = elab env a3 in
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_095 *)
      if not (is_scalar_type env b1.etyp) then
        error "first argument of '?:' is not a scalar type (invalid %a)"
           (print_typ env) b1.etyp;
      begin match pointer_decay env b2.etyp, pointer_decay env b3.etyp with
      | (TInt _ | TFloat _ | TEnum _), (TInt _ | TFloat _ | TEnum _) ->
          { edesc = EConditional(b1, b2, b3);
            etyp = binary_conversion env b2.etyp b3.etyp },env
      | (TPtr(ty1, a1) as pty1), (TPtr(ty2, a2)  as pty2) ->
          let tyres =
            if is_void_type env ty1 || is_void_type env ty2 then
              TPtr(TVoid (add_attributes a1 a2), [])
            else
              match combine_types AttrIgnoreAll env
                                  (TPtr(ty1, a1)) (TPtr(ty2, a2)) with
              | None ->
                  (*- #Link_to E_COMPCERT_TR_Function_ELAB_156 *)
                  warning Pointer_type_mismatch "the second and third argument of '?:' have incompatible pointer types (%a and %a)"
                     (print_typ env) pty1  (print_typ env) pty2;
                  (* tolerance *)
                  TPtr(TVoid (add_attributes a1 a2), [])
              | Some ty -> ty
            in
          { edesc = EConditional(b1, b2, b3); etyp = tyres },env
      | TPtr(ty1, a1), TInt _ when is_literal_0 b3 ->
          { edesc = EConditional(b1, b2, nullconst); etyp = TPtr(ty1, []) },env
      | TInt _, TPtr(ty2, a2) when is_literal_0 b2 ->
          { edesc = EConditional(b1, nullconst, b3); etyp = TPtr(ty2, []) },env
      | ty1, ty2 ->
          match combine_types AttrIgnoreAll env ty1 ty2 with
          | None ->
              (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_096 *)
              fatal_error "the second and third argument of '?:' incompatible types (%a and %a)"
                 (print_typ env) ty1  (print_typ env) ty2
          | Some tyres ->
              { edesc = EConditional(b1, b2, b3); etyp = tyres },env
      end
  (*- #End *)

(* 6.5.16 Assignment expressions *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_032 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_184 *)
  | BINARY(ASSIGN, a1, a2) ->
      let b1,env = elab env a1 in
      let b2,env = elab env a2 in
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_097 *)
      if List.mem AConst (attributes_of_type env b1.etyp) then
        error "left-hand side of assignment has 'const' type";
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_174 *)
      if not (is_modifiable_lvalue env b1) then
        (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_098 *)
        error "expression is not assignable";
      if not (wrap2 valid_assignment loc env b2 b1.etyp) then begin
        if wrap2 valid_cast loc env b2.etyp b1.etyp then
          (*- #Link_to E_COMPCERT_TR_Function_ELAB_176 *)
          if wrap2 int_pointer_conversion loc env b2.etyp b1.etyp then
            (*- #Link_to E_COMPCERT_TR_Function_ELAB_100 *)
            warning Int_conversion
              "incompatible integer-pointer conversion: assigning to %a from %a"
              (print_typ env) b1.etyp (print_typ env) b2.etyp
          else
            (*- #Link_to E_COMPCERT_TR_Function_ELAB_100 *)
            warning Unnamed
              "incompatible conversion: assigning to %a from %a"
               (print_typ env) b1.etyp (print_typ env) b2.etyp
        else
          (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_099 *)
          error "assigning to %a from incompatible type %a"
            (print_typ env) b1.etyp  (print_typ env) b2.etyp;
      end;
      { edesc = EBinop(Oassign, b1, b2, b1.etyp); etyp = b1.etyp },env
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_033 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_184 *)
  | BINARY((ADD_ASSIGN | SUB_ASSIGN | MUL_ASSIGN | DIV_ASSIGN | MOD_ASSIGN
            | BAND_ASSIGN | BOR_ASSIGN | XOR_ASSIGN | SHL_ASSIGN | SHR_ASSIGN
            as op), a1, a2) ->
      let (sop, top) =
        match op with
        | ADD_ASSIGN -> (ADD, Oadd_assign)
        | SUB_ASSIGN -> (SUB, Osub_assign)
        | MUL_ASSIGN -> (MUL, Omul_assign)
        | DIV_ASSIGN -> (DIV, Odiv_assign)
        | MOD_ASSIGN -> (MOD, Omod_assign)
        | BAND_ASSIGN -> (BAND, Oand_assign)
        | BOR_ASSIGN -> (BOR, Oor_assign)
        | XOR_ASSIGN -> (XOR, Oxor_assign)
        | SHL_ASSIGN -> (SHL, Oshl_assign)
        | SHR_ASSIGN -> (SHR, Oshr_assign)
        | _ -> assert false in
      begin match elab env (BINARY(sop, a1, a2)) with
      | ({ edesc = EBinop(_, b1, b2, _); etyp = ty } as b),env  ->
          (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_097 *)
          if List.mem AConst (attributes_of_type env b1.etyp) then
            error "left-hand side of assignment has 'const' type";
          (*- #Link_to E_COMPCERT_TR_Function_ELAB_174 *)
          if not (is_modifiable_lvalue env b1) then
            (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_098 *)
            error "expression is not assignable";
          if not (wrap2 valid_assignment loc env b b1.etyp) then begin
            if wrap2 valid_cast loc env ty b1.etyp then
              (*- #Link_to E_COMPCERT_TR_Function_ELAB_176 *)
              if wrap2 int_pointer_conversion loc env ty b1.etyp then
                (*- #Link_to E_COMPCERT_TR_Function_ELAB_100 *)
                warning Int_conversion
                  "incompatible integer-pointer conversion: assigning to %a from %a"
                   (print_typ env) b1.etyp  (print_typ env) ty
              else
                (*- #Link_to E_COMPCERT_TR_Function_ELAB_100 *)
                warning Unnamed
                  "incompatible conversion: assigning to %a from %a"
                  (print_typ env) b1.etyp (print_typ env) ty
            else
              (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_099 *)
              error "assigning to %a from incompatible type %a"
                 (print_typ env) b1.etyp (print_typ env) ty;
          end;
          { edesc = EBinop(top, b1, b2, ty); etyp = b1.etyp },env
      | _ -> assert false
      end
  (*- #End *)

(* 6.5.17 Sequential expressions *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_elab_034 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_184 *)
  | BINARY(COMMA, a1, a2) ->
      let b1,env = elab env a1 in
      let b2,env = elab env a2 in
      let  ty2 = pointer_decay env b2.etyp in
      { edesc = EBinop (Ocomma, b1, b2, ty2); etyp = ty2 },env
  (*- #End *)

(* Elaboration of pre- or post- increment/decrement *)

  (*- E_COMPCERT_CODE_Elab_elab_pre_post_incr_decr_001 *)
  and elab_pre_post_incr_decr env op msg a1 =
    let b1,env = elab env a1 in
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_101 *)
    if not (is_modifiable_lvalue env b1) then
      error "expression is not assignable";
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_101 *)
    if not (is_scalar_type env b1.etyp) then
      error "cannot %s value of type %a" msg (print_typ env) b1.etyp;
    begin match unroll env b1.etyp with
    | TPtr (ty, _) | TArray (ty, _ , _) ->
      check_ptr_arith env ty ("unary " ^ msg)
    | _ -> ()
    end;
    { edesc = EUnop(op, b1); etyp = b1.etyp },env
  (*- #End *)

(* Elaboration of binary operators over integers *)

  (*- E_COMPCERT_CODE_Elab_elab_binary_integer_001 *)
  and elab_binary_integer env msg op a1 a2 =
    let b1,env = elab env a1 in
    let b2,env = elab env a2 in
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_092 *)
    if not ((is_integer_type env b1.etyp) && (is_integer_type env b2.etyp)) then
      fatal_error "invalid operands to binary '%s' (%a and %a)" msg
        (print_typ env) b1.etyp (print_typ env) b2.etyp;
    let tyres = binary_conversion env b1.etyp b2.etyp in
    { edesc = EBinop(op, b1, b2, tyres); etyp = tyres },env
  (*- #End *)

(* Elaboration of binary operators over arithmetic types *)

  (*- E_COMPCERT_CODE_Elab_elab_binary_arithmetic_001 *)
  and elab_binary_arithmetic env msg op a1 a2 =
    let b1,env = elab env a1 in
    let b2,env = elab env a2 in
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_092 *)
    if not ((is_arith_type env b1.etyp) && (is_arith_type env b2.etyp)) then
      fatal_error "invalid operands to binary '%s' (%a and %a)" msg
        (print_typ env) b1.etyp (print_typ env) b2.etyp;
    let tyres = binary_conversion env b1.etyp b2.etyp in
    { edesc = EBinop(op, b1, b2, tyres); etyp = tyres },env
  (*- #End *)

(* Elaboration of shift operators *)

  (*- E_COMPCERT_CODE_Elab_elab_shift_001 *)
  and elab_shift env msg op a1 a2 =
    let b1,env = elab env a1 in
    let b2,env = elab env a2 in
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_092 *)
    if not ((is_integer_type env b1.etyp) && (is_integer_type env b2.etyp)) then
      fatal_error "invalid operands to '%s' (%a and %a)" msg
        (print_typ env) b1.etyp (print_typ env) b2.etyp;
    let tyres = unary_conversion env b1.etyp in
    { edesc = EBinop(op, b1, b2, tyres); etyp = tyres },env
  (*- #End *)

(* Elaboration of comparisons *)

  (*- E_COMPCERT_CODE_Elab_elab_comparison_001 *)
  and elab_comparison env op a1 a2 =
      let b1,env = elab env a1 in
      let b2,env = elab env a2 in
      let resdesc =
        match pointer_decay env b1.etyp, pointer_decay env b2.etyp with
        | (TInt _ | TFloat _ | TEnum _), (TInt _ | TFloat _ | TEnum _) ->
            EBinop(op, b1, b2, binary_conversion env b1.etyp b2.etyp)
        | TInt _, TPtr(ty, _) when is_literal_0 b1 ->
            EBinop(op, nullconst, b2, TPtr(ty, []))
        | TPtr(ty, _), TInt _ when is_literal_0 b2 ->
            EBinop(op, b1, nullconst, TPtr(ty, []))
        | TPtr(ty1, _), TPtr(ty2, _)
          when is_void_type env ty1 ->
            EBinop(op, b1, b2, TPtr(ty2, []))
        | TPtr(ty1, _), TPtr(ty2, _)
          when is_void_type env ty2 ->
            EBinop(op, b1, b2, TPtr(ty1, []))
        | TPtr(ty1, _), TPtr(ty2, _) ->
            (*- #Link_to E_COMPCERT_TR_Function_ELAB_102 *)
            if not (compatible_types AttrIgnoreAll env ty1 ty2) then
              warning Compare_distinct_pointer_types "comparison of distinct pointer types (%a and %a)"
                (print_typ env) b1.etyp (print_typ env) b2.etyp;
            let incomp_ty1 = wrap incomplete_type loc env ty1
            and incomp_ty2 = wrap incomplete_type loc env ty2 in
            (*- #Link_to E_COMPCERT_TR_Function_ELAB_102 *)
            if incomp_ty1 <> incomp_ty2 then
              warning Unnamed "comparison of complete and incomplete pointers";
            EBinop(op, b1, b2, TPtr(ty1, []))
        | TPtr _, (TInt _ | TEnum _)
        | (TInt _ | TEnum _), TPtr _ ->
            (*- #Link_to E_COMPCERT_TR_Function_ELAB_102 *)
            warning Unnamed "comparison between pointer and integer (%a and %a)"
              (print_typ env) b1.etyp (print_typ env) b2.etyp;
            EBinop(op, b1, b2, TPtr(TVoid [], []))
        | ty1, ty2 ->
            (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_103 *)
            fatal_error "illegal comparison between types@ %a@ and %a"
              (print_typ env) b1.etyp (print_typ env) b2.etyp; in
      { edesc = resdesc; etyp = TInt(IInt, []) },env
  (*- #End *)

(* Elaboration of && and || *)

  (*- E_COMPCERT_CODE_Elab_elab_logical_operator_001 *)
  and elab_logical_operator env msg op a1 a2 =
    let b1,env = elab env a1 in
    let b2,env = elab env a2 in
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_093 *)
    if not ((is_scalar_type env b1.etyp) && (is_scalar_type env b2.etyp)) then
      fatal_error "invalid operands to binary '%s' (%a and %a)" msg
        (print_typ env) b1.etyp (print_typ env) b2.etyp;
    { edesc = EBinop(op, b1, b2, TInt(IInt, [])); etyp = TInt(IInt, []) },env
  (*- #End *)

(* Type-checking of function arguments *)

  (*- E_COMPCERT_CODE_Elab_elab_arguments_001 *)
  and elab_arguments argno args params vararg =
    match args, params with
    | ([],env), [] -> [],env
    | ([],env), _::_ ->
       let found = argno - 1 in
       let expected = List.length params + found in
       let vararg = if vararg then "at least " else "" in
       (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_104 *)
       error "too few arguments to function call, expected %s%d, have %d" vararg expected found; [],env
   | (_::_,env), [] ->
        if vararg
        then args
        else
          let expected = argno - 1 in
          let found = List.length (fst args) + expected in
          (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_104 *)
          (error "too many arguments to function call, expected %d, have %d" expected found; args)
    | (arg1 :: argl,env), (_, ty_p) :: paraml ->
        let ty_a = argument_conversion env arg1.etyp in
        if not (wrap2 valid_assignment loc env {arg1 with etyp = ty_a} ty_p)
        then begin
          if wrap2 valid_cast loc env ty_a ty_p then begin
            (*- #Link_to E_COMPCERT_TR_Function_ELAB_176 *)
            if wrap2 int_pointer_conversion loc env ty_a ty_p then
              (*- #Link_to E_COMPCERT_TR_Function_ELAB_105 *)
              warning Int_conversion
                "incompatible integer-pointer conversion: passing %a to parameter %d of type %a"
                (print_typ env) ty_a argno (print_typ env) ty_p
            else
              (*- #Link_to E_COMPCERT_TR_Function_ELAB_105 *)
              warning Unnamed
                "incompatible conversion: passing %a to parameter %d of type %a"
                (print_typ env) ty_a argno (print_typ env) ty_p end
          else
            (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_106 *)
            error
              "passing %a to parameter %d of incompatible type %a"
              (print_typ env) ty_a argno (print_typ env) ty_p
        end;
        let rest,env = elab_arguments (argno + 1) (argl,env) paraml vararg in
        arg1 :: rest,env
  (*- #End *)


  (*- E_COMPCERT_CODE_Elab_elab_float_generic_builtin_one_arg_001 *)
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_221 *)
  (* Helper function for the single argument type generic float builtins for ARM *)
  and elab_float_generic_builtin_one_arg env b_id double_id single_id al =
    match al with
      | [a1] ->
        let b1, env = elab env a1 in
        let compat fkind = compatible_types AttrIgnoreAll env b1.etyp (TFloat (fkind, [])) in
        let ident  =
          if compat FFloat then
            lookup_known_id env single_id
          else if compat FDouble then
            lookup_known_id env double_id
          else if compat FLongDouble then
            lookup_known_id env double_id (* Works only if long double is double *)
          else
            fatal_error "non-floating-point argument in call to function '%s'" b_id
        in
        let tyres = match unroll env ident.etyp with
          | TFun (res, Some proto, vararg, a) -> res
          | _ -> assert false (* We know that the builtin has function type *) in
        {edesc = ECall (ident, [b1]); etyp = tyres}, env
      | _ ->
        (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_211 *)
        fatal_error "'%s' expects one argument" b_id
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_nan_variants_001 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_215 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_216 *)
  and elab_nan_variants env conv id fk builtin_id al =
    (* We lookup the built-in function to get the types etc. *)
    let ident = lookup_known_id env builtin_id in
    let (bl, env) = mmap (fun env e -> elab env e) env al in
    let (res, proto, vararg) = match unroll env ident.etyp with
      | TFun (res, Some proto, vararg, a) -> (res, proto, vararg)
      | _ -> assert false (* We know that the builtin has this type *) in
    let (bl, env) = elab_arguments 1 (bl, env) proto vararg in
    begin match bl with
      | [bl] ->
        begin match eval_int_of_string_literal env bl with
          | None ->
            let ident = lookup_known_id env id in
            (* None constant argument we call the library function *)
            { edesc = ECall(ident, [bl]); etyp = res },env
          | Some i ->
            let i = conv i in
            {edesc = EConst (CFloat (FBits i, fk)); etyp = TFloat (fk, [])}, env
        end
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_211 *)
      | _ -> fatal_error "'__builtin_%s' expects one argument" id
    end
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_expr_001 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_178 *)
  in elab env a
  (*- #End *)




(* Filling in forward declaration *)

let _ = elab_expr_f := (elab_expr ctx_constexp)

(*- E_COMPCERT_CODE_Elab_elab_opt_expr_001 *)
(*- #Justify_Derived "Utility function" *)
let elab_opt_expr ctx loc env = function
  | None -> None,env
  | Some a -> let a,env = (elab_expr ctx loc env a) in
    Some a,env
(*- #End *)

(*- E_COMPCERT_CODE_Elab_elab_for_expr_001 *)
(*- #Justify_Derived "Utility function" *)
let elab_for_expr ctx loc env = function
  | None -> { sdesc = Sskip; sloc = elab_loc loc },env
  | Some a -> let a,env = elab_expr ctx loc env a in
    { sdesc = Sdo a; sloc = elab_loc loc },env
(*- #End *)

(* Handling of __func__ (section 6.4.2.2) *)

(*- E_COMPCERT_CODE_Elab_func_type_and_init_001 *)
(*- #Justify_Derived "Utility function" *)
let __func__type_and_init s =
  (TArray(TInt(IChar, [AConst]), Some(Int64.of_int (String.length s + 1)), []),
   init_char_array_string None s)
(*- #End *)



(* Elaboration of top-level and local definitions *)

(*- E_COMPCERT_CODE_Elab_enter_typedef_001 *)
let enter_typedef loc env sto (s, ty, init) =
  if init <> NO_INIT then
    error loc "initializer in typedef";
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_157 *)
  if has_std_alignas env ty then
    error loc "alignment specified for typedef '%s'" s;
  List.iter
    (fun a -> match class_of_attribute a with
       | Attr_object | Attr_struct ->
         (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_201 *)
         error loc "attribute '%s' not allowed in 'typedef'"
           (name_of_attribute a)
       | _ -> ())
    (attributes_of_type_no_expand ty);
  match previous_def Env.lookup_typedef env s with
  | Some (s',ty') when Env.in_current_scope env s' ->
    (*- #Link_to E_COMPCERT_TR_Function_ELAB_109 *)
    (*- #Link_to E_COMPCERT_TR_Function_ELAB_154 *)
    if equal_types env ty ty' then begin
      warning loc Celeven_extension "redefinition of typedef '%s' is a C11 extension" s;
      env
    end
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_110 *)
    else begin
      error loc "redefinition of typedef '%s' with different type (%a vs %a)"
        s (print_typ env) ty (print_typ env) ty';
      env
    end
  | _ ->
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_111 *)
    if redef Env.lookup_ident env s then
      error loc "redefinition of '%s' as different kind of symbol" s;
    let (id, env') = Env.enter_typedef env s ty in
    check_reduced_alignment loc env' ty;
    (*- #Link_to E_COMPCERT_TR_Function_ELAB_001 *)
    emit_elab env loc (Gtypedef(id, ty));
    env'
(*- #End *)

(*- E_COMPCERT_CODE_Elab_enter_decdef_001 *)
let enter_decdef local nonstatic_inline loc sto (decls, env) (s, ty, init) =
  let isfun = is_function_type env ty in
  let has_init = init <> NO_INIT in
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_160 *)
  if sto = Storage_register && has_std_alignas env ty then
    error loc "alignment specified for 'register' object '%s'" s;
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_114 *)
  if sto = Storage_extern && has_init then
    error loc "'extern' declaration variable has an initializer";
  if local && isfun then begin
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_113 *)
    match sto with
    | Storage_static ->
      error loc "function declared in block scope cannot have 'static' storage class"
    | Storage_auto | Storage_register ->
      error loc "illegal storage class %s on function"
        (name_of_storage_class sto)
    | _ -> ()
  end;
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_169 *)
  if is_qualified_array ty then
    error loc "type qualifier used in array declarator outside of function prototype";
  (* Local variable declarations with default storage are treated as 'auto'.
     Local function declarations with default storage remain with
     default storage. *)
  let sto1 =
    if local && sto = Storage_default && not isfun
    then Storage_auto
    else sto in
  (* enter ident in environment with declared type, because
     initializer can refer to the ident *)
  let (id, sto', env1, ty, linkage) =
    enter_or_refine_ident local loc env s sto1 ty in
  if has_init && not local then
    add_global_define loc s;
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_116 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_175 *)
  (* check if the type is void or incomplete and the declaration is initialized *)
  if not isfun then begin
    let incomplete_init = not (is_array_type env1 ty) && wrap incomplete_type loc env1 ty && has_init in
    if is_void_type env1 ty || incomplete_init then
      fatal_error loc "variable '%s' has incomplete type %a" s (print_typ env) ty;
  end;
  (* process the initializer *)
  let (ty', init') = elab_initializer loc env1 s ty init in
  (* update environment with refined type *)
  let env2 = Env.add_ident env1 id sto' ty' in
  (* check for incomplete type *)
  if not isfun && wrap incomplete_type loc env ty' then
    (*- #Link_to E_COMPCERT_TR_Function_ELAB_168 *)
    if not local && sto' = Storage_static then begin
      warning loc Tentative_incomplete_static "tentative static definition with incomplete type";
    end
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_117 *)
    else if local && sto' <> Storage_extern then
      error loc "variable '%s' has incomplete type %a" s (print_typ env) ty';
  (* check if alignment is reduced *)
  check_reduced_alignment loc env ty';
  (* check for static variables in nonstatic inline functions *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_167 *)
  if local && nonstatic_inline
     && sto' = Storage_static
     && not (List.mem AConst (attributes_of_type env ty')) then
    warning loc Static_in_inline "non-constant static local variable '%s' in inline function may be different in different files" s;
  if local && not isfun && sto' <> Storage_extern && sto' <> Storage_static then
    (* Local definition *)
    ((sto', id, ty', init') :: decls, env2)
  else begin
    (* Global definition *)
    emit_elab ~linkage env2 loc (Gdecl(sto', id, ty', init'));
    (* Make sure the initializer is constant. *)
    (*- #Link_to E_COMPCERT_TR_Function_CEVAL_001 *)
    begin match init' with
      | Some i when not (Ceval.is_constant_init env2 i) ->
        (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_118 *)
        (*- #Link_to E_COMPCERT_TR_Robustness_PACKED_STRUCT_007 *)
        error loc "initializer is not a compile-time constant"
      | _ -> ()
    end;
    (decls, env2)
  end
(*- #End *)


(* Processing of K&R-style function definitions.  Synopsis:
      T f(X1, ..., Xn)
          T1 Y1; ...; Tm Ym;
      { ... }
  "params" is the list [X1; ...; Xn]
  "defs" is the list of declarations [T1 Y1; ... Tm Ym]
  We need to match the names Xi's with the Yj's so as to find the types Ti'
  of the Xi and produce a typed argument list in prototyped style.
  Owing to default argument promotion, the types Ti' and Tj may not match,
  in which case we need to declare a local variable with the correct type.
  Consider:
      float f(x)  float x;  { return x; }
  Since float arguments are promoted by default to double, this must
  be converted as
      float f(double x)  { float x1 = x; return x1; }
*)

(*- E_COMPCERT_CODE_Elab_elab_KR_function_parameters_001 *)
let elab_KR_function_parameters env params defs loc =
  (* Check that the parameters have unique names *)
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_119 *)
  List.iter (fun id ->
    if List.length (List.filter ((=) id) params) > 1 then
      fatal_error loc "redefinition of parameter '%s'" id)
    params;
  (* Check that the declarations only declare parameters *)
  let extract_name (Init_name(Name(s, dty, attrs, loc') as name, ie)) =
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_120 *)
    if not (List.mem s params) then
      error loc' "declaration of '%s' which is not a function parameter" s;
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_121 *)
    if ie <> NO_INIT then
      error loc' "illegal initialization of parameter '%s'" s;
    name
  in
  (* Extract names and types from the declarations *)
  let elab_param_def env = function
  | DECDEF((spec', name_init_list), loc') ->
      let name_list = List.map extract_name name_init_list in
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_122 *)
      if name_list = [] then
        error loc' "declaration does not declare a parameter";
      let (paramsenv, sto) = elab_name_group loc' env (spec', name_list) in
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_123 *)
      if sto <> Storage_default && sto <> Storage_register then
        error loc'                               (* NB: 'auto' not allowed *)
           "invalid storage class %s for function parameter"
           (name_of_storage_class sto);
      paramsenv
  | d -> (* Should never be produced by the parser *)
      fatal_error (Cabshelper.get_definitionloc d)
                      "illegal declaration of function parameter" in
  let kr_params_defs,paramsenv =
    let params,paramsenv = mmap elab_param_def env defs in
    List.concat params,paramsenv in
  (* Find the type of a parameter *)
  let type_of_param param =
    match List.filter (fun (p, _) -> p = param) kr_params_defs with
    | [] ->
        (* Parameter is not declared, defaults to "int" in ISO C90,
           is an error in ISO C99.  Just emit a warning. *)
        (*- #Link_to E_COMPCERT_TR_Function_ELAB_124 *)
        warning loc Implicit_int "type of '%s' defaults to 'int'" param;
        TInt (IInt, [])
    | (_, ty) :: rem ->
        (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_119 *)
        if rem <> [] then
          error loc "redefinition of parameter '%s'" param;
        ty in
  (* Match parameters against declarations *)
  let rec match_params params' extra_decls = function
    | [] ->
        (List.rev params', List.rev extra_decls)
    | p :: ps ->
        let ty = type_of_param p in
        let ty_var = argument_conversion env ty
        and ty_param = default_argument_conversion env ty in
        if compatible_types AttrIgnoreTop env ty_var ty_param then begin
          (* No need for an extra conversion *)
          let id = Env.fresh_ident p in
          match_params ((id, ty_var) :: params') extra_decls ps
        end else begin
          (* Local variable of type ty_var is to be initialized from
             the parameter of type ty_param *)
          let id_param = Env.fresh_ident p in
          let id_var = Env.fresh_ident p in
          let init = Init_single { edesc = EVar id_param; etyp = ty_param } in
          match_params ((id_param, ty_param) :: params')
                       ((Storage_default, id_var, ty_var, Some init)
                                                           :: extra_decls)
                       ps
        end
  in
  let a,b = match_params [] [] params in
  a,b,paramsenv
(*- #End *)


(* Look for varargs flag in previous definitions of a function *)

(*- E_COMPCERT_CODE_Elab_inherit_vararg_001 *)
(*- #Justify_Derived "Utility function" *)
let inherit_vararg env s sto ty =
  match previous_def Env.lookup_ident env s with
  | Some(id, Env.II_ident(_, old_ty))
    when sto = Storage_extern || Env.in_current_scope env id ->
    begin
      match old_ty, ty with
      | TFun(_, _, true, _), TFun(_, _, _, _) -> true
      | _, _ -> false
    end
  | _ -> false
(*- #End *)


(* Function definitions *)

(*- E_COMPCERT_CODE_Elab_elab_fundef_001 *)
(*- #Link_to E_COMPCERT_TR_Function_ELAB_198 *)
let elab_fundef genv spec name defs body loc =
  (* We maintain two environments:
     - genv is the "global", file-scope environment.  It is enriched
       with the declaration of the function, and also with
       structs and unions defined as part of its return type.
     - lenv is the "local" environment used to elaborate the function body.
       It contains everything that genv contains, including
       a declaration for the function, so as to support recursive calls.
       In addition, it contains declarations for function parameters
       and structs and unions defined in the parameter list. *)
  let (fun_id, sto, inline, noret, ty, kr_params, genv, lenv) =
    elab_fundef_name genv spec name in
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_209 *)
  if Env.is_builtin fun_id.C.name then
    error loc "definition of builtin function '%s'" fun_id.C.name;
  let s = fun_id.C.name in
  (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_125 *)
  if sto = Storage_auto || sto = Storage_register then
    fatal_error loc "invalid storage class %s on function"
                    (name_of_storage_class sto);
  begin match kr_params, defs with
  | None, d::_ ->
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_126 *)
    error (Cabshelper.get_definitionloc d)
      "old-style parameter declarations in prototyped function definition"
  | _ -> ()
  end;
  (* Process the parameters and the K&R declarations, if any, to obtain:
      - [ty]: the full, prototyped type of the function
      - [extra_decls]: extra declarations to be inserted at the
        beginning of the function
      - [lenv]: a first cut at the local environment, containing in particular
        the structs and unions defined in the parameter list. *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_002 *)
  let (ty, extra_decls, lenv) =
    match ty, kr_params with
    | TFun(ty_ret, None, vararg, attr), None ->
        (TFun(ty_ret, Some [], vararg, attr), [], lenv)
    | ty, None ->
        (ty, [], lenv)
    | TFun(ty_ret, None, false, attr), Some params ->
        (*- #Link_to E_COMPCERT_TR_Function_ELAB_127 *)
        warning loc CompCert_conformance "non-prototype, pre-standard function definition, converting to prototype form";
        let (params', extra_decls, lenv) =
          elab_KR_function_parameters lenv params defs loc in
        (TFun(ty_ret, Some params', inherit_vararg genv s sto ty, attr), extra_decls, lenv)
    | _, Some params ->
        assert false
  in
  (* Extract infos from the type of the function.
     Checks on the return type must be done in the global environment. *)
  let (ty_ret, params, vararg, attr) =
    match ty with
    | TFun(ty_ret, Some params, vararg, attr) ->
         (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_129 *)
         if has_std_alignas genv ty then
           error loc "alignment specified for function '%s'" s;
         (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_128 *)
         if wrap incomplete_type loc genv ty_ret && not (is_void_type genv ty_ret) then
           fatal_error loc "incomplete result type %a in function definition"
             (print_typ genv) ty_ret;
        (ty_ret, params, vararg, attr)
    | _ -> fatal_error loc "wrong type for function definition" in
  (* Enter function in the global environment *)
  let (fun_id, sto1, genv, new_ty, _) =
    enter_or_refine_function loc genv fun_id sto ty in
  add_global_define loc s;
  (* Also enter it in the local environment, for recursive references *)
  let lenv = Env.add_ident lenv fun_id sto new_ty in
  (* Take into account attributes from previous declarations of the function *)
  let attr = attributes_of_type genv new_ty in
  (* Additional checks on function parameters. They should have a complete type
     and additionally they should have an identifier. In both cases a fatal
     error is raised in order to avoid problems at later places. *)
  let add_param env (id, ty) =
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_158 *)
    if id.C.name = "" then
      fatal_error loc "parameter name omitted";
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_130 *)
    if wrap incomplete_type loc env ty then
      fatal_error loc "parameter '%s' has incomplete type %a" id.C.name (print_typ env) ty;
    Env.add_ident env id Storage_default ty
  in
  (* Enter parameters and extra declarations in the local environment.
     For K&R functions this hasn't been done yet.
     For prototyped functions this has been done by [elab_fundef_name]
     already, but some parameter may have been shadowed by the
     function name, while it should be the other way around, e.g.
     [int f(int f) { return f+1; }], with [f] referring to the
     parameter [f] and not to the function [f] within the body of the
     function. *)
  let lenv =
    List.fold_left add_param lenv params in
  let lenv =
    List.fold_left (fun e (sto, id, ty, init) -> Env.add_ident e id sto ty)
                   lenv extra_decls in
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_012 *)
  (* Define "__func__" and enter it in the local environment *)
  let (func_ty, func_init) = __func__type_and_init s in
  let (func_id, _, lenv, func_ty, _) =
    enter_or_refine_ident true loc lenv "__func__" Storage_static func_ty in
  emit_elab ~debuginfo:false lenv loc
                  (Gdecl(Storage_static, func_id, func_ty, Some func_init));
  (* Elaborate function body *)
  let body1 = !elab_funbody_f ty_ret vararg (inline && sto <> Storage_static)
                              lenv body in
  (* Analyse it for returns *)
  let (can_return, can_fallthrough) = Cflow.function_returns lenv body1 in
  (* Special treatment of the "main" function. *)
  let body2 =
    if s = "main" then begin
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_131 *)
      if inline then
        error loc "'main' is not allowed to be declared inline";
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_132 *)
      if noret then
        warning loc Unnamed "'main' is not allowed to be declared _Noreturn";
      match unroll genv ty_ret with
      | TInt(IInt, []) ->
          (* Add implicit "return 0;" at end of function body.
             If we trusted the return analysis, we would do this only if
             this control point is reachable, i.e if can_fallthrough is true. *)
          (*- #Link_to E_COMPCERT_TR_Function_ELAB_012 *)
          sseq no_loc body1
               {sdesc = Sreturn(Some(intconst 0L IInt)); sloc = no_loc}
      | _ ->
          (*- #Link_to E_COMPCERT_TR_Function_ELAB_133 *)
          warning loc Main_return_type "return type of 'main' should be 'int'";
          body1
    end else begin
      (* For non-"main" functions, warn if the body can fall through
         and the return type is not "void". *)
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_134 *)
      if can_fallthrough && not (is_void_type genv ty_ret) then
        warning loc Return_type "control reaches end of non-void function";
      body1
    end in
  (* Add the extra declarations if any *)
  let body3 =
    if extra_decls = [] then body2 else begin
      let mkdecl d = { sdesc = Sdecl d; sloc = no_loc } in
      { sdesc = Sblock (List.map mkdecl extra_decls @ [body2]);
        sloc = no_loc }
    end in
  (* Handling of _Noreturn and of attribute("noreturn") *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_135 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_154 *)
  if noret then
    warning loc Celeven_extension "_Noreturn functions are a C11 extension";
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_136 *)
  if (noret || find_custom_attributes ["noreturn"; "__noreturn__"] attr <> [])
  && can_return then
    warning loc Invalid_noreturn "function '%s' declared 'noreturn' should not return" s;
  (* Warnings and errors for the weak attribute.
     Weak functions are not allowed to be static and should not be declared inline *)
  let is_weak = has_weak_attribute attr in
  if sto = Storage_static && is_weak then
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_225 *)
    error loc "weak declaration of '%s' cannot have internal linkage" s;
  if inline && is_weak then
    (*- #Link_to E_COMPCERT_TR_Function_ELAB_226 *)
    warning loc Unnamed "inline function '%s' declared weak" s;
  (* Build and emit function definition *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_001 *)
  let fn =
    { fd_storage = sto1;
      fd_inline = inline;
      fd_name = fun_id;
      fd_attrib = if noret then add_attributes [Attr("noreturn",[])] attr
                           else attr;
      fd_ret = ty_ret;
      fd_params = params;
      fd_vararg = vararg;
      fd_locals = [];
      fd_body = body3 } in
  emit_elab ~linkage:true genv loc (Gfundef fn);
  genv
(*- #End *)

(* Definitions *)

(*- E_COMPCERT_CODE_Elab_elab_decdef_001 *)
let elab_decdef (for_loop: bool) (local: bool) (nonstatic_inline: bool)
                (env: Env.t) ((spec, namelist): Cabs.init_name_group)
                (loc: Cabs.loc) : decl list * Env.t =
  let (sto, inl, noret, tydef, bty, env') =
    elab_specifier ~only:(namelist=[]) loc env spec in
  (* Sanity checks on storage class *)
  if tydef then begin
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_107 *)
    if sto <> Storage_default then
      error loc "non-default storage class on 'typedef' definition";
    (*- #Link_to E_COMPCERT_TR_Function_ELAB_108 *)
    if namelist = [] then
      warning loc Missing_declarations "typedef requires a name";
  end else begin
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_112 *)
    if (sto = Storage_auto || sto = Storage_register) && not local then
      fatal_error loc "illegal storage class %s on file-scoped variable"
        (name_of_storage_class sto);
    (*- #Link_to E_COMPCERT_TR_Function_ELAB_115 *)
    if sto <> Storage_default && namelist = [] then
      warning loc Missing_declarations "declaration does not declare anything";
  end;
  let elab_one_name (decls, env) (Init_name (Name (id, decl, attr, loc), init)) =
    let ((ty, _), env1) =
      elab_type_declarator loc env bty decl in
    let a = elab_attributes env attr in
    let has_fun_typ = is_function_type env ty in
    let is_weak = has_weak_attribute a || has_weak_attribute (attributes_of_type env ty) in
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_138 *)
    if for_loop && (has_fun_typ || sto = Storage_extern || sto = Storage_static || tydef) then
      error loc "declaration of non-local variable in 'for' loop" ;
    if is_weak && sto = Storage_static then
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_225 *)
      error loc "weak declaration of '%s' cannot have internal linkage" id;
    if has_fun_typ then begin
      if noret then
        (*- #Link_to E_COMPCERT_TR_Function_ELAB_154 *)
        warning loc Celeven_extension "_Noreturn functions are a C11 extension";
      if inl && is_weak then
        (*- #Link_to E_COMPCERT_TR_Function_ELAB_226 *)
        warning loc Unnamed "inline function '%s' declared weak" id;
    end else begin
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_033 *)
      if inl then
        error loc "'inline' can only appear on functions";
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_033 *)
      if noret then
        error loc "'_Noreturn' can only appear on functions";
    end;
    let a' = if noret then add_attributes [Attr ("noreturn", [])] a else a in
    (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_129 *)
    if has_std_alignas env ty && has_fun_typ then
      error loc "alignment specified for function '%s'" id;
    let decl = (id, add_attributes_type a' ty, init) in
    if tydef then
      (decls, enter_typedef loc env1 sto decl)
    else
      enter_decdef local nonstatic_inline loc sto (decls, env1) decl
  in
  let (decls, env') = List.fold_left elab_one_name ([],env') namelist in
  (List.rev decls, env')
(*- #End *)

(*- E_COMPCERT_CODE_Elab_elab_definition_001 *)
(*- #Link_to E_COMPCERT_TR_Function_ELAB_199 *)
let elab_definition (for_loop: bool) (local: bool) (nonstatic_inline: bool)
                    (env: Env.t) (def: Cabs.definition)
                    : decl list * Env.t =
  match def with
  (* "int f(int x) { ... }" *)
  (* "int f(x, y) double y; { ... }" *)
  | FUNDEF(spec, name, defs, body, loc) ->
      (* This should actually never be triggered, catched by pre-parser *)
      if local then error loc "function definition is not allowed here";
      let env1 = elab_fundef env spec name defs body loc in
      ([], env1)

  (* "int x = 12, y[10], *z" *)
  | DECDEF(init_name_group, loc) ->
    elab_decdef for_loop local nonstatic_inline env init_name_group loc

  (* pragma *)
  | PRAGMA(s, loc) ->
      if local then
        (*- #Link_to E_COMPCERT_TR_Function_ELAB_219 *)
        warning loc Unnamed "pragmas are ignored inside functions"
      else
        emit_elab env loc (Gpragma s);
      ([], env)

  (* static assertion *)
  | STATIC_ASSERT(exp, loc_exp, msg, loc_msg, loc) ->
      elab_static_assert env exp loc_exp msg loc_msg loc;
      (*- #Link_to E_COMPCERT_TR_Function_ELAB_213 *)
      ([], env)
(*- #End *)

(* Extended asm *)

(*- E_COMPCERT_CODE_Elab_elab_asm_operand_001 *)
(*- #Justify_Derived "Utility function" *)
let elab_asm_operand ctx loc env (ASMOPERAND(label, wide, chars, e)) =
  let s = elab_simple_string loc wide chars in
  let e',env = elab_expr ctx loc env e in
  (label, s, e'),env
(*- #End *)



(* Operations over contexts *)

(*- E_COMPCERT_CODE_Elab_stmt_labels_001 *)
(*- #Justify_Derived "Utility function" *)
let stmt_labels stmt =
  let lbls = ref StringSet.empty in
  let rec do_stmt = function
  | BLOCK(b, _) -> do_block b
  | If(_, s1, Some s2, _) -> do_stmt s1; do_stmt s2
  | If(_, s1, None, _) -> do_stmt s1
  | WHILE(_, s1, _) -> do_stmt s1
  | DOWHILE(_, s1, _) -> do_stmt s1
  | FOR(_, _, _, s1, _) -> do_stmt s1
  | SWITCH(_, s1, _) -> do_stmt s1
  | CASE(_, s1, _) -> do_stmt s1
  | DEFAULT(s1, _) -> do_stmt s1
  | LABEL(lbl, s1, loc) ->
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_139 *)
      if StringSet.mem lbl !lbls then
        error loc "redefinition of label '%s'\n" lbl;
      lbls := StringSet.add lbl !lbls;
      do_stmt s1
  | _ -> ()
  and do_block b = List.iter do_stmt b
  in do_stmt stmt; !lbls
(*- #End *)

let ctx_loop ctx = { ctx with ctx_break = true; ctx_continue = true }

let ctx_switch ctx = { ctx with ctx_break = true; ctx_in_switch = true }

(* Check the uniqueness of 'case' and 'default' in a 'switch' *)

module Int64Set = Set.Make(Int64)

(*- E_COMPCERT_CODE_Elab_check_switch_cases_001 *)
(*- #Justify_Derived "Utility function" *)
let check_switch_cases switch_body =
  let cases = ref Int64Set.empty
  and default = ref false in
  let rec check s =
    match s.sdesc with
    | Sskip -> ()
    | Sdo _ -> ()
    | Sseq(s1, s2) -> check s1; check s2
    | Sif(_, s1, s2) -> check s1; check s2
    | Swhile(_, s1) -> check s1
    | Sdowhile(s1, _) -> check s1
    | Sfor(s1, _, s2, s3) -> check s1; check s2; check s3
    | Sbreak -> ()
    | Scontinue -> ()
    | Sswitch(_, _) -> () (* already checked during elaboration of this switch *)
    | Slabeled(lbl, s1) ->
        begin match lbl with
        | Slabel _ -> ()
        | Scase(_, n) ->
            (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_140 *)
            if Int64Set.mem n !cases then
              Diagnostics.error s.sloc "duplicate case value '%Ld'" n
            else
              cases := Int64Set.add n !cases
        | Sdefault ->
            (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_140 *)
            if !default then
              Diagnostics.error s.sloc "multiple default labels in one switch"
            else
              default := true
        end;
        check s1
    | Sgoto _ -> ()
    | Sreturn _ -> ()
    | Sblock sl -> List.iter check sl
    | Sdecl _ -> ()
    | Sasm _ -> ()
  in check switch_body
(*- #End *)

(* Elaboration of statements *)

let rec elab_stmt env ctx s =

  match s with

(* 6.8.3 Expression statements *)

  (*- E_COMPCERT_CODE_Elab_elab_stmt_001 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_195 *)
  | COMPUTATION(a, loc) ->
      let a,env =  elab_expr ctx loc env a in
      { sdesc = Sdo a; sloc = elab_loc loc },env
  (*- #End *)

(* 6.8.1 Labeled statements *)

  (*- E_COMPCERT_CODE_Elab_elab_stmt_002 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_193 *)
  | LABEL(lbl, s1, loc) ->
      let s1,env = elab_stmt env ctx s1 in
      { sdesc = Slabeled(Slabel lbl, s1); sloc = elab_loc loc },env
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_stmt_003 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_007 *)
  | CASE(a, s1, loc) ->
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_141 *)
      if not ctx.ctx_in_switch then
        error loc "'case' statement not in switch statement";
      let a',env = elab_expr ctx loc env a in
      let n =
        (*- #Link_to E_COMPCERT_TR_Function_CEVAL_001 *)
        match Ceval.integer_expr env a' with
        | None ->
            (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_142 *)
            error loc "expression of 'case' label is not an integer constant expression"; 0L
        | Some n -> n in
      let s1,env = elab_stmt env ctx s1 in
      { sdesc = Slabeled(Scase(a', n), s1); sloc = elab_loc loc },env
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_stmt_004 *)
  | DEFAULT(s1, loc) ->
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_141 *)
      if not ctx.ctx_in_switch then
        error loc "'case' statement not in switch statement";
      let s1,env = elab_stmt env ctx s1 in
      { sdesc = Slabeled(Sdefault, s1); sloc = elab_loc loc },env
  (*- #End *)

(* 6.8.2 Compound statements *)

  (*- E_COMPCERT_CODE_Elab_elab_stmt_005 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_194 *)
  | BLOCK(b, loc) ->
      elab_block loc env ctx b
  (*- #End *)

(* 6.8.4 Conditional statements *)

  (*- E_COMPCERT_CODE_Elab_elab_stmt_006 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_196 *)
  | If(a, s1, s2, loc) ->
      let a',env' = elab_expr ctx loc (Env.new_scope env) a in
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_143 *)
      if not (is_scalar_type env' a'.etyp) then
        error loc "controlling expression of 'if' does not have scalar type (%a invalid)"
          (print_typ env') a'.etyp;
      let s1' = elab_stmt_new_scope env' ctx s1 in
      let s2' =
        match s2 with
          | None -> sskip
          | Some s2 -> elab_stmt_new_scope env' ctx s2
      in
      { sdesc = Sif(a', s1', s2'); sloc = elab_loc loc },env
  (*- #End *)

(* 6.8.5 Iterative statements *)

  (*- E_COMPCERT_CODE_Elab_elab_stmt_007 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_197 *)
  | WHILE(a, s1, loc) ->
      let a',env' = elab_expr ctx loc (Env.new_scope env) a in
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_144 *)
      if not (is_scalar_type env' a'.etyp) then
        error loc "controlling expression of 'while' does not have scalar type (%a invalid)"
          (print_typ env') a'.etyp;
      let s1' = elab_stmt_new_scope env' (ctx_loop ctx) s1 in
      { sdesc = Swhile(a', s1'); sloc = elab_loc loc },env
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_stmt_008 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_197 *)
  | DOWHILE(a, s1, loc) ->
      let s1' = elab_stmt_new_scope env (ctx_loop ctx) s1 in
      let a',env' = elab_expr ctx loc (Env.new_scope env) a in
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_144 *)
      if not (is_scalar_type env' a'.etyp) then
        error loc "controlling expression of 'while' does not have scalar type (%a invalid)"
          (print_typ env') a'.etyp;
      { sdesc = Sdowhile(s1', a'); sloc = elab_loc loc },env
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_stmt_009 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_197 *)
  | FOR(fc, a2, a3, s1, loc) ->
      let env' = Env.new_scope env in
      let (a1', env_decls, decls') =
        match fc with
        | Some (FC_EXP a1) ->
            let a1,env = elab_for_expr ctx loc env' (Some a1) in
            (a1, env, None)
        | None ->
            let a1,env = elab_for_expr ctx loc env' None in
            (a1, env, None)
        | Some (FC_DECL def) ->
            let (dcl, env') = elab_definition true true ctx.ctx_nonstatic_inline
                                              env' def in
            let loc = elab_loc (Cabshelper.get_definitionloc def) in
            (sskip, env',
             Some(List.map (fun d -> {sdesc = Sdecl d; sloc = loc}) dcl)) in
      let a2',env_test =
        match a2 with
          | None -> intconst 1L IInt,env_decls
          | Some a2 -> elab_expr ctx loc env_decls a2
      in
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_144 *)
      if not (is_scalar_type env_test a2'.etyp) then
        error loc "controlling expression of 'for' does not have scalar type (%a invalid)" (print_typ env) a2'.etyp;
      let a3',env_for = elab_for_expr ctx loc env_test a3 in
      let s1' = elab_stmt_new_scope env_for (ctx_loop ctx) s1 in
      let sfor = { sdesc = Sfor(a1', a2', a3', s1'); sloc = elab_loc loc } in
      begin match decls' with
      | None -> sfor,env
      | Some sl -> { sdesc = Sblock (sl @ [sfor]); sloc = elab_loc loc },env
      end
  (*- #End *)

(* 6.8.4 Switch statement *)

  (*- E_COMPCERT_CODE_Elab_elab_stmt_010 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_196 *)
  | SWITCH(a, s1, loc) ->
      let a',env' = elab_expr ctx loc (Env.new_scope env) a in
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_145 *)
      if not (is_integer_type env' a'.etyp) then
        error loc "controlling expression of 'switch' does not have integer type (%a invalid)"
          (print_typ env') a'.etyp;
      let s1' = elab_stmt_new_scope env' (ctx_switch ctx) s1 in
      check_switch_cases s1';
      { sdesc = Sswitch(a', s1'); sloc = elab_loc loc },env
  (*- #End *)

(* 6.8.6 Break and continue statements *)

  (*- E_COMPCERT_CODE_Elab_elab_stmt_011 *)
  | BREAK loc ->
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_146 *)
      if not ctx.ctx_break then
        error loc "'break' statement not in loop or switch statement";
      { sdesc = Sbreak; sloc = elab_loc loc },env
  (*- #End *)

  (*- E_COMPCERT_CODE_Elab_elab_stmt_012 *)
  | CONTINUE loc ->
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_147 *)
      if not ctx.ctx_continue then
        error loc "'continue' statement not in loop statement";
      { sdesc = Scontinue; sloc = elab_loc loc },env
  (*- #End *)

(* 6.8.6 Return statements *)

  (*- E_COMPCERT_CODE_Elab_elab_stmt_013 *)
  | RETURN(a, loc) ->
      let a',env = elab_opt_expr ctx loc env a in
      begin match (unroll env ctx.ctx_return_typ, a') with
      | TVoid _, None -> ()
      | TVoid _, Some _ ->
          (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_148 *)
          error loc
            "'return' with a value in a function returning void"
      | _, None ->
          (*- #Link_to E_COMPCERT_TR_Function_ELAB_149 *)
          warning loc Return_type
            "'return' with no value, in a function returning non-void"
      | _, Some b ->
          if not (wrap2 valid_assignment loc env b ctx.ctx_return_typ)
          then begin
            if wrap2 valid_cast loc env b.etyp ctx.ctx_return_typ then
              (*- #Link_to E_COMPCERT_TR_Function_ELAB_176 *)
              if wrap2 int_pointer_conversion loc env b.etyp ctx.ctx_return_typ then
                (*- #Link_to E_COMPCERT_TR_Function_ELAB_150 *)
                warning loc Int_conversion
                  "incompatible integer-pointer conversion: returning %a from a function with result type %a"
                  (print_typ env) b.etyp (print_typ env) ctx.ctx_return_typ
              else
                (*- #Link_to E_COMPCERT_TR_Function_ELAB_150 *)
                warning loc Unnamed
                  "incompatible conversion: returning %a from a function with result type %a"
                  (print_typ env) b.etyp (print_typ env) ctx.ctx_return_typ
            else
              (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_151 *)
              error loc
                "returning %a from a function with incompatible result type %a"
                (print_typ env) b.etyp (print_typ env) ctx.ctx_return_typ
          end
      end;
      { sdesc = Sreturn a'; sloc = elab_loc loc },env
  (*- #End *)

(* 6.8.6 Goto statements *)

  (*- E_COMPCERT_CODE_Elab_elab_stmt_014 *)
  | GOTO(lbl, loc) ->
      (*- #Link_to E_COMPCERT_TR_Robustness_ELAB_152 *)
      if not (StringSet.mem lbl ctx.ctx_labels) then
        error loc "use of undeclared label '%s'" lbl;
      { sdesc = Sgoto lbl; sloc = elab_loc loc },env
  (*- #End *)

(* 6.8.3 Null statements *)

  (*- E_COMPCERT_CODE_Elab_elab_stmt_015 *)
  (*- #Link_to E_COMPCERT_TR_Function_ELAB_195 *)
  | NOP loc ->
      { sdesc = Sskip; sloc = elab_loc loc },env
  (*- #End *)

(* Traditional extensions *)

  (*- E_COMPCERT_CODE_Elab_elab_stmt_016 *)
  | ASM(cv_specs, wide, chars, outputs, inputs, flags, loc) ->
      let a = elab_cvspecs env cv_specs in
      let s = elab_simple_string loc wide chars in
      let outputs,env = mmap (elab_asm_operand ctx loc) env outputs in
      List.iter
        (fun (lbl, cst, e) ->
           if not (is_modifiable_lvalue env e) then
              (*- #Link_to E_COMPCERT_TR_Robustness_EXTASM_005 *)
             error loc "asm output is not a modifiable l-value";)
        outputs;
      let inputs ,env= mmap (elab_asm_operand ctx loc) env inputs in
      let flags = List.map (fun (w,c) -> elab_simple_string loc w c) flags in
      { sdesc = Sasm(a, s, outputs, inputs, flags);
        sloc = elab_loc loc },env
  (*- #End *)

(* Unsupported *)

  | DEFINITION def ->
      error (Cabshelper.get_definitionloc def) "ill-placed definition";
      sskip,env
(* Elaborate a statement as a block whose scope is a strict subset of the scope
   of its enclosing block. *)
(*- E_COMPCERT_CODE_Elab_elab_stmt_new_scope_001 *)
(*- #Justify_Derived "Utility function" *)
and elab_stmt_new_scope env ctx s =
  fst (elab_stmt (Env.new_scope env) ctx s)
(*- #End *)

(*- E_COMPCERT_CODE_Elab_elab_block_001 *)
(*- #Link_to E_COMPCERT_TR_Function_ELAB_192 *)
and elab_block loc env ctx b =
  let b',_ = elab_block_body (Env.new_scope env) ctx b in
  { sdesc = Sblock b'; sloc = elab_loc loc },env
(*- #End *)

(*- E_COMPCERT_CODE_Elab_elab_block_body_001 *)
(*- #Justify_Derived "Utility function" *)
and elab_block_body env ctx sl =
  match sl with
  | [] ->
      [],env
  | DEFINITION def :: sl1 ->
      let (dcl, env') =
        elab_definition false true ctx.ctx_nonstatic_inline env def in
      let loc = elab_loc (Cabshelper.get_definitionloc def) in
      let dcl = List.map (fun ((sto,id,ty,_) as d) ->
        Debug.insert_local_declaration sto id ty loc;
        {sdesc = Sdecl d; sloc = loc}) dcl in
      let sl1',env' = elab_block_body env' ctx sl1 in
      dcl @ sl1',env'
  | s :: sl1 ->
      let s',env = elab_stmt env ctx s in
      let sl1',env = elab_block_body env ctx sl1 in
      s' :: sl1',env
(*- #End *)


(* Elaboration of a function body.  Return the corresponding C statement. *)

(*- E_COMPCERT_CODE_Elab_elab_funbody_001 *)
(*- #Justify_Derived "Utility function" *)
let elab_funbody return_typ vararg nonstatic_inline env b =
  let ctx =
    { ctx_return_typ = return_typ;
      ctx_labels = stmt_labels b;
      ctx_break = false;
      ctx_continue = false;
      ctx_in_switch = false;
      ctx_vararg = vararg;
      ctx_nonstatic_inline = nonstatic_inline } in
  (* The function body appears as a block in the AST but should not create
     a new scope.  Instead, the scope used for function parameters must be
     used for the body. *)
  match b with
  | BLOCK (b,loc) ->
      let b',_ = elab_block_body env ctx b in
      { sdesc = Sblock b'; sloc = elab_loc loc }
  | _ ->
      assert false
(*- #End *)

(* Filling in forward declaration *)
let _ = elab_funbody_f := elab_funbody

let enter_lib_fun env (s, (res, args, va)) =
  let (args, env) =  mmap (fun env ty ->
      let (id, env) = Env.enter_ident env "" C.Storage_auto ty in
      ((id, ty), env)) env args in
  let ty = TFun (res, Some args, va, []) in
  let (id, env) = Env.enter_ident env s Storage_extern ty in
  let dec = { gdesc = (Gdecl (Storage_extern, id, ty, None)); gloc = no_loc} in
  top_declarations := dec :: !top_declarations;
  top_environment := Env.add_ident !top_environment id Storage_extern ty;
  env

let known_lib_funs = [
  "nanf",
  (TFloat (FFloat, []),  [TPtr(TInt(IChar, [AConst]), [])], false);
  "nansf",
  (TFloat (FFloat, []),  [TPtr(TInt(IChar, [AConst]), [])], false);
  "nan",
  (TFloat (FDouble, []),  [TPtr(TInt(IChar, [AConst]), [])], false);
  "nans",
  (TFloat (FDouble, []),  [TPtr(TInt(IChar, [AConst]), [])], false);
]



(** * Entry point *)

(*- E_COMPCERT_CODE_Elab_elab_file_001 *)
(*- #Justify_Derived "Utility function" *)
let elab_file prog =
  reset();
  let env = Env.initial () in
  let env = List.fold_left enter_lib_fun env known_lib_funs in
  let elab_def env d = snd (elab_definition false false false env d) in
  ignore (List.fold_left elab_def env prog);
  let p = elaborated_program () in
  Checks.unused_variables p;
  Checks.unknown_attrs_program p;
  Checks.non_linear_conditional p;
  p
(*- #End *)
