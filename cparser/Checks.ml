(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*         Bernhard Schommer, AbsInt Angewandte Informatik GmbH        *)
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

open C
open Diagnostics
open Cutil
open Env

(* AST traversal functions *)

(*- E_COMPCERT_CODE_Checks_fold_over_stmt_loc_001 *)
(*- #Justify_Derived "Utility function" *)
let fold_over_stmt_loc ~(expr: 'a -> location -> exp -> 'a)
    ~(decl: 'a -> location -> decl -> 'a)
    (a: 'a) (s: stmt) : 'a =
  let rec fold a s =
    match s.sdesc with
    | Sskip -> a
    | Sbreak -> a
    | Scontinue -> a
    | Slabeled(_, s1) -> fold a s1
    | Sgoto _ -> a
    | Sreturn None -> a
    | Sreturn (Some e) -> expr a s.sloc e
    | Sasm(_, _, outs, ins, _) -> asm_operands (asm_operands a s.sloc outs) s.sloc ins
    | Sdo e -> expr a s.sloc e
    | Sif (e, s1, s2) -> fold (fold (expr a s.sloc e) s1) s2
    | Sseq (s1, s2) -> fold (fold a s1) s2
    | Sfor (s1, e, s2, s3) -> fold (fold (expr (fold a s1) s.sloc e) s2) s3
    | Swhile(e, s1) -> fold (expr a s.sloc e) s1
    | Sdowhile (s1, e) -> expr (fold a s1) s.sloc e
    | Sswitch (e, s1) -> fold (expr a s.sloc e) s1
    | Sblock sl -> List.fold_left fold a sl
    | Sdecl d -> decl a s.sloc d
  and asm_operands a loc l =
    List.fold_left (fun a (_, _, e) -> expr a loc e) a l
  in fold a s
(*- #End *)

(*- E_COMPCERT_CODE_Checks_iter_over_stmt_loc_001 *)
(*- #Justify_Derived "Utility function" *)
let iter_over_stmt_loc
    ?(expr = fun loc e -> ())
    ?(decl = fun loc decl -> ())
    (s: stmt) : unit =
  fold_over_stmt_loc ~expr: (fun () loc e -> expr loc e)
    ~decl: (fun () loc d -> decl loc d)
    () s
(*- #End *)

(*- E_COMPCERT_CODE_Checks_fold_over_stmt_001 *)
(*- #Justify_Derived "Utility function" *)
let fold_over_stmt ~(expr: 'a -> exp -> 'a)
    ~(decl: 'a -> location -> decl -> 'a)
    (a: 'a) (s: stmt) : 'a =
  fold_over_stmt_loc ~expr:(fun a _ e -> expr a e) ~decl:decl a s
(*- #End *)

(*- E_COMPCERT_CODE_Checks_iter_over_stmt_001 *)
(*- #Justify_Derived "Utility function" *)
let iter_over_stmt ?(expr = fun e -> ())
    ?(decl = fun loc decl -> ())
    (s:stmt) : unit =
  fold_over_stmt_loc ~expr:(fun () _ e -> expr e)
    ~decl:(fun () loc d -> decl loc d) () s
(*- #End *)

(*- E_COMPCERT_CODE_Checks_fold_over_init_001 *)
(*- #Justify_Derived "Utility function" *)
let fold_over_init ~(expr: 'a -> exp -> 'a) (a: 'a) (i: init) : 'a =
  let rec fold a = function
  | Init_single e -> expr a e
  | Init_array il -> List.fold_left fold a il
  | Init_struct (_, sl) -> List.fold_left (fun a (_,i) -> fold a i) a sl
  | Init_union (_, _, ui) -> fold a ui
  in fold a i
(*- #End *)

(*- E_COMPCERT_CODE_Checks_iter_over_init_001 *)
(*- #Justify_Derived "Utility function" *)
let iter_over_init ~(expr: exp -> unit) (i:init) : unit =
  fold_over_init ~expr:(fun () e -> expr e) () i
(*- #End *)

(*- E_COMPCERT_CODE_Checks_fold_over_decl_001 *)
(*- #Justify_Derived "Utility function" *)
let fold_over_decl ~(expr: 'a -> exp -> 'a) (a: 'a) loc (sto, id, ty, init) : 'a=
  match init with
  | Some i -> fold_over_init ~expr a i
  | None -> a
(*- #End *)

(*- E_COMPCERT_CODE_Checks_traverse_program_001 *)
(*- #Justify_Derived "Utility function" *)
let traverse_program
    ?(decl = fun env loc d -> ())
    ?(fundef = fun env loc fd -> ())
    ?(compositedecl = fun env loc su id attr -> ())
    ?(compositedef = fun env loc su id attr fl -> ())
    ?(typedef = fun env loc id ty -> ())
    ?(enum = fun env loc id attr members -> ())
    ?(pragma = fun env loc s -> ())
    p =
  let rec traverse env = function
    | [] -> ()
    | g :: gl ->
      let env =
        match g.gdesc with
        | Gdecl ((sto, id, ty, init) as d) ->
          decl env g.gloc d;
          add_ident env id sto ty
        | Gfundef f ->
          fundef env g.gloc f;
          add_ident env f.fd_name f.fd_storage (fundef_typ f)
        | Gcompositedecl (su,id,attr) ->
          compositedecl env g.gloc su id attr;
          add_composite env id (composite_info_decl su attr)
        | Gcompositedef (su,id,attr,fl) ->
          compositedef env g.gloc su id attr fl;
          add_composite env id (composite_info_def env su attr fl)
        | Gtypedef (id,ty) ->
          typedef env g.gloc id ty;
          add_typedef env id ty
        | Genumdef (id,attr,members) ->
          enum env g.gloc id attr members;
          add_enum env id {ei_members = members; ei_attr = attr}
        | Gpragma s ->
          pragma env g.gloc s;
          env in
      traverse env gl in
  traverse (Env.initial ()) p
(*- #End *)

(* Unknown attributes warning *)

(*- E_COMPCERT_CODE_Checks_unknown_attrs_001 *)
(*- #Link_to E_COMPCERT_TR_Function_CHECKS_002 *)
let unknown_attrs loc attrs =
  let unknown attr =
    let attr_class = class_of_attribute attr in
    if attr_class = Attr_unknown then
      warning loc Unknown_attribute
        "unknown attribute '%s' ignored" (name_of_attribute attr) in
  List.iter unknown attrs
(*- #End *)

(*- E_COMPCERT_CODE_Checks_unknown_attrs_typ_001 *)
(*- #Justify_Derived "Utility function" *)
let unknown_attrs_typ env loc ty =
  let attr = attributes_of_type env ty in
  unknown_attrs loc attr
(*- #End *)

(*- E_COMPCERT_CODE_Checks_unknown_attrs_decl_001 *)
(*- #Justify_Derived "Utility function" *)
let unknown_attrs_decl env loc (sto, id, ty, init) =
  unknown_attrs_typ env loc ty
(*- #End *)

(*- E_COMPCERT_CODE_Checks_unknown_attrs_stmt_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let unknown_attrs_stmt env s =
  iter_over_stmt ~decl:(unknown_attrs_decl env) s
(*- #End *)

(*- E_COMPCERT_CODE_Checks_unknown_attrs_program_001 *)
(*- #Link_to E_COMPCERT_TR_Function_CHECKS_002 *)
let unknown_attrs_program p =
  let decl env loc d =
    unknown_attrs_decl env loc d
  and fundef env loc f =
     List.iter (fun (id,typ) -> unknown_attrs_typ env loc typ) f.fd_params;
     unknown_attrs loc f.fd_attrib;
     unknown_attrs_stmt env f.fd_body;
     List.iter (unknown_attrs_decl env loc) f.fd_locals;
  and compositedecl env loc su id attr =
    unknown_attrs loc attr
  and compositedef env loc su id attr fl =
    unknown_attrs loc attr;
    List.iter (fun fld ->  unknown_attrs_typ env loc fld.fld_typ) fl
  and typedef env loc id ty =
    unknown_attrs_typ env loc ty
  and enum env loc id attr members =
    unknown_attrs loc attr
  in
  traverse_program
    ~decl:decl
    ~fundef:fundef
    ~compositedecl:compositedecl
    ~compositedef:compositedef
    ~typedef:typedef
    ~enum:enum
    p
(*- #End *)

(* Unused variables and parameters warning *)

(*- E_COMPCERT_CODE_Checks_vars_used_expr_001 *)
(*- #Justify_Derived "Utility function" *)
let rec vars_used_expr env e =
  match e.edesc with
  | EConst _
  | ESizeof _
  | EAlignof _ -> env
  | EVar id -> IdentSet.add id env
  | ECast (_,e)
  | EUnop (_,e) -> vars_used_expr env e
  | EBinop (_,e1,e2,_) ->
    let env = vars_used_expr env e1 in
    vars_used_expr env e2
  | EConditional (e1,e2,e3) ->
    let env = vars_used_expr env e1 in
    let env = vars_used_expr env e2 in
    vars_used_expr env e3
  | ECompound (_,init) -> vars_used_init env init
  | ECall (e,p) ->
    let env = vars_used_expr env e in
    List.fold_left vars_used_expr env p
(*- #End *)

(*- E_COMPCERT_CODE_Checks_vars_used_init_001 *)
(*- #Justify_Derived "Utility function" *)
and vars_used_init env init =
  fold_over_init ~expr:vars_used_expr env init
(*- #End *)

(*- E_COMPCERT_CODE_Checks_vars_used_stmt_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let vars_used_stmt env s =
  fold_over_stmt ~expr: vars_used_expr
    ~decl: (fold_over_decl ~expr: vars_used_expr) env s
(*- #End *)

(*- E_COMPCERT_CODE_Checks_unused_variable_001 *)
(*- #Justify_Derived "Utility function" *)
let unused_variable env used loc (id, ty) =
  let attr = attributes_of_type env ty in
  let unused_attr = find_custom_attributes ["unused";"__unused__"] attr <> [] in
  if not ((IdentSet.mem id used) || unused_attr) then
    warning loc Unused_variable "unused variable '%s'" id.name
(*- #End *)

(*- E_COMPCERT_CODE_Checks_unused_variables_stmt_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let unused_variables_stmt env used s =
  iter_over_stmt ~decl:(fun loc (sto, id, ty, init) -> unused_variable env used loc (id,ty)) s
(*- #End *)

(*- E_COMPCERT_CODE_Checks_unused_variables_001 *)
(*- #Link_to E_COMPCERT_TR_Function_CHECKS_001 *)
let unused_variables p =
  let fundef env loc fd =
    let used = vars_used_stmt IdentSet.empty fd.fd_body in
    unused_variables_stmt env used fd.fd_body;
    List.iter (unused_variable env used loc) fd.fd_params in
  traverse_program
    ~fundef:fundef
    p
(*- #End *)

(* Warning for conditionals that cannot be transformed into linear code *)

(* Compute the set of local variables that do not have their address taken *)

(*- E_COMPCERT_CODE_Checks_non_stack_locals_expr_001 *)
(*- #Justify_Derived "Utility function" *)
let rec non_stack_locals_expr vars e =
  match e.edesc with
  | ECast (_,e) -> non_stack_locals_expr vars e
  | EUnop (Oaddrof,e) ->
    begin match e.edesc with
    | EVar id ->
      IdentSet.remove id vars
    | _ -> vars
    end
  | EUnop (Oderef, e) ->
    (* Special optimization *(& ...) is removed in SimplExpr *)
    begin match e.edesc with
      | EUnop (Oaddrof,e) -> non_stack_locals_expr vars e
      | _ -> non_stack_locals_expr vars e
    end
  | EUnop (_, e) ->
    non_stack_locals_expr vars e
  | EBinop (_,e1,e2,_) ->
    let vars = non_stack_locals_expr vars e1 in
    non_stack_locals_expr vars e2
  | EConditional (e1,e2,e3) ->
    let vars = non_stack_locals_expr vars e1 in
    let vars = non_stack_locals_expr vars e2 in
    non_stack_locals_expr vars e3
  | ECompound (_,init) -> non_stack_locals_init vars init
  | ECall (e,p) ->
    let vars = non_stack_locals_expr vars e in
    List.fold_left non_stack_locals_expr vars p
  | _ -> vars
(*- #End *)

(*- E_COMPCERT_CODE_Checks_non_stack_locals_init_001 *)
(*- #Justify_Derived "Utility function" *)
and non_stack_locals_init vars init =
  fold_over_init ~expr:non_stack_locals_expr vars init
(*- #End *)

(*- E_COMPCERT_CODE_Checks_add_vars_001 *)
(*- #Justify_Derived "Utility function" *)
let add_vars env vars (id,ty) =
  let volatile = List.mem AVolatile (attributes_of_type env ty) in
  if not volatile then
    IdentSet.add id vars
  else
    vars
(*- #End *)

(*- E_COMPCERT_CODE_Checks_non_stack_locals_stmt_001 *)
(*- #Justify_Derived "Utility function" *)
let non_stack_locals_stmt env vars s =
  let decl vars loc (sto, id, ty, init) =
    let vars = match init with
      | Some init -> non_stack_locals_init vars init
      | None -> vars in
    add_vars env vars (id,ty) in
  fold_over_stmt ~expr:non_stack_locals_expr ~decl:decl
    vars s
(*- #End *)

(* Check whether an expression is safe and can be always evaluated *)

(*- E_COMPCERT_CODE_Checks_safe_cast_001 *)
(*- #Justify_Derived "Utility function" *)
let safe_cast env tfrom tto =
  match unroll env tfrom, unroll env tto with
  | (TInt _ | TPtr _ | TArray _ | TFun _ | TEnum _),
    (TInt _ | TPtr _ | TEnum _) -> true
  | TFloat _, TFloat _ -> true
  | _, _ -> equal_types env tfrom tto
(*- #End *)

(*- E_COMPCERT_CODE_Checks_safe_expr_001 *)
(*- #Justify_Derived "Utility function" *)
let safe_expr vars env e =
  let rec expr e =
    match e.edesc with
    | EConst _ | ESizeof _ | EAlignof _   | ECompound _  -> true
    | EVar id -> (IdentSet.mem id vars) || not (is_scalar_type env e.etyp)
    | ECast (ty, e) ->
      safe_cast env e.etyp ty && expr e
    | EUnop (op, e) ->
      unop op  e
    | EBinop (op, e1, e2, ty) ->
      binop op e1  e2
    | EConditional _  -> false
    | ECall _ -> false
  and binop op e1 e2 =
    let is_long_long_type ty =
      match unroll env ty with
      | TInt (ILongLong, _)
      | TInt (IULongLong, _) -> true
      | _ -> false in
    match op with
    | Oadd | Osub | Omul | Oand | Oor | Oxor | Oshl | Oshr ->
      expr e1 && expr e2
    | Oeq | One | Olt | Ogt | Ole | Oge ->
      let not_long_long = not (is_long_long_type e1.etyp) && not (is_long_long_type e2.etyp) in
      not_long_long && expr e1 && expr e2
    | _ -> false
  (* x.f if f has array or struct or union type *)
  and unop  op e =
    match op with
    | Ominus | Onot | Olognot | Oplus -> expr e
    | Oaddrof ->
      begin match e.edesc with
        (* skip &*e *)
        | EUnop (Oderef, e) -> expr e
        (* skip &(e.f) *)
        | EUnop (Odot f, e) -> expr e
        | _ -> expr e
      end
    (* skip *&e *)
    | Oderef ->
      begin match e.edesc with
        | EUnop (Oaddrof,e) -> expr e
        | _ -> false
      end
    (* e.f is okay if f has array or composite type *)
    | Odot m ->
      let fld = field_of_dot_access env e.etyp m in
      (is_array_type env fld.fld_typ || is_composite_type env fld.fld_typ) && expr e
    | _ -> false in
  expr e
(*- #End *)


(* Check expressions if they contain conditionals that cannot be transformed in
   linear code. The inner_cond parameter is used to mimic the translation of short
   circuit logical or and logical and as well as conditional to if statements in
   SimplExpr. *)

(*- E_COMPCERT_CODE_Checks_has_move_for_type_001 *)
(*- #Justify_Derived "Utility function" *)
let has_move_for_type env ty =
  (* The type is not an integer larger than the sizeof the registers *)
  let not_too_large_int =
    if is_integer_type env ty then
      match sizeof env ty with
      | None -> assert false (* Can never happen *)
      | Some sz -> Machine.(!config.sizeof_intreg) >= sz
    else
      true in
  match Configuration.arch with
  (* Architectures supporting all types *)
  | "aarch64" -> true
  (* Architectures not supporting any types *)
  | "peaktop" -> false
  | "riscV" -> false
  (* Architectures not support int types > regsize *)
  | "arm"
  | "powerpc"
  | "powerpc_vle"
  | "tricore" -> not_too_large_int
  (* Architectures not supporting float and int types  > regsize *)
  | "x86" -> not (is_float_type env ty) && not_too_large_int
  | _ -> assert false
(*- #End *)


(*- E_COMPCERT_CODE_Checks_non_linear_cond_exprx_001 *)
(*- #Link_to E_COMPCERT_TR_Function_IFCONV_002 *)
let rec non_linear_cond_expr inner_cond vars env loc e =
  match e.edesc with
  | EConst _ | ESizeof _ | EAlignof _ | EVar _ -> ()
  | ECast (_ , e) | EUnop (_, e)-> non_linear_cond_expr false vars env loc e
  | EBinop (op, e1, e2, ty) ->
    let inner_cond = match op with
      | Ocomma -> inner_cond
      | Ologand | Ologor -> true
      | _ -> false
    in
    non_linear_cond_expr false vars env loc e1;
    non_linear_cond_expr inner_cond vars env loc e2
  | EConditional (c, e1, e2) ->
    let can_cast = safe_cast env e1.etyp e.etyp && safe_cast env e2.etyp e.etyp
    and unsafe_e1 = not (safe_expr vars env e1)
    and unsafe_e2 = not (safe_expr vars env e2)
    and has_move = has_move_for_type env e.etyp in
    if not can_cast || inner_cond || unsafe_e1 || unsafe_e2 || not has_move then
      warning loc Non_linear_cond_expr "conditional expression may not be linearized";
    non_linear_cond_expr inner_cond vars env loc e1;
    non_linear_cond_expr inner_cond vars env loc e2;
  | ECompound (ty, init) -> non_linear_cond_init vars env loc init
  | ECall (e, params) ->
    non_linear_cond_expr false vars env loc e;
    List.iter (non_linear_cond_expr false vars env loc) params
(*- #End *)

(*- E_COMPCERT_CODE_Checks_non_linear_cond_init_001 *)
(*- #Justify_Derived "Utility function" *)
and non_linear_cond_init vars env loc init =
  iter_over_init ~expr:(non_linear_cond_expr false vars env loc) init
(*- #End *)

(*- E_COMPCERT_CODE_Checks_non_linear_cond_stmt_001 *)
(*- #Justify_Derived "Utility function" *)
let non_linear_cond_stmt vars env s =
  let decl loc (sto, id, ty, init) =
    match init with
    | None -> ()
    | Some init -> non_linear_cond_init vars env loc init in
  iter_over_stmt_loc ~expr:(non_linear_cond_expr false vars env) ~decl:decl s
(*- #End *)

(*- E_COMPCERT_CODE_Checks_non_linear_conditional_001 *)
(*- #Link_to E_COMPCERT_TR_Function_IFCONV_002 *)
let non_linear_conditional p =
  if active_warning Non_linear_cond_expr && !Clflags.option_Obranchless then begin
    let fundef env loc fd =
      let vars = List.fold_left (add_vars env) IdentSet.empty fd.fd_params in
      let vars = non_stack_locals_stmt env vars fd.fd_body in
      non_linear_cond_stmt vars env fd.fd_body;
    in
    traverse_program
      ~fundef:fundef
      p
  end
(*- #End *)
