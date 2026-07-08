(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Utility functions used for the expansion of built-ins and some
   pseudo-instructions *)

open Maps
open Asm
open AST
open Camlcoq

exception AsmexpandError of string

(* Buffering the expanded code *)

(*- E_COMPCERT_CODE_Asmexpandaux_current_code_001 *)
(*- #Justify_Derived "Variable for global state" *)
let current_code = ref ([]: instruction list)
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpandaux_emit_001 *)
(*- #Justify_Derived "Utility function" *)
let emit i = current_code := i :: !current_code
(*- #End *)

(* Generation of fresh labels *)

(*- E_COMPCERT_CODE_Asmexpandaux_dummy_function_001 *)
(*- #Justify_Derived "Utility constant" *)
let dummy_function = { fn_code = []; fn_sig = signature_main }
(*- #End *)
(*- E_COMPCERT_CODE_Asmexpandaux_current_function_001 *)
(*- #Justify_Derived "Utility function" *)
let current_function = ref dummy_function
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpandaux_next_label_001 *)
(*- #Justify_Derived "Variable for local state" *)
let next_label = ref (None: label option)
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpandaux_new_label_001 *)
(*- #Justify_Derived "Utility function" *)
let new_label () =
  let lbl =
    match !next_label with
    | Some l -> l
    | None ->
        (* on-demand computation of the next available label *)
        List.fold_left
          (fun next instr ->
            match instr with
            | Plabel l -> if P.lt l next then next else P.succ l
            | _ -> next)
          P.one (!current_function).fn_code
  in
    next_label := Some (P.succ lbl);
    lbl
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpandaux_set_current_function_001 *)
(*- #Justify_Derived "Utility function" *)
let set_current_function f =
  current_function := f; next_label := None; current_code := []
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpandaux_get_current_function_args_001 *)
(*- #Justify_Derived "Utility function" *)
let get_current_function_args () =
  proj_sig_args (!current_function).fn_sig
(*- #End *)


(*- E_COMPCERT_CODE_Asmexpandaux_is_current_function_variadic_001 *)
(*- #Justify_Derived "Utility function" *)
let is_current_function_variadic () =
  (!current_function).fn_sig.sig_cc.cc_vararg <> None
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpandaux_get_current_function_sig_001 *)
(*- #Justify_Derived "Utility function" *)
let get_current_function_sig () =
  (!current_function).fn_sig
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpandaux_get_current_function_001 *)
(*- #Justify_Derived "Utility function" *)
let get_current_function () =
  let c = List.rev !current_code in
  let fn = !current_function in
  set_current_function dummy_function;
  {fn with fn_code = c}
(*- #End *)

(* Expand function for debug information *)

(*- E_COMPCERT_CODE_Asmexpandaux_expand_scope_001 *)
(*- #Justify_Derived "Utility function" *)
let expand_scope id lbl oldscopes newscopes =
  let opening = List.filter (fun a -> not (List.mem a oldscopes)) newscopes
  and closing = List.filter (fun a -> not (List.mem a newscopes)) oldscopes in
  List.iter (fun i -> Debug.open_scope id i lbl) opening;
  List.iter (fun i -> Debug.close_scope id i lbl) closing
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpandaux_translate_annot_001 *)
(*- #Justify_Derived "Utility function" *)
let translate_annot sp preg_to_dwarf annot =
  let rec aux = function
    | BA x ->
      Some (sp,BA (preg_to_dwarf x))
    | BA_int _
    | BA_long _
    | BA_float _
    | BA_single _
    | BA_loadglobal _
    | BA_addrglobal _
    | BA_loadstack _
    | BA_addptr _ -> None
    | BA_addrstack ofs -> Some (sp,BA_addrstack ofs)
    | BA_splitlong (hi,lo) ->
        begin
          match (aux hi,aux lo) with
          | Some (_,hi) ,Some (_,lo) -> Some (sp,BA_splitlong (hi,lo))
          | _,_ -> None
        end in
  (match annot with
  | [] -> None
  | a::_ -> aux a)
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpandaux_builtin_nop_001 *)
(*- #Justify_Derived "Utility function" *)
let builtin_nop =
  let signature ={sig_args = []; sig_res = Xvoid; sig_cc = cc_default} in
  Pbuiltin(EF_builtin("__builtin_nop", signature), [], BR_none)
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpandaux_lbl_follows_001 *)
(*- #Justify_Derived "Utility function" *)
let rec lbl_follows = function
  | Pbuiltin (EF_debug _, _, _):: rest ->
    lbl_follows rest
  | Plabel _ :: _ -> true
  | _ -> false
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpandaux_expand_debug_001 *)
(*- #Link_to E_COMPCERT_TR_Function_DEBUG_002 *)
(*- #Link_to E_COMPCERT_TR_Function_DEBUG_003 *)
let expand_debug id sp preg simple l =
  let get_lbl = function
    | None ->
        let lbl = new_label () in
        emit (Plabel lbl);
        lbl
    | Some lbl -> lbl in
  let rec  aux lbl scopes = function
    | [] -> ()
    | (Pbuiltin(EF_debug (kind,txt,_x),args,_) as i)::rest ->
        let kind = (P.to_int kind) in
        begin
          match kind with
          | 1->
              emit i;aux lbl scopes rest
          | 2 ->
              aux  lbl scopes rest
          | 3 ->
             begin
               match translate_annot sp preg args with
               | Some a ->
                   let lbl = get_lbl lbl in
                   Debug.start_live_range (id,txt) lbl a;
                   aux (Some lbl) scopes rest
               | None ->  aux lbl scopes rest
             end
          | 4 ->
              let lbl = get_lbl lbl in
              Debug.end_live_range (id,txt) lbl;
              aux (Some lbl) scopes rest
          | 5 ->
              begin
                match translate_annot sp preg args with
                | Some a->
                    Debug.stack_variable (id,txt) a;
                    aux lbl scopes rest
                | _ ->  aux lbl scopes rest
              end
          | 6  ->
              let lbl = get_lbl lbl in
              let scopes' = List.map (function BA_int x ->
                  let id = camlint_of_coqint x in
                  let id' = Int32.to_int id in
                  assert (Int32.of_int id' = id);
                  id' | _ -> assert false) args in
              expand_scope id lbl scopes scopes';
              aux (Some lbl) scopes' rest
          | _ ->
              aux None scopes rest
        end
    | (Pbuiltin(EF_annot (kind, _, _),_,_) as annot)::rest ->
      simple annot;
      if P.to_int kind = 2 && lbl_follows rest then
        simple builtin_nop;
      aux None scopes rest
    | (Plabel lbl)::rest -> simple (Plabel lbl); aux (Some lbl) scopes rest
    | i::rest -> simple i; aux None scopes rest in

  (* We need to move all closing debug annotations before the last real statement *)
  let rec move_debug acc bcc = function
    | (Pbuiltin(EF_debug (kind,_,_),_,_) as i)::rest ->
        let kind = (P.to_int kind) in
        if kind = 1 then
          move_debug acc (i::bcc) rest (* Do not move debug line *)
        else
          move_debug (i::acc) bcc rest (* Move the debug annotations forward *)
    | b::rest -> List.rev ((List.rev (b::bcc)@List.rev acc)@rest) (* We found the first non debug location *)
    | [] -> List.rev acc (* This actually can never happen *) in
  aux None [] (move_debug [] [] (List.rev l))
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpandaux_expand_simple_001 *)
(*- #Link_to E_COMPCERT_TR_Function_DEBUG_001 *)
let expand_simple simple l =
  let rec aux = function
   | (Pbuiltin(EF_annot (kind, _, _),_,_) as annot)::rest ->
     simple annot;
     if P.to_int kind = 2 && lbl_follows rest then
       simple builtin_nop;
     aux rest
   | i::rest -> simple i; aux rest
   | [] -> () in
  aux l
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpandaux_expand_001 *)
(*- #Link_to E_COMPCERT_TR_Function_DEBUG_001 *)
let expand id sp preg simple l =
  if !Clflags.option_g then
    expand_debug id sp preg simple l
  else
    expand_simple simple l
(*- #End *)


(*- E_COMPCERT_CODE_Asmexpandaux_check_stack_size_001 *)
let check_stack_size =
  let max_signed = Z.to_string Ptrofs.max_signed in
  fun sz ->
    if not (Z.le _0 sz && Z.lt sz Ptrofs.max_signed) then
      (*- #Link_to E_COMPCERT_TR_Robustness_EXPAND_001 *)
      let msg = Printf.sprintf "total size of local objects (%s bytes) exceeds allowed maximum (%s bytes)"
          (Z.to_string sz) max_signed in
      raise (AsmexpandError msg)
(*- #End *)

(* Branch relaxation *)

(*- E_COMPCERT_CODE_Asmexpandaux_module_branch_information_001 *)
(*- #Justify_Derived "Type definitions" *)
module type BRANCH_INFORMATION = sig
  val instr_size: instruction -> int
  val need_relaxation: map: (label -> int) -> int -> instruction -> bool
  val relax_instruction: instruction -> instruction list
end
(*- #End *)

module Branch_relaxation (B: BRANCH_INFORMATION) = struct

(* Fill the table label -> position in code *)

(*- E_COMPCERT_CODE_Asmexpandaux_set_label_positions_001 *)
(*- #Justify_Derived "Utility function" *)
let rec set_label_positions tbl pc = function
  | [] ->
      tbl
  | Plabel lbl :: code ->
      set_label_positions (PTree.set lbl pc tbl) pc code
  | instr :: code ->
      set_label_positions tbl (pc + B.instr_size instr) code
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpandaux_get_label_positions_001 *)
(*- #Justify_Derived "Utility function" *)
let get_label_position tbl lbl =
  match PTree.get lbl tbl with
  | Some pc -> pc
  | None -> 
      invalid_arg
        (Printf.sprintf "Fatal error: unknown label %d" (P.to_int lbl))
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpandaux_need_relaxation_001 *)
(*- #Justify_Derived "Utility function" *)
let rec need_relaxation tbl pc = function
  | [] ->
      false
  | instr :: code ->
      B.need_relaxation ~map:(get_label_position tbl) pc instr
      || need_relaxation tbl (pc + B.instr_size instr) code
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpandaux_do_relaxation_001 *)
(*- #Justify_Derived "Utility function" *)
let rec do_relaxation tbl accu pc = function
  | [] ->
      List.rev accu
  | instr :: code ->
      do_relaxation
        tbl
        (if B.need_relaxation ~map:(get_label_position tbl) pc instr
         then List.rev_append (B.relax_instruction instr) accu
         else instr :: accu)
        (pc + B.instr_size instr)
        code
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpandaux_relaxaction_001 *)
(*- #Justify_Derived "Utility function" *)
let relaxation fn =
  set_current_function fn;
  let rec relax fn =
    let tbl = set_label_positions PTree.empty 0 fn.fn_code in
    if not (need_relaxation tbl 0 fn.fn_code) then fn else begin
      let code' = do_relaxation tbl [] 0 fn.fn_code in
      relax {fn with fn_code = code'}
    end in
  let res = relax fn in
  set_current_function dummy_function;
  res
(*- #End *)

end
