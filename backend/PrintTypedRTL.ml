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

(** Pretty-printers for typed RTL code *)

open Printf
open Camlcoq
open Datatypes
open Maps
open AST
open RTL
open RTLtyping
open PrintAST

(* Printing of typed RTL code *)

(*- E_COMPCERT_CODE_PrintTypedRTL_reg_001 *)
(*- #Justify_Derived "Utility function" *)
let reg env pp r =
  fprintf pp "x%d:%s" (P.to_int r) (PrintAST.name_of_ptype (env r))
(*- #End *)

(*- E_COMPCERT_CODE_PrintTypedRTL_regs_001 *)
(*- #Justify_Derived "Utility function" *)
let rec regs env pp = function
  | [] -> ()
  | [r] -> reg env pp r
  | r1::rl -> fprintf pp "%a, %a" (reg env) r1 (regs env) rl
(*- #End *)

(*- E_COMPCERT_CODE_PrintTypedRTL_ros_001 *)
(*- #Justify_Derived "Utility function" *)
let ros env pp = function
  | Coq_inl r -> reg env pp r
  | Coq_inr s -> fprintf pp "\"%s\"" (extern_atom s)
(*- #End *)

(*- E_COMPCERT_CODE_PrintTypedRTL_print_instruction_001 *)
(*- #Justify_Derived "Utility function" *)
let print_instruction env pp (pc, i) =
  fprintf pp "%5d:\t" pc;
  let reg = reg env in
  let regs = regs env in
  let ros = ros env in 
  match i with
  | Inop s ->
      let s = P.to_int s in
      if s = pc - 1
      then fprintf pp "nop\n"
      else fprintf pp "goto %d\n" s
  | Iop(op, args, res, s) ->
      fprintf pp "%a = %a\n"
         reg res (PrintOp.print_operation reg) (op, args);
      PrintRTL.print_succ pp s (pc - 1)
  | Iload(chunk, addr, args, dst, s) ->
      fprintf pp "%a = %s[%a]\n"
         reg dst (name_of_chunk chunk)
         (PrintOp.print_addressing reg) (addr, args);
      PrintRTL.print_succ pp s (pc - 1)
  | Istore(chunk, addr, args, src, s) ->
      fprintf pp "%s[%a] = %a\n"
         (name_of_chunk chunk)
         (PrintOp.print_addressing reg) (addr, args)
         reg src;
      PrintRTL.print_succ pp s (pc - 1)
  | Icall(sg, fn, args, res, s) ->
      fprintf pp "%a = %a(%a)\n"
        reg res ros fn regs args;
      PrintRTL.print_succ pp s (pc - 1)
  | Itailcall(sg, fn, args) ->
      fprintf pp "tailcall %a(%a)\n"
        ros fn regs args
  | Ibuiltin(ef, args, res, s) ->
      fprintf pp "%a = %s(%a)\n"
        (print_builtin_res reg) res
        (name_of_external ef)
        (print_builtin_args reg) args;
      PrintRTL.print_succ pp s (pc - 1)
  | Icond(cond, args, s1, s2) ->
      fprintf pp "if (%a) goto %d else goto %d\n"
        (PrintOp.print_condition reg) (cond, args)
        (P.to_int s1) (P.to_int s2)
  | Ijumptable(arg, tbl) ->
      let tbl = Array.of_list tbl in
      fprintf pp "jumptable (%a)\n" reg arg;
      for i = 0 to Array.length tbl - 1 do
        fprintf pp "\t\tcase %d: goto %d\n" i (P.to_int tbl.(i))
      done
  | Ireturn None ->
      fprintf pp "return\n"
  | Ireturn (Some arg) ->
      fprintf pp "return %a\n" reg arg
(*- #End *)

(*- E_COMPCERT_CODE_PrintTypedRTL_print_function_001 *)
(*- #Justify_Derived "Utility function" *)
let print_function pp id (TF (g, env)) =
  fprintf pp "%s(%a) {\n" (extern_atom id) (regs env) g.fn_params;
  let instrs =
    List.sort
      (fun (pc1, _) (pc2, _) -> compare pc2 pc1)
      (List.rev_map
        (fun (pc, i) -> (P.to_int pc, i))
        (PTree.elements g.fn_code)) in
  PrintRTL.print_succ pp g.fn_entrypoint
    (match instrs with (pc1, _) :: _ -> pc1 | [] -> -1);
  List.iter (print_instruction env pp) instrs;
  fprintf pp "}\n\n"
(*- #End *)

(*- E_COMPCERT_CODE_PrintTypedRTL_print_globdef_001 *)
(*- #Justify_Derived "Utility function" *)
let print_globdef pp (id, gd) =
  match gd with
  | Gfun(Internal f) -> print_function pp id f
  | _ -> ()
(*- #End *)

(*- E_COMPCERT_CODE_PrintTypedRTL_print_program_001 *)
(*- #Justify_Derived "Utility function" *)
let print_program pp (prog: RTLtyping.program) =
  List.iter (print_globdef pp) prog.prog_defs
(*- #End *)

(*- E_COMPCERT_CODE_PrintTypedRTL_destination_001 *)
(*- #Justify_Derived "Variable for global state" *)
let destination : string option ref = ref None
(*- #End *)

(*- E_COMPCERT_CODE_PrintTypedRTL_print_if_001 *)
(*- #Link_to E_COMPCERT_TR_Function_DRIVER_001 *)
let print_if passno prog =
  match !destination with
  | None -> ()
  | Some f ->
      let oc = open_out (f ^ "." ^ Z.to_string passno) in
      print_program oc prog;
      close_out oc
(*- #End *)
