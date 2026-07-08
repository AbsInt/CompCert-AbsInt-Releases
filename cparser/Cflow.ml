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

(* A simple control flow analysis for C statements.
   Main purpose: emit warnings for non-void functions that fall through,
   and for _Noreturn functions that can return. *)

open C
open Cutil

module StringSet = Set.Make(String)

(*- E_COMPCERT_CODE_Cflow_std_noreturn_functions_001 *)
(*- #Justify_Derived "Utility constant" *)
(* Functions declared noreturn by the standard *)
(* We also add our own "__builtin_unreachable" function because, currently,
   it is difficult to attach attributes to a built-in function. *)

let std_noreturn_functions =
   ["longjmp";"exit";"_exit";"abort";"_Exit";"quick_exit";"thrd_exit";
    "__builtin_unreachable"]
(*- #End *)

(* Statements are abstracted as "flow transformers":
   functions from possible inputs to possible outcomes.
   Possible inputs are:
   - start normally at the beginning of the statement
   - start at a "case" or "default" label because of an enclosing switch
   - start at a named label because of a "goto"
   Possible outputs are:
   - terminate normally and fall through
   - terminate early on "break"
   - terminate early on "continue"
   - terminate early on "return"
   - terminate early on "goto" to a label
*)

(*- E_COMPCERT_CODE_Cflow_flow_001 *)
(*- #Justify_Derived "Type definition" *)
type flow = inflow -> outflow
(*- #End *)

(*- E_COMPCERT_CODE_Cflow_inflow_001 *)
(*- #Justify_Derived "Type definition" *)
and inflow = {
  inormal: bool;           (* start normally at beginning of statement *)
  iswitch: bool;           (* start at any "case" or "default" label *)
  igoto: StringSet.t;      (* start at one of the goto labels in the set *)
}
(*- #End *)

(*- E_COMPCERT_CODE_Cflow_outflow_001 *)
(*- #Justify_Derived "Type definition" *)
and outflow = {
  onormal: bool;           (* terminates normally by falling through *)
  obreak: bool;            (* terminates early by "break" *)
  ocontinue: bool;         (* terminates early by "continue" *)
  oreturn: bool;           (* terminates early by "return" *)
  ogoto: StringSet.t       (* terminates early by "goto" *)
                           (* to one of the labels in the set *)
}
(*- #End *)

(* The l.u.b. of two out flows *)

(*- E_COMPCERT_CODE_Cflow_join_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let join o1 o2 =
  { onormal = o1.onormal || o2.onormal;
    obreak = o1.obreak || o2.obreak;
    ocontinue = o1.ocontinue || o2.ocontinue;
    oreturn = o1.oreturn || o2.oreturn;
    ogoto = StringSet.union o1.ogoto o2.ogoto }
(*- #End *)

(* Some elementary flows *)

(*- E_COMPCERT_CODE_Cflow_normal_001 *)
(*- #Justify_Derived "Utility function" *)
let normal : flow = fun i ->
  { onormal = i.inormal;
    obreak = false; ocontinue = false; oreturn = false;
    ogoto = StringSet.empty }
(*- #End *)

(*- E_COMPCERT_CODE_Cflow_break_001 *)
(*- #Justify_Derived "Utility function" *)
let break : flow = fun i ->
  { obreak = i.inormal;
    onormal = false; ocontinue = false; oreturn = false;
    ogoto = StringSet.empty }
(*- #End *)

(*- E_COMPCERT_CODE_Cflow_continue_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let continue : flow = fun i ->
  { ocontinue = i.inormal;
    onormal = false; obreak = false; oreturn = false;
    ogoto = StringSet.empty }
(*- #End *)

(*- E_COMPCERT_CODE_Cflow_return_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let return : flow = fun i ->
  { oreturn = i.inormal;
    onormal = false; obreak = false; ocontinue = false;
    ogoto = StringSet.empty }
(*- #End *)

(*- E_COMPCERT_CODE_Cflow_goto_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let goto lbl : flow = fun i ->
  { onormal = false; obreak = false; ocontinue = false; oreturn = false;
    ogoto = if i.inormal then StringSet.singleton lbl else StringSet.empty }
(*- #End *)

(*- E_COMPCERT_CODE_Cflow_noflow_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let noflow : flow = fun i ->
  { onormal = false; obreak = false; ocontinue = false; oreturn = false;
    ogoto = StringSet.empty }
(*- #End *)

(* Some flow transformers *)

(* Sequential composition *)

(*- E_COMPCERT_CODE_Cflow_seq_001 *)
(*- #Justify_Derived "Utility function" *)
let seq (s1: flow) (s2: flow) : flow = fun i ->
  let o1 = s1 i in
  let o2 = s2 {i with inormal = o1.onormal} in
  { onormal = o2.onormal;
    obreak = o1.obreak || o2.obreak;
    ocontinue = o1.ocontinue || o2.ocontinue;
    oreturn = o1.oreturn || o2.oreturn;
    ogoto = StringSet.union o1.ogoto o2.ogoto }
(*- #End *)

(* Nondeterministic choice *)

(*- E_COMPCERT_CODE_Cflow_either_001 *)
(*- #Justify_Derived "Utility function" *)
let either (s1: flow) (s2: flow) : flow = fun i ->
  join (s1 i) (s2 i)
(*- #End *)

(* If-then-else, with special cases for conditions that are always true
   or always false. *)

(*- E_COMPCERT_CODE_Cflow_resolve_test_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let resolve_test env e =
  match Ceval.integer_expr env e with
  | None -> None
  | Some n -> Some (n <> 0L)
  | exception Env.Error _ -> None (* Any error due to local types should be ignored *)
(*- #End *)

(*- E_COMPCERT_CODE_Cflow_if_001 *)
(*- #Justify_Derived "Utility function" *)
let if_ env e (s1: flow) (s2: flow) : flow =
  match resolve_test env e with
  | Some true -> s1
  | Some false -> s2
  | None -> either s1 s2
(*- #End *)

(* Convert "continue" into "fallthrough".  Typically applied to a loop body. *)

(*- E_COMPCERT_CODE_Cflow_catch_continue_001 *)
(*- #Justify_Derived "Utility function" *)
let catch_continue (s: flow) : flow = fun i ->
  let o = s i in
  { o with onormal = o.onormal || o.ocontinue; ocontinue = false}
(*- #End *)

(* Convert "break" into "fallthrough".  Typically applied to a loop. *)

(*- E_COMPCERT_CODE_Cflow_catch_break_001 *)
(*- #Justify_Derived "Utility function" *)
let catch_break (s: flow) : flow = fun i ->
  let o = s i in
  { o with onormal = o.onormal || o.obreak; obreak = false}
(*- #End *)

(* Statements labeled with a goto label *)

(*- E_COMPCERT_CODE_Cflow_label_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let label lbl (s: flow) : flow = fun i ->
  s { i with inormal = i.inormal || StringSet.mem lbl i.igoto }
(*- #End *)

(* For "case" and "default" labeled statements, we assume they can be
   entered normally as soon as the nearest enclosing "switch" can be
   entered normally. *)

(*- E_COMPCERT_CODE_Cflow_case_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let case (s: flow) : flow = fun i ->
  s { i with inormal = i.inormal || i.iswitch }
(*- #End *)

(*- E_COMPCERT_CODE_Cflow_switch_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let switch (s: flow) : flow = fun i ->
  s { i with inormal = false; iswitch = i.inormal }
(*- #End *)

(* This is the flow for an infinite loop with body [s].  
   There is no fallthrough exit, but all other exits from [s] are preserved. *)

(*- E_COMPCERT_CODE_Cflow_loop_001 *)
(*- #Justify_Derived "Utility function" *)
let loop (s: flow) : flow = fun i ->
  let o = s i in
  if o.onormal && not i.inormal then
    (* Corner case: on the first iteration, [s] was not entered normally,
       but it exits by fallthrough.  Then on the next iteration [s] is
       entered normally.  So, we need to recompute the flow of [s]
       assuming it is entered normally. *)
     s { i with inormal = true}
   else
     (* In all other cases, iterating [s] once more does not produce new
        exits that we did not compute on the first iteration.  Just remove
        the fallthrough exit. *)
     { o with onormal = false }
(*- #End *)

(* Detect the presence of a 'default' case reachable from an enclosing
   'switch' *)

(*- E_COMPCERT_CODE_Cflow_contains_default_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let rec contains_default s =
  match s.sdesc with
  | Sskip -> false
  | Sdo _ -> false
  | Sseq(s1, s2) -> contains_default s1 || contains_default s2
  | Sif(e, s1, s2) -> contains_default s1 || contains_default s2
  | Swhile(e, s) -> contains_default s
  | Sdowhile(s, e) -> contains_default s
  | Sfor(s1, e, s2, s3) ->
      contains_default s1 || contains_default s2 || contains_default s3
  | Sbreak -> false
  | Scontinue -> false
  | Sswitch(e, s) -> false
     (* the default that could appear inside the switch
        cannot be reached by the enclosing switch *)
  | Slabeled(Sdefault, s) -> true
  | Slabeled(_, s) -> contains_default s
  | Sgoto lbl -> false
  | Sreturn opte -> false
  | Sblock sl -> List.exists contains_default sl
  | Sdecl dcl -> false
  | Sasm _ -> false
(*- #End *)

(* Extract the attributes of a function type, looking for "noreturn". *)

(*- E_COMPCERT_CODE_Cflow_function_attributes_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let rec function_attributes env = function
  | TFun(_, _, _, a) -> a
  | TPtr(t, _) -> function_attributes env t
  | TNamed _ as t ->
      begin match unroll env t with
      | t' -> function_attributes env t'
      | exception Env.Error _ -> []
            (* Any error due to local types should be ignored *)
      end
  | _ -> []
(*- #End *)

(* Functions to check whether an expression does return, i.e does not contain a
   a call to a function without return *)

(*- E_COMPCERT_CODE_Cflow_expr_returns_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let rec expr_returns env e =
  match e.edesc with
  | EConst _ | ESizeof _ | EAlignof _ | EVar _ -> true
  | EUnop (_, e) -> expr_returns env e
  | EBinop (op, e1, e2, _) ->
    begin match op with
    | Ologand ->
      if expr_returns env e1 then begin
        match resolve_test env e1 with
            | Some true -> expr_returns env e2
            | Some false -> true
            (* We don't know wether the first expression evaluates to false. *)
            | None -> true
      end else
        false
    | Ologor ->
      if expr_returns env e1 then begin
        match resolve_test env e1 with
            | Some true -> true
            | Some false ->  expr_returns env e2
            (* We don't know wether the first expression evaluates to true. *)
            | None -> true
      end else
        false
    | _ -> expr_returns env e1 && expr_returns env e2
    end
  | EConditional (c, e1, e2) ->
    (* If one of the expression returns, the conditional might return as well *)
    expr_returns env c && (expr_returns env e1 || expr_returns env e2)
  | ECast (_, e) -> expr_returns env e
  | ECompound (ty, it) ->
    init env it
  | ECall (fn, args) ->
    let fn_noret = has_noret_attribute (function_attributes env fn.etyp)
    and std_noret_fun = List.exists (is_call_to_fun fn) std_noreturn_functions
    and fn_expr_ret = expr_returns env fn
    and args_ret = List.for_all (expr_returns env) args in
    not fn_noret && not std_noret_fun && fn_expr_ret && args_ret

and init env it =
  match it with
  | Init_single e -> expr_returns env e
  | Init_array il -> List.for_all (init env) il
  | Init_struct (_, sl) -> List.for_all (fun (_, i) -> init env i) sl
  | Init_union (_, _, ui) -> init env ui
(*- #End *)

(* This is the main analysis function.  Given a C statement [s] it returns
   a flow that overapproximates the behavior of [s]. *)

(*- E_COMPCERT_CODE_Cflow_outcomes_001 *)
(*- #Justify_Derived "Utility function" *)
let rec outcomes env s : flow =
  match s.sdesc with
  | Sskip ->
      normal
  | Sdo e ->
      if expr_returns env e then normal else noflow
  | Sseq(s1, s2) ->
      seq (outcomes env s1) (outcomes env s2)
  | Sif(e, s1, s2) ->
      if_ env e (outcomes env s1) (outcomes env s2)
  | Swhile(e, s) ->
      catch_break (
        loop (
          if_ env e
             (catch_continue (outcomes env s)) (* e is true: execute body [s] *)
             break))                           (* e is false: exit loop *)
  | Sdowhile(s, e) ->
      catch_break (
        loop (
          seq (catch_continue (outcomes env s)) (* do the body *)
              (if_ env e normal break)))        (* then continue or break *)
  | Sfor(s1, e, s2, s3) ->
      seq (outcomes env s1)              (* initialization, runs once *)
          (catch_break (
            loop (
              if_ env e                  (* e is true: do body, do next *)
                (seq (catch_continue (outcomes env s2)) (outcomes env s3))
                break)))                 (* e is false: exit loop *)
  | Sbreak ->
      break
  | Scontinue ->
      continue
  | Sswitch(e, s) ->
      let fl = catch_break (switch (outcomes env s)) in
      if contains_default s then fl else either normal fl
      (* if there is no 'default' case, the switch can fall through *)
  | Slabeled(Slabel lbl, s) ->
      label lbl (outcomes env s)
  | Slabeled((Scase _ | Sdefault), s) ->
      case (outcomes env s)
  | Sgoto lbl ->
      goto lbl
  | Sreturn opte ->
      return
  | Sblock sl ->
      outcomes_block env sl
  | Sdecl dcl ->
      normal
  | Sasm _ ->
      normal
(*- #End *)

(*- E_COMPCERT_CODE_Cflow_outcomes_block_001 *)
(*- #Justify_Derived "Functional decomposition" *)
and outcomes_block env sl =
  match sl with
  | [] ->
      normal
  | s1 :: sl ->
      seq (outcomes env s1) (outcomes_block env sl)
(*- #End *)

(* This is the entry point in this module.  Given the body of a function,
   estimate if and how this function can return. *)

(*- E_COMPCERT_CODE_Cflow_function_returns_001 *)
(*- #Link_to E_COMPCERT_TR_Function_ELAB_134 *)
(*- #Link_to E_COMPCERT_TR_Function_ELAB_136 *)
let function_returns env body =
  (* Iterate [outcomes] until all gotos are accounted for *)
  let rec fixpoint i =
    let o = outcomes env body i in
    if StringSet.subset o.ogoto i.igoto
    then o
    else fixpoint { i with igoto = StringSet.union i.igoto o.ogoto } in
  let o =
    fixpoint { inormal = true; iswitch = false; igoto = StringSet.empty } in
  (* First boolean is: function can return
     Second boolean is: function can return by fall-through *)
  (o.onormal || o.oreturn, o.onormal)
(*- #End *)

