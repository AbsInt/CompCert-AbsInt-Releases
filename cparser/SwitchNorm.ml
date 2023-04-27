(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, Collège de France and Inria                  *)
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

(* Normalization of structured "switch" statements
   and emulation of unstructured "switch" statements (e.g. Duff's device) *)

(* Assumes: code without blocks
   Produces: code without blocks and with normalized "switch" statements *)

(* A normalized switch has the following form:
     Sswitch(e, Sseq (Slabeled(lbl1, case1),
                  Sseq (...
                    Sseq (Slabeled(lblN,caseN), Sskip) ...)))
*)

open Printf
open C
open Cutil

(*- E_COMPCERT_CODE_SwitchNorm_support_unstructured_001 *)
(*- #Justify_Derived "Variable for global state" *)
let support_unstructured = ref false
(*- #End *)

(*- E_COMPCERT_CODE_SwitchNorm_switchlabel_001 *)
(*- #Justify_Derived "Type definitions" *)
type switchlabel =
  | Case of exp * int64
  | Default
(*- #End *)

(*- E_COMPCERT_CODE_SwitchNorm_switchbody_001 *)
(*- #Justify_Derived "Type definitions" *)
type switchbody =
  | Label of switchlabel * location
  | Stmt of stmt
(*- #End *)

(*- E_COMPCERT_CODE_SwitchNorm_flatten_switch_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let rec flatten_switch = function
  | {sdesc = Sseq(s1, s2)} :: rem ->
      flatten_switch (s1 :: s2 :: rem)
  | {sdesc = Slabeled(Scase(e, n), s1); sloc = loc} :: rem ->
      Label(Case(e, n), loc) :: flatten_switch (s1 :: rem)
  | {sdesc = Slabeled(Sdefault, s1); sloc = loc} :: rem ->
      Label(Default, loc) :: flatten_switch (s1 :: rem)
  | {sdesc = Slabeled(Slabel lbl, s1); sloc = loc} :: rem ->
      Stmt {sdesc = Slabeled(Slabel lbl, Cutil.sskip); sloc = loc}
      :: flatten_switch (s1 :: rem)
  | s :: rem ->
      Stmt s :: flatten_switch rem
  | [] ->
      []
(*- #End *)

(*- E_COMPCERT_CODE_SwitchNorm_group_switch_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let rec group_switch = function
  | [] ->
      (Cutil.sskip, [])
  | Label(case, loc) :: rem ->
      let (fst, cases) = group_switch rem in
      (Cutil.sskip, (case, loc, fst) :: cases)
  | Stmt s :: rem ->
      let (fst, cases) = group_switch rem in
      (Cutil.sseq s.sloc s fst, cases)
(*- #End *)

(*- E_COMPCERT_CODE_SwitchNorm_label_of_switchlabel_001 *)
(*- #Justify_Derived "Utility function" *)
let label_of_switchlabel = function
  | Case(e, n) -> Scase(e, n)
  | Default -> Sdefault
(*- #End *)

(*- E_COMPCERT_CODE_SwitchNorm_make_slabeled_001 *)
(*- #Justify_Derived "Utility function" *)
let make_slabeled (l, loc, s) =
  { sdesc = Slabeled(label_of_switchlabel l, s); sloc = loc }
(*- #End *)

(*- E_COMPCERT_CODE_SwitchNorm_make_sequence_001 *)
(*- #Justify_Derived "Utility function" *)
let make_sequence sl =
  List.fold_right (Cutil.sseq no_loc) sl Cutil.sskip
(*- #End *)

(*- E_COMPCERT_CODE_SwitchNorm_make_normalized_switch_001 *)
(*- #Justify_Derived "Utility function" *)
let make_normalized_switch e cases =
  Sswitch(e, make_sequence (List.map make_slabeled cases))
(*- #End *)

(*- E_COMPCERT_CODE_SwitchNorm_all_cases_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let rec all_cases accu s =
  match s.sdesc with
  | Sseq(s1, s2) -> all_cases (all_cases accu s1) s2
  | Sif(_, s1, s2) -> all_cases (all_cases accu s1) s2
  | Swhile(_, s1) -> all_cases accu s1
  | Sdowhile(s1, _) -> all_cases accu s1
  | Sfor(s1, _, s2, s3) -> all_cases (all_cases (all_cases accu s1) s2) s3
  | Sswitch(_, _) -> accu
  | Slabeled(Scase(e, n), s1) -> all_cases (Case(e, n) :: accu) s1
  | Slabeled(Sdefault, s1) -> all_cases (Default :: accu) s1
  | Slabeled(Slabel _, s1) -> all_cases accu s1
  | Sblock _ -> assert false
  | _ -> accu
(*- #End *)

(*- E_COMPCERT_CODE_SwitchNorm_substitute_cases_001 *)
(*- #Justify_Derived "Utility function" *)
let substitute_cases case_table body end_label =
  let sub = Hashtbl.create 32 in
  List.iter
    (fun (case, lbl) -> Hashtbl.add sub case (Slabel lbl))
    case_table;
  let transf_label = function
    | Scase(e, n) ->
        (try Hashtbl.find sub (Case(e, n)) with Not_found -> assert false)
    | Sdefault ->
        (try Hashtbl.find sub Default with Not_found -> assert false)
    | Slabel _ as lbl -> lbl in
  let rec transf inloop s =
    {s with sdesc =
      match s.sdesc with
      | Sseq(s1, s2) -> Sseq(transf inloop s1, transf inloop s2)
      | Sif(e, s1, s2) -> Sif(e, transf inloop s1, transf inloop s2)
      | Swhile(e, s1) -> Swhile(e, transf true s1)
      | Sdowhile(s1, e) -> Sdowhile(transf true s1, e)
      | Sfor(s1, e, s2, s3) ->
          Sfor(transf inloop s1, e, transf inloop s2, transf true s3)
      | Sbreak -> if inloop then Sbreak else Sgoto end_label
      | Slabeled(lbl, s1) -> Slabeled(transf_label lbl, transf inloop s1)
      | Sblock  _ -> assert false
      | sd -> sd }
  in transf false body
(*- #End *)

(*- E_COMPCERT_CODE_SwitchNorm_is_skip_or_debug_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let rec is_skip_or_debug s =
  match s.sdesc with
  | Sseq (a, b) -> is_skip_or_debug a && is_skip_or_debug b
  | Sskip -> true
  | _ -> Cutil.is_debug_stmt s
(*- #End *)

(*- E_COMPCERT_CODE_SwitchNorm_new_label_001 *)
(*- #Justify_Derived "Variable for global state" *)
let new_label = ref 0
(*- #End *)

(*- E_COMPCERT_CODE_SwitchNorm_gen_label_001 *)
(*- #Justify_Derived "Utility function" *)
let gen_label () = incr new_label; sprintf "@%d" !new_label
(*- #End *)

(*- E_COMPCERT_CODE_SwitchNorm_normalize_switch_001 *)
(*- #Link_to E_COMPCERT_TR_Function_SwitchNorm_001 *)
let normalize_switch loc e body =
  let (init, cases) = [body] |> flatten_switch |> group_switch
  and allcases = List.rev (all_cases [] body) in
  if is_skip_or_debug init && List.length cases = List.length allcases then
    (* This is a structured switch *)
    make_normalized_switch e cases
  else begin
    (* This switch needs to be converted *)
    if not !support_unstructured then
      (*- #Link_to E_COMPCERT_TR_Robustness_SwitchNorm_002 *)
      Diagnostics.error loc
        "unsupported feature: non-structured 'switch' statement \
         (consider adding option [-funstructured-switch])";
    let case_table = List.map (fun case -> (case, gen_label())) allcases in
    let end_lbl = gen_label() in
    let newbody = substitute_cases case_table body end_lbl in
    let goto_case (case, lbl) =
      (case, no_loc, {sdesc = Sgoto lbl; sloc = no_loc}) in
    let case_table' =
      if List.mem_assoc Default case_table
      then case_table
      else (Default, end_lbl) :: case_table in
    Sseq({sdesc = make_normalized_switch e (List.map goto_case case_table');
          sloc = loc},
         sseq no_loc newbody
              {sdesc = Slabeled(Slabel end_lbl, sskip); sloc = no_loc})
  end
(*- #End *)

(*- E_COMPCERT_CODE_SwitchNorm_transform_stmt_001 *)
(*- #Justify_Derived "Utility function" *)
let rec transform_stmt s =
  { s with sdesc =
      match s.sdesc with
      | Sseq(s1, s2) -> Sseq(transform_stmt s1, transform_stmt s2)
      | Sif(e, s1, s2) -> Sif(e, transform_stmt s1, transform_stmt s2)
      | Swhile(e, s1) -> Swhile(e, transform_stmt s1)
      | Sdowhile(s1, e) -> Sdowhile(transform_stmt s1, e)
      | Sfor(s1, e, s2, s3) ->
          Sfor(transform_stmt s1, e, transform_stmt s2, transform_stmt s3)
      | Sswitch(e, s1) -> normalize_switch s.sloc e (transform_stmt s1)
      | Slabeled(lbl, s1) -> Slabeled(lbl, transform_stmt s1)
      | Sblock sl -> Sblock(List.map transform_stmt sl)
      | sd -> sd}
(*- #End *)

(*- E_COMPCERT_CODE_SwitchNorm_transform_fundef_001 *)
(*- #Justify_Derived "Utility function" *)
let transform_fundef env loc fd =
  { fd with fd_body = transform_stmt fd.fd_body }
(*- #End *)

(* Entry point *)

(*- E_COMPCERT_CODE_SwitchNorm_program_001 *)
(*- #Justify_Derived "Utility function" *)
let program unstructured p =
  support_unstructured := unstructured;
  Transform.program ~fundef: transform_fundef p
(*- #End *)
