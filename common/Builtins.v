(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, Collège de France and Inria Paris            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Known built-in functions *)

Require Import String Coqlib.
Require Import AST Integers Floats Values.
Require Export Builtins0 Builtins1.

(*- E_COMPCERT_FTR_Function_Builtins_builtin_function_0_001 *)
(*- #Justify_Derived "Internal type" *)
Inductive builtin_function : Type :=
  | BI_standard (b: standard_builtin)
  | BI_platform (b: platform_builtin).
(*- #End *)

(*- E_COMPCERT_FTR_Function_Builtins_builtin_function_sig_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_EXTERNAL_FUNCTIONS_001 *)
Definition builtin_function_sig (b: builtin_function) : signature :=
  match b with
  | BI_standard b => standard_builtin_sig b
  | BI_platform b => platform_builtin_sig b
  end.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Builtins_builtin_function_sem_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_EXTERNAL_FUNCTIONS_001 *)
Definition builtin_function_sem (b: builtin_function) : builtin_sem (sig_res (builtin_function_sig b)) :=
  match b with
  | BI_standard b => standard_builtin_sem b
  | BI_platform b => platform_builtin_sem b
  end.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Builtins_lookup_builtin_function_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_EXTERNAL_FUNCTIONS_001 *)
Definition lookup_builtin_function (name: string) (sg: signature) : option builtin_function :=
  match lookup_builtin standard_builtin_sig name sg standard_builtin_table with
  | Some b => Some (BI_standard b)
  | None => 
  match lookup_builtin platform_builtin_sig name sg platform_builtin_table with
  | Some b => Some (BI_platform b)
  | None => None
  end end.
(*- #End *)

Lemma lookup_builtin_function_sig:
  forall name sg b, lookup_builtin_function name sg = Some b -> builtin_function_sig b = sg.
Proof.
  unfold lookup_builtin_function; intros.
  destruct (lookup_builtin standard_builtin_sig name sg standard_builtin_table) as [bs|] eqn:E.
  inv H. simpl. eapply lookup_builtin_sig; eauto.
  destruct (lookup_builtin platform_builtin_sig name sg platform_builtin_table) as [bp|] eqn:E'.
  inv H. simpl. eapply lookup_builtin_sig; eauto.
  discriminate.
Qed.


