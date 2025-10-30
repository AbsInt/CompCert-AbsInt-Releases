(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, Collège de France and Inria Paris            *)
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

(** Platform-specific built-in functions *)

From Coq Require Import String.
Require Import Coqlib AST Integers Floats Values.
Require Import Builtins0.
Local Open Scope asttyp_scope.

(*- E_COMPCERT_FTR_Function_Builtins1_platform_builtin_0_001 *)
(*- #Justify_Derived "Internal type" *)
Inductive platform_builtin : Type :=
  | BI_udivl.
(*- #End *)

Local Open Scope string_scope.

(*- E_COMPCERT_FTR_Function_Builtins1_platform_builtin_table_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_MULTIPLICATIVE_OPERATORS_005 *)
Definition platform_builtin_table : list (string * platform_builtin) :=
   ("__builtin_udivl", BI_udivl) :: nil.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Builtins1_platform_builtin_sig_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_MULTIPLICATIVE_OPERATORS_005 *)
Definition platform_builtin_sig (b: platform_builtin) : signature :=
  match b with
  | BI_udivl =>
      [Xlong; Xlong ---> Xlong]
  end.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Builtins1_platform_builtin_sem_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_MULTIPLICATIVE_OPERATORS_005 *)
Program Definition platform_builtin_sem (b: platform_builtin) : builtin_sem (sig_res (platform_builtin_sig b)) :=
  match b with
  | BI_udivl => mkbuiltin_v2p Xlong Val.divlu _ _
  end.
Next Obligation.
  red. destruct v1; simpl; auto. destruct v2; simpl; auto. destruct Int64.eq; exact I.
Qed.
Next Obligation.
    red. inv H; simpl; auto. inv H0; auto. destruct Int64.eq; auto.
Qed.
(*- #End *)

Definition eq_platform_builtin: forall (x y: platform_builtin), {x=y} + {x<>y}.
Proof.
  decide equality.
Defined.
