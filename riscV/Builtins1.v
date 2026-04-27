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

Inductive platform_builtin : Type :=
  | BI_czero_eqz
  | BI_czero_nez.

Local Open Scope string_scope.

Definition platform_builtin_table : list (string * platform_builtin) :=
    ("__builtin_czero_eqz", BI_czero_eqz)
  :: ("__builtin_czero_nez", BI_czero_nez)
  :: nil.

Definition platform_builtin_sig (b: platform_builtin) : signature :=
  match b with
  | BI_czero_eqz | BI_czero_nez =>
     [Xint; Xint ---> Xint]
  end.

Definition platform_builtin_sem (b: platform_builtin) : builtin_sem (sig_res (platform_builtin_sig b)) :=
  match b with
  | BI_czero_eqz =>
      mkbuiltin_n2t Tint Tint Xint (fun c n => if Int.eq c Int.zero then Int.zero else n)
  | BI_czero_nez =>
      mkbuiltin_n2t Tint Tint Xint (fun c n => if negb (Int.eq c Int.zero) then Int.zero else n)
  end.

Definition eq_platform_builtin: forall (x y: platform_builtin), {x=y} + {x<>y}.
Proof.
  decide equality.
Defined.
