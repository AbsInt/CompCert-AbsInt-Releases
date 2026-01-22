(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  AbsInt Angewandte Informatik GmbH. All rights reserved. This file  *)
(*  is distributed under the terms of the INRIA Non-Commercial         *)
(*  License Agreement.                                                 *)
(*                                                                     *)
(* *********************************************************************)

(** Platform-specific built-in functions *)

From Coq Require Import String.
Require Import Coqlib.
Require Import AST Integers Floats Values.
Require Import Builtins0.
Local Open Scope asttyp_scope.

Inductive platform_builtin : Type :=
  | BI_cadd
  | BI_csub.

Local Open Scope string_scope.

Definition platform_builtin_table : list (string * platform_builtin) :=
    ("__builtin_cadd", BI_cadd)
  :: ("__builtin_csub", BI_csub)
  :: nil.

Definition platform_builtin_sig (b: platform_builtin) : signature :=
  match b with
  | BI_cadd | BI_csub =>
    [Xint; Xint; Xint ---> Xint]
  end.

Definition platform_builtin_sem (b: platform_builtin) : builtin_sem (sig_res (platform_builtin_sig b)) :=
  match b with
  | BI_cadd =>
      mkbuiltin_n3t Tint Tint Tint Xint (fun c n1 n2 => if negb (Int.eq c Int.zero) then Int.add n1 n2 else n1)
  | BI_csub =>
      mkbuiltin_n3t Tint Tint Tint Xint (fun c n1 n2 => if negb (Int.eq c Int.zero) then Int.sub n1 n2 else n1)
  end.

Definition eq_platform_builtin: forall (x y: platform_builtin), {x=y} + {x<>y}.
Proof.
  decide equality.
Defined.
