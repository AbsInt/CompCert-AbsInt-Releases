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

Require Import String Coqlib.
Require Import AST Integers Floats Values.
Require Import Builtins0.

Inductive platform_builtin : Type :=
    | BI_madd
    | BI_msub.

Local Open Scope string_scope.

Definition platform_builtin_table : list (string * platform_builtin) :=
      ("__builtin_madd", BI_madd)
    :: ("__builtin_msub", BI_msub)
    :: nil.

Definition platform_builtin_sig (b: platform_builtin) : signature :=
  match b with
  | BI_madd | BI_msub =>
      mksignature (Tint :: Tint :: Tint :: nil) Tint cc_default
  end.

Definition platform_builtin_sem (b: platform_builtin) : builtin_sem (sig_res (platform_builtin_sig b)) :=
  match b with
  | BI_madd =>
     mkbuiltin_n3t Tint Tint Tint Tint
      (fun n1 n2 n3 => Int.add (Int.mul n1 n2) n3)
  | BI_msub =>
     mkbuiltin_n3t Tint Tint Tint Tint
      (fun n1 n2 n3 => Int.sub (Int.mul n1 n2) n3)
  end.
