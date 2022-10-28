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

(** Instruction selection for 64-bit integer operations *)

Require Import String Coqlib Maps Integers Floats Errors.
Require Archi.
Require Import AST Values Memory Globalenvs Events Builtins.
Require Import Cminor Op CminorSel.
Require Import SelectOp SelectOpproof SplitLong SplitLongproof.
Require Import SelectLong.


Local Open Scope cminorsel_scope.
Local Open Scope string_scope.

Section CMCONSTR.

Variable prog: program.
Variable hf: helper_functions.
Hypothesis HELPERS: helper_functions_declared prog hf.
Let ge := Genv.globalenv prog.
Variable sp: val.
Variable e: env.
Variable m: mem.

Theorem eval_longofsingle:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.longofsingle x = Some y ->
  exists v, eval_expr ge sp e m le (longofsingle a) v /\ Val.lessdef y v.
Proof.
  intros; unfold longofsingle.
  econstructor. split.
  eapply (eval_helper_1 prog sp e m (BI_standard BI_i64_ftos)); eauto.
  red in HELPERS; decompose [Logic.and] HELPERS; eauto.
  auto. auto.
Qed.


Theorem eval_longuofsingle:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.longuofsingle x = Some y ->
  exists v, eval_expr ge sp e m le (longuofsingle a) v /\ Val.lessdef y v.
Proof.
  intros; unfold longuofsingle.
  econstructor. split.
  eapply (eval_helper_1 prog sp e m (BI_standard BI_i64_ftou)); eauto.
  red in HELPERS; decompose [Logic.and] HELPERS; eauto.
  auto. auto.
Qed.


End CMCONSTR.
