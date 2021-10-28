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

(** Architecture-dependent parameters for Peaktop in 32-bit mode *)

Require Import ZArith List.
(*From Flocq*)
Require Import Binary Bits.

Definition ptr64 := false.

Definition big_endian := false.

Definition align_int64 := 4%Z.
Definition align_float64 := 4%Z.

Definition splitlong := negb ptr64.

Lemma splitlong_ptr32: splitlong = true -> ptr64 = false.
Proof.
  unfold splitlong. destruct ptr64; simpl; congruence.
Qed.

Definition default_nan_64 := (false, iter_nat 51 _ xO xH).
Definition default_nan_32 := (false, iter_nat 22 _ xO xH).

(* TODO check *)

Definition choose_nan_64 (l: list (bool * positive)) : bool * positive :=
  match l with nil => default_nan_64 | n :: _ => n end.

Definition choose_nan_32 (l: list (bool * positive)) : bool * positive :=
  match l with nil => default_nan_32 | n :: _ => n end.

Lemma choose_nan_64_idem: forall n,
  choose_nan_64 (n :: n :: nil) = choose_nan_64 (n :: nil).
Proof. auto. Qed.

Lemma choose_nan_32_idem: forall n,
  choose_nan_32 (n :: n :: nil) = choose_nan_32 (n :: nil).
Proof. auto. Qed.

Definition fma_order {A: Type} (x y z: A) := (x, y, z).

Definition fma_invalid_mul_is_nan := false.

Definition float_of_single_preserves_sNaN := false.

Definition one_register_class := true.

Global Opaque ptr64 big_endian splitlong
              default_nan_64 choose_nan_64
              default_nan_32 choose_nan_32
              fma_order fma_invalid_mul_is_nan
              float_of_single_preserves_sNaN
              one_register_class.
