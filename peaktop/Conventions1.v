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

(** Function calling conventions and other conventions regarding the use of
    machine registers and stack slots. *)

Require Import Coqlib.
Require Import Decidableplus.
Require Import AST.
Require Import Events.
Require Import Locations.
Require Archi.

(** * Classification of machine registers *)

(** Machine registers (type [mreg] in module [Locations]) are divided in
  the following groups:
- Temporaries used for spilling, reloading, and parallel move operations.
- Allocatable registers, that can be assigned to RTL pseudo-registers.
  These are further divided into:
-- Callee-save registers, whose value is preserved across a function call.
-- Caller-save registers that can be modified during a function call.

*)

Definition is_callee_save (r: mreg): bool :=
  match r with
  | R2  | R3  | R4  | R5  | R6  | R7  | R8  | R9  | R10 | R11 => false
  | R12 | R13 | R14 | R15 | R16 | R17 | R18 | R19 | R20 | R21
  | R22 | R23 | R24 | R25 | R26 | R27 | R28 | R29 | R30 | R31 => true
  | ErrorReg => false
  end.

Definition int_caller_save_regs :=
  R2 :: R3 :: R4 :: R5 :: R6 :: R7 :: R8 :: R9 :: R10 :: R11 :: nil.

Definition float_caller_save_regs : list mreg := nil.

Definition int_callee_save_regs :=
  R12 :: R13 :: R14 :: R15 :: R16 :: R17 :: R18 :: R19 :: R20 :: R21 :: R22 :: R23 ::
  R24 :: R25 :: R26 :: R27 :: R28 :: R29 :: R30 :: R31 :: nil.

Definition float_callee_save_regs : list mreg := nil.

Definition destroyed_at_call :=
  List.filter (fun r => negb (is_callee_save r)) all_mregs.

Definition dummy_int_reg := R2.     (**r Used in [Coloring]. *)

Definition dummy_float_reg := R3.   (**r Used in [Coloring]. *)

Definition callee_save_type := mreg_type.

Definition is_float_reg (r: mreg) := false.

(** * Function calling conventions *)

(** The functions in this section determine the locations (machine registers
  and stack slots) used to communicate arguments and results between the
  caller and the callee during function calls.  These locations are functions
  of the signature of the function and of the call instruction.
  Agreement between the caller and the callee on the locations to use
  is guaranteed by our dynamic semantics for Cminor and RTL, which demand
  that the signature of the call instruction is identical to that of the
  called function.

  Calling conventions are largely arbitrary: they must respect the properties
  proved in this section (such as no overlapping between the locations
  of function arguments), but this leaves much liberty in choosing actual
  locations.
**)

(** ** Location of function result *)

(** The result value of a function is passed back to the caller in
  registers [R4] or [R4,R5], depending on the type of the
  returned value.  We treat a function without result as a function
  with one integer result. *)

Definition loc_result (s: signature) : rpair mreg :=
  match proj_sig_res s with
  | Tint | Tany32 => One R4
  | Tsingle => One R4
  | Tlong =>  Twolong R5 R4
  | Tfloat | Tany64 => One ErrorReg
  end.

(** The result registers have types compatible with that given in the signature. *)

Lemma loc_result_type:
  forall sig,
  subtype (proj_sig_res sig) (typ_rpair mreg_type (loc_result sig)) = true.
Proof.
  intros. unfold loc_result, mreg_type;
  destruct (proj_sig_res sig); auto.
Qed.

(** The result locations are caller-save registers *)

Lemma loc_result_caller_save:
  forall (s: signature),
  forall_rpair (fun r => is_callee_save r = false) (loc_result s).
Proof.
  intros. unfold loc_result, is_callee_save;
  destruct (proj_sig_res s); simpl; auto.
Qed.

(** If the result is in a pair of registers, those registers are distinct and have type [Tint] at least. *)

Lemma loc_result_pair:
  forall sg,
  match loc_result sg with
  | One _ => True
  | Twolong r1 r2 =>
        r1 <> r2 /\ proj_sig_res sg = Tlong
     /\ subtype Tint (mreg_type r1) = true /\ subtype Tint (mreg_type r2) = true
     /\ Archi.ptr64 = false
  end.
Proof.
  intros; unfold loc_result; destruct (proj_sig_res sg); auto.
  destruct Archi.big_endian; intuition congruence.
Qed.

(** The location of the result depends only on the result part of the signature *)

Lemma loc_result_exten:
  forall s1 s2, s1.(sig_res) = s2.(sig_res) -> loc_result s1 = loc_result s2.
Proof.
  intros. unfold loc_result, proj_sig_res. rewrite H; auto.
Qed.

(** ** Location of function arguments *)

(** This ABI is the one we came up with and is not final at all. Conventions for
  that are passed to a function:

  - The first 8 arguments are passed in registers [R4] to [R11]
  - Arguments of size 64 bits that must be passed in integer registers are
    passed in two consecutive integer registers (a(i), a(i+1)) or in a(8)
    and on a 32-bit word on the stack. Stack-allocated arguments are aligned
    to their natural alignment.
  - Extra arguments are passed on the stack, in [Outgoing] slots, consecutively
    assigned (1 word for an integer argument, 2 words for a float), starting at
    word offset 0.
  - No stack space is reserved for the arguments that are passed in registers.
*)

Definition param_regs :=
  R4 :: R5 :: R6 :: R7 :: R8 :: R9 ::  R10 :: R11 :: nil.

Definition lookup_register l r c (va: option Z) : option mreg :=
  match va with
  | Some z =>
    if zlt c z then
      list_nth_z l r
    else
      None
  | None => list_nth_z l r
  end.

Fixpoint loc_arguments_rec
    (tyl: list typ) (r ofs c: Z) (va: option Z) {struct tyl} : list (rpair loc) :=
  match tyl with
  | nil => nil
  | (Tint | Tany32 | Tsingle) as ty :: tys =>
      match lookup_register param_regs r c va with
      | None =>
          One (S Outgoing ofs ty) :: loc_arguments_rec tys r (ofs + 1) (c + 1) va
      | Some ireg =>
          One (R ireg) :: loc_arguments_rec tys (r + 1)  ofs (c + 1) va
      end
  | (Tfloat | Tany64) as ty :: tys =>
    One (S Outgoing ofs ty) :: loc_arguments_rec tys r (ofs + 2) (c + 1) va
  | Tlong :: tys =>
      match  lookup_register param_regs r c va,  lookup_register param_regs (r + 1) c va with
      | Some r1, Some r2 =>
        Twolong (R r2) (R r1) :: loc_arguments_rec tys (r + 2) ofs (c + 1) va
      | Some r1, None =>
        Twolong (S Outgoing ofs Tint) (R r1) :: loc_arguments_rec tys (r + 1) (ofs + 1) (c + 1) va
      | _, _ =>
        Twolong (S Outgoing (ofs + 1) Tint) (S Outgoing ofs Tint) ::
                loc_arguments_rec tys r (ofs + 2)  (c + 1) va
      end
  end.

(** [loc_arguments s] returns the list of locations where to store arguments
  when calling a function with signature [s].  *)

Definition loc_arguments (s: signature) : list (rpair loc) :=
  loc_arguments_rec s.(sig_args) 0 0 0 s.(sig_cc).(cc_vararg).

(** Argument locations are either non-temporary registers or [Outgoing]
  stack slots at nonnegative offsets. *)


Definition loc_argument_acceptable (l: loc) : Prop :=
  match l with
  | R r => is_callee_save r = false
  | S Outgoing ofs ty => ofs >= 0 /\ (typealign ty | ofs)
  | _ => False
  end.

Definition loc_argument_charact (ofs: Z) (l: loc) : Prop :=
  match l with
  | R r => In r param_regs
  | S Outgoing ofs' ty => ofs' >= ofs /\ (typealign ty | ofs')
  | _ => False
  end.

Remark lookup_register_in:
  forall l r c va x,
    lookup_register l r c va = Some x -> In x l.
Proof.
  unfold lookup_register; intros.
  destruct va; try discriminate H.
  destruct (zlt c z); try discriminate H.
  eapply list_nth_z_in; eauto.
  eapply list_nth_z_in; eauto.
Qed.

Remark loc_arguments_rec_charact:
  forall tyl r ofs c va p,
  In p (loc_arguments_rec tyl r ofs c va) ->
  forall_rpair (loc_argument_charact ofs) p.
Proof.
  assert (X: forall ofs1 ofs2 l, loc_argument_charact ofs2 l -> ofs1 <= ofs2 -> loc_argument_charact ofs1 l).
  { destruct l; simpl; intros; auto. destruct sl; auto. intuition lia. }
  assert (Y: forall ofs1 ofs2 p, forall_rpair (loc_argument_charact ofs2) p -> ofs1 <= ofs2 -> forall_rpair (loc_argument_charact ofs1) p).
  { destruct p; simpl; intuition eauto. }
Opaque list_nth_z.
  induction tyl; simpl loc_arguments_rec; intros.
  elim H.
  destruct a.
- (* int *)
  destruct (lookup_register param_regs r c va) as [ir|] eqn:E; destruct H.
  subst. eapply lookup_register_in; eauto.
  eapply IHtyl; eauto.
  subst. split. lia. apply Z.divide_1_l.
  eapply Y; eauto. lia.
- (* float *)
  assert (ofs <= align ofs 2) by (apply align_le; lia).
  destruct H.
  subst. split. lia. apply Z.divide_1_l.
  eapply Y; eauto. lia.
- (* long *)
  assert (ofs <= align ofs 2) by (apply align_le; lia).
  destruct (lookup_register param_regs r c va) as [r1|] eqn:E1.
  destruct (lookup_register param_regs (r + 1) c va) as [r2|] eqn:E2.
  destruct H.
  subst; split; eapply lookup_register_in; eauto.
  eapply IHtyl; eauto.
  destruct H.
  subst; split. split; try lia. apply Z.divide_1_l.
  subst;  eapply lookup_register_in; eauto.
  eapply Y; eauto. lia.
  destruct H.
  subst; split; split; try lia; try (apply Z.divide_1_l).
  eapply Y; eauto; lia.
- (* single *)
  assert (ofs <= align ofs 1) by (apply align_le; lia).
  assert (ofs <= align ofs 2) by (apply align_le; lia).
  destruct (lookup_register param_regs r c va) as [r'|] eqn:E; destruct H.
  subst.  eapply lookup_register_in; eauto.
  eapply IHtyl; eauto.
  subst.  simpl; split.  lia. apply Z.divide_1_l.
  eapply Y; eauto; simpl; lia.
- (* any32 *)
  destruct (lookup_register param_regs r c va) as [r'|] eqn:E; destruct H.
  subst. eapply lookup_register_in; eauto.
  eapply IHtyl; eauto.
  subst. split. lia. apply Z.divide_1_l.
  eapply Y; eauto. lia.
- (* float *)
  assert (ofs <= align ofs 2) by (apply align_le; lia).
  destruct H.
  subst. split. lia. apply Z.divide_1_l.
  eapply Y; eauto. lia.
Qed.

Lemma loc_arguments_acceptable:
  forall (s: signature) (p: rpair loc),
  In p (loc_arguments s) -> forall_rpair loc_argument_acceptable p.
Proof.
  unfold loc_arguments; intros.
  exploit loc_arguments_rec_charact; eauto.
  assert (A: forall r, In r param_regs -> is_callee_save r = false) by decide_goal.
  assert (X: forall l, loc_argument_charact 0 l -> loc_argument_acceptable l).
  { unfold loc_argument_charact, loc_argument_acceptable.
    destruct l as [r | [] ofs ty]; auto.  }
  unfold forall_rpair; destruct p; intuition auto.
Qed.

Global Hint Resolve loc_arguments_acceptable: locs.

Lemma loc_arguments_main:
  loc_arguments signature_main = nil.
Proof.
  reflexivity.
Qed.

(** ** Normalization of function results *)

(** No normalization needed. *)

Definition return_value_needs_normalization (t: rettype) := false.
Definition parameter_needs_normalization (t: rettype) := false.
