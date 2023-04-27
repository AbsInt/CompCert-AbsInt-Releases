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

(** How to use registers for register allocation.
    We favor the use of caller-save registers, using callee-save registers
    only when no caller-save is available. *)

Record alloc_regs := mk_alloc_regs {
  preferred_int_regs: list mreg;
  remaining_int_regs: list mreg;
  preferred_float_regs: list mreg;
  remaining_float_regs: list mreg
}.

Definition allocatable_registers (_: unit) :=
  {| preferred_int_regs := int_caller_save_regs;
     remaining_int_regs := int_callee_save_regs;
     preferred_float_regs := float_caller_save_regs;
     remaining_float_regs := float_callee_save_regs |}.

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
  forall s1 s2, simpl_rettype_match false s1.(sig_res) s2.(sig_res) -> loc_result s1 = loc_result s2.
Proof.
  intros. unfold loc_result, proj_sig_res.
  erewrite (simpl_rettype_match_proj_rettype); eauto.
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

Definition lookup_register l r fixed : option mreg :=
  if zle fixed 0 then
    None
  else
      list_nth_z l r.

Definition stack_arg (ty: typ) (r ofs: Z)
                     (rec: Z -> Z -> list (rpair loc)) :=
  let arg :=
    if typ_eq ty Tlong then
      Twolong (S Outgoing (ofs + 1) Tint) (S Outgoing ofs Tint)
    else
      One (S Outgoing ofs ty) in
  arg :: rec r (ofs + typesize ty).


Fixpoint loc_arguments_stack (tyl: list typ) (ofs: Z) {struct tyl} : list (rpair loc) :=
  match tyl with
  | nil => nil
  | ty :: tys => stack_arg ty 0 ofs (fun r ofs => loc_arguments_stack tys ofs)
  end.

Definition simple_arg (ty: typ) (r ofs: Z)
                     (rec: Z -> Z -> list (rpair loc)) :=
  match list_nth_z param_regs r with
  | None =>
    stack_arg ty r ofs rec
  | Some p =>
    One (R p) :: rec (r + 1) ofs
  end.

Definition long_arg (r ofs: Z)
                    (rec: Z -> Z -> list (rpair loc)) :=
  match list_nth_z param_regs r, list_nth_z param_regs (r + 1) with
  | Some r1, Some r2 =>
    Twolong (R r2) (R r1) :: rec (r + 2) ofs
  | Some r1, None =>
    Twolong (S Outgoing ofs Tint) (R r1) :: rec (r + 1) (ofs + 1)
  | _, _ =>
    stack_arg Tlong r ofs rec
  end.

Fixpoint loc_arguments_rec
    (tyl: list typ) (fixed r ofs: Z) {struct tyl} : list (rpair loc) :=
  match tyl with
  | nil => nil
  | ty :: tys => if zle fixed 0 then loc_arguments_stack tyl ofs  else
    match ty with
    | (Tint | Tany32 | Tsingle) =>
      simple_arg ty r ofs (loc_arguments_rec tys (fixed - 1))
    | (Tfloat | Tany64) =>
      stack_arg ty r ofs (loc_arguments_rec tys (fixed - 1))
    | Tlong =>
      long_arg r ofs (loc_arguments_rec tys (fixed - 1))
    end
  end.

Definition fixed_arguments (s: signature) :=
  match s.(sig_cc).(cc_vararg) with
  | Some z => z
  | None => list_length_z s.(sig_args)
  end.

(** [loc_arguments s] returns the list of locations where to store arguments
  when calling a function with signature [s].  *)

Definition loc_arguments (s: signature) : list (rpair loc) :=
  loc_arguments_rec (proj_sig_args s) (fixed_arguments s) 0 0.

(** Argument locations are either non-temporary registers or [Outgoing]
  stack slots at nonnegative offsets. *)


Definition loc_argument_acceptable (l: loc) : Prop :=
  match l with
  | R r => is_callee_save r = false
  | S Outgoing ofs ty => ofs >= 0 /\ (typealign ty | ofs)
  | _ => False
  end.

Lemma loc_arguments_rec_charact:
  forall tyl fixed r ofs p,
  ofs >= 0 ->
  In p (loc_arguments_rec tyl fixed r ofs) -> forall_rpair loc_argument_acceptable p.
Proof.
  set (OK := fun (l: list (rpair loc)) =>
               forall p, In p l -> forall_rpair loc_argument_acceptable p).
  set (OKF := fun (f: Z -> Z -> list (rpair loc)) =>
                forall r ofs, ofs >= 0 -> OK (f r ofs)).
  assert (CSP: forall r, In r param_regs -> is_callee_save r = false).
  { decide_goal. }
  assert (STK: forall tyl ofs,
           ofs >= 0 -> OK (loc_arguments_stack tyl ofs)).
  { induction tyl as [ | ty tyl]; intros ofs OO; red; simpl; intros.
    - contradiction.
    - destruct H.
      + subst p. destruct (typ_eq ty Tlong).
        * split. simpl. split. lia. apply Z.divide_1_l. split; simpl. lia. apply Z.divide_1_l.
        * split. simpl. lia. destruct ty; try apply Z.divide_1_l. contradiction.
      + apply IHtyl with (ofs := ofs + ( typesize ty)). destruct ty; simpl; lia. auto.
  }
  assert (A: forall ty r ofs f,
           OKF f -> ofs >= 0 -> OK (stack_arg ty r ofs f)).
  { intros until f; intros OF OO; red; unfold stack_arg; intros.
    destruct H.
    - subst p; simpl; auto. destruct typ_eq; auto.
      split. split. lia. simpl; apply Z.divide_1_l.
      split. lia. apply Z.divide_1_l.
      split. lia. destruct ty; try apply Z.divide_1_l. contradiction.
    - eapply OF; [|eauto]. destruct ty; simpl; lia.
  }
  assert (B: forall ty r ofs f,
           OKF f -> ofs >= 0 -> OK (simple_arg ty r ofs f)).
  {intros until f; intros OF OO; red; unfold simple_arg; intros.
   destruct (list_nth_z param_regs r) as [ir|] eqn:NTH; [destruct H|].
   - subst p; simpl. apply CSP. eapply list_nth_z_in; eauto.
   - eapply OF; eauto.
   - eapply A; eauto.
  }
  assert (C: forall r ofs f,
           OKF f -> ofs >= 0 -> OK (long_arg r ofs f)).
  { intros until f; intros OF OO; red; unfold long_arg; intros.
    destruct (list_nth_z param_regs r) as [r1|] eqn:NTH1; destruct (list_nth_z param_regs (r + 1)) as [r2|] eqn:NTH2.
    destruct H. subst p; simpl. split; apply CSP; eapply list_nth_z_in; eauto.
    eapply OF; eauto.
    destruct H. subst p; simpl. split. split. lia. apply Z.divide_1_l.
    apply CSP; eapply list_nth_z_in; eauto.
    eapply (OF (r + 1) (ofs + 1)); eauto. lia.
    eapply A; eauto.
    eapply A; eauto.
  }
  cut (forall tyl fixed r ofs, ofs >= 0 -> OK (loc_arguments_rec tyl fixed r ofs)).
  unfold OK. eauto.
  induction tyl as [ | ty1 tyl]; intros until ofs; intros OO; simpl.
  - red; simpl; tauto.
  - destruct (zle fixed  0).
    + apply (STK (ty1 :: tyl)); auto.
    +  unfold OKF in *; destruct ty1; eauto.
Qed.


Lemma loc_arguments_acceptable:
  forall (s: signature) (p: rpair loc),
  In p (loc_arguments s) -> forall_rpair loc_argument_acceptable p.
Proof.
  unfold loc_arguments; intros.
  eapply loc_arguments_rec_charact; eauto. lia.
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
Definition ptr_return_ptr_reg := false.

(** ** Properties of destroyed registers. *)

Definition no_callee_saves (l: list mreg) : Prop :=
  existsb is_callee_save l = false.

Remark destroyed_by_op_caller_save:
  forall op, no_callee_saves (destroyed_by_op op).
Proof.
  unfold no_callee_saves; destruct op; (reflexivity || destruct c; reflexivity).
Qed.
