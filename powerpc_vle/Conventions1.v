(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
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
- Callee-save registers, whose value is preserved across a function call.
- Caller-save registers that can be modified during a function call.

*)

(*- E_COMPCERT_FTR_Function_Conventions1_is_callee_save_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_EABI_001 *)
Definition is_callee_save (r: mreg): bool :=
  match r with
  | R3  | R4  | R5  | R6  | R7  | R8  | R9  | R10  | R11 | R12 => false
  | R14 | R15 | R16 | R17 | R18 | R19 | R20 | R21 | R22 | R23 | R24
  | R25 | R26 | R27 | R28 | R29 | R30 | R31 => true
  | ErrorReg => false
  end.
(*- #End *)

Definition destroyed_at_call :=
  List.filter (fun r => negb (is_callee_save r)) all_mregs.

(** The following definitions are used by the register allocator. *)

Definition callee_save_type (r: mreg): typ :=
  match r with
  | R3  | R4  | R5  | R6  | R7  | R8  | R9  | R10  | R11 | R12
  | R14 | R15 | R16 | R17 | R18 | R19 | R20 | R21 | R22 | R23 | R24
  | R25 | R26 | R27 | R28 | R29 | R30 | R31 => Tany32
  | ErrorReg => Tany64
  end.

Definition is_float_reg (r: mreg): bool := false.

Definition int_caller_save_regs :=
  R3 :: R4 :: R5 :: R6 :: R7 :: R8 :: R9 :: R10 :: R11 :: R12 :: nil.

Definition float_caller_save_regs : list mreg :=
  nil.

Definition int_callee_save_regs :=
  R31 :: R30 :: R29 :: R28 :: R27 :: R26 :: R25 :: R24 :: R23 ::
  R22 :: R21 :: R20 :: R19 :: R18 :: R17 :: R16 :: R15 :: R14 :: nil.

Definition float_callee_save_regs : list mreg :=
  nil.

Definition dummy_int_reg := R3.     (**r Used in [Coloring]. *)
Definition dummy_float_reg := ErrorReg.   (**r Used in [Coloring]. *)

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
  locations.  To ensure binary interoperability of code generated by our
  compiler with libraries compiled by another PowerPC compiler, we
  implement the standard conventions defined in the PowerPC/EABI
  application binary interface. *)

(** ** Location of function result *)

(** The result value of a function is passed back to the caller in
  registers [R3] or [R3, R4], depending on the type of the returned value.
  We treat a function without result as a function with one integer result. *)

(*- E_COMPCERT_FTR_Function_Conventions1_loc_result_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_EABI_001 *)
Definition loc_result (s: signature) : rpair mreg :=
  match proj_sig_res s with
  | Tint | Tany32 | Tsingle => One R3
  | Tfloat | Tany64 => One ErrorReg
  | Tlong => Twolong R3 R4
  end.
(*- #End *)

(** The result registers have types compatible with that given in the signature. *)

Lemma loc_result_type:
  forall sig,
  subtype (proj_sig_res sig) (typ_rpair mreg_type (loc_result sig)) = true.
Proof.
  intros. unfold loc_result, mreg_type.
  destruct Archi.ptr64 eqn:?; destruct (proj_sig_res sig); simpl; auto.
Qed.

(** The result locations are caller-save registers *)

Lemma loc_result_caller_save:
  forall (s: signature),
  forall_rpair (fun r => is_callee_save r = false) (loc_result s).
Proof.
  intros. unfold loc_result, is_callee_save;
  destruct Archi.ptr64; destruct (proj_sig_res s); simpl; auto.
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
  intros; unfold loc_result, mreg_type.
  destruct (proj_sig_res sg); simpl; auto.
  split; auto. congruence.
Qed.

(** The location of the result depends only on the result part of the signature *)

Lemma loc_result_exten:
  forall s1 s2, simpl_rettype_match false s1.(sig_res) s2.(sig_res) -> loc_result s1 = loc_result s2.
Proof.
  intros. unfold loc_result, proj_sig_res.
  erewrite (simpl_rettype_match_proj_rettype); eauto.
Qed.

(** ** Location of function arguments *)

(** The PowerPC E500 ABI states the following convention for passing arguments
  to a function:
- The first 8 integer or single-precisison float arguments are passed in registers [R3] to [R10].
- The first 4 long integer arguments are passed in register pairs [R3,R4] ... [R9,R10].
- Extra arguments are passed on the stack, in [Outgoing] slots, consecutively assigned, and
  starting at word offset 0:
    - 1 word for an integer or single-precisison float arguments,
    - 2 words for long integer arguments.
- No stack space is reserved for the arguments that are passed in registers.
*)

(*- E_COMPCERT_FTR_Function_Conventions1_param_regs_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_EABI_001 *)
Definition param_regs :=
  R3 :: R4 :: R5 :: R6 :: R7 :: R8 :: R9 :: R10 :: nil.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Conventions1_loc_arguments_rec_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_EABI_001 *)
Fixpoint loc_arguments_rec
    (tyl: list typ) (r ofs: Z) {struct tyl} : list (rpair loc) :=
  match tyl with
  | nil => nil
  | (Tint | Tany32 | Tsingle) as ty :: tys =>
      match list_nth_z param_regs r with
      | None =>
          One (S Outgoing ofs ty) :: loc_arguments_rec tys r (ofs + 1)
      | Some ireg =>
          One (R ireg) :: loc_arguments_rec tys (r + 1) ofs
      end
  | (Tfloat | Tany64) as ty :: tys =>
    (* We don't have double precision floats, the results are just passed on the stack *)
    let ofs := align ofs 2 in
    One (S Outgoing ofs ty) :: loc_arguments_rec tys r (ofs + 2)
  | Tlong :: tys =>
      let r := align r 2 in
      match list_nth_z param_regs r, list_nth_z param_regs (r + 1) with
      | Some r1, Some r2 =>
          Twolong (R r1) (R r2) :: loc_arguments_rec tys (r + 2) ofs
      | _, _ =>
          let ofs := align ofs 2 in
          Twolong (S Outgoing ofs Tint) (S Outgoing (ofs + 1) Tint) ::
          loc_arguments_rec tys r (ofs + 2)
      end
  end.
(*- #End *)

(** [loc_arguments s] returns the list of locations where to store arguments
  when calling a function with signature [s].  *)

(*- E_COMPCERT_FTR_Function_Conventions1_loc_arguments_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_EABI_001 *)
Definition loc_arguments (s: signature) : list (rpair loc) :=
  loc_arguments_rec (proj_sig_args s) 0 0.
(*- #End *)

(** Argument locations are either caller-save registers or [Outgoing]
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

Remark loc_arguments_rec_charact:
  forall tyl r ofs p,
  In p (loc_arguments_rec tyl r ofs) ->
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
  destruct (list_nth_z param_regs r) as [r'|] eqn:E; destruct H.
  subst.  eapply list_nth_z_in; eauto.
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
  set (ir' := align r 2) in *.
  destruct (list_nth_z param_regs ir') as [r1|] eqn:E1.
  destruct (list_nth_z param_regs (ir' + 1)) as [r2|] eqn:E2.
  destruct H. subst; split;  eapply list_nth_z_in; eauto.
  eapply IHtyl; eauto.
  destruct H.
  subst. split;split; try lia; apply Z.divide_1_l.
  eapply Y; eauto. lia.
  destruct H.
  subst. split;split; try lia; apply Z.divide_1_l.
  eapply Y; eauto. lia.
- (* single *)
  assert (ofs <= align ofs 1) by (apply align_le; lia).
  assert (ofs <= align ofs 2) by (apply align_le; lia).
  destruct (list_nth_z param_regs r) as [r'|] eqn:E; destruct H.
  subst. eapply list_nth_z_in; eauto.
  eapply IHtyl; eauto.
  subst. split. lia.
  apply Z.divide_1_l.
  eapply Y; eauto. lia.
- (* any32 *)
  destruct (list_nth_z param_regs r) as [r'|] eqn:E; destruct H.
  subst. eapply list_nth_z_in; eauto.
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
    destruct l as [r | [] ofs ty]; auto. }
  unfold forall_rpair; destruct p; intuition auto.
Qed.

Global Hint Resolve loc_arguments_acceptable: locs.

Lemma loc_arguments_main:
  loc_arguments signature_main = nil.
Proof.
  reflexivity.
Qed.

(** ** Normalization of function results and parameters *)

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
