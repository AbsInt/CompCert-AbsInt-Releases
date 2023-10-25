(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*           Prashanth Mundkur, SRI International                      *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(*  The contributions by Prashanth Mundkur are reused and adapted      *)
(*  under the terms of a Contributor License Agreement between         *)
(*  SRI International and INRIA.                                       *)
(*                                                                     *)
(* *********************************************************************)

(** Function calling conventions and other conventions regarding the use of
    machine registers and stack slots. *)

Require Import Coqlib Decidableplus.
Require Import AST Machregs Locations.

(** * Classification of machine registers *)

(** Machine registers (type [mreg] in module [Locations]) are divided in
  the following groups:
- Callee-save registers, whose value is preserved across a function call.
- Caller-save registers that can be modified during a function call.

  We follow the RISC-V application binary interface (ABI) in our choice
  of callee- and caller-save registers.
*)

Definition is_callee_save (r: mreg) : bool :=
  match r with
  | R5 | R6 | R7 => false
  | R8 | R9 => true
  | R10 | R11 | R12 | R13 | R14 | R15 | R16 | R17 => false
  | R18 | R19 | R20 | R21 | R22 | R23 | R24 | R25 | R26 | R27 => true
  | R28 | R29 | R30 => false
  | F0 | F1 | F2 | F3 | F4 | F5 | F6 | F7 => false
  | F8 | F9 => true
  | F10 | F11 | F12 | F13 | F14 | F15 | F16 | F17 => false
  | F18 | F19 | F20 | F21 | F22 | F23 | F24 | F25 | F26 | F27 => true
  | F28 | F29 | F30 | F31 => false
  end.

Definition int_caller_save_regs :=
  R5  :: R6  :: R7 ::
  R10 :: R11 :: R12 :: R13 :: R14 :: R15 :: R16 :: R17 ::
  R28 :: R29 :: R30 ::
  nil.

Definition float_caller_save_regs :=
  F0  :: F1  :: F2  :: F3  :: F4  :: F5  :: F6  :: F7  ::
  F10 :: F11 :: F12 :: F13 :: F14 :: F15 :: F16 :: F17 ::
  F28 :: F29 :: F30 :: F31 ::
  nil.

Definition int_callee_save_regs :=
  R8  :: R9  ::
  R18 :: R19 :: R20 :: R21 :: R22 :: R23 :: R24 :: R25 :: R26 :: R27 ::
  nil.

Definition float_callee_save_regs :=
  F8  :: F9  ::
  F18 :: F19 :: F20 :: F21 :: F22 :: F23 :: F24 :: F25 :: F26 :: F27 ::
  nil.

Definition destroyed_at_call :=
  List.filter (fun r => negb (is_callee_save r)) all_mregs.

Definition dummy_int_reg   := R6.    (**r Used in [Coloring]. *)
Definition dummy_float_reg := F0 .   (**r Used in [Coloring]. *)

Definition callee_save_type := mreg_type.
  
Definition is_float_reg (r: mreg) :=
  match r with
        | R5  | R6  | R7  | R8  | R9  | R10 | R11
  | R12 | R13 | R14 | R15 | R16 | R17 | R18 | R19
  | R20 | R21 | R22 | R23 | R24 | R25 | R26 | R27
  | R28 | R29 | R30 => false

  | F0  | F1  | F2  | F3  | F4  | F5  | F6  | F7
  | F8  | F9  | F10 | F11 | F12 | F13 | F14 | F15
  | F16 | F17 | F18 | F19 | F20 | F21 | F22 | F23
  | F24 | F25 | F26 | F27 | F28 | F29 | F30 | F31 => true
  end.

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
  compiler with libraries compiled by another compiler, we
  implement the standard RISC-V conventions as found here:
  https://github.com/riscv/riscv-elf-psabi-doc/blob/master/riscv-elf.md
*)

(** ** Location of function result *)

(** The result value of a function is passed back to the caller in
  registers [R10] or [F10] or [R10,R11], depending on the type of the
  returned value.  We treat a function without result as a function
  with one integer result. *)

Definition loc_result (s: signature) : rpair mreg :=
  match proj_sig_res s with
  | Tint | Tany32 => One R10
  | Tfloat | Tsingle | Tany64 => One F10
  | Tlong => if Archi.ptr64 then One R10 else Twolong R11 R10
  end.

(** The result registers have types compatible with that given in the signature. *)

Lemma loc_result_type:
  forall sig,
  subtype (proj_sig_res sig) (typ_rpair mreg_type (loc_result sig)) = true.
Proof.
  intros. unfold loc_result, mreg_type;
  destruct (proj_sig_res sig); auto; destruct Archi.ptr64; auto.
Qed.

(** The result locations are caller-save registers *)

Lemma loc_result_caller_save:
  forall (s: signature),
  forall_rpair (fun r => is_callee_save r = false) (loc_result s).
Proof.
  intros. unfold loc_result, is_callee_save;
  destruct (proj_sig_res s); simpl; auto; destruct Archi.ptr64; simpl; auto.
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
  intros.
  unfold loc_result; destruct (proj_sig_res sg); auto.
  unfold mreg_type; destruct Archi.ptr64; auto.
  split; auto. congruence.
Qed.

(** The location of the result depends only on the result part of the signature *)

Lemma loc_result_exten:
  forall s1 s2, simpl_rettype_match false s1.(sig_res) s2.(sig_res)  -> loc_result s1 = loc_result s2.
Proof.
  intros. unfold loc_result, proj_sig_res.
  erewrite (simpl_rettype_match_proj_rettype); eauto.
Qed.

(** ** Location of function arguments *)

(** The RISC-V ABI states the following conventions for passing arguments
  to a function.  First for non-variadic functions:

- RV64: pass the first 8 integer arguments in integer registers
  (a1...a8: int_param_regs), the first 8 FP arguments in FP registers
  (fa1...fa8: float_param_regs) then in integer registers (a1...a8),
  and the remaining arguments on the stack, in 8-byte slots.

- RV32: same, but arguments of size 64 bits that must be passed in
  integer registers are passed in two consecutive integer registers
  (a(i), a(i+1)), or in a(8) and on a 32-bit word on the stack.
  Stack-allocated arguments are aligned to their natural alignment.

For variadic functions, the fixed arguments are passed as described
above, then the variadic arguments receive special treatment:

- RV64: FP registers are not used for passing variadic arguments.
  All variadic arguments, including FP arguments, are passed in the
  remaining integer registers (a1...a8), then on the stack, in 8-byte
  slots.

- RV32: likewise, but arguments of 64-bit types (integers as well
  as floats) are passed in two consecutive aligned integer registers
  (a(2i), a(2i+1)), or on the stack, in aligned 8-byte slots.

The passing of FP arguments to variadic functions in integer registers
doesn't quite fit CompCert's model.  We do our best by passing the FP
arguments in registers, as usual, and reserving the corresponding
integer registers, so that fixup code can be introduced in the
Asmexpand pass.
*)

Definition int_param_regs :=
  R10 :: R11 :: R12 :: R13 :: R14 :: R15 :: R16 :: R17 :: nil.
Definition float_param_regs :=
  F10 :: F11 :: F12 :: F13 :: F14 :: F15 :: F16 :: F17 :: nil.

(** To evaluate FP arguments that must be passed in integer registers,
    we can use any FP caller-save register that is not already used to pass
    a fixed FP argument.  Since there are 8 integer registers for argument
    passing, we need at most 8 extra more FP registers for these FP
    arguments. *)

Definition float_extra_param_regs :=
  F0 :: F1 :: F2 :: F3 :: F4 :: F5 :: F6 :: F7 :: nil.

Definition int_arg (ri rf ofs: Z) (ty: typ)
                   (rec: Z -> Z -> Z -> list (rpair loc)) :=
  match list_nth_z int_param_regs ri with
  | Some r =>
      One(R r) :: rec (ri + 1) rf ofs
  | None   =>
      let ofs := align ofs (typesize ty) in
      One(S Outgoing ofs ty)
      :: rec ri rf (ofs + (if Archi.ptr64 then 2 else typesize ty))
  end.

Definition float_arg (va: bool) (ri rf ofs: Z) (ty: typ)
                     (rec: Z -> Z -> Z -> list (rpair loc)) :=
  match list_nth_z (if va then nil else float_param_regs) rf with
  | Some r =>
      One (R r) :: rec ri (rf + 1) ofs
  | None =>
      (* We are out of FP registers, or cannot use them because vararg,
         so try to put the argument in an extra FP register while
         reserving an integer register or register pair into which
         fixup code will move the extra FP register. *)
      let regpair := negb Archi.ptr64 && zeq (typesize ty) 2 in
      let ri' := if va && regpair then align ri 2 else ri in
      match list_nth_z float_extra_param_regs ri' with
      | Some r =>
          let ri'' := ri' + (if Archi.ptr64 then 1 else typesize ty) in
          let ofs'' := if regpair && zeq ri' 7 then ofs + 1 else ofs in
          One (R r) :: rec ri'' rf ofs''
      | None =>
          (* We are out of integer registers, pass argument on stack *)
            let ofs := align ofs (typesize ty) in
            One(S Outgoing ofs ty)
            :: rec ri' rf (ofs + (if Archi.ptr64 then 2 else typesize ty))
      end
  end.

Definition split_long_arg (va: bool) (ri rf ofs: Z)
                          (rec: Z -> Z -> Z -> list (rpair loc)) :=
  let ri := if va then align ri 2 else ri in
  match list_nth_z int_param_regs ri, list_nth_z int_param_regs (ri + 1) with
  | Some r1, Some r2 =>
      Twolong (R r2) (R r1) :: rec (ri + 2) rf ofs
  | Some r1, None =>
      Twolong (S Outgoing ofs Tint) (R r1) :: rec (ri + 1) rf (ofs + 1)
  | None, _ =>
      let ofs := align ofs 2 in
      Twolong (S Outgoing (ofs + 1) Tint) (S Outgoing ofs Tint) ::
      rec ri rf (ofs + 2)
  end.

Fixpoint loc_arguments_rec
    (tyl: list typ) (fixed ri rf ofs: Z) {struct tyl} : list (rpair loc) :=
  match tyl with
  | nil => nil
  | (Tint | Tany32) as ty :: tys =>
      (* pass in one integer register or on stack *)
      int_arg ri rf ofs ty (loc_arguments_rec tys (fixed - 1))
  | Tsingle as ty :: tys =>
      (* pass in one FP register or on stack.
         If vararg, reserve 1 integer register. *)
      float_arg (zle fixed 0) ri rf ofs ty (loc_arguments_rec tys (fixed - 1))
  | Tlong as ty :: tys =>
      if Archi.ptr64 then
        (* pass in one integer register or on stack *)
        int_arg ri rf ofs ty (loc_arguments_rec tys (fixed - 1))
      else
        (* pass in register pair or on stack; align register pair if vararg *)
        split_long_arg (zle fixed 0) ri rf ofs(loc_arguments_rec tys (fixed - 1))
  | (Tfloat | Tany64) as ty :: tys =>
      (* pass in one FP register or on stack.
         If vararg, reserve 1 or 2 integer registers. *)
      float_arg (zle fixed 0) ri rf ofs ty (loc_arguments_rec tys (fixed - 1))
  end.

(** Number of fixed arguments for a function with signature [s]. *)

Definition fixed_arguments (s: signature) : Z :=
  match s.(sig_cc).(cc_vararg) with
  | Some n => n
  | None => list_length_z s.(sig_args)
  end.

(** [loc_arguments s] returns the list of locations where to store arguments
  when calling a function with signature [s].  *)

Definition loc_arguments (s: signature) : list (rpair loc) :=
  loc_arguments_rec (proj_sig_args s) (fixed_arguments s) 0 0 0.

(** Argument locations are either non-temporary registers or [Outgoing]
  stack slots at nonnegative offsets. *)

Definition loc_argument_acceptable (l: loc) : Prop :=
  match l with
  | R r => is_callee_save r = false
  | S Outgoing ofs ty => ofs >= 0 /\ (typealign ty | ofs)
  | _ => False
  end.

Lemma loc_arguments_rec_charact:
  forall va tyl ri rf ofs p,
  ofs >= 0 ->
  In p (loc_arguments_rec va tyl ri rf ofs) -> forall_rpair loc_argument_acceptable p.
Proof.
  set (OK := fun (l: list (rpair loc)) =>
             forall p, In p l -> forall_rpair loc_argument_acceptable p).
  set (OKF := fun (f: Z -> Z -> Z -> list (rpair loc)) =>
              forall ri rf ofs, ofs >= 0 -> OK (f ri rf ofs)).
  assert (CSI: forall r, In r int_param_regs -> is_callee_save r = false).
  { decide_goal. }
  assert (CSF: forall r, In r float_param_regs -> is_callee_save r = false).
  { decide_goal. }
  assert (CSFX: forall r, In r float_extra_param_regs -> is_callee_save r = false).
  { decide_goal. }
  assert (AL: forall ofs ty, ofs >= 0 -> align ofs (typesize ty) >= 0).
  { intros. 
    assert (ofs <= align ofs (typesize ty)) by (apply align_le; apply typesize_pos).
    lia. }
  assert (ALD: forall ofs ty, ofs >= 0 -> (typealign ty | align ofs (typesize ty))).
  { intros. eapply Z.divide_trans. apply typealign_typesize.
    apply align_divides. apply typesize_pos. }
  assert (SK: (if Archi.ptr64 then 2 else 1) > 0).
  { destruct Archi.ptr64; lia. }
  assert (SKK: forall ty, (if Archi.ptr64 then 2 else typesize ty) > 0).
  { intros. destruct Archi.ptr64. lia. apply typesize_pos.  }
  assert (A: forall ri rf ofs ty f,
             OKF f -> ofs >= 0 -> OK (int_arg ri rf ofs ty f)).
  { intros until f; intros OF OO; red; unfold int_arg; intros.
    destruct (list_nth_z int_param_regs ri) as [r|] eqn:NTH; destruct H.
  - subst p; simpl. apply CSI. eapply list_nth_z_in; eauto. 
  - eapply OF; eauto. 
  - subst p; simpl. auto using align_divides, typealign_pos.
  - eapply OF; [idtac|eauto].
    generalize (AL ofs ty OO) (SKK ty); lia.
  }
  assert (B: forall va ri rf ofs ty f,
             OKF f -> ofs >= 0 -> OK (float_arg va ri rf ofs ty f)).
  { intros until f; intros OF OO; red; unfold float_arg; intros.
    destruct (list_nth_z (if va then nil else float_param_regs) rf) as [r|] eqn:NTH.
  - destruct H.
    + subst p; simpl. apply CSF. destruct va. simpl in NTH; discriminate. eapply list_nth_z_in; eauto.
    + eapply OF; eauto.
  - set (regpair := negb Archi.ptr64 && zeq (typesize ty) 2) in *.
    set (ri' := if va && regpair then align ri 2 else ri) in *.
    destruct (list_nth_z float_extra_param_regs ri') as [r|] eqn:NTH'; destruct H.
    + subst p; simpl. apply CSFX. eapply list_nth_z_in; eauto.
    + eapply OF; [|eauto]. destruct (regpair && zeq ri' 7); lia.
    + subst p; simpl. auto.
    + eapply OF; [|eauto]. generalize (AL ofs ty OO) (SKK ty); lia.
  }
  assert (C: forall va ri rf ofs f,
             OKF f -> ofs >= 0 -> OK (split_long_arg va ri rf ofs f)).
  { intros until f; intros OF OO; unfold split_long_arg.
    set (ri' := if va then align ri 2 else ri).
    set (ofs' := align ofs 2).
    assert (OO': ofs' >= 0) by (apply (AL ofs Tlong); auto).
    destruct (list_nth_z int_param_regs ri') as [r1|] eqn:NTH1;
    [destruct (list_nth_z int_param_regs (ri'+1)) as [r2|] eqn:NTH2 | idtac].
  - red; simpl; intros; destruct H.
    + subst p; split; apply CSI; eauto using list_nth_z_in.
    + eapply OF; [idtac|eauto]. lia.
  - red; simpl; intros; destruct H.
    + subst p; split. split; auto using Z.divide_1_l. apply CSI; eauto using list_nth_z_in.
    + eapply OF; [idtac|eauto]. lia.
  - red; simpl; intros; destruct H.
    + subst p; repeat split; auto using Z.divide_1_l. lia. 
    + eapply OF; [idtac|eauto]. lia.
  }
  cut (forall tyl fixed ri rf ofs, ofs >= 0 -> OK (loc_arguments_rec tyl fixed ri rf ofs)).
  unfold OK. eauto.
  induction tyl as [ | ty1 tyl]; intros until ofs; intros OO; simpl.
- red; simpl; tauto.
- destruct ty1.
+ (* int *) apply A; unfold OKF; auto.
+ (* float *) apply B; unfold OKF; auto.
+ (* long *)
  destruct Archi.ptr64.
  apply A; unfold OKF; auto.
  apply C; unfold OKF; auto.
+ (* single *) apply B; unfold OKF; auto.
+ (* any32 *) apply A; unfold OKF; auto.
+ (* any64 *) apply B; unfold OKF; auto.
Qed.

Lemma loc_arguments_acceptable:
  forall (s: signature) (p: rpair loc),
  In p (loc_arguments s) -> forall_rpair loc_argument_acceptable p.
Proof.
  unfold loc_arguments; intros. eapply loc_arguments_rec_charact; eauto. lia.
Qed.

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
