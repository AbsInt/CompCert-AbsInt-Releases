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
Require Import Conventions0.
Require Archi.

(** * Classification of machine registers *)

(** Machine registers (type [mreg] in module [Machregs]) are divided in
  the following groups:
- Caller-save registers that can be modified during a function call.
    Caller-save registers are also said to be part of the lower context.
- Auto-save registers, whose value is automatically stored in memory when executing 
    a `call` instruction, and restored when executing a `ret` instruction.
    Auto-save registers are also said to be part of the upper context.

  We follow the TriCore embedded application binary interface (EABI) in our choice
  of caller- and auto-save registers. No registers are designated as callee-save by the EABI.
*)

Module CC.
  (* Upper context registers include the data registers D[8]-D[15] and address registers A[10]-A[15].
     On the mreg type we do not model all of those registers since they serve special functions and should not be allocated.
     Concretely, A[10] is the stack register, A[11] holds the return address and A[14] holds temporary values. *)
  Definition reg_cc (r: mreg): RegCC :=
    match r with
    | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15 => RCAuto
    | P12 | P13 | P14 | P15 => RCAuto
    | _ => RCCaller
    end.
End CC.

Module RegCC := Conventions0.Make(CC).
Include RegCC.

(* TriCore does not have callee-saved registers. *)
Lemma regcc_not_callee:
  forall r,
  reg_cc r = RCCallee -> False.
Proof.
  intros. destruct r; simpl in H; discriminate.
Qed.

Definition callee_save_type (r: mreg): typ :=
  match r with
  | ErrorReg => Tany64
  | _ => Tany32
  end.

Definition is_float_reg (r: mreg): bool := false.

Definition is_addr_reg (r:mreg): bool :=
  match r with
  | P2 | P4 | P5 | P6 | P7 | P12 | P13 | P14 | P15 => true
  | _ => false end. 

Definition int_lower_ctx_regs : list mreg :=
  R1 :: R2 :: R3  :: R4  :: R5  :: R6  :: R7 :: nil.

Definition int_upper_ctx_regs : list mreg :=
  R8 :: R9 :: R10 :: R11 :: R12 :: R13 :: R14 :: R15 :: nil.

Definition ptr_lower_ctx_regs : list mreg := 
  P2 :: P4 :: P5 :: P6 :: P7 :: nil.

Definition ptr_upper_ctx_regs : list mreg := 
  P12 :: P13 :: P14 :: P15 :: nil.

(* As defined by the EABI there are no callee-save registers at all. *)
Definition int_callee_save_regs : list mreg := nil.
Definition ptr_callee_save_regs : list mreg := nil.

Definition dummy_regs := R4 :: P2 :: nil. (**r Used in [Coloring]. *)

(** How to use registers for register allocation.
    In other architectures, only callee-save registers are assigned to the remaining_regs field in order to use them as a second choice, if no caller-save registers are available.
    To be consistent with other architectures, we therefore treat both the upper and lower context as a preferred choice for allocation. *)

(* The lists need to coincide with the order of the register classes
        Including the empty class of forced stack_allocation! *)
Record alloc_regs := mk_alloc_regs {
  preferred_regs: list (list mreg);
  remaining_regs: list (list mreg)
}.

Definition allocatable_registers (_: unit) :=
  {| preferred_regs := (int_upper_ctx_regs ++ int_lower_ctx_regs) :: (ptr_upper_ctx_regs ++ ptr_lower_ctx_regs) :: nil :: nil;
     remaining_regs := int_callee_save_regs :: ptr_callee_save_regs :: nil :: nil|}.

(* Size of the area where auto-save registers are saved. *)
Definition csa_size: Z := 64.

Lemma csa_size_no_overflow :
  csa_size <= Integers.Ptrofs.modulus.
Proof.
  unfold csa_size.
  let x := fresh in set Integers.Ptrofs.modulus as x in *; vm_compute in x; subst x. lia.
Qed.

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
  compiler with libraries compiled by another Tricore compiler, we
  implement the standard conventions defined in the Tricore/EABI
  application binary interface. *)

(** ** Location of function result *)

(** The result value of a function is passed back to the caller in
  registers [R2] or [R2, R3], depending on the type of the returned value.
  We treat a function without result as a function with one integer result.
 *)

Definition loc_result (s: signature) : rpair mreg :=
  match s.(sig_res) with
  | Xbool | Xint8signed | Xint8unsigned | Xint16signed | Xint16unsigned | Xvoid| Xint | Xany32 | Xsingle => One R2
  | Xptr => One P2
  | Xfloat | Xany64 => One ErrorReg
  | Xlong => Two R3 R2
  end.

(** The result registers have types compatible with that given in the signature. *)

Lemma loc_result_type:
  forall sig,
  subtype (proj_sig_res sig) (mreg_pair_type (loc_result sig)) = true.
Proof.
  intros. unfold loc_result, mreg_type, proj_sig_res.
  destruct (sig_res sig) eqn:?; simpl; auto.
Qed.

(** The result locations are caller-save registers *)

Lemma loc_result_caller_save:
  forall (s: signature),
  forall_rpair (fun r => is_caller_save r = true) (loc_result s).
Proof.
  intros. unfold loc_result, is_caller_save;
  destruct (sig_res s), (proj_sig_res s); try  destruct t; simpl; auto.
Qed.

(** If the result is in a pair of registers, those registers are distinct and have type [Tint] at least. *)

Lemma loc_result_pair:
  forall sg,
  match loc_result sg with
  | One _ => True
  | Two r1 r2 =>
        r1 <> r2 /\ proj_sig_res sg = Tlong
     /\ subtype Tint (mreg_type r1) = true /\ subtype Tint (mreg_type r2) = true
     /\ Archi.ptr64 = false
  end.
Proof.
  intros; unfold loc_result, mreg_type, proj_sig_res.
  destruct (sig_res sg) eqn:?; try destruct t; simpl; auto.
  split; auto. congruence.
Qed.


(** The location of the result depends only on the result part of the signature *)

Lemma loc_result_exten:
  forall s1 s2, s1.(sig_res) = s2.(sig_res) -> loc_result s1 = loc_result s2.
Proof.
  intros. unfold loc_result, proj_sig_res.
  destruct (sig_res s1), (sig_res s2); inv H; auto.
Qed.

(** ** Location of function arguments *)

(**
   - None pointer arguments are passed in registers [D4...D7]
   - Pointer arguments are passed in registers [A4...A7]

  Arguments that are larger than 64 bits are passed via stack.
  64 bit arguments are passed in aligned registers, e.g. D4,
  D5 or D6 and D7. If D5 is not used first due to a 64 bit
  argument then it can be used for a later 32 bit argument.
  For example WORD, DWORD, WORD are passed D4, D6/D7 and D5.

  Arguments on the stack are either WORD or DWORD aligned.
  Non fixed varargs are also passed on the stack.
*)

Definition param_regs :=
  R4 :: R5 :: R6 :: R7 :: nil.

Definition ptr_param_regs :=
  P4 :: P5 :: P6 :: P7 :: nil.

(** [lookup_register l r5_skipped fixed r] returns  the register at position r
    from the param registers list, if [r5_skipped] is true the register R5 was
    skipped due to the constraint that 64 bit arguments should be passed in
    either R4/R5 or R6/R7. *)
Definition lookup_register l (r5_skipped: bool)  r : option mreg :=
  if r5_skipped then
    list_nth_z l 1
  else
    list_nth_z l r.

Definition stack_arg (ty: xtype) (r5_skipped : bool) (r p ofs: Z)
                     (rec: bool -> Z -> Z -> Z -> list (rpair loc)) :=
  let arg :=
    if typ_eq (proj_xtype_typ ty) Tlong then
      Two (S Outgoing (ofs + 1) Tint) (S Outgoing ofs Tint)
    else
      One (S Outgoing ofs (proj_xtype_typ ty)) in
  arg :: rec r5_skipped r p (ofs + typesize (proj_xtype_typ ty)).

Fixpoint loc_arguments_stack (tyl: list xtype) (ofs: Z) {struct tyl} : list (rpair loc) :=
  match tyl with
  | nil => nil
  | ty :: tys =>
      stack_arg ty false 0 0 ofs (fun r5 r p ofs => loc_arguments_stack tys ofs)
  end.

Definition simple_arg (ty: xtype) (r5_skipped: bool) (r p ofs: Z)
                      (rec: bool -> Z -> Z -> Z -> list (rpair loc)) :=
  match lookup_register param_regs r5_skipped r  with
  | None =>
      stack_arg ty false r p ofs rec
  | Some ireg =>
      One (R ireg) :: rec false (r + 1) p ofs
  end.

Definition ptr_arg (r5_skipped : bool) (r p ofs: Z)
                   (rec: bool -> Z -> Z -> Z -> list (rpair loc)) :=
  match list_nth_z ptr_param_regs p with
  | None =>
      stack_arg Xptr r5_skipped r p ofs rec
  | Some areg =>
      One (R areg) :: rec r5_skipped r (p + 1) ofs
  end.

Definition long_arg (r5_skipped: bool) (r p ofs: Z)
                    (rec: bool -> Z -> Z -> Z -> list (rpair loc)) :=
  let r' := align r 2 in
  match list_nth_z param_regs r',  list_nth_z param_regs (r' + 1) with
  | Some r1, Some r2 =>
      Two (R r2) (R r1) :: rec (zeq r 1) (r' + 2) p ofs
  | _, _ =>
      stack_arg Xlong r5_skipped r p ofs rec
  end.

(** [loc_arguments_rec tyl r5_skipped fixed r ofs] computes the location of the current
    argument based upon the type in [tyl]. [r] is the next free data register, [p] is 
    the next free address register, and [ofs] is the stack offset. 
    [fixed] is the number of non vararg arguments that are not used.
    [r5_skipped] is only true if we are in the case that R5 is skipped due to a 64 bit
    argument, then the next 32 bit argument is placed R5. *)
Fixpoint loc_arguments_rec
  (tyl: list xtype) (fixed: Z) (r5_skipped: bool) (r p ofs: Z) {struct tyl} : list (rpair loc) :=
  match tyl with
  | nil => nil
  | ty :: tys =>
      if (zle fixed 0) then loc_arguments_stack tyl ofs else
        match ty with
        | Xptr  => ptr_arg r5_skipped r p ofs (loc_arguments_rec tys (fixed - 1))
        | (Xvoid | Xbool | Xint8signed | Xint8unsigned | Xint16signed | Xint16unsigned | Xint | Xany32 | Xsingle) as ty => simple_arg ty r5_skipped r p ofs (loc_arguments_rec tys (fixed - 1))
        | (Xfloat | Xany64) as ty =>
            stack_arg ty r5_skipped r p ofs (loc_arguments_rec tys (fixed - 1))
        | Xlong => long_arg r5_skipped r p ofs (loc_arguments_rec tys (fixed - 1))
        end
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
  loc_arguments_rec s.(sig_args) (fixed_arguments s) false 0 0 0.


(** Argument locations are either non-temporary registers or [Outgoing]
  stack slots at nonnegative offsets. *)


Definition loc_argument_acceptable (l: loc) : Prop :=
  match l with
  | R r => is_caller_save r = true
  | S Outgoing ofs ty => ofs >= 0 /\ (typealign ty | ofs)
  | _ => False
  end.

Remark lookup_register_in:
  forall l r5_skipped r x,
    lookup_register l r5_skipped r = Some x -> In x l.
Proof.
  unfold lookup_register; intros.
  destruct r5_skipped; try discriminate H.
  eapply list_nth_z_in; eauto.
  eapply list_nth_z_in; eauto.
Qed.

Remark loc_arguments_rec_acceptable:
  forall tyl r5_skipped fixed r ofs rp p,
  ofs >= 0 ->
  In p (loc_arguments_rec tyl fixed r5_skipped r rp ofs) ->
  forall_rpair loc_argument_acceptable p.
Proof.
  set (OK := fun (l: list (rpair loc)) =>
               forall p, In p l -> forall_rpair loc_argument_acceptable p).
  set (OKF := fun (f: bool -> Z ->  Z -> Z -> list (rpair loc)) =>
                forall r5 r p ofs, ofs >= 0 -> OK (f r5 r p ofs)).
  assert (CSI: forall r, In r param_regs -> is_caller_save r = true).
  { decide_goal. }
  assert (CSP: forall r, In r ptr_param_regs -> is_caller_save r = true).
  { decide_goal. }
  assert (STK: forall tyl ofs,
               ofs >= 0 -> OK (loc_arguments_stack tyl ofs)).
  { induction tyl as [ | ty tyl]; intros ofs OO; red; simpl; intros.
  - contradiction.
  - destruct (typ_eq (proj_xtype_typ ty) Tlong).
    + destruct H.
      * subst p. split; split; try lia; simpl; apply Z.divide_1_l.
      * unfold typesize in H. rewrite e in H. apply IHtyl with (ofs := ofs + typesize Tlong).
        cbn. lia. auto.
    + destruct H.
      * subst p. split. lia. destruct (proj_xtype_typ ty) eqn:E; cbn; auto with divide.
      * apply IHtyl with (ofs := ofs + typesize (proj_xtype_typ ty)).
        destruct (proj_xtype_typ); simpl; lia. auto.
  }
  assert (A : forall ty r5 r p ofs f,
           OKF f -> ofs >= 0 -> OK (stack_arg ty r5 r p ofs f)).
  { intros until f; intros OF OO; red; unfold stack_arg; intros.
    destruct H.
    - subst p0; simpl; auto. destruct typ_eq; auto.
      split; split; try lia; simpl; apply Z.divide_1_l.
      split. lia. destruct proj_xtype_typ; try contradiction; apply Z.divide_1_l.
    - eapply OF; [|eauto]. generalize (typesize_pos (proj_xtype_typ ty)). lia.
  }
  assert (B: forall ty r5 r p ofs f,
           OKF f -> ofs >= 0 -> OK (simple_arg ty r5 r p ofs f)).
  { intros until f; intros OF OO; red; unfold simple_arg; intros.
    destruct (lookup_register param_regs r5 r) as [r'|] eqn:NTH; [destruct H|].
    - subst p0; simpl. apply CSI. eapply lookup_register_in; eauto.
    - eapply OF; eauto.
    - eapply A; eauto.
  }
  assert (C: forall r5 r p ofs f,
         OKF f -> ofs >= 0 -> OK (ptr_arg r5 r p ofs f)).
  { intros until f; intros OF OO; red; unfold ptr_arg; intros.
    destruct (list_nth_z ptr_param_regs p) as [p'|] eqn:NTH; [destruct H|].
    - subst p0; simpl. apply CSP. eapply list_nth_z_in; eauto.
    - eapply OF; eauto.
    - eapply A; eauto.
  }
  assert (D: forall r5 r p ofs f,
         OKF f -> ofs >= 0 -> OK (long_arg r5 r p ofs f)).
  { intros until f; intros OF OO; red; unfold long_arg; intros.
    set (r' := align r 2) in *.
    destruct (list_nth_z param_regs r') as [r1|] eqn:NTH1; destruct (list_nth_z param_regs (r' + 1)) as [r2|] eqn:NTH2.
    - destruct H. subst p0; simpl. split; apply CSI; eapply list_nth_z_in; eauto.
      eapply OF; eauto.
    - destruct H. subst p0; simpl. split; split; try lia; apply Z.divide_1_l.
      simpl in H. eapply OF with (ofs := (ofs + 2)); eauto. lia.
    - eapply A; eauto.
    - eapply A; eauto.
  }
  cut (forall tyl fixed r5 r p ofs, ofs >= 0 -> OK (loc_arguments_rec tyl r5 fixed r p ofs)).
  unfold OK. eauto.
  induction tyl as [| ty1 tyl]; intros until ofs; intros OO; simpl.
  - red; simpl; tauto.
  - destruct (zle r5 0).
    + apply (STK (ty1 :: tyl)); auto.
    + unfold OKF in *; destruct ty1; try destruct t; eauto.
Qed.

Lemma loc_arguments_acceptable:
  forall (s: signature) (p: rpair loc),
  In p (loc_arguments s) -> forall_rpair loc_argument_acceptable p.
Proof.
  unfold loc_arguments; intros.
  eapply loc_arguments_rec_acceptable; eauto. lia.
Qed.

Global Hint Resolve loc_arguments_acceptable: locs.

Lemma loc_arguments_main:
  loc_arguments signature_main = nil.
Proof.
  reflexivity.
Qed.

(** ** Normalization of function results *)

(** No normalization needed. *)

Definition return_value_needs_normalization (t: xtype) := false.
Definition parameter_needs_normalization (t: xtype) :=
  match t with
  | Xbool | Xint8signed | Xint8unsigned | Xint16signed | Xint16unsigned => true
  | _ => false
  end.
