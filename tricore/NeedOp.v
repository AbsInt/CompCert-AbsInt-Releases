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

Require Import Coqlib.
Require Import AST Integers Floats.
Require Import Values Memory Globalenvs.
Require Import Op RTL.
Require Import NeedDomain.

(** Neededness analysis for TriCore operators *)

Definition op1 (nv: nval) := nv :: nil.
Definition op2 (nv: nval) := nv :: nv :: nil.
Definition op3 (nv: nval) := nv :: nv :: nv :: nil.

Definition needs_of_condition (cond: condition): list nval := nil.

Definition needs_of_operation (op: operation) (nv: nval): list nval :=
  match op with
  | Omove => op1 nv
  | Ointconst n => nil
  | Ofloatconst n => nil
  | Osingleconst n => nil
  | Oaddrsymbol id ofs => nil
  | Oaddrstack ofs => nil

  | Oadd => op2 (modarith nv)
  | Oaddimm n => op1 (modarith nv)
  | Osub => op2 (default nv)
  | Orsubimm n => op1 (default nv)

  | Oand => op2 (bitwise nv)
  | Oandimm n => op1 (andimm nv n)
  | Oandn => op2 (bitwise nv)
  | Onand => op2 (bitwise nv)
  | Onandimm n => op1 (andimm nv n)
  | Oneg => op1 (modarith nv)
  | Onor => op2 (bitwise nv)
  | Onorimm n => op1 (orimm nv n)
  | Onot => op1 (bitwise nv)
  | Oor => op2 (bitwise nv)
  | Oorimm n => op1 (orimm nv n)
  | Oorn => op2 (bitwise nv)
  | Oxnor => op2 (bitwise nv)
  | Oxnorimm n => op1 (bitwise nv)
  | Oxor => op2 (bitwise nv)
  | Oxorimm n => op1 (bitwise nv)

  | Osl => op2 (default nv)
  | Oslimm n => op1 (shlimm nv n)
  | Oasr => op2 (default nv)
  | Oasrimm n => op1 (shrimm nv n)
  | Olsr => op2 (default nv)
  | Olsrimm n => op1 (shruimm nv n)
  | Oshrximm n => op1 (default nv)

  | Ocmp c => needs_of_condition c
  | Osel c ty => nv :: nv :: needs_of_condition c

  | Odiv | Odivu | Omod | Omodu => op2 (default nv)

  | Oextr _ _ => op1 (default nv)
  | Oextru _ _ => op1 (default nv)
  | Oinsert _ _ => op2 (default nv)
  | Oinsertimm _ _ _ => op1 (default nv)

  | Omadd => op3 (default nv)
  | Omaddimm _ => op2 (default nv)
  | Omsub => op3 (default nv)
  | Omsubimm _ => op2 (default nv)
  | Omul => op2 (modarith nv)
  | Omulimm n => op1 (modarith nv)
  | Omulhs | Omulhu => op2 (default nv)

  | Omakelong => op2 (default nv)
  | Olowlong | Ohighlong => op1 (default nv)


  | Onegf | Oabsf => op1 (default nv)
  | Oaddf | Osubf | Omulf | Odivf => op2 (default nv)
  | Onegfs | Oabsfs => op1 (default nv)
  | Oaddfs | Osubfs | Omulfs | Odivfs => op2 (default nv)
  | Ofloatofsingle | Osingleoffloat => op1 (default nv)
  | Ointoffloat | Ointuoffloat | Ofloatofint | Ofloatofintu => op1 (default nv)
  | Ointofsingle | Ointuofsingle | Osingleofint | Osingleofintu => op1 (default nv)
  end.

Definition operation_is_redundant (op: operation) (nv: nval): bool :=
  match op with
  | Oandimm n => andimm_redundant nv n
  | Oorimm n => orimm_redundant nv n
  | _ => false
  end.

Ltac InvAgree :=
  match goal with
  | [H: vagree_list nil _ _ |- _ ] => inv H; InvAgree
  | [H: vagree_list (_::_) _ _ |- _ ] => inv H; InvAgree
  | _ => idtac
  end.

Ltac TrivialExists :=
  match goal with
  | [ |- exists v, Some ?x = Some v /\ _ ] => exists x; split; auto
  | _ => idtac
  end.


Section SOUNDNESS.

Variable ge: genv.
Variable sp: block.
Variables m m': mem.
Hypothesis PERM: forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p.

Lemma needs_of_condition_sound:
  forall cond args b args',
  eval_condition cond args m = Some b ->
  vagree_list args args' (needs_of_condition cond) ->
  eval_condition cond args' m' = Some b.
Proof.
  intros. unfold needs_of_condition in H0.
  eapply default_needs_of_condition_sound; eauto.
Qed.

Lemma needs_of_operation_sound:
  forall op args v nv args',
  eval_operation ge (Vptr sp Ptrofs.zero) op args m = Some v ->
  vagree_list args args' (needs_of_operation op nv) ->
  nv <> Nothing ->
  exists v',
     eval_operation ge (Vptr sp Ptrofs.zero) op args' m' = Some v'
  /\ vagree v v' nv.
Proof.
  unfold needs_of_operation; intros; destruct op; try (eapply default_needs_of_operation_sound; eauto; fail);
  simpl in *; FuncInv; InvAgree; TrivialExists.
- apply add_sound; auto.
- apply add_sound; auto with na.
- apply and_sound; auto with na.
- apply andimm_sound; auto.
- apply and_sound; auto. apply notint_sound; auto.
- destruct (eval_condition c args m) as [b|] eqn:EC.
  erewrite needs_of_condition_sound by eauto.
  apply select_sound; auto.
  simpl; auto with na.
- apply mul_sound; auto.
- apply mul_sound; auto with va. apply vagree_same.
- apply notint_sound, and_sound; auto.
- apply notint_sound, andimm_sound; auto.
- apply neg_sound; auto.
- apply notint_sound, or_sound; auto.
- apply notint_sound, orimm_sound; auto.
- apply notint_sound; auto.
- apply or_sound; auto.
- apply orimm_sound; auto.
- apply or_sound, notint_sound; auto.
- apply shlimm_sound; auto.
- apply shrimm_sound; auto.
- apply shruimm_sound; auto.
- apply notint_sound, xor_sound; auto.
- apply notint_sound, xor_sound; auto. apply vagree_same.
- apply xor_sound; auto.
- apply xor_sound; auto. apply vagree_same.
Qed.

Lemma operation_is_redundant_sound:
  forall op nv arg1 args v arg1' args',
  operation_is_redundant op nv = true ->
  eval_operation ge (Vptr sp Ptrofs.zero) op (arg1 :: args) m = Some v ->
  vagree_list (arg1 :: args) (arg1' :: args') (needs_of_operation op nv) ->
  vagree v arg1' nv.
Proof.
  intros. destruct op; simpl in *; try discriminate; inv H1; FuncInv; subst.
- apply andimm_redundant_sound; auto.
- apply orimm_redundant_sound; auto.
Qed.

End SOUNDNESS.
