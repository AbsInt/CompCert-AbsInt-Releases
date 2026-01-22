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

Require Import Coqlib Compopts.
Require Import AST Integers Floats Values Memory Globalenvs.
Require Import Op RTL ValueDomain.

(** Value analysis for Tricore operators *)

Definition eval_static_condition (cond: condition) (vl: list aval): abool :=
  match cond, vl with
  | Ccomp c, v1 :: v2 :: nil => cmp_bool c v1 v2
  | Ccompu c, v1 :: v2 :: nil => cmpu_bool c v1 v2
  | Ccompimm c n, v1 :: nil => cmp_bool c v1 (I n)
  | Ccompuimm c n, v1 :: nil => cmpu_bool c v1 (I n)
  | Ccompf c, v1 :: v2 :: nil => cmpf_bool c v1 v2
  | Cnotcompf c, v1 :: v2 :: nil => cnot (cmpf_bool c v1 v2)
  | Ccompfs c, v1 :: v2 :: nil => cmpfs_bool c v1 v2
  | Cnotcompfs c, v1 :: v2 :: nil => cnot (cmpfs_bool c v1 v2)
  | _, _ => Bnone
  end.

Definition eval_static_addressing (addr: addressing) (vl: list aval): aval :=
  match addr, vl with
  | Aindexed n, v1::nil => add v1 (I n)
  | Aglobal s ofs, nil => Ptr (Gl s ofs)
  | Ainstack ofs, nil => Ptr(Stk ofs)
  | _, _ => Vbot
  end.

Definition eval_extr (pos width: amount32) (v: aval) :=
  if Int.ltu Int.zero width && Int.eq pos Int.zero then
    sign_ext (Int.unsigned width) v
  else
    let sa := Int.sub Int.iwordsize width in
    shr (shl v (I (Int.sub sa pos))) (I sa).

Definition eval_static_operation (op: operation) (vl: list aval): aval :=
  match op, vl with
  | Omove, v1::nil => v1
  | Ointconst n, nil => I n
  | Ofloatconst n, nil => if propagate_float_constants tt then F n else ntop
  | Osingleconst n, nil => if propagate_float_constants tt then FS n else ntop
  | Oaddrsymbol id ofs, nil => Ptr (Gl id ofs)
  | Oaddrstack ofs, nil => Ptr (Stk ofs)
  | Opcast, v1::nil => Vtop
  | Oadd, v1::v2::nil => add v1 v2
  | Oaddl, v1::v2::nil => addl v1 v2
  | Oaddimm n, v1::nil => add v1 (I n)
  | Osub, v1::v2::nil => sub v1 v2
  | Osubl, v1::v2::nil => subl v1 v2
  | Orsubimm n, v1::nil => sub (I n) v1
  | Oand, v1::v2::nil => and v1 v2
  | Oandimm n, v1::nil => and v1 (I n)
  | Oandn, v1::v2::nil => and v1 (notint v2)
  | Onand, v1::v2::nil => notint (and v1 v2)
  | Onandimm n, v1::nil => notint (and v1 (I n))
  | Oneg, v1::nil => neg v1
  | Onegl, v1::nil => negl v1
  | Onor, v1::v2::nil => notint (or v1 v2)
  | Onorimm n, v1::nil => notint (or v1 (I n))
  | Onot, v1::nil => notint v1
  | Oor, v1::v2::nil => or v1 v2
  | Oorimm n, v1::nil => or v1 (I n)
  | Oorn, v1::v2::nil => or v1 (notint v2)
  | Oxnor, v1::v2::nil => notint (xor v1 v2)
  | Oxnorimm n, v1::nil => notint (xor v1 (I n))
  | Oxor, v1::v2::nil => xor v1 v2
  | Oxorimm n, v1::nil => xor v1 (I n)
  | Osl, v1::v2::nil => shl v1 v2
  | Oslimm n, v1::nil => shl v1 (I n)
  | Oasr, v1::v2::nil => shr v1 v2
  | Oasrimm n, v1::nil => shr v1 (I n)
  | Olsr, v1::v2::nil => shru v1 v2
  | Olsrimm n, v1::nil => shru v1 (I n)
  | Oshrximm n, v1::nil => shrx v1 (I n)
  | Osel c ty, v1::v2::vl => select (eval_static_condition c vl) v1 v2 ty
  | Ocadd, v1::v2::v3::nil => select (eval_static_condition (Ccompimm Cne Int.zero) (v1 :: nil)) (add v2 v3) v2 Tint
  | Ocsub, v1::v2::v3::nil => select (eval_static_condition (Ccompimm Cne Int.zero) (v1 :: nil)) (sub v2 v3) v2 Tint
  | Ocmp c, _ => of_optbool (eval_static_condition c vl)
  | Odiv, v1::v2::nil => divs v1 v2
  | Odivu, v1::v2::nil => divu v1 v2
  | Omod, v1::v2::nil => mods v1 v2
  | Omodu, v1::v2::nil => modu v1 v2
  | Oextr pos width, v1::nil => eval_extr pos width v1
  | Oextru pos width, v1::nil =>
      let sa := Int.sub Int.iwordsize width in
      shru (shl v1 (I (Int.sub sa pos))) (I sa)
  | Oinsert pos width, v1::v2::nil =>
      let
        mask := Int.shl (Int.sub (Int.repr (two_p (Int.unsigned width))) Int.one) pos
      in
      or (and v1 (I (Int.not mask))) (and (shl v2 (I pos)) (I mask))
  | Oinsertimm n pos width, v1::nil =>
      let
        mask := Int.shl (Int.sub (Int.repr (two_p (Int.unsigned width))) Int.one) pos
      in
      or (and v1 (I (Int.not mask))) (and (shl (I n) (I pos)) (I mask))
  | Omadd, v1::v2::v3::nil => add v1 (mul v2 v3)
  | Omaddimm n, v1::v2::nil => add v1 (mul v2 (I n))
  | Omsub, v1::v2::v3::nil => sub v1 (mul v2 v3)
  | Omsubimm n, v1::v2::nil => sub v1 (mul v2 (I n))
  | Omul, v1::v2::nil => mul v1 v2
  | Omulimm n, v1::nil => mul v1 (I n)
  | Omulhs, v1::v2::nil => mulhs v1 v2
  | Omulhu, v1::v2::nil => mulhu v1 v2
  | Omulu, v1::v2::nil => mull' v1 v2
  | Omakelong, v1::v2::nil => longofwords v1 v2
  | Olowlong, v1::nil => lowordoflong v1
  | Ohighlong, v1::nil => hiwordoflong v1
  | Onegf, v1::nil => negf v1
  | Oabsf, v1::nil => absf v1
  | Oaddf, v1::v2::nil => addf v1 v2
  | Osubf, v1::v2::nil => subf v1 v2
  | Omulf, v1::v2::nil => mulf v1 v2
  | Odivf, v1::v2::nil => divf v1 v2
  | Onegfs, v1::nil => negfs v1
  | Oabsfs, v1::nil => absfs v1
  | Oaddfs, v1::v2::nil => addfs v1 v2
  | Osubfs, v1::v2::nil => subfs v1 v2
  | Omulfs, v1::v2::nil => mulfs v1 v2
  | Odivfs, v1::v2::nil => divfs v1 v2
  | Osingleoffloat, v1::nil => singleoffloat v1
  | Ofloatofsingle, v1::nil => floatofsingle v1
  | Ointoffloat, v1::nil => intoffloat v1
  | Ointuoffloat, v1::nil => intuoffloat v1
  | Ofloatofint, v1::nil => floatofint v1
  | Ofloatofintu, v1::nil => floatofintu v1
  | Ointofsingle, v1::nil => intofsingle v1
  | Ointuofsingle, v1::nil => intuofsingle v1
  | Osingleofint, v1::nil => singleofint v1
  | Osingleofintu, v1::nil => singleofintu v1
  | _, _ => Vbot
  end.
Section SOUNDNESS.

Variable bc: block_classification.
Variable ge: genv.
Hypothesis GENV: genv_match bc ge.
Variable sp: block.
Hypothesis STACK: bc sp = BCstack.

Theorem eval_static_condition_sound:
  forall cond vargs m aargs,
  list_forall2 (vmatch bc) vargs aargs ->
  cmatch (eval_condition cond vargs m) (eval_static_condition cond aargs).
Proof.
  intros until aargs; intros VM.
  inv VM.
  destruct cond; auto with va.
  inv H0.
  destruct cond; simpl; eauto with va.
  inv H2.
  destruct cond; simpl; eauto with va.
  destruct cond; auto with va.
Qed.

Lemma symbol_address_sound:
  forall id ofs,
  vmatch bc (Genv.symbol_address ge id ofs) (Ptr (Gl id ofs)).
Proof.
  intros; apply symbol_address_sound; apply GENV.
Qed.

Hint Resolve symbol_address_sound: va.

Ltac InvHyps :=
  match goal with
  | [H: None = Some _ |- _ ] => discriminate
  | [H: Some _ = Some _ |- _] => inv H
  | [H1: match ?vl with nil => _ | _ :: _ => _ end = Some _ ,
     H2: list_forall2 _ ?vl _ |- _ ] => inv H2; InvHyps
  | _ => idtac
  end.

Theorem eval_static_addressing_sound:
  forall addr vargs vres aargs,
  eval_addressing ge (Vptr sp Ptrofs.zero) addr vargs = Some vres ->
  list_forall2 (vmatch bc) vargs aargs ->
  vmatch bc vres (eval_static_addressing addr aargs).
Proof.
  unfold eval_addressing, eval_static_addressing; intros;
  destruct addr; InvHyps; eauto with va.
  rewrite Ptrofs.add_zero_l; auto with va.
Qed.

Lemma pcast_sound:
  forall v x bc, vmatch bc v x -> vmatch bc (Val.pcast v) Vtop.
Proof.
  intros. destruct v; cbn; unfold Vtop; eauto with va.
  eapply vmatch_top; eassumption.
Qed.

Lemma eval_extr_sound:
  forall pos width v x,
  vmatch bc v x ->
  vmatch bc (extr (a32_amount pos) (a32_amount width) v) (eval_extr pos width x).
Proof.
  intros. unfold eval_extr, extr.
  destruct (Int.ltu Int.zero width && Int.eq pos Int.zero) eqn:?; auto with va.
  rewrite andb_true_iff in Heqb; destruct Heqb.
  rewrite (Int.same_if_eq pos Int.zero H1), Int.sub_zero_l.
  rewrite Val.sign_ext_shr_shl; auto with va.
  rewrite H0. destruct width. simpl. rewrite a32_range. auto.
Qed.

Theorem eval_static_operation_sound:
  forall op vargs m vres aargs,
  eval_operation ge (Vptr sp Ptrofs.zero) op vargs m = Some vres ->
  list_forall2 (vmatch bc) vargs aargs ->
  vmatch bc vres (eval_static_operation op aargs).
Proof.
  unfold eval_operation, extr, extru, eval_static_operation; intros;
    destruct op; InvHyps; eauto with va.
  destruct (propagate_float_constants tt); constructor.
  destruct (propagate_float_constants tt); constructor.
  rewrite Ptrofs.add_zero_l; eauto with va.
  apply (pcast_sound a1 b1); auto.
  apply select_sound; auto. eapply eval_static_condition_sound; eauto.
  apply select_sound; auto with va.
  exploit (eval_static_condition_sound (Ccompimm Cne Int.zero) (a1 :: nil) m).
  econstructor; eauto. econstructor. simpl. auto.
  apply select_sound; auto with va.
  exploit (eval_static_condition_sound (Ccompimm Cne Int.zero) (a1 :: nil) m).
  econstructor; eauto. econstructor. simpl. auto.
  apply of_optbool_sound. eapply eval_static_condition_sound; eauto.
  eapply eval_extr_sound; eauto with va.
  apply or_sound; eauto with va. simpl. apply and_sound; eauto with va.
  apply or_sound; eauto with va. simpl. apply and_sound; eauto with va.
  fold (Val.sub (Vint n) a1). auto with va.
Qed.

End SOUNDNESS.
