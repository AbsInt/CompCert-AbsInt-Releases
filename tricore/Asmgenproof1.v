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

(** Correctness proof for TriCore generation: auxiliary results. *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Zbits.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import Mach.
Require Import Compopts.
Require Import Asm.
Require Import Asmgen.
Require Import Conventions.
Require Import Asmgenproof0.

Local Transparent Archi.ptr64.

(** * Properties of low half/high half decomposition *)

Lemma shru_zero_ext:
  forall n, u_amount 16 (mk_uconst16 (Int.shru n (Int.repr 16))) = Int.shru n (Int.repr 16).
Proof.
  intros. simpl. apply Int.same_bits_eq. intros.
  rewrite Int.bits_zero_ext ; try lia. rewrite Int.bits_shru; try lia.
  destruct (zlt i 16). reflexivity. rewrite Int.unsigned_repr.
  change Int.zwordsize with 32. destruct (zlt (i + 16) 32); try lia.
  unfold Int.max_unsigned. simpl. lia.
Qed.

Lemma low_high_s:
  forall n, Int.add (Int.shl (high_s n) (Int.repr 16)) (low_s n) = n.
Proof.
  intros.
  rewrite Int.shl_mul_two_p.
  unfold high_s. rewrite shru_zero_ext.
  rewrite <- (Int.divu_pow2 (Int.sub n (low_s n)) (Int.repr 65536) (Int.repr 16)).
  2: reflexivity.
  change (two_p (Int.unsigned (Int.repr 16))) with 65536.
  set (x := Int.sub n (low_s n)).
  assert (x = Int.add (Int.mul (Int.divu x (Int.repr 65536)) (Int.repr 65536))
                      (Int.modu x (Int.repr 65536))).
    apply Int.modu_divu_Euclid. vm_compute; congruence.
  assert (Int.modu x (Int.repr 65536) = Int.zero).
    unfold Int.modu, Int.zero. decEq.
    change 0 with (0 mod 65536).
    change (Int.unsigned (Int.repr 65536)) with 65536.
    apply eqmod_mod_eq. lia.
    unfold x, low_s. eapply eqmod_trans.
    apply  eqmod_divides with Int.modulus.
    unfold Int.sub. apply Int.eqm_unsigned_repr_l. apply Int.eqm_refl.
    exists 65536. compute; auto.
    replace 0 with (Int.unsigned n - Int.unsigned n) by lia.
    apply eqmod_sub. apply eqmod_refl. apply Int.eqmod_sign_ext'.
    compute; auto.
  rewrite H0 in H. rewrite Int.add_zero in H.
  rewrite <- H. unfold x. rewrite Int.sub_add_opp. rewrite Int.add_assoc.
  rewrite (Int.add_commut (Int.neg (low_s n))). rewrite <- Int.sub_add_opp.
  rewrite Int.sub_idem. apply Int.add_zero.
Qed.

(** * Properties of the constant functions *)

Lemma get_uconst4_sound:
  forall n x, get_uconst4 n = Some x ->
    u_amount 4 x = n.
Proof.
  intros. unfold get_uconst4 in H.
  destruct (Int.ltu n (Int.repr 16)) eqn:?; inv H.
  apply Int.zero_ext_range_eq; auto.
Qed.

Lemma get_uconst9_sound:
  forall n x, get_uconst9 n = Some x ->
    u_amount 9 x = n.
Proof.
  intros. unfold get_uconst9 in H.
  destruct (Int.ltu n (Int.repr (two_p 9))) eqn:?; inv H.
  apply Int.zero_ext_range_eq; auto.
Qed.

Lemma get_sconst4_sound:
  forall n x, get_sconst4 n = Some x ->
    s_amount 4 x = n.
Proof.
  intros. unfold get_sconst4 in H.
  destruct (is_in_signed_range 4 n) eqn:?; inv H.
  apply Int.sign_ext_range_eq; auto.
Qed.

Lemma get_sconst9_sound:
  forall n x, get_sconst9 n = Some x ->
    s_amount 9 x = n.
Proof.
  intros. unfold get_sconst9 in H.
  destruct (is_in_signed_range 9 n) eqn:?; inv H.
  apply Int.sign_ext_range_eq; auto.
Qed.

Lemma get_sconst16_sound:
  forall n x, get_sconst16 n = Some x ->
    s_amount 16 x = n.
Proof.
  intros. unfold get_sconst16 in H.
  destruct (is_in_signed_range 16 n) eqn:?; inv H.
  apply Int.sign_ext_range_eq; auto.
Qed.

(** Properties of registers *)

Lemma ireg_of_not_TMP:
  forall m r, ireg_of m = OK r -> DREG r <> TMP.
Proof.
  intros. erewrite <- ireg_of_eq; eauto with asmgen.
Qed.

Lemma ireg_of_not_TMP':
  forall m r, ireg_of m = OK r -> r <> TMP.
Proof.
  intros. apply ireg_of_not_TMP in H. congruence.
Qed.

Lemma data_preg_not_TMP:
  forall r, data_preg r = true -> r <> TMP.
Proof.
  unfold data_preg. intros. destruct r; try congruence.
  destruct r; congruence.
Qed.

Lemma data_preg_not_PC:
  forall r, data_preg r = true -> r <> PC.
Proof.
  unfold data_preg. intros. destruct r; congruence.
Qed.

Global Hint Resolve ireg_of_not_TMP ireg_of_not_TMP' data_preg_not_TMP data_preg_not_PC: asmgen.

(** Useful simplification tactic *)

Ltac Simplif :=
  ((rewrite nextinstr_inv by eauto with asmgen)
  || (rewrite nextinstr_inv1 by eauto with asmgen)
  || (rewrite Pregmap.gss)
  || (rewrite nextinstr_pc)
  || (rewrite Pregmap.gso by eauto with asmgen)); auto with asmgen.

Ltac Simpl := repeat Simplif.

(** * Correctness of TriCore constructor functions *)

Section CONSTRUCTORS.

Variable ge: genv.
Variable fn: function.


(** Move between registers. *)

Lemma move_rr_correct:
  forall rd r k rs m,
  exists rs',
     exec_straight_opt ge fn (move_rr rd r k) rs m  k rs' m
  /\ rs'#rd = rs#r
  /\ forall r': preg, r' <> rd -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold move_rr.
  destruct (dreg_eq rd r).
  exists rs. split. econstructor. rewrite e. intuition Simpl.
  exists (nextinstr (rs#rd <- (rs#r))). split. econstructor.
  apply exec_straight_one; simpl; eauto. intuition Simpl.
Qed.

Lemma loadimm_correct:
 forall rd n k rs m,
  exists rs',
     exec_straight ge fn (loadimm rd n k) rs m k rs' m
  /\ rs'#rd = Vint n
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  unfold loadimm; intros.
  predSpec Int.eq Int.eq_spec (high_s n) Int.zero;
    [|predSpec Int.eq Int.eq_spec (low_s n) Int.zero].
  - (* movi *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl. f_equal.
    rewrite <- low_high_s, H, Int.add_zero_l.
    reflexivity.
  - (* movh *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl. f_equal.
    rewrite <- low_high_s, H0, Int.add_zero. reflexivity.
  - (* movh + addi *)
    econstructor; split. eapply exec_straight_two; simpl; eauto.
    split; intuition Simpl. simpl. f_equal.
    rewrite <- low_high_s. reflexivity.
Qed.

(* Lemma to show that encoding selection is correct *)
Lemma select_encoding_instr_correct:
  forall (instr1: dreg -> dreg -> instruction)
    (instr2: dreg -> dreg -> dreg -> instruction)
    (sem: val -> val -> val)
    commut rd r1 r2 k rs m,
  (forall v1 v2, commut = true -> sem v1 v2 = sem v2 v1) ->
  (forall rd r1 rs m,
    exec_instr ge fn (instr1 rd r1) rs m =
    Next (nextinstr (rs#rd <- (sem rs#rd rs#r1))) m) ->
  (forall rd r1 r2 rs m,
    exec_instr ge fn (instr2 rd r1 r2) rs m =
    Next (nextinstr (rs#rd <- (sem rs#r1 rs#r2))) m) ->
  exists rs',
    exec_straight ge fn (select_encoding_instr instr1 instr2 commut rd r1 r2 k) rs m k rs' m
  /\ rs'#rd = sem rs#r1 rs#r2
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  intros. unfold select_encoding_instr.
  assert (BASE: exists rs',
           exec_straight ge fn (instr2 rd r1 r2 :: k) rs m k rs' m
           /\ rs'#rd = sem (rs r1) (rs r2)
           /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r).
  { econstructor. split. apply exec_straight_one. apply H1. Simpl. split; intuition Simpl. }
  destruct (dreg_eq rd r1).
  rewrite e. econstructor; split. eapply exec_straight_one; simpl; eauto. split; intuition Simpl.
  destruct commut, (dreg_eq rd r2); eauto.
  simpl. econstructor; split. apply exec_straight_one; simpl; eauto.
  rewrite e, H; eauto. split; intuition Simpl.
Qed.

Lemma add_correct:
  forall rd r1 r2 k rs m,
  exists rs',
  exec_straight ge fn (add rd r1 r2 k) rs m k rs' m
  /\ rs'#rd = Val.add (rs#r1) (rs#r2)
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  intros. unfold add. apply select_encoding_instr_correct; intros; try reflexivity.
  apply Val.add_commut.
Qed.

Lemma sub_correct:
  forall rd r1 r2 k rs m,
  exists rs',
  exec_straight ge fn (sub rd r1 r2 k) rs m k rs' m
  /\ rs'#rd = Val.sub (rs#r1) (rs#r2)
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  intros. unfold add. apply select_encoding_instr_correct; intros; try reflexivity.
  inv H.
Qed.

Lemma mul_correct:
  forall rd r1 r2 k rs m,
  exists rs',
  exec_straight ge fn (mul rd r1 r2 k) rs m k rs' m
  /\ rs'#rd = Val.mul (rs#r1) (rs#r2)
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  intros. unfold mul. apply select_encoding_instr_correct; intros; try reflexivity.
  apply Val.mul_commut.
Qed.

Lemma and_correct:
  forall rd r1 r2 k rs m,
  exists rs',
  exec_straight ge fn (and rd r1 r2 k) rs m k rs' m
  /\ rs'#rd = Val.and (rs#r1) (rs#r2)
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  intros. unfold and. apply select_encoding_instr_correct; intros; try reflexivity.
  apply Val.and_commut.
Qed.

Lemma or_correct:
  forall rd r1 r2 k rs m,
  exists rs',
  exec_straight ge fn (or rd r1 r2 k) rs m k rs' m
  /\ rs'#rd = Val.or (rs#r1) (rs#r2)
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  intros. unfold or. apply select_encoding_instr_correct; intros; try reflexivity.
  apply Val.or_commut.
Qed.

Lemma xor_correct:
  forall rd r1 r2 k rs m,
  exists rs',
  exec_straight ge fn (xor rd r1 r2 k) rs m k rs' m
  /\ rs'#rd = Val.xor (rs#r1) (rs#r2)
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  intros. unfold xor. apply select_encoding_instr_correct; intros; try reflexivity.
  apply Val.xor_commut.
Qed.

Lemma addimm_correct:
  forall (rd r : dreg) n k rs m,
  r <> TMP ->
  exists rs',
    exec_straight ge fn (addimm rd r n k) rs m k rs' m
  /\ rs'#rd = Val.add (rs#r) (Vint n)
  /\ forall r': preg, r' <> PC -> r' <> TMP -> r' <> rd -> rs'#r' = rs#r'.
Proof.
  intros. unfold addimm, addimm_gen.
  destruct (dreg_eq rd r && is_in_signed_range 4 n) eqn:cond;
    [|clear cond; predSpec Int.eq Int.eq_spec (high_s n) Int.zero;
    [|clear H0; predSpec Int.eq Int.eq_spec (low_s n) Int.zero]].
  - (* add_sc4 *)
    rewrite andb_true_iff in cond. destruct cond as (reg_eq, range).
    replace rd with r  by (destruct rd, r; try inv reg_eq; try reflexivity).
    econstructor. split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl. rewrite Int.sign_ext_range_eq; auto.
  - (* addi *)
    econstructor.  split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl. do 2 f_equal. rewrite <- low_high_s.
    rewrite H0, Int.add_zero_l. reflexivity.
  - (* addih *)
    econstructor.  split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl. do 2 f_equal. rewrite <- low_high_s.
    rewrite H0, Int.add_zero. reflexivity.
  - (* loadimm + add *)
    Local Opaque high_s low_s.
    econstructor; split. eapply exec_straight_two; simpl; eauto.
    split; intuition Simpl.
    rewrite Val.add_assoc. simpl. rewrite low_high_s. reflexivity.
Qed.

Lemma rsubimm_correct:
  forall (rd r : dreg) n k rs m,
  r <> TMP ->
  exists rs',
    exec_straight ge fn (rsubimm rd r n k) rs m k rs' m
  /\ rs'#rd = Val.sub (Vint n) (rs#r)
  /\ forall r': preg, r' <> PC -> r' <> TMP -> r' <> rd -> rs'#r' = rs#r'.
Proof.
  intros. unfold rsubimm, op_sc9.
  destruct (dreg_eq rd r && Int.eq n Int.zero) eqn:?; [|destruct (get_sconst9 n) eqn:?].
  - (* rsub_r *)
    rewrite andb_true_iff in Heqb. destruct Heqb.
    assert (rd = r). destruct rd, r; simpl in H0; try inv H0; try reflexivity.
    rewrite H2. rewrite (Int.same_if_eq n Int.zero); auto.
    econstructor; split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl.
  - (* rsub *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    rewrite (get_sconst9_sound n s Heqo).
    split; intuition Simpl.
  - (* loadimm + sub *)
    destruct (loadimm_correct TMP n (sub rd TMP r k) rs m) as [rs' [EX [RES OTH]]].
    destruct (sub_correct rd TMP r k rs' m) as [rs'' [EX' [RES' OTH']]].
    exists rs''; split.
    eapply exec_straight_trans. eexact EX. eexact EX'.
    rewrite RES'. rewrite RES. rewrite (OTH r); try congruence.
    split. reflexivity. intros. rewrite OTH'; auto.
Qed.

Lemma mulimm_correct:
  forall (rd r : dreg) n k rs m,
  r <> TMP ->
  exists rs',
    exec_straight ge fn (mulimm rd r n k) rs m k rs' m
  /\ rs'#rd = Val.mul (rs#r) (Vint n)
  /\ forall r': preg, r' <> PC -> r' <> TMP -> r' <> rd -> rs'#r' = rs#r'.
Proof.
  intros. unfold mulimm, op_sc9.
  destruct (get_sconst9 n) eqn:?.
  - econstructor; split. apply exec_straight_one; simpl; eauto.
    rewrite (get_sconst9_sound n s Heqo). split; intuition Simpl.
  - (* loadimm + mul *)
    destruct (loadimm_correct TMP n (mul rd r TMP k) rs m) as [rs' [EX [RES OTH]]].
    destruct (mul_correct rd r TMP k rs' m) as [rs'' [EX' [RES' OTH']]].
    exists rs''; split.
    eapply exec_straight_trans. eexact EX. eexact EX'.
    rewrite RES'. rewrite RES. rewrite (OTH r); try congruence.
    split. reflexivity. intros. rewrite OTH'; auto.
Qed.

Lemma sh_shl:
  forall n1 n2,
  Int.ltu n2 Int.iwordsize = true ->
  sh n1 (Vint n2) = Val.shl n1 (Vint n2).
Proof.
  intros. unfold sh.
  assert (Int.lt n2 Int.zero = false).
  apply zlt_false.
  apply Int.ltu_inv in H. change (Int.unsigned Int.iwordsize) with 32 in H.
  rewrite Int.signed_zero. rewrite Int.signed_eq_unsigned; try lia.
  unfold Int.max_signed; simpl; lia. rewrite H0.
  destruct n1; auto. simpl. rewrite H. reflexivity.
Qed.

Lemma sh_shru:
  forall n1 n2,
  Int.ltu n2 Int.iwordsize = true ->
  sh n1 (Vint (Int.neg n2)) = Val.shru n1 (Vint n2).
Proof.
  intros. unfold sh.
  assert (Int.unsigned n2 = 0 \/ 0 < Int.unsigned n2 < 32).
  apply Int.ltu_inv in H. change (Int.unsigned Int.iwordsize) with 32 in *. lia.
  destruct H0.
  assert (Int.lt (Int.neg n2) Int.zero = false).
  apply zlt_false. unfold Int.neg. rewrite Int.signed_repr; rewrite H0. rewrite Int.signed_zero. lia.
  unfold Int.min_signed, Int.max_signed; simpl; lia. rewrite H1.
  destruct n1; auto. unfold Int.neg. rewrite H0.
  rewrite Int.shl_zero. simpl.
  replace (Int.ltu n2 Int.iwordsize) with true. unfold Int.shru. rewrite H0.
  rewrite Z.shiftr_0_r. rewrite Int.repr_unsigned. reflexivity.
  assert (Int.lt (Int.neg n2) Int.zero = true).
  apply zlt_true.
  rewrite Int.signed_zero. unfold Int.neg.
  rewrite Int.signed_repr. lia. unfold Int.min_signed, Int.max_signed; simpl. lia.
  rewrite H1. rewrite Int.neg_involutive. destruct n1; auto. simpl. rewrite H. reflexivity.
Qed.

Lemma sha_shr:
  forall n1 n2,
  Int.ltu n2 Int.iwordsize = true ->
  sha n1 (Vint (Int.neg n2)) = Val.shr n1 (Vint n2).
Proof.
  intros. unfold sha.
  assert (n2 = Int.zero \/ 0 < Int.unsigned n2 < 32).
  apply Int.ltu_inv in H. change (Int.unsigned Int.iwordsize) with 32 in *.
  assert (Int.unsigned n2 = 0 \/ 0 < Int.unsigned n2 < 32).
  lia. destruct H0. left. unfold Int.zero. rewrite <- H0. rewrite Int.repr_unsigned.
  reflexivity. right. lia.
  destruct H0.
  rewrite H0. rewrite Int.neg_involutive. destruct n1; auto.
  rewrite Int.neg_zero.
  replace (Int.lt Int.zero Int.zero) with false by auto. rewrite Int.shl_zero.
  simpl.
  replace (Int.ltu Int.zero Int.iwordsize) with true by auto.
  rewrite Int.shr_zero. reflexivity.
  assert (Int.lt (Int.neg n2) Int.zero = true).
  apply zlt_true.
  rewrite Int.signed_zero. unfold Int.neg.
  rewrite Int.signed_repr. lia. unfold Int.min_signed, Int.max_signed; simpl. lia.
  rewrite H1. rewrite Int.neg_involutive. destruct n1; auto. simpl. rewrite H. reflexivity.
Qed.

Remark shift_sc4_eq:
  forall n,
  Int.ltu n (Int.repr 8) = true ->
  Int.sign_ext 4 n = n.
Proof.
  intros. apply Int.sign_ext_range_eq.
  change (two_p (4 - 1)) with 8. simpl.
  apply Int.ltu_inv in H. change (Int.unsigned (Int.repr 8)) with 8 in H.
  rewrite <- Int.signed_eq_unsigned in H by (unfold Int.max_signed; simpl; lia).
  apply andb_true_iff. split; apply zlt_true.
  change (Int.signed (Int.repr (-9))) with (-9). lia.
  change (Int.signed (Int.repr 8)) with 8. lia.
Qed.

Remark shift_sc4_eq':
  forall n,
  Int.ltu n (Int.repr 9) = true ->
  Int.sign_ext 4 (Int.neg n) = (Int.neg n).
Proof.
  intros. apply Int.sign_ext_range_eq.
  change (two_p (9 - 1)) with 8.
  apply Int.ltu_inv in H.
  change (Int.unsigned (Int.repr 9)) with 9 in H.
  assert (Int.signed (Int.neg n) = - (Int.unsigned n)).
  unfold Int.neg. apply Int.signed_repr. unfold Int.min_signed, Int.max_signed; simpl; lia.
  apply andb_true_iff.
  split; apply zlt_true; rewrite H0. simpl.
  change (Int.signed (Int.repr (-9))) with (-9). lia.
  change (Int.signed (Int.repr (two_p (4 - 1)))) with 8. lia.
Qed.

Remark shift_sc9_eq:
  forall n,
  Int.ltu n Int.iwordsize = true ->
  Int.sign_ext 9 n = n.
Proof.
  intros. apply Int.sign_ext_range_eq.
  change (two_p (9 - 1)) with 256. apply andb_true_iff.
  apply Int.ltu_inv in H.
  change (Int.unsigned Int.iwordsize) with 32 in H.
  rewrite <- Int.signed_eq_unsigned in H by (unfold Int.max_signed; simpl; lia).
  split; apply zlt_true; simpl. change (Int.signed (Int.repr (-257))) with (-257). lia.
  change (Int.signed (Int.repr 256)) with 256. lia.
Qed.

Remark shift_sc9_eq':
  forall n,
  Int.ltu n Int.iwordsize = true ->
  Int.sign_ext 9 (Int.neg n) = Int.neg n.
Proof.
  intros. apply Int.sign_ext_range_eq.
  change (two_p (9 - 1)) with 256. simpl.
  apply Int.ltu_inv in H.
  change (Int.unsigned Int.iwordsize) with 32 in H.
  apply andb_true_iff.
  assert (Int.signed (Int.neg n) = - (Int.unsigned n)).
  unfold Int.neg. apply Int.signed_repr. unfold Int.min_signed, Int.max_signed; simpl; lia.
  split; apply zlt_true; rewrite H0.
  change (Int.signed (Int.repr (-257))) with (-257). lia.
  change (Int.signed (Int.repr 256)) with 256. lia.
Qed.

Lemma slimm_correct:
  forall (rd r : dreg) (n: amount32) k rs m,
  r <> TMP ->
  exists rs',
    exec_straight ge fn (slimm rd r n k) rs m k rs' m
  /\ rs'#rd = Val.shl (rs#r) (Vint n)
  /\ forall r': preg, r' <> PC -> r' <> TMP -> r' <> rd -> rs'#r' = rs#r'.
Proof.
  intros.
  destruct n as [n Range]; simpl in *.
  unfold slimm.
  destruct (dreg_eq rd r && Int.ltu n (Int.repr 8)) eqn:?.
  - (* sh_sc4 *)
    rewrite andb_true_iff in Heqb. destruct Heqb.
    replace r with rd by (destruct rd, r; simpl in H0; congruence).
    econstructor; split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl. rewrite shift_sc4_eq; auto. rewrite sh_shl; auto.
  - (* sh_sc9 *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl. rewrite shift_sc9_eq; auto. rewrite sh_shl; auto.
Qed.

Lemma lsrimm_correct:
  forall (rd r : dreg) (n: amount32) k rs m,
  r <> TMP ->
  exists rs',
    exec_straight ge fn (lsrimm rd r n k) rs m k rs' m
  /\ rs'#rd = Val.shru (rs#r) (Vint n)
  /\ forall r': preg, r' <> PC -> r' <> TMP -> r' <> rd -> rs'#r' = rs#r'.
Proof.
  intros.
  unfold lsrimm.
  destruct n as [n Range]; simpl in *.
  destruct (dreg_eq rd r && Int.ltu n (Int.repr 9)) eqn:?.
  - (* sh_sc4 *)
    rewrite andb_true_iff in Heqb. destruct Heqb.
    replace r with rd by (destruct rd, r; simpl in H0; congruence).
    econstructor; split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl. rewrite shift_sc4_eq', sh_shru; auto.
  - (* sh_sc9 *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl. rewrite shift_sc9_eq'; auto. rewrite sh_shru; auto.
Qed.

Lemma asrimm_correct:
  forall (rd r : dreg) (n: amount32) k rs m,
  r <> TMP ->
  exists rs',
    exec_straight ge fn (asrimm rd r n k) rs m k rs' m
  /\ rs'#rd = Val.shr (rs#r) (Vint n)
  /\ forall r': preg, r' <> PC -> r' <> TMP -> r' <> rd -> rs'#r' = rs#r'.
Proof.
  intros.
  unfold asrimm.
  destruct n as [n Range]; simpl in *.
  destruct (dreg_eq rd r && Int.ltu n (Int.repr 9)) eqn:?.
  - (* sha_sc4 *)
    rewrite andb_true_iff in Heqb. destruct Heqb.
    replace r with rd by (destruct rd, r; simpl in H0; congruence).
    econstructor; split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl. rewrite shift_sc4_eq', sha_shr; auto.
  - (* sha_sc9 *)
   econstructor; split. apply exec_straight_one; simpl; eauto.
   split; intuition Simpl. rewrite shift_sc9_eq'; auto. rewrite sha_shr; auto.
Qed.

Lemma maddimm_correct:
  forall (rd r1 r2: dreg) n k rs m,
  r1 <> TMP ->
  r2 <> TMP ->
  exists rs',
    exec_straight ge fn (maddimm rd r1 r2 n k) rs m k rs' m
  /\ rs'#rd = (Val.add rs#r1 (Val.mul rs#r2 (Vint n)))
  /\ forall r': preg, r' <> PC -> r' <> TMP -> r' <> rd -> rs'#r' = rs#r'.
Proof.
  intros. unfold maddimm, op_sc9.
  destruct (get_sconst9 n) eqn:SC.
  - (* madd_sc9 *)
    econstructor; split.
    apply exec_straight_one; simpl; eauto.
    rewrite (get_sconst9_sound n s); auto.
    split; intuition Simpl.
  - (* loadimm + madd *)
    destruct (loadimm_correct TMP n (Pmadd rd r1 r2 TMP :: k) rs m) as [rs' [EX [RES OTH]]].
    econstructor; split.
    eapply exec_straight_trans. eexact EX.
    apply exec_straight_one; simpl; reflexivity.
    rewrite RES. rewrite !OTH; auto with asmgen.
    split; intuition Simpl.
Qed.

Lemma msubimm_correct:
  forall (rd r1 r2: dreg) n k rs m,
  r1 <> TMP ->
  r2 <> TMP ->
  exists rs',
    exec_straight ge fn (msubimm rd r1 r2 n k) rs m k rs' m
  /\ rs'#rd = (Val.sub rs#r1 (Val.mul rs#r2 (Vint n)))
  /\ forall r': preg, r' <> PC -> r' <> TMP -> r' <> rd -> rs'#r' = rs#r'.
Proof.
  intros. unfold msubimm, op_sc9.
  destruct (get_sconst9 n) eqn:SC.
  - (* msub_sc9 *)
    econstructor; split.
    apply exec_straight_one; simpl; eauto.
    rewrite (get_sconst9_sound n s); auto.
    split; intuition Simpl.
  - (* loadimm + msub *)
    destruct (loadimm_correct TMP n (Pmsub rd r1 r2 TMP :: k) rs m) as [rs' [EX [RES OTH]]].
    econstructor; split.
    eapply exec_straight_trans. eexact EX.
    apply exec_straight_one; simpl; reflexivity.
    rewrite RES. rewrite !OTH; auto with asmgen.
    split; intuition Simpl.
Qed.

Lemma andimm_correct:
  forall (rd r: dreg) n k rs m,
  r <> TMP ->
  exists rs',
    exec_straight ge fn (andimm rd r n k) rs m k rs' m
  /\ rs'#rd = (Val.and rs#r (Vint n))
  /\ forall r': preg, r' <> PC -> r' <> TMP -> r' <> rd -> rs'#r' = rs#r'.
Proof.
  intros. unfold andimm, op_uc9_not, op_uc9.
  destruct (dreg_eq rd r && dreg_eq rd D15 && Int.ltu n (Int.repr (two_p 8))) eqn:?;
           [|destruct (get_uconst9 (Int.not n)) eqn:?; [|destruct (get_uconst9 n) eqn:?]].
  - (* and_d15uc8 *)
    rewrite !andb_true_iff in Heqb. destruct Heqb as [[EQ1 EQ2] R].
    destruct rd; inv EQ2. destruct r; inv EQ1.
    econstructor; split. apply exec_straight_one; simpl; eauto.
    rewrite Int.zero_ext_range_eq; auto. split; intuition Simpl.
  - (* andn_uc9 *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl. rewrite (get_uconst9_sound (Int.not n) u); auto.
    rewrite Int.not_involutive. reflexivity.
  - (* and_ruc9 *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    rewrite (get_uconst9_sound n u); auto.
    split; intuition Simpl.
  - (* loadimm + and *)
    destruct (loadimm_correct TMP n (and rd r TMP k) rs m) as [rs' [EX [RES OTH]]].
    destruct (and_correct rd r TMP k rs' m) as [rs'' [EX' [RES' OTH']]].
    exists rs''; split. apply (exec_straight_trans ge fn _ _ m _ _ m _ _ _ EX EX').
    rewrite RES', RES, (OTH r); auto with asmgen.
    split; auto. intros. rewrite OTH', OTH; auto with asmgen.
Qed.

Lemma nandimm_correct:
  forall (rd r: dreg) n k rs m,
  r <> TMP ->
  exists rs',
    exec_straight ge fn (nandimm rd r n k) rs m k rs' m
  /\ rs'#rd = (Val.notint (Val.and rs#r (Vint n)))
  /\ forall r': preg, r' <> PC -> r' <> TMP -> r' <> rd -> rs'#r' = rs#r'.
Proof.
  intros. unfold nandimm, op_uc9.
  destruct (get_uconst9 n) eqn:?.
  - (* nand_uc9 *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    rewrite (get_uconst9_sound n u); auto.
    split; intuition Simpl.
  - (* loadimm + nand *)
    destruct (loadimm_correct TMP n (Pnand rd r TMP :: k) rs m) as [rs' [EX [RES OTH]]].
    econstructor; split.
    eapply exec_straight_trans. eexact EX.
    apply exec_straight_one; simpl; reflexivity.
    rewrite RES. rewrite OTH; auto with asmgen.
    split; intuition Simpl.
Qed.

Lemma orimm_correct:
  forall (rd r: dreg) n k rs m,
  r <> TMP ->
  exists rs',
    exec_straight ge fn (orimm rd r n k) rs m k rs' m
  /\ rs'#rd = (Val.or rs#r (Vint n))
  /\ forall r': preg, r' <> PC -> r' <> TMP -> r' <> rd -> rs'#r' = rs#r'.
Proof.
  intros. unfold orimm, op_uc9_not, op_uc9.
  destruct (dreg_eq rd r && dreg_eq rd D15 && Int.ltu n (Int.repr (two_p 8))) eqn:?;
           [|destruct (get_uconst9 (Int.not n)) eqn:?; [|destruct (get_uconst9 n) eqn:?]].
  - (* or_d15uc8 *)
    rewrite !andb_true_iff in Heqb. destruct Heqb as [[EQ1 EQ2] R].
    destruct rd; inv EQ2. destruct r; inv EQ1.
    econstructor; split. apply exec_straight_one; simpl; eauto.
    rewrite Int.zero_ext_range_eq; auto. split; intuition Simpl.
  - (* orn_uc9 *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl. rewrite (get_uconst9_sound (Int.not n) u); auto.
    rewrite Int.not_involutive. reflexivity.
  - (* or_ruc9 *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    rewrite (get_uconst9_sound n u); auto.
    split; intuition Simpl.
  - (* loadimm + or *)
    destruct (loadimm_correct TMP n (or rd r TMP k) rs m) as [rs' [EX [RES OTH]]].
    destruct (or_correct rd r TMP k rs' m) as [rs'' [EX' [RES' OTH']]].
    exists rs''; split. apply (exec_straight_trans ge fn _ _ m _ _ m _ _ _ EX EX').
    rewrite RES', RES, (OTH r); auto with asmgen.
    split; auto. intros. rewrite OTH', OTH; auto with asmgen.
Qed.

Lemma norimm_correct:
  forall (rd r: dreg) n k rs m,
  r <> TMP ->
  exists rs',
    exec_straight ge fn (norimm rd r n k) rs m k rs' m
  /\ rs'#rd = (Val.notint (Val.or rs#r (Vint n)))
  /\ forall r': preg, r' <> PC -> r' <> TMP -> r' <> rd -> rs'#r' = rs#r'.
Proof.
  intros. unfold norimm, op_uc9.
  destruct (get_uconst9 n) eqn:?.
  - (* nor_uc9 *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    rewrite (get_uconst9_sound n u); auto.
    split; intuition Simpl.
  - (* loadimm + nor *)
    destruct (loadimm_correct TMP n (Pnor rd r TMP :: k) rs m) as [rs' [EX [RES OTH]]].
    econstructor; split.
    eapply exec_straight_trans. eexact EX.
    apply exec_straight_one; simpl; reflexivity.
    rewrite RES. rewrite OTH; auto with asmgen.
    split; intuition Simpl.
Qed.

Lemma xorimm_correct:
  forall (rd r: dreg) n k rs m,
  r <> TMP ->
  exists rs',
    exec_straight ge fn (xorimm rd r n k) rs m k rs' m
  /\ rs'#rd = (Val.xor rs#r (Vint n))
  /\ forall r': preg, r' <> PC -> r' <> TMP -> r' <> rd -> rs'#r' = rs#r'.
Proof.
  intros. unfold xorimm, op_uc9.
  destruct (get_uconst9 n) eqn:?.
  - (* xor_uc9 *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    rewrite (get_uconst9_sound n u); auto.
    split; intuition Simpl.
  - (* loadimm + xor *)
    destruct (loadimm_correct TMP n (xor rd r TMP k) rs m) as [rs' [EX [RES OTH]]].
    destruct (xor_correct rd r TMP k rs' m) as [rs'' [EX' [RES' OTH']]].
    exists rs''; split. apply (exec_straight_trans ge fn _ _ m _ _ m _ _ _ EX EX').
    rewrite RES', RES, (OTH r); auto with asmgen.
    split; auto. intros. rewrite OTH', OTH; auto with asmgen.
Qed.

Lemma xnorimm_correct:
  forall (rd r: dreg) n k rs m,
  r <> TMP ->
  exists rs',
    exec_straight ge fn (xnorimm rd r n k) rs m k rs' m
  /\ rs'#rd = (Val.notint (Val.xor rs#r (Vint n)))
  /\ forall r': preg, r' <> PC -> r' <> TMP -> r' <> rd -> rs'#r' = rs#r'.
Proof.
  intros. unfold xnorimm, op_uc9.
  destruct (get_uconst9 n) eqn:?.
  - (* xnor_uc9 *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    rewrite (get_uconst9_sound n u); auto.
    split; intuition Simpl.
  - (* loadimm + xnor *)
    destruct (loadimm_correct TMP n (Pxnor rd r TMP :: k) rs m) as [rs' [EX [RES OTH]]].
    econstructor; split.
    eapply exec_straight_trans. eexact EX.
    apply exec_straight_one; simpl; reflexivity.
    rewrite RES. rewrite OTH; auto with asmgen.
    split; intuition Simpl.
Qed.

(** Translation of conditional branches *)

Lemma transl_cbranch_int32s_correct:
  forall cmp (r1 r2: dreg) lbl (rs: regset) m b,
  Val.cmp_bool cmp rs#r1 rs#r2 = Some b ->
  exec_instr ge fn (transl_cbranch_int32s cmp r1 r2 lbl) rs m =
  eval_branch fn lbl rs m (Some b).
Proof.
  intros. destruct cmp; simpl; rewrite ? H; auto.
- destruct rs#r1; simpl in H; try discriminate. destruct rs#r2; inv H.
  simpl; auto.
- destruct rs#r1; simpl in H; try discriminate. destruct rs#r2; inv H.
  simpl; auto.
- rewrite <- Val.swap_cmp_bool. simpl. rewrite H; auto.
- rewrite <- Val.swap_cmp_bool. simpl. rewrite H; auto.
Qed.

Lemma transl_cbranch_int32u_correct:
  forall cmp (r1 r2: dreg) lbl (rs: regset) m b,
  Val.cmpu_bool (Mem.valid_pointer m) cmp rs#r1 rs#r2 = Some b ->
  exec_instr ge fn (transl_cbranch_int32u cmp r1 r2 lbl) rs m =
  eval_branch fn lbl rs m (Some b).
Proof.
  intros. destruct cmp; simpl; rewrite ? H; auto.
  - rewrite <- Val.swap_cmpu_bool. simpl. rewrite H; auto.
  - rewrite <- Val.swap_cmpu_bool. simpl. rewrite H; auto.
Qed.

Lemma lt_add_one:
  forall i n c,
  0 < c < 31 ->
  Int.lt (Int.repr (-two_p (c - 1) - 2)) n && Int.lt n (Int.repr (two_p (c - 1) - 1)) = true ->
  Int.lt i (Int.sign_ext c (Int.add n Int.one)) = negb (Int.lt n i).
Proof.
  intros.
  apply andb_true_iff in H0. destruct H0.
  unfold Int.lt in *.
  set (r' := two_p (c - 1)) in *.
  assert (Int.min_signed <= r' - 1 <= Int.max_signed).
  {
    subst r'. unfold Int.min_signed, Int.max_signed.
    generalize (two_p_monotone (c - 1) 30).
    generalize (two_p_gt_ZERO (c-1)).
    change (two_p 30) with 1073741824 in *. simpl. split; lia.
  }
  assert (Int.min_signed <= - r' - 2 <= Int.max_signed).
  {
    subst r'. unfold Int.min_signed, Int.max_signed.
    generalize (two_p_monotone (c - 1) 30).
    generalize (two_p_gt_ZERO (c-1)).
    change (two_p 30) with 1073741824 in *. simpl. split; lia.
  }
  rewrite Int.signed_repr in H0, H1; auto.
  destruct (zlt  (- r' - 2) (Int.signed n)); inv H0.
  destruct (zlt (Int.signed n) (r' - 1)); inv H1.
  assert (Int.signed (Int.add n Int.one) = (Int.signed n) + 1).
  { rewrite Int.add_signed. change (Int.signed Int.one) with 1.
    rewrite Int.signed_repr. reflexivity. lia.
  }
  rewrite Int.sign_ext_range_eq.
  rewrite H0. destruct (zlt (Int.signed n) (Int.signed i)).
  apply zlt_false. lia. apply zlt_true. lia.
  apply andb_true_iff. split; apply zlt_true; subst r'.
  rewrite Int.signed_repr; lia. rewrite H0. rewrite Int.signed_repr. lia.
  unfold Int.min_signed, Int.max_signed; simpl. split.
  generalize (two_p_gt_ZERO (c - 1)). lia.
  generalize (two_p_monotone (c - 1) 30).
  change (two_p 30) with 1073741824 in *. lia.
Qed.

Lemma transl_cbranch_int32s_imm_correct:
  forall cmp n r lbl k c m b (rs: regset),
  r <> TMP ->
  transl_cbranch_int32s_imm cmp n r lbl k = c ->
  Val.cmp_bool cmp (rs r) (Vint n) = Some b ->
  exists rs', exists insn,
     exec_straight_opt ge fn c rs m (insn :: k) rs' m
  /\ exec_instr ge fn insn rs' m = eval_branch fn lbl rs' m (Some b)
  /\ forall r, r <> PC -> r <> TMP -> rs'#r = rs#r.
Proof.
  unfold transl_cbranch_int32s_imm. intros.
  assert (DEF:
           exists (rs' : regset) (insn : instruction),
           exec_straight_opt ge fn (loadimm D0 n (transl_cbranch_int32s cmp r D0 lbl :: k)) rs m (insn :: k) rs' m /\
             exec_instr ge fn insn rs' m = eval_branch fn lbl rs' m (Some b) /\
             (forall r0 : preg, r0 <> PC -> r0 <> D0 -> rs' r0 = rs r0)).
  {
    exploit (loadimm_correct TMP n); eauto. intros (rs' & A & B & C).
    exists rs', (transl_cbranch_int32s cmp r D0 lbl); split.
    constructor. eexact A. split.
    apply transl_cbranch_int32s_correct. rewrite B. rewrite C; auto with asmgen.
    intuition Simpl.
  }
  destruct cmp; inv H0; eauto.
  - destruct (get_sconst4 n) eqn:?; eauto.
    exists rs ,(Pjeq_sc4 r s lbl); split.
    apply exec_straight_opt_refl. split; intuition Simpl.
    simpl.  destruct (rs r); simpl in *; inv H1.
    rewrite (get_sconst4_sound n s); auto.
  - destruct (get_sconst4 n) eqn:?; eauto.
    exists rs ,(Pjne_sc4 r s lbl); split.
    apply exec_straight_opt_refl. split; intuition Simpl.
    simpl.  destruct (rs r); simpl in *; inv H1.
    rewrite (get_sconst4_sound n s); auto.
  - destruct (get_sconst4 n) eqn:?; eauto.
    exists rs ,(Pjlt_sc4 r s lbl); split.
    apply exec_straight_opt_refl. split; intuition Simpl.
    simpl.  destruct (rs r); simpl in *; inv H1.
    rewrite (get_sconst4_sound n s); auto.
  - destruct (Int.lt (Int.repr (-10)) n && Int.lt n (Int.repr 7)) eqn:?; eauto.
    exists rs ,(Pjlt_sc4 r (mk_sconst4 (Int.add n Int.one)) lbl); split.
    apply exec_straight_opt_refl. split; intuition Simpl.
    simpl.  destruct (rs r); simpl in *; inv H1.
    rewrite lt_add_one; auto. lia.
  - destruct (Int.lt (Int.repr (-10)) n && Int.lt n (Int.repr 7)) eqn:?; eauto.
    exists rs ,(Pjge_sc4 r (mk_sconst4 (Int.add n Int.one)) lbl); split.
    apply exec_straight_opt_refl. split; intuition Simpl.
    simpl.  destruct (rs r); simpl in *; inv H1.
    rewrite lt_add_one; try rewrite negb_involutive; auto. lia.
  - destruct (get_sconst4 n) eqn:?; eauto.
    exists rs ,(Pjge_sc4 r s lbl); split.
    apply exec_straight_opt_refl. split; intuition Simpl.
    simpl.  destruct (rs r); simpl in *; inv H1.
    rewrite (get_sconst4_sound n s); auto.
Qed.

Lemma transl_cbranch_int32u_imm_correct:
  forall cmp n r lbl k c m b (rs: regset),
  r <> TMP ->
  transl_cbranch_int32u_imm cmp n r lbl k = c ->
  Val.cmpu_bool (Mem.valid_pointer m) cmp (rs r) (Vint n) = Some b ->
  exists rs', exists insn,
     exec_straight_opt ge fn c rs m (insn :: k) rs' m
  /\ exec_instr ge fn insn rs' m = eval_branch fn lbl rs' m (Some b)
  /\ forall r, r <> PC -> r <> TMP -> rs'#r = rs#r.
Proof.
  unfold transl_cbranch_int32u_imm. intros.
 assert (DEF:
           exists (rs' : regset) (insn : instruction),
           exec_straight_opt ge fn (loadimm D0 n (transl_cbranch_int32u cmp r D0 lbl :: k)) rs m (insn :: k) rs' m /\
             exec_instr ge fn insn rs' m = eval_branch fn lbl rs' m (Some b) /\
             (forall r0 : preg, r0 <> PC -> r0 <> D0 -> rs' r0 = rs r0)).
  {
    exploit (loadimm_correct TMP n); eauto. intros (rs' & A & B & C).
    exists rs', (transl_cbranch_int32u cmp r D0 lbl); split.
    constructor. eexact A. split.
    apply transl_cbranch_int32u_correct. rewrite B. rewrite C; auto with asmgen.
    intuition Simpl.
  }
  destruct cmp; inv H0; eauto.
  - destruct (get_sconst4 n) eqn:?; eauto.
    exists rs ,(Pjeq_sc4 r s lbl); split.
    apply exec_straight_opt_refl. split; intuition Simpl.
    simpl.
    rewrite (get_sconst4_sound n s); auto. unfold eval_branch.
    rewrite H1. reflexivity.
  - destruct (get_sconst4 n) eqn:?; eauto.
    exists rs ,(Pjne_sc4 r s lbl); split.
    apply exec_straight_opt_refl. split; intuition Simpl.
    simpl.
    rewrite (get_sconst4_sound n s); auto. unfold eval_branch.
    rewrite H1. reflexivity.
  - destruct (get_uconst4 n) eqn:?; eauto.
    exists rs ,(Pjltu_sc4 r u lbl); split.
    apply exec_straight_opt_refl. split; intuition Simpl.
    simpl.
    rewrite (get_uconst4_sound n u); auto. unfold eval_branch.
    rewrite H1. reflexivity.
  -  destruct (Int.eq n Int.zero) eqn:?;[|destruct (Int.ltu n (Int.repr 15)) eqn:?]; eauto.
     +  apply Int.same_if_eq in Heqb0.
       exists rs, (Pjeq_sc4 r (mk_sconst4 Int.zero) lbl); split.
       apply exec_straight_opt_refl. split; intuition Simpl.
       simpl.
       change (Int.sign_ext 4 Int.zero) with Int.zero.
       destruct (rs r); inv H1. simpl.
       rewrite Int.not_ltu.
       replace (Int.ltu i Int.zero) with false. simpl. reflexivity.
       unfold Int.ltu. symmetry. apply zlt_false.
       rewrite Int.unsigned_zero. generalize (Int.unsigned_range i). lia.
       change (Int.eq Int.zero Int.zero) with true in *.
       simpl in *.
       destruct ( Mem.valid_pointer m b0 (Ptrofs.unsigned i) || Mem.valid_pointer m b0 (Ptrofs.unsigned i - 1)); inv H2.
     + apply Int.ltu_inv in Heqb1. change (Int.unsigned (Int.repr 15)) with 15 in Heqb1.
       assert (Int.unsigned (Int.add n Int.one) = Int.unsigned n + 1).
       {
         rewrite Int.add_unsigned. rewrite Int.unsigned_one.  rewrite Int.unsigned_repr.
         reflexivity.  unfold Int.max_unsigned; simpl; lia.
       }
       exists rs, (Pjltu_sc4 r (mk_uconst4 (Int.add n Int.one)) lbl); split.
       apply exec_straight_opt_refl. split; intuition Simpl.
       simpl. rewrite Int.zero_ext_range_eq.
       destruct (rs r); inv H1; simpl.
       assert (Int.ltu i (Int.add n Int.one) = negb (Int.ltu n i)).
       unfold Int.ltu. rewrite H0.
       destruct (zlt (Int.unsigned n) (Int.unsigned i)).
       apply zlt_false. lia. apply zlt_true. lia. rewrite H1; reflexivity.
       rewrite Heqb0 in H5. inv H5.
       unfold Int.ltu. rewrite H0. apply zlt_true.
       change (Int.unsigned (Int.repr (two_p 4))) with 16. lia.
  - destruct (Int.ltu n (Int.repr 15)) eqn:?; eauto.
    apply Int.ltu_inv in Heqb0. change (Int.unsigned (Int.repr 15)) with 15 in Heqb0.
    assert (Int.unsigned (Int.add n Int.one) = Int.unsigned n + 1).
    {
      rewrite Int.add_unsigned. rewrite Int.unsigned_one.  rewrite Int.unsigned_repr.
      reflexivity.  unfold Int.max_unsigned; simpl; lia.
    }
    exists rs , (Pjgeu_sc4 r (mk_uconst4 (Int.add n Int.one)) lbl); split.
    apply exec_straight_opt_refl. split; intuition Simpl.
    simpl. destruct (rs r); inv H1.
    simpl. rewrite Int.zero_ext_range_eq.
    assert (Int.ltu i (Int.add n Int.one) = negb (Int.ltu n i)).
    unfold Int.ltu. rewrite H0.
    destruct (zlt (Int.unsigned n) (Int.unsigned i)).
    apply zlt_false. lia. apply zlt_true. lia.
    rewrite H1. rewrite negb_involutive. reflexivity.
    apply zlt_true. rewrite H0.
    change (Int.unsigned (Int.repr (two_p 4))) with 16. lia.
    simpl.
    destruct (Int.eq n Int.zero && (Mem.valid_pointer m b0 (Ptrofs.unsigned i) || Mem.valid_pointer m b0 (Ptrofs.unsigned i - 1))); inv H5.
  - destruct (get_uconst4 n) eqn:?; eauto.
    exists rs ,(Pjgeu_sc4 r u lbl); split.
    apply exec_straight_opt_refl. split; intuition Simpl.
    simpl.
    rewrite (get_uconst4_sound n u); auto. unfold eval_branch.
    rewrite H1. reflexivity.
Qed.

Lemma transl_cond_single_branch_correct:
  forall cmp (rd r1 r2: dreg) rs k m,
  exists rs',
    exec_straight ge fn (transl_cond_single_branch cmp rd r1 r2 k) rs m k rs' m
    /\ tb_bool (rs'#rd) (fst (bit_of_cond_single cmp)) =
      (if snd (bit_of_cond_single cmp)
       then Val.cmpfs_bool cmp (rs#r1) (rs#r2)
       else option_map negb (Val.cmpfs_bool cmp (rs#r1) (rs#r2)))
    /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  intros. unfold transl_cond_single_branch.
  destruct cmp; simpl.
  - econstructor; split.
    apply exec_straight_one; simpl; eauto.
    split; intuition Simpl. unfold tb_bool, cmpfs, Val.cmpfs_bool.
    change (Int.zero_ext 5 Int.one) with Int.one.
    destruct (rs r1), (rs r2); auto.
    destruct (Float32.cmp Ceq f f0); auto.
    destruct (Float32.cmp Cgt f f0); auto.
    destruct (Float32.cmp Clt f f0); auto.
  - econstructor; split.
    apply exec_straight_one; simpl; eauto.
    split; intuition Simpl.  unfold tb_bool, cmpfs, Val.cmpfs_bool.
    change (Int.zero_ext 5 Int.one) with Int.one.
    destruct (rs r1), (rs r2); auto.
    rewrite  Float32.cmp_ne_eq.
    destruct (Float32.cmp Ceq f f0) eqn:?; simpl. auto.
    destruct (Float32.cmp Cgt f f0) eqn:?; simpl. auto.
    destruct (Float32.cmp Clt f f0) eqn:?; simpl; auto.
  - econstructor; split.
    apply exec_straight_one; simpl; eauto.
    split; intuition Simpl.  unfold tb_bool, cmpfs, Val.cmpfs_bool.
    change (Int.zero_ext 5 Int.zero) with Int.zero.
    destruct (rs r1), (rs r2); auto.
    destruct (Float32.cmp Ceq f f0) eqn:Heq1; destruct (Float32.cmp Clt f f0) eqn:Heq2;
      destruct (Float32.cmp Cgt f f0) eqn:Heq3; try (destruct (Float32.cmp_lt_eq_false f f0 Heq2 Heq1));
      try (destruct (Float32.cmp_lt_gt_false f f0 Heq2 Heq3));
      try (destruct (Float32.cmp_gt_eq_false f f0 Heq3 Heq1)); try reflexivity.
  - econstructor; split.
    eapply exec_straight_two; simpl; eauto.
    split; intuition Simpl. unfold tb_bool, or_t, cmpfs, Val.cmpfs_bool.
    destruct (rs r1), (rs r2); auto.
    rewrite Float32.cmp_le_lt_eq.
    destruct (Float32.cmp Ceq f f0) eqn:Heq1; destruct (Float32.cmp Clt f f0) eqn:Heq2;
      destruct (Float32.cmp Cgt f f0) eqn:Heq3; try (destruct (Float32.cmp_lt_eq_false f f0 Heq2 Heq1));
      try (destruct (Float32.cmp_lt_gt_false f f0 Heq2 Heq3));
      try (destruct (Float32.cmp_gt_eq_false f f0 Heq3 Heq1)); try reflexivity.
  - econstructor; split.
    apply exec_straight_one; simpl; eauto.
    split; intuition Simpl.  unfold tb_bool, cmpfs, Val.cmpfs_bool.
    change (Int.zero_ext 5 Int.zero) with Int.zero.
    destruct (rs r1), (rs r2); auto.
    destruct (Float32.cmp Ceq f f0) eqn:Heq1; destruct (Float32.cmp Clt f f0) eqn:Heq2;
      destruct (Float32.cmp Cgt f f0) eqn:Heq3; try (destruct (Float32.cmp_lt_eq_false f f0 Heq2 Heq1));
      try (destruct (Float32.cmp_lt_gt_false f f0 Heq2 Heq3));
      try (destruct (Float32.cmp_gt_eq_false f f0 Heq3 Heq1)); try reflexivity.
  - econstructor; split.
    eapply exec_straight_two; simpl; eauto.
    split; intuition Simpl. unfold tb_bool, or_t, cmpfs, Val.cmpfs_bool.
    destruct (rs r1), (rs r2); auto.
    rewrite Float32.cmp_ge_gt_eq.
    destruct (Float32.cmp Ceq f f0) eqn:Heq1; destruct (Float32.cmp Clt f f0) eqn:Heq2;
      destruct (Float32.cmp Cgt f f0) eqn:Heq3; try (destruct (Float32.cmp_lt_eq_false f f0 Heq2 Heq1));
      try (destruct (Float32.cmp_lt_gt_false f f0 Heq2 Heq3));
      try (destruct (Float32.cmp_gt_eq_false f f0 Heq3 Heq1)); try reflexivity.
Qed.

Ltac ArgsInv :=
  repeat (match goal with
  | [ H: Error _ = OK _ |- _ ] => discriminate
  | [ H: match ?args with nil => _ | _ :: _ => _ end = OK _ |- _ ] => destruct args
  | [ H: bind _ _ = OK _ |- _ ] => monadInv H
  | [ H: match _ with left _ => _ | right _ => assertion_failed end = OK _ |- _ ] => monadInv H; ArgsInv
  | [ H: match _ with true => _ | false => assertion_failed end = OK _ |- _ ] => monadInv H; ArgsInv
  end);
  subst;
  repeat (match goal with
  | [ H: ireg_of _ = OK _ |- _ ] => simpl in *; rewrite (ireg_of_eq _ _ H) in *
  | [ H: freg_of _ = OK _ |- _ ] => simpl in *; rewrite (freg_of_eq _ _ H) in *
          end).


Lemma transl_cbranch_correct_1:
  forall cond args lbl k c m ms b sp rs m',
  transl_cbranch cond args lbl k = OK c ->
  eval_condition cond (List.map ms args) m = Some b ->
  agree ms sp rs ->
  Mem.extends m m' ->
  exists rs', exists insn,
     exec_straight_opt ge fn c rs m' (insn :: k) rs' m'
  /\ exec_instr ge fn insn rs' m' = eval_branch fn lbl rs' m' (Some b)
  /\ forall r, r <> PC -> r <> TMP -> rs'#r = rs#r.
Proof.
  intros until m'; intros TRANSL EVAL AG MEXT.
  set (vl' := map rs (map preg_of args)).
  assert (EVAL': eval_condition cond vl' m' = Some b).
  { apply eval_condition_lessdef with (map ms args) m; auto. eapply preg_vals; eauto. }
  clear EVAL MEXT AG.
  destruct cond; simpl in TRANSL; ArgsInv.
  - (* branch signed int *)
    exists rs, (transl_cbranch_int32s c0 x x0 lbl).
    intuition auto. constructor. apply transl_cbranch_int32s_correct; auto.
  - (* branch unsigned int *)
    exists rs, (transl_cbranch_int32u c0 x x0 lbl).
    intuition auto. constructor. apply transl_cbranch_int32u_correct; auto.
  - (* branch signed int with immediate *)
    eapply transl_cbranch_int32s_imm_correct; eauto with asmgen.
  - (* branch unsigned int with immediate *)
    eapply transl_cbranch_int32u_imm_correct; eauto with asmgen.
  - (* branch float *)
    set (bit' := fst (bit_of_cond_single c0)).
    set (normal' := snd (bit_of_cond_single c0)).
    set (inst:= if normal' then Pjnz_t TMP bit' lbl else Pjz_t TMP bit' lbl).
    assert (c = transl_cond_single_branch c0 TMP x x0 (inst :: k)).
    destruct c0; simpl in *; subst inst bit'; inv EQ2; reflexivity.
    exploit (transl_cond_single_branch_correct c0 TMP x x0 rs). intros (rs' & A  & B & C).
    exists rs', inst; split.
    constructor. rewrite H. eexact A. split; auto.
    destruct normal' eqn:?; subst normal' inst bit'; simpl.
    rewrite B. rewrite Heqb0. rewrite EVAL'. reflexivity.
    unfold tbz_bool, tb_bool in *.
    change Ceq with (negate_comparison Cne).
    rewrite Val.negate_cmp_bool. rewrite B. rewrite EVAL'. rewrite Heqb0.
    simpl. rewrite negb_involutive. reflexivity.
  - (* branch not float *)
    set (bit' := fst (bit_of_cond_single c0)).
    set (normal' := snd (bit_of_cond_single c0)).
    set (inst:= if normal' then Pjz_t TMP bit' lbl else Pjnz_t TMP bit' lbl).
    assert (c = transl_cond_single_branch c0 TMP x x0 (inst :: k)).
    destruct c0; simpl in *; subst inst bit'; inv EQ2; reflexivity.
    exploit (transl_cond_single_branch_correct c0 TMP x x0 rs). intros (rs' & A  & B & C).
    exists rs', inst; split.
    constructor. rewrite H. eexact A. split; auto.
    destruct normal' eqn:?. subst normal' inst bit'. rewrite Heqb0 in B.
    simpl. rewrite <- B in EVAL'. unfold tbz_bool, tb_bool in *.
    change Ceq with (negate_comparison Cne).
    rewrite Val.negate_cmp_bool. rewrite EVAL'. reflexivity.
    subst normal' inst bit'. rewrite Heqb0 in B.
    simpl. rewrite B. rewrite EVAL'. reflexivity.
Qed.


Lemma transl_cbranch_correct_true:
  forall cond args lbl k c m ms sp rs m',
  transl_cbranch cond args lbl k = OK c ->
  eval_condition cond (List.map ms args) m = Some true ->
  agree ms sp rs ->
  Mem.extends m m' ->
  exists rs', exists insn,
     exec_straight_opt ge fn c rs m' (insn :: k) rs' m'
  /\ exec_instr ge fn insn rs' m' = goto_label fn lbl rs' m'
  /\ forall r, r <> PC -> r <> TMP -> rs'#r = rs#r.
Proof.
  intros. eapply transl_cbranch_correct_1 with (b := true); eauto.
Qed.

Lemma transl_cbranch_correct_false:
  forall cond args lbl k c m ms sp rs m',
  transl_cbranch cond args lbl k = OK c ->
  eval_condition cond (List.map ms args) m = Some false ->
  agree ms sp rs ->
  Mem.extends m m' ->
  exists rs',
     exec_straight ge fn c rs m' k rs' m'
  /\ forall r, r <> PC -> r <> TMP -> rs'#r = rs#r.
Proof.
  intros. exploit transl_cbranch_correct_1; eauto. simpl.
  intros (rs' & insn & A & B & C).
  exists (nextinstr rs').
  split. eapply exec_straight_opt_right; eauto. apply exec_straight_one; auto.
  intros; Simpl.
Qed.


(** Translation of condition operators *)

Lemma transl_cond_int32s_correct:
  forall cmp rd r1 r2 k rs m,
  exists rs',
     exec_straight ge fn (transl_cond_int32s cmp rd r1 r2 :: k) rs m k rs' m
  /\ Val.lessdef (Val.cmp cmp rs#r1 rs#r2) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  intros. destruct cmp; simpl.
  - (* Ceq *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl. destruct (rs r1), (rs r2); auto.
  - (* Cne *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl. destruct (rs r1), (rs r2); auto.
  - (* Clt *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl.
  - (* Cle *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl. unfold Val.cmp. rewrite <- Val.swap_cmp_bool.
    simpl. auto.
  - (* Cgt *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl. unfold Val.cmp. rewrite <- Val.swap_cmp_bool.
    simpl. auto.
  - (* Cget *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl.
Qed.

Lemma transl_cond_int32u_correct:
  forall cmp rd r1 r2 k rs m,
  exists rs',
     exec_straight ge fn (transl_cond_int32u cmp rd r1 r2 :: k) rs m k rs' m
  /\ rs'#rd = Val.cmpu (Mem.valid_pointer m) cmp rs#r1 rs#r2
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  intros. destruct cmp; simpl.
  - (* Ceq *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl.
  - (* Cne *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl.
  - (* Clt *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl.
  - (* Cle *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    unfold Val.cmpu. rewrite <- Val.swap_cmpu_bool.
    split; intuition Simpl.
  - (* Cgt *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    unfold Val.cmpu. rewrite <- Val.swap_cmpu_bool.
    split; intuition Simpl.
  - (* Cge *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl.
Qed.

Lemma transl_condimm_int32s_correct:
  forall cmp rd r n k rs m,
  r <> TMP ->
  exists rs',
     exec_straight ge fn (transl_condimm_int32s cmp rd r n k) rs m k rs' m
  /\ Val.lessdef (Val.cmp cmp rs#r (Vint n)) rs'#rd
  /\ forall r, r <> PC -> r <> TMP -> r <> rd -> rs'#r = rs#r.
Proof.
  intros.
  assert (DEF:
           exists rs',
           exec_straight ge fn (loadimm TMP n (transl_cond_int32s cmp rd r TMP :: k)) rs m k rs' m
           /\ Val.lessdef (Val.cmp cmp rs#r (Vint n)) rs'#rd
           /\ forall r, r <> PC -> r <> TMP -> r <> rd -> rs'#r = rs#r).
  {
    destruct (loadimm_correct TMP n (transl_cond_int32s cmp rd r TMP :: k) rs m) as [rs' [EX [RES OTH]]].
    destruct (transl_cond_int32s_correct cmp rd r TMP k rs' m) as [rs'' [EX' [RES' OTH']]].
    exists rs''; split.
    eapply exec_straight_trans. eexact EX. eexact EX'.
    rewrite RES in RES'. rewrite (OTH r) in RES'; try congruence.
    split; auto. intros. rewrite OTH'; auto.
  }
  destruct cmp; simpl; eauto.
  - (* Ceq *)
    destruct (get_sconst9 n) eqn:?; eauto.
    econstructor; split. apply exec_straight_one; simpl; eauto.
    rewrite (get_sconst9_sound n s Heqo). split; intuition Simpl.
    destruct (rs r); auto.
  - (* Cne *)
    destruct (get_sconst9 n) eqn:?; eauto.
    econstructor; split. apply exec_straight_one; simpl; eauto.
    rewrite (get_sconst9_sound n s Heqo). split; intuition Simpl.
    destruct (rs r); auto.
  - (* Clt *)
    destruct (get_sconst9 n) eqn:?; eauto.
    econstructor; split. apply exec_straight_one; simpl; eauto.
    rewrite (get_sconst9_sound n s Heqo). split; intuition Simpl.
  - (* Cle *)
    destruct (Int.lt (Int.repr (-258)) n && Int.lt n (Int.repr 255)) eqn:?; eauto.
    econstructor; split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl.
    destruct (rs r); auto. unfold Val.cmp. simpl.
    rewrite lt_add_one; auto. lia.
  - (* Cge *)
    destruct (Int.lt (Int.repr (-258)) n && Int.lt n (Int.repr 255)) eqn:?; eauto.
    econstructor; split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl.
    destruct (rs r); auto. unfold Val.cmp. simpl.
    rewrite lt_add_one; try rewrite negb_involutive; auto. lia.
  - (* Cgt *)
    destruct (get_sconst9 n) eqn:?; eauto.
    econstructor; split. apply exec_straight_one; simpl; eauto.
    rewrite (get_sconst9_sound n s Heqo). split; intuition Simpl.
Qed.

Lemma transl_condimm_int32u_correct:
  forall cmp rd r n k rs m,
  r <> TMP ->
  exists rs',
     exec_straight ge fn (transl_condimm_int32u cmp rd r n k) rs m k rs' m
  /\  Val.lessdef (Val.cmpu (Mem.valid_pointer m) cmp rs#r (Vint n)) rs'#rd
  /\ forall r, r <> PC -> r <> TMP -> r <> rd -> rs'#r = rs#r.
Proof.
  intros.
  assert (DEF:
           exists rs',
           exec_straight ge fn (loadimm TMP n (transl_cond_int32u cmp rd r TMP :: k)) rs m k rs' m
           /\ Val.lessdef (Val.cmpu (Mem.valid_pointer m) cmp rs#r (Vint n)) rs'#rd
           /\ forall r, r <> PC -> r <> TMP -> r <> rd -> rs'#r = rs#r).
  {
    destruct (loadimm_correct TMP n (transl_cond_int32u cmp rd r TMP :: k) rs m) as [rs' [EX [RES OTH]]].
    destruct (transl_cond_int32u_correct cmp rd r TMP k rs' m) as [rs'' [EX' [RES' OTH']]].
    exists rs''; split.
    eapply exec_straight_trans. eexact EX. eexact EX'.
    rewrite RES'. rewrite RES. rewrite (OTH r); try congruence.
    split; auto. intros. rewrite OTH'; auto.
  }
  destruct cmp; simpl; eauto.
  - (* Ceq *)
    destruct (get_sconst9 n) eqn:?; auto.
    econstructor; split. apply exec_straight_one; simpl; eauto.
    rewrite (get_sconst9_sound n s Heqo). split; intuition Simpl.
  - (* Cne *)
    destruct (get_sconst9 n) eqn:?; auto.
    econstructor; split. apply exec_straight_one; simpl; eauto.
    rewrite (get_sconst9_sound n s Heqo). split; intuition Simpl.
  - (* Clt *)
    destruct (get_uconst9 n) eqn:?; auto.
    econstructor; split. apply exec_straight_one; simpl; eauto.
    rewrite (get_uconst9_sound n u Heqo). split; intuition Simpl.
  - (* Cle *)
    destruct (Int.eq n Int.zero) eqn:?; [|destruct (Int.ltu n (Int.repr 511)) eqn:?]; eauto.
    + econstructor; split. apply exec_straight_one; simpl; eauto.
      split; intuition Simpl.
      destruct (rs r); auto. apply Int.same_if_eq in Heqb. rewrite Heqb.
      change (Int.sign_ext 9 Int.zero) with Int.zero.
      unfold Val.cmpu. simpl. rewrite Int.not_ltu.
      replace (Int.ltu i Int.zero) with false. simpl. auto.
      symmetry. apply zlt_false. rewrite Int.unsigned_zero. generalize (Int.unsigned_range i). lia.
      unfold Val.cmpu. simpl. rewrite Heqb. change (Int.eq (Int.sign_ext 9 Int.zero) Int.zero) with true.
      simpl.
      destruct (Mem.valid_pointer m b (Ptrofs.unsigned i) || Mem.valid_pointer m b (Ptrofs.unsigned i - 1)); auto.
    + apply Int.ltu_inv in Heqb0. change (Int.unsigned (Int.repr 511)) with 511 in Heqb0.
      assert (Int.unsigned (Int.add n Int.one) = Int.unsigned n + 1).
      {
        rewrite Int.add_unsigned. rewrite Int.unsigned_one.  rewrite Int.unsigned_repr.
        reflexivity. unfold Int.max_unsigned; simpl; lia.
      }
      econstructor; split. apply exec_straight_one; simpl; eauto.
      split; intuition Simpl.
      destruct (rs r); auto. unfold Val.cmpu. simpl.
      rewrite Int.zero_ext_range_eq.
      assert (negb (Int.ltu n i) = Int.ltu i (Int.add n Int.one)).
      unfold Int.ltu. rewrite H0. destruct (zlt (Int.unsigned n) (Int.unsigned i));
        symmetry; [apply zlt_false | apply zlt_true]; lia.
      rewrite H3. auto.
      apply zlt_true. rewrite H0. change (Int.unsigned (Int.repr (two_p 9))) with 512. lia.
      unfold Val.cmpu. simpl. rewrite Heqb. simpl. auto.
  - (* Cgt *)
    destruct (Int.ltu n (Int.repr 511)) eqn:?; eauto.
    apply Int.ltu_inv in Heqb. change (Int.unsigned (Int.repr 511)) with 511 in Heqb.
    assert (Int.unsigned (Int.add n Int.one) = Int.unsigned n + 1).
    {
      rewrite Int.add_unsigned, Int.unsigned_one, Int.unsigned_repr.
      reflexivity. unfold Int.max_unsigned; simpl; lia.
    }
    econstructor; split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl.
    destruct (rs r); auto; simpl; unfold Val.cmpu.
    rewrite Int.zero_ext_range_eq. simpl.
    assert (Int.ltu n i = negb (Int.ltu i (Int.add n Int.one))).
    unfold Int.ltu. rewrite H0. destruct (zlt (Int.unsigned n) (Int.unsigned i));
      symmetry; change true with (negb false); change false with (negb true); f_equal; [apply zlt_false | apply zlt_true]; lia.
    rewrite H3. auto. unfold Int.ltu. rewrite H0. apply zlt_true.
    change (Int.unsigned (Int.repr (two_p 9))) with 512. lia.
    simpl. destruct (Int.eq n Int.zero && (Mem.valid_pointer m b (Ptrofs.unsigned i) || Mem.valid_pointer m b (Ptrofs.unsigned i - 1)));
    simpl; auto.
  - (* Cge *)
    destruct (get_uconst9 n) eqn:?; auto.
    econstructor; split. apply exec_straight_one; simpl; eauto.
    rewrite (get_uconst9_sound n u Heqo). split; intuition Simpl.
Qed.

Lemma notbool_nor_or:
  forall rd r1 r2 bit_1 bit_2 k rs m (inv : bool),
  exists rs',
    exec_straight ge fn ((if inv then Pnor_t rd r1 bit_1 r2 bit_2 else Por_t rd r1 bit_1 r2 bit_2) :: k) rs m k rs' m
  /\ rs'#rd = (if inv then Val.notbool (or_t rs#r1 rs#r2 bit_1 bit_2) else (or_t rs#r1 rs#r2 bit_1 bit_2))
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  intros.
  destruct inv.
  econstructor; split. apply exec_straight_one; simpl; eauto.
  split; intuition Simpl.
  econstructor; split. apply exec_straight_one; simpl; eauto.
  split; intuition Simpl.
Qed.

Lemma ort_cmpfs:
  forall v1 v2 bit_1 bit_2 cmp n,
  cmp <> Cne ->
  bits_of_cond_single cmp = (bit_1, bit_2, n) ->
  or_t (cmpfs v1 v2) (cmpfs v1 v2) bit_1 bit_2 = Val.cmpfs cmp v1 v2.
Proof.
  intros.
  destruct cmp; try congruence;  inv H0; simpl; rewrite !Int.zero_ext_range_eq; auto;
    unfold tb, cmpfs, Val.cmpfs, Val.cmpfs_bool.
  - (* Ceq *)
    destruct v1, v2; auto.
    destruct (Float32.cmp Ceq f f0); auto.
    destruct (Float32.cmp Cgt f f0); auto.
    destruct (Float32.cmp Clt f f0); auto.
  - (* Clt *)
    destruct v1, v2; auto.
    destruct (Float32.cmp Ceq f f0) eqn:Heq1; destruct (Float32.cmp Clt f f0) eqn:Heq2;
      destruct (Float32.cmp Cgt f f0) eqn:Heq3; try (destruct (Float32.cmp_lt_eq_false f f0 Heq2 Heq1));
      try (destruct (Float32.cmp_lt_gt_false f f0 Heq2 Heq3));
      try (destruct (Float32.cmp_gt_eq_false f f0 Heq3 Heq1)); try reflexivity.
  - (* Cle *)
    destruct v1, v2; auto.
    rewrite Float32.cmp_le_lt_eq.
    destruct (Float32.cmp Ceq f f0) eqn:Heq1; destruct (Float32.cmp Clt f f0) eqn:Heq2;
      destruct (Float32.cmp Cgt f f0) eqn:Heq3; try (destruct (Float32.cmp_lt_eq_false f f0 Heq2 Heq1));
      try (destruct (Float32.cmp_lt_gt_false f f0 Heq2 Heq3));
      try (destruct (Float32.cmp_gt_eq_false f f0 Heq3 Heq1)); try reflexivity.
  - (* Cgt *)
    destruct v1, v2; auto.
    destruct (Float32.cmp Ceq f f0) eqn:Heq1; destruct (Float32.cmp Clt f f0) eqn:Heq2;
      destruct (Float32.cmp Cgt f f0) eqn:Heq3; try (destruct (Float32.cmp_lt_eq_false f f0 Heq2 Heq1));
      try (destruct (Float32.cmp_lt_gt_false f f0 Heq2 Heq3));
      try (destruct (Float32.cmp_gt_eq_false f f0 Heq3 Heq1)); try reflexivity.
  - (* Cge *)
    destruct v1, v2; auto.
    rewrite Float32.cmp_ge_gt_eq.
    destruct (Float32.cmp Ceq f f0) eqn:Heq1; destruct (Float32.cmp Clt f f0) eqn:Heq2;
      destruct (Float32.cmp Cgt f f0) eqn:Heq3; try (destruct (Float32.cmp_lt_eq_false f f0 Heq2 Heq1));
      try (destruct (Float32.cmp_lt_gt_false f f0 Heq2 Heq3));
      try (destruct (Float32.cmp_gt_eq_false f f0 Heq3 Heq1)); try reflexivity.
Qed.

Lemma transl_cond_single_op_correct:
  forall cmp rd r1 r2 k rs m inv,
  exists rs',
     exec_straight ge fn (transl_cond_single_op inv cmp rd r1 r2 k) rs m k rs' m
  /\ rs'#rd = (if inv then Val.notbool (Val.cmpfs cmp rs#r1 rs#r2) else (Val.cmpfs cmp rs#r1 rs#r2))
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  intros.
  assert (cmp = Cne \/ cmp <> Cne).
  destruct cmp; try (right; congruence). left; reflexivity.
  destruct H.
  - subst cmp. simpl.
    set (rs' := nextinstr rs # rd <- (cmpfs (rs r1) (rs r2))).
    destruct (notbool_nor_or rd rd rd bit1 bit1 k rs' m (negb inv)) as [rs'' [EX [RES OTH]]].
    assert (or_t (cmpfs (rs r1) (rs r2)) (cmpfs (rs r1) (rs r2)) bit1 bit1 = Val.notbool (Val.cmpfs Cne (rs r1) (rs r2))).
    rewrite Val.negate_cmpfs_eq. apply (ort_cmpfs (rs r1) (rs r2) bit1 bit1 Ceq true); auto. congruence.
    exists rs''; split. eapply exec_straight_trans. apply exec_straight_one; simpl; eauto. destruct inv; eexact EX.
    rewrite RES. unfold rs'. Simpl. rewrite H.
    split; intuition Simpl. destruct inv; simpl. reflexivity.
    apply Val.notbool_idem4. rewrite OTH; unfold rs'; auto. Simpl.
  - assert (exists bit_1 bit_2,
             bits_of_cond_single cmp = (bit_1, bit_2, true)
             /\ transl_cond_single_op inv cmp rd r1 r2 k =
             Pcmpf rd r1 r2 :: (if inv then Pnor_t rd rd bit_1 rd bit_2 else Por_t rd rd bit_1 rd bit_2) :: k).
    { unfold transl_cond_single_op. destruct cmp; simpl;
        destruct inv; eauto.
      destruct H; auto. destruct H; auto. }
    destruct H0 as [bit_1 [bit_2 [H1 H2]]].
    rewrite H2.
    set (rs' := nextinstr rs # rd <- (cmpfs (rs r1) (rs r2))).
    destruct (notbool_nor_or rd rd rd bit_1 bit_2 k rs' m inv) as [rs'' [EX [RES OTH]]].
    econstructor; split.
    eapply exec_straight_trans. apply exec_straight_one; simpl; eauto. eexact EX.
    unfold rs' in *.
    split; intuition Simpl. rewrite RES. Simpl.
    rewrite (ort_cmpfs (rs r1) (rs r2) bit_1 bit_2 cmp true); auto.
    rewrite OTH; auto.  Simpl.
Qed.


Lemma transl_cond_op_correct:
  forall cond rd args k c rs m,
  transl_cond_op cond rd args k = OK c ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ Val.lessdef (Val.of_optbool (eval_condition cond (map rs (map preg_of args)) m)) rs'#rd
  /\ forall r, r <> PC -> r <> TMP -> r <> rd -> rs'#r = rs#r.
Proof.
  assert (MKTOT: forall ob, Val.of_optbool ob = Val.maketotal (option_map Val.of_bool ob)).
  { destruct ob as [[]|]; reflexivity. }
  intros until m; intros TR.
  destruct cond; simpl in TR; ArgsInv.
  - (* cmp *)
  exploit transl_cond_int32s_correct; eauto. intros (rs' & A & B & C). exists rs'; eauto.
  - (* cmpu *)
  exploit transl_cond_int32u_correct; eauto. intros (rs' & A & B & C).
  exists rs'; repeat split; eauto. rewrite B; auto.
  - (* cmpimm *)
  apply transl_condimm_int32s_correct; eauto with asmgen.
  - (* cmpuimm *)
  apply transl_condimm_int32u_correct; eauto with asmgen.
  - (* cmpfs *)
    destruct ( transl_cond_single_op_correct c0 rd x x0 k rs m false) as [rs' [EX [RES OTH]]].
    exists rs'. split; eauto. rewrite RES.
    fold (Val.cmpfs c0 (rs x) (rs x0)).
    split; auto.
  - (* notcmpfs *)
    destruct ( transl_cond_single_op_correct c0 rd x x0 k rs m true) as [rs' [EX [RES OTH]]].
    exists rs'. split; eauto. rewrite RES.
    rewrite Val.notbool_negb_3.
    fold (Val.cmpfs c0 (rs x) (rs x0)).
    split; auto.
Qed.

(* Translation of arithmetic operations *)

Ltac SimplEval H :=
  match type of H with
  | Some _ = None _ => discriminate
  | Some _ = Some _ => inv H
  | ?a = Some ?b => let A := fresh in assert (A: Val.maketotal a = b) by (rewrite H; reflexivity)
end.

Ltac TranslOpSimpl :=
  econstructor; split;
  [ apply exec_straight_one; [simpl; eauto | reflexivity]
  | split; [ apply Val.lessdef_same; Simpl; fail | intros; Simpl; fail ] ].

Lemma transl_op_correct:
  forall op args res k (rs: regset) m v c,
  transl_op op args res k = OK c ->
  eval_operation ge (rs#SP) op (map rs (map preg_of args)) m = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ Val.lessdef v rs'#(preg_of res)
  /\ forall r, data_preg r = true -> r <> preg_of res -> preg_notin r (destroyed_by_op op) -> rs' r = rs r.
Proof.
  assert (SAME: forall v1 v2, v1 = v2 -> Val.lessdef v2 v1). { intros; subst; auto. }
  intros until c; intros TR EV.
  unfold transl_op in TR; destruct op; ArgsInv; simpl in EV; SimplEval EV; try TranslOpSimpl.
  - (* move *)
    destruct (preg_of res), (preg_of m0); inv TR; TranslOpSimpl.
  - (* intconst *)
    exploit loadimm_correct; eauto.  intros (rs' & A & B & C).
    exists rs'; split; [eauto| rewrite B; auto with asmgen].
  - (* addrsymbol *)
    econstructor; split.
    eapply exec_straight_two; simpl; eauto.
    split; intuition Simpl. rewrite low_high_half. auto.
  - (* addrstack *)
    set (rs' := nextinstr (rs#x <- (rs A10))).
    exploit (addimm_correct x x (Ptrofs.to_int ofs) k rs'); eauto with asmgen.  intros (rs'' & A & B & C).
    exists rs''. split.
    eapply exec_straight_trans.
    apply exec_straight_one; simpl; eauto.
    eexact A. rewrite B. subst rs'.
    split; Simpl.
    destruct (rs A10); auto. simpl. rewrite Ptrofs.of_int_to_int; auto.
    intros. rewrite C; auto with asmgen. Simpl.
  - (* add *)
    exploit add_correct; eauto.  intros (rs' & A & B & C).
    exists rs'; split; [eauto| rewrite B; auto with asmgen].
  - (* addimm *)
    exploit (addimm_correct x0 x n); eauto with asmgen.  intros (rs' & A & B & C).
    exists rs'; split. eauto with asmgen. rewrite B; auto with asmgen.
  - (* and *)
    exploit and_correct; eauto.  intros (rs' & A & B & C).
    exists rs'; split; [eauto| rewrite B; auto with asmgen].
  - (* andimm *)
    exploit (andimm_correct x0 x n); eauto with asmgen.  intros (rs' & A & B & C).
    exists rs'; split; [eauto| rewrite B; auto with asmgen].
  - (* select *)
    exploit transl_cond_op_correct; eauto. intros (rs' & A & B & C).
    inv EQ3.
    econstructor; split.
    eapply exec_straight_trans. eexact A.
    apply exec_straight_one; simpl; eauto.
    split; Simpl.
    destruct (eval_condition c0 rs ## (preg_of ## args) m) as [b|]; simpl in *; auto.
    assert (rs' TMP = if b then Vtrue else Vfalse) by (destruct b, (rs' TMP); inv B; auto).
    rewrite H. rewrite !C; eauto with asmgen.
    destruct b; simpl; change (Int.eq Int.one Int.zero) with false; change (Int.eq Int.zero Int.zero) with true;
      simpl; apply Val.lessdef_normalize.
    intros. Simpl.
  - (* cond *)
    exploit transl_cond_op_correct; eauto. intros (rs' & A & B & C).
    inv EQ0.
    exists rs'; split. eexact A.
    split; auto with asmgen.
  - econstructor; split.
    apply exec_straight_one; simpl; eauto.
    split; intuition Simpl.
    Local Transparent destroyed_by_op.
    simpl in H2. destruct H2. Simpl.
  - econstructor; split.
    apply exec_straight_one; simpl; eauto.
    split; intuition Simpl.
    Local Transparent destroyed_by_op.
    simpl in H2. destruct H2. Simpl.
  - econstructor; split.
    apply exec_straight_one; simpl; eauto.
    split; intuition Simpl.
    Local Transparent destroyed_by_op.
    simpl in H2. destruct H2. Simpl.
  - econstructor; split.
    apply exec_straight_one; simpl; eauto.
    split; intuition Simpl.
    Local Transparent destroyed_by_op.
    simpl in H2. destruct H2. Simpl.
  - (* extr *)
    econstructor; split.
    apply exec_straight_one; simpl; eauto.
    split; intuition Simpl.
    destruct pos, width. simpl.
    rewrite !Int.zero_ext_range_eq; auto.
  - (* extru *)
    econstructor; split.
    apply exec_straight_one; simpl; eauto.
    split; intuition Simpl.
    destruct pos, width. simpl.
    rewrite !Int.zero_ext_range_eq; auto.
  - (* insert *)
    econstructor; split.
    apply exec_straight_one; simpl; eauto.
    split; intuition Simpl.
    destruct pos, width. simpl.
    rewrite !Int.zero_ext_range_eq; auto.
  - (* maddimm *)
    exploit (maddimm_correct x1 x x0 n); eauto with asmgen. intros (rs' & A & B & C).
    exists rs'; split; [eauto| rewrite B; auto with asmgen].
  - (* msubimm *)
    exploit (msubimm_correct x1 x x0 n); eauto with asmgen. intros (rs' & A & B & C).
    exists rs'; split; [eauto| rewrite B; auto with asmgen].
  - (* mul *)
    exploit mul_correct; eauto with asmgen. intros (rs' & A & B & C).
    exists rs'; split; [eauto| rewrite B; auto with asmgen].
  - (* mulimm *)
    exploit (mulimm_correct x0 x n); eauto with asmgen. intros (rs' & A & B & C).
    exists rs'; split; [eauto| rewrite B; auto with asmgen].
  - (* mulhs *)
    econstructor; split.
    apply exec_straight_one; simpl; eauto.
    split; intuition Simpl.
    Local Transparent destroyed_by_op.
    simpl in H1. destruct H1. Simpl.
  - (* mulhu *)
    econstructor; split.
    apply exec_straight_one; simpl; eauto.
    split; intuition Simpl.
    Local Transparent destroyed_by_op.
    simpl in H1. destruct H1. Simpl.
  - (* nandimm *)
    exploit (nandimm_correct x0 x n); eauto with asmgen. intros (rs' & A & B & C).
    exists rs'; split; [eauto| rewrite B; auto with asmgen].
  - (* neg *)
    exploit (move_rr_correct x0 x); eauto with asmgen. intros (rs' & A & B & C).
    econstructor; split. eapply exec_straight_opt_right. eexact A.
    apply exec_straight_one; simpl; eauto. rewrite B. split; intros; Simpl.
  - (* norimm *)
    exploit (norimm_correct x0 x n); eauto with asmgen. intros(rs' & A & B & C).
    exists rs'; split; [eauto| rewrite B; auto with asmgen].
  - (* not *)
    exploit (move_rr_correct x0 x); eauto with asmgen. intros (rs' & A & B & C).
    econstructor; split. eapply exec_straight_opt_right. eexact A.
    apply exec_straight_one; simpl; eauto. rewrite B. split; intros; Simpl.
  - (* or *)
    exploit or_correct; eauto with asmgen. intros (rs' & A & B & C).
    exists rs'; split; [eauto| rewrite B; auto with asmgen].
  - (* orimm *)
    exploit (orimm_correct x0 x n); eauto with asmgen. intros (rs' & A & B & C).
    exists rs'; split; [eauto| rewrite B; auto with asmgen].
  - (* rsubimm *)
    exploit (rsubimm_correct x0 x n); eauto with asmgen. intros (rs' & A & B & C).
    exists rs'; split; [eauto| rewrite B; auto with asmgen].
  - (* shl *)
    econstructor; split.
    apply exec_straight_one; simpl; eauto.
    split; intuition Simpl. unfold Val.shl.
    destruct (rs x), (rs x0); auto.
    destruct (Int.ltu i0 Int.iwordsize) eqn:?; auto.
    rewrite sh_shl; auto. simpl. rewrite Heqb. auto.
  - (* slimm *)
    exploit (slimm_correct x0 x a); eauto with asmgen. intros (rs' & A & B & C).
    exists rs'; split; [eauto| rewrite B; auto with asmgen].
  - (* shr *)
    econstructor; split. eapply exec_straight_two; simpl; auto.
    split; intuition Simpl.
    rewrite Int.sign_ext_range_eq; auto.
    destruct (rs x), (rs x0); auto. rewrite Int.sub_zero_r.
    unfold Val.shr. destruct (Int.ltu i0 Int.iwordsize) eqn:?; auto.
    rewrite sha_shr; auto. simpl. rewrite Heqb. auto.
  - (* asrimm *)
    exploit (asrimm_correct x0 x a); eauto  with asmgen. intros (rs' & A & B & C).
    exists rs'; split; [eauto| rewrite B; auto with asmgen].
  - (* shru *)
    econstructor; split. eapply exec_straight_two; simpl; auto.
    split; intuition Simpl.
    rewrite Int.sign_ext_range_eq; auto.
    destruct (rs x), (rs x0); auto. rewrite Int.sub_zero_r.
    unfold Val.shru. destruct (Int.ltu i0 Int.iwordsize) eqn:?; auto.
    rewrite sh_shru; auto. simpl. rewrite Heqb. auto.
  - (* lsrimm *)
    exploit (lsrimm_correct x0 x a); eauto  with asmgen. intros (rs' & A & B & C).
    exists rs'; split; [eauto| rewrite B; auto with asmgen].
  - (* shrx *)
    clear H. exploit Val.shrx_shr_2; eauto. intros E; subst v; clear EV.
    destruct (Int.eq n Int.zero) eqn:?.
    + econstructor; split. apply exec_straight_one; simpl; eauto.
      split; intuition Simpl.
    + destruct n as [n Range]; simpl in *.
      econstructor; split.
      eapply exec_straight_step. simpl; reflexivity. auto.
      eapply exec_straight_step. simpl; reflexivity. auto.
      eapply exec_straight_step. simpl; reflexivity. auto.
      apply exec_straight_one. simpl; reflexivity. auto.
      split; intros; Simpl.
      rewrite (Int.sign_ext_range_eq (Int.neg (Int.repr 31))) by auto.
      assert (Int.ltu (Int.sub Int.iwordsize n) Int.iwordsize  = true).
      { apply Int.ltu_inv in Range.
        unfold Int.sub.
        change (Int.unsigned Int.iwordsize) with 32 in *.
        apply zlt_true.
        rewrite Int.unsigned_repr.
        change (Int.unsigned Int.iwordsize) with 32.
        assert (Int.unsigned n <> 0). unfold Int.eq in Heqb.
        rewrite Int.unsigned_zero in Heqb.
        destruct (zeq (Int.unsigned n) 0) eqn:?; auto; inv Heqb.
        lia. change (Int.max_unsigned) with 4294967295. lia.
      }
      rewrite !shift_sc9_eq'; auto.
      rewrite !sha_shr; auto.
      rewrite sh_shru; auto.
  - (* sub *)
    exploit sub_correct;  eauto  with asmgen. intros (rs' & A & B & C).
    exists rs'; split; [eauto| rewrite B; auto with asmgen].
  - (* xnorimm *)
     exploit (xnorimm_correct x0 x n); eauto  with asmgen. intros (rs' & A & B & C).
     exists rs'; split; [eauto| rewrite B; auto with asmgen].
  - (* xor *)
    exploit xor_correct;  eauto  with asmgen. intros (rs' & A & B & C).
    exists rs'; split; [eauto| rewrite B; auto with asmgen].
  - (* xorimm *)
     exploit (xorimm_correct x0 x n); eauto  with asmgen. intros (rs' & A & B & C).
     exists rs'; split; [eauto| rewrite B; auto with asmgen].
Qed.

(** Memory accesses *)

Lemma indexed_memory_access_correct:
  forall mk1 mk2 (base : areg) ofs k (rs: regset) m ,
  exists base' ofs' rs',
     exec_straight_opt ge fn (indexed_memory_access mk1 mk2 base ofs k) rs m
                       (if Ptrofs.eq ofs Ptrofs.zero then mk1 base' :: k else mk2 base' ofs' :: k) rs' m
  /\ Val.offset_ptr (rs'#base') (if Ptrofs.eq ofs Ptrofs.zero then Ptrofs.zero else (Ptrofs.of_int ofs')) = Val.offset_ptr rs#base ofs
  /\ forall r, r <> PC -> r <> TMPA -> rs'#r = rs#r.
Proof.
  intros.
  unfold indexed_memory_access.
  destruct (Ptrofs.eq ofs Ptrofs.zero) eqn:?;
           [|destruct (get_sconst16 (Ptrofs.to_int ofs)) eqn:?].
  - exists base, sconst16_zero, rs; split.
    constructor. simpl.
    rewrite (Ptrofs.same_if_eq ofs Ptrofs.zero); auto.
  - exists base, s, rs; split.
    constructor. simpl. rewrite (get_sconst16_sound (Ptrofs.to_int ofs) s); auto.
    rewrite Ptrofs.of_int_to_int; auto.
  - generalize (low_high_s (Ptrofs.to_int ofs)). intros.
    exists TMPA, (low_s (Ptrofs.to_int ofs)).
    Local Opaque low_s high_s.
    econstructor; split.
    constructor. apply exec_straight_one; simpl; eauto.
    split; Simpl. destruct (rs base); auto; simpl.
    rewrite Ptrofs.add_assoc. f_equal. f_equal.
    rewrite <- Ptrofs.of_int_to_int; auto.
    rewrite <- H at 3.
    symmetry; auto with ptrofs.
    intuition Simpl.
Qed.


Lemma indexed_load_access_correct:
  forall chunk
    (mk1: areg -> instruction)
    (mk2: areg -> sconst16 -> instruction) rd m,
  (forall base rs,
     exec_instr ge fn (mk1 base) rs m = exec_load chunk rs m rd base sconst16_zero) ->
  (forall base ofs rs,
     exec_instr ge fn (mk2 base ofs) rs m = exec_load chunk rs m rd base ofs) ->
  forall (base: areg) ofs k (rs: regset) v,
  Mem.loadv chunk m (Val.offset_ptr rs#base ofs) = Some v ->
  rd <> PC ->
  exists rs',
     exec_straight ge fn (indexed_memory_access mk1 mk2 base ofs k) rs m k rs' m
  /\ rs'#rd = v
  /\ forall r, r <> PC -> r <> TMPA -> r <> rd -> rs'#r = rs#r.
Proof.
  intros until m; intros EXEC1 EXEC2; intros until v; intros LOAD NOTPC.
  exploit indexed_memory_access_correct; eauto.
  intros (base' & ofs' & rs' & A & B & C).
  destruct (Ptrofs.eq ofs Ptrofs.zero) eqn:?.
  - econstructor; split.
    eapply exec_straight_opt_right. eexact A. rewrite Heqb in *. apply exec_straight_one. rewrite EXEC1.
    unfold exec_load. simpl. change (Ptrofs.of_int Int.zero) with Ptrofs.zero.
    rewrite B. rewrite LOAD. auto. Simpl.  split; intuition Simpl.
  - econstructor; split.
    eapply exec_straight_opt_right. eexact A. rewrite Heqb in *. apply exec_straight_one. rewrite EXEC2.
    unfold exec_load. rewrite B. rewrite LOAD. auto. Simpl. split; intuition Simpl.
Qed.

Lemma indexed_store_access_correct:
  forall chunk
    (mk1: areg -> instruction)
    (mk2: areg -> sconst16 -> instruction) r1 m,
  (forall base rs,
     exec_instr ge fn (mk1 base) rs m = exec_store chunk rs m r1 base sconst16_zero) ->
  (forall base ofs rs,
     exec_instr ge fn (mk2 base ofs) rs m = exec_store chunk rs m r1 base ofs) ->
  forall (base: areg) ofs k (rs: regset) m',
  Mem.storev chunk m (Val.offset_ptr rs#base ofs) (rs#r1) = Some m' ->
  r1 <> TMPA -> r1 <> PC ->
  exists rs',
     exec_straight ge fn (indexed_memory_access mk1 mk2 base ofs k) rs m k rs' m'
  /\ forall r, r <> PC -> r <> TMPA -> rs'#r = rs#r.
Proof.
  intros until m; intros EXEC1 EXEC2; intros until m'; intros STORE NOT31' NOTPC.
  exploit indexed_memory_access_correct; eauto.
  intros (base' & ofs' & rs' & A & B & C).
  destruct (Ptrofs.eq ofs Ptrofs.zero) eqn:?.
  - econstructor; split.
    eapply exec_straight_opt_right. eexact A. rewrite Heqb in *. apply exec_straight_one. rewrite EXEC1.
    unfold exec_store. simpl. change (Ptrofs.of_int Int.zero) with Ptrofs.zero.
    rewrite B, C, STORE; auto.  eauto. intuition Simpl.
  - econstructor; split.
    eapply exec_straight_opt_right. eexact A. rewrite Heqb in *. apply exec_straight_one. rewrite EXEC2.
    unfold exec_store. rewrite B, C, STORE; auto. Simpl. intuition Simpl.
Qed.

Lemma loadind_correct:
  forall base ofs ty dst k c (rs: regset) m v,
  loadind base ofs ty dst k = OK c ->
  Mem.loadv (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, r <> PC -> r <> TMPA -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  intros until v; intros TR LOAD.
  assert (A: exists mk1 mk2,
                c = indexed_memory_access mk1 mk2 base ofs k
             /\ forall base' ofs' rs',
                  exec_instr ge fn (mk1 base') rs' m =
                  exec_load (chunk_of_type ty) rs' m (preg_of dst) base' sconst16_zero
                /\
                  exec_instr ge fn (mk2 base' ofs') rs' m =
                  exec_load (chunk_of_type ty) rs' m (preg_of dst) base' ofs').
  { unfold loadind in TR. destruct ty, (preg_of dst); inv TR; econstructor; econstructor; eauto. }
  destruct A as (mk1 & mk2 & B & C). subst c.
  eapply indexed_load_access_correct; eauto with asmgen.
  intros. destruct (C base0 sconst16_zero rs0). auto.
  intros. destruct (C base0 ofs0 rs0). auto.
Qed.

Lemma loadind2_correct:
  forall base ofs ty dst k c (rs: regset) m v,
  loadind2 base ofs ty dst k = OK c ->
  Mem.loadv (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, r <> PC -> r <> TMPA -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  intros.  unfold loadind2 in H. monadInv H.
  set (rs' := nextinstr (rs#A14 <- (rs#base))).
  destruct (loadind_correct A14 ofs ty dst k x rs' m v EQ H0) as (rs'' & A & B & C).
  exists rs''; split. eapply exec_straight_trans. apply exec_straight_one; simpl; reflexivity.
  eexact A. subst rs'. split; eauto with asmgen. intros. rewrite C; auto with asmgen.
  Simpl.
Qed.

Lemma storeind_correct:
  forall base ofs ty src k c (rs: regset) m m',
  storeind src base ofs ty k = OK c ->
  Mem.storev (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) rs#(preg_of src) = Some m' ->
  base <> TMPA ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, r <> PC -> r <> TMPA -> rs'#r = rs#r.
Proof.
  intros until m'; intros TR STORE NOT31.
  assert (A: exists mk1 mk2,
                c = indexed_memory_access mk1 mk2 base ofs k
             /\ forall base' ofs' rs',
                  exec_instr ge fn (mk1 base') rs' m =
                  exec_store (chunk_of_type ty) rs' m (preg_of src) base' sconst16_zero
                /\
                  exec_instr ge fn (mk2 base' ofs') rs' m =
                  exec_store (chunk_of_type ty) rs' m (preg_of src) base' ofs').
  { unfold storeind in TR. destruct ty, (preg_of src); inv TR; econstructor; econstructor; eauto. }
  destruct A as (mk1 & mk2 & B & C). subst c.
  eapply indexed_store_access_correct; eauto with asmgen.
  intros. destruct (C base0 sconst16_zero rs0). auto.
  intros. destruct (C base0 ofs0 rs0). auto.
Qed.


Lemma loadind_ptr_correct:
  forall (base: areg) ofs (dst: areg) k (rs: regset) m v,
  Mem.loadv Mptr m (Val.offset_ptr rs#base ofs) = Some v ->
  base <> TMPA ->
  exists rs',
     exec_straight ge fn (loadind_ptr base ofs dst k) rs m k rs' m
  /\ rs'#dst = v
  /\ forall r, r <> PC -> r <> TMPA -> r <> dst -> rs'#r = rs#r.
Proof.
  unfold Mptr. simpl. intros.
  eapply indexed_load_access_correct; intros; simpl; eauto with asmgen.
Qed.
Lemma loadind_ptr2_correct:
  forall (base: areg) ofs (dst: dreg) k (rs: regset) m v,
  Mem.loadv Mptr m (Val.offset_ptr rs#base ofs) = Some v ->
  base <> TMPA ->
  exists rs',
     exec_straight ge fn (loadind_ptr2 base ofs dst k) rs m k rs' m
  /\ rs'#dst = v
  /\ forall r, r <> PC -> r <> TMPA -> r <> dst -> rs'#r = rs#r.
Proof.
  unfold Mptr. simpl. intros.
  eapply indexed_load_access_correct; intros; simpl; eauto with asmgen.
Qed.

Lemma storeind_ptr_correct:
  forall (base: areg) ofs (src: areg) k (rs: regset) m m',
  Mem.storev Mptr m (Val.offset_ptr rs#base ofs) rs#src = Some m' ->
  base <> TMPA -> src <> TMPA ->
  exists rs',
     exec_straight ge fn (storeind_ptr src base ofs k) rs m k rs' m'
  /\ forall r, r <> PC -> r <> TMPA -> rs'#r = rs#r.
Proof.
  unfold Mptr. simpl. intros.
  eapply indexed_store_access_correct; intros; simpl; eauto with asmgen.
Qed.

Lemma lea_correct:
  forall rd id k rs m,
  exists rs',
  exec_straight ge fn (lea rd id k) rs m k rs' m
  /\ rs'#rd = Genv.symbol_address ge id Ptrofs.zero
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  intros; unfold lea.
  econstructor; split.
  eapply exec_straight_two; simpl; eauto.
  split; intuition Simpl. rewrite low_high_half.
  reflexivity.
Qed.

Lemma transl_load_access_correct:
  forall chunk
    (mk1: areg -> instruction)
    (mk2: areg -> sconst16 -> instruction)
    addr args k c rd (rs: regset) m v v',
  (forall base rs,
     exec_instr ge fn (mk1 base) rs m = exec_load chunk rs m rd base sconst16_zero) ->
  (forall base ofs rs,
     exec_instr ge fn (mk2 base ofs) rs m = exec_load chunk rs m rd base ofs) ->
  transl_memory_access mk1 mk2 addr args k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some v ->
  Mem.loadv chunk m v = Some v' ->
  rd <> PC ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#rd = v'
  /\ forall r, r <> PC -> r <> TMPA -> r <> rd -> rs'#r = rs#r.
Proof.
  intros until v'; intros INSTR1 INSTR2 TR EV LOAD NOTPC.
  unfold transl_memory_access in TR; destruct addr; ArgsInv.
  - (* Aindexed *)
    inv EV.
    set (rs' := nextinstr (rs#TMPA <- (rs#x))).
    exploit (indexed_load_access_correct chunk mk1 mk2 rd m INSTR1 INSTR2 TMPA (Ptrofs.of_int ofs) k rs'); eauto.
    subst rs'. Simpl. destruct (rs x); inv LOAD; eauto.
    intros (rs'' & A & B & C).
    exists rs''; split.
    eapply exec_straight_trans. apply exec_straight_one; simpl; eauto. eexact A. split. assumption.
    intros. rewrite C; eauto. subst rs'. Simpl.
  - (* Aglobal *)
    inv EV. inv TR.
    destruct (lea_correct TMPA id (indexed_memory_access mk1 mk2 A14 ofs k) rs m) as [rs' [EX [RES OTH]]].
    exploit (indexed_load_access_correct chunk mk1 mk2 rd m INSTR1 INSTR2 TMPA ofs k rs'); eauto.
    rewrite RES. rewrite <- Genv.shift_symbol_address.
    rewrite Ptrofs.add_zero_l. eexact LOAD.
    intros (rs'' & EX' & RES' & OTH').
    exists rs''; split.
    eapply exec_straight_trans. eexact EX. eexact EX'. rewrite RES'.
    split; auto. intros. rewrite OTH'; eauto.
  - (* Ainstack *)
    inv EV. inv TR. eapply indexed_load_access_correct; eauto.
Qed.

Lemma transl_store_access_correct:
  forall chunk
    (mk1: areg -> instruction)
    (mk2: areg -> sconst16 -> instruction) addr args k c r1 (rs: regset) m v m',
  (forall base rs,
     exec_instr ge fn (mk1 base) rs m = exec_store chunk rs m r1 base sconst16_zero) ->
  (forall base ofs rs,
     exec_instr ge fn (mk2 base ofs) rs m = exec_store chunk rs m r1 base ofs) ->
  transl_memory_access mk1 mk2 addr args k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some v ->
  Mem.storev chunk m v rs#r1 = Some m' ->
  r1 <> PC -> r1 <> TMPA ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, r <> PC -> r <>TMPA -> rs'#r = rs#r.
Proof.
  intros until m'; intros INSTR1 INSTR2 TR EV STORE NOTPC NOTTMPA.
  unfold transl_memory_access in TR; destruct addr; ArgsInv.
  - (* Aindexed *)
    inv EV.
    set (rs' := nextinstr (rs#TMPA <- (rs#x))).
    exploit (indexed_store_access_correct chunk mk1 mk2 r1 m INSTR1 INSTR2 TMPA (Ptrofs.of_int ofs) k rs'); eauto.
    subst rs'. Simpl. destruct (rs x); inv STORE; eauto.
    intros (rs'' & A & B).
    exists rs''; split.
    eapply exec_straight_trans. apply exec_straight_one; simpl; eauto. eexact A.
    intros. rewrite B; eauto. subst rs'. Simpl.
  - (* Aglobal *)
    inv EV. inv TR.
    destruct (lea_correct TMPA id (indexed_memory_access mk1 mk2 A14 ofs k) rs m) as [rs' [EX [RES OTH]]].
    exploit (indexed_store_access_correct chunk mk1 mk2 r1 m INSTR1 INSTR2 TMPA ofs k rs'); eauto.
    rewrite RES. rewrite <- Genv.shift_symbol_address.
    rewrite Ptrofs.add_zero_l. rewrite OTH; eauto with asmgen.
    intros (rs'' & EX' & OTH').
    exists rs''; split. eapply exec_straight_trans. eexact EX. eexact EX'.
    intros. rewrite OTH'; auto.
  - (* Ainstack *)
    inv EV. inv TR. eapply indexed_store_access_correct; eauto.
Qed.

Lemma transl_load_correct:
  forall chunk addr args dst k c (rs: regset) m a v,
  transl_load chunk addr args dst k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some a ->
  Mem.loadv chunk m a = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, r <> PC -> r <> TMPA -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  intros until v; intros TR EV LOAD.
  assert (A: exists mk1 mk2,
           transl_memory_access mk1 mk2 addr args k = OK c
           /\ (forall base' ofs' rs',
               exec_instr ge fn (mk1 base') rs' m =
               exec_load chunk rs' m (preg_of dst) base' sconst16_zero
               /\
                 exec_instr ge fn (mk2 base' ofs') rs' m =
                 exec_load chunk rs' m (preg_of dst) base' ofs')).
  { unfold transl_load in TR. destruct chunk; ArgsInv;
      econstructor; econstructor; split; eauto.
  }
  destruct A as (mk1 & mk2 & A & B).
  eapply transl_load_access_correct; eauto with asmgen.
  intros. destruct (B base sconst16_zero rs0). auto.
  intros. destruct (B base ofs rs0). auto.
Qed.


Lemma transl_store_correct:
  forall chunk addr args src k c (rs: regset) m a m',
  transl_store chunk addr args src k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some a ->
  Mem.storev chunk m a rs#(preg_of src) = Some m' ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, r <> PC -> r <> TMPA -> rs'#r = rs#r.
Proof.
  intros until m'; intros TR EV STORE.
  assert (A: exists mk1 mk2 chunk',
      transl_memory_access mk1 mk2 addr args k = OK c
   /\ (forall base ofs rs,
       exec_instr ge fn (mk1 base) rs m = exec_store chunk' rs m (preg_of src) base sconst16_zero
       /\ exec_instr ge fn (mk2 base ofs) rs m = exec_store chunk' rs m (preg_of src) base ofs)
      /\ Mem.storev chunk m a rs#(preg_of src) = Mem.storev chunk' m a rs#(preg_of src)).
  {unfold transl_store in TR. destruct chunk; ArgsInv;
      (econstructor; econstructor; econstructor; split; eauto; split; [ intros; simpl; split; reflexivity | auto]).
   destruct a; auto. apply Mem.store_signed_unsigned_8.
   destruct a; auto. apply Mem.store_signed_unsigned_16.
  }
  destruct A as (mk1 & mk2 & chunk' & A & B & C).
  rewrite C in STORE; clear C.
  eapply transl_store_access_correct; eauto with asmgen.
  intros. destruct (B base sconst16_zero rs0). auto.
  intros. destruct (B base ofs rs0). auto.
Qed.

(** Function epilogues *)

Lemma make_epilogue_correct:
  forall ge0 f m stk soff cs m' ms rs k tm,
  load_stack m (Vptr stk soff) Tptr f.(fn_link_ofs) = Some (parent_sp cs) ->
  load_stack m (Vptr stk soff) Tptr f.(fn_retaddr_ofs) = Some (parent_ra cs) ->
  Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
  agree ms (Vptr stk soff) rs ->
  Mem.extends m tm ->
  match_stack ge0 cs ->
  exists rs', exists tm',
     exec_straight ge fn (make_epilogue f k) rs tm k rs' tm'
  /\ agree ms (parent_sp cs) rs'
  /\ Mem.extends m' tm'
  /\ rs'#RA = parent_ra cs
  /\ rs'#SP = parent_sp cs
  /\ (forall r, r <> PC -> r <> RA -> r <> SP -> r <> TMP -> r <> TMPA -> rs'#r = rs#r).
Proof.
  intros until tm; intros LP LRA FREE AG MEXT MCS.
  exploit Mem.loadv_extends. eauto. eexact LP. auto. simpl. intros (parent' & LP' & LDP').
  exploit Mem.loadv_extends. eauto. eexact LRA. auto. simpl. intros (ra' & LRA' & LDRA').
  exploit lessdef_parent_sp; eauto. intros EQ; subst parent'; clear LDP'.
  exploit lessdef_parent_ra; eauto. intros EQ; subst ra'; clear LDRA'.
  exploit Mem.free_parallel_extends; eauto. intros (tm' & FREE' & MEXT').
  unfold make_epilogue.
  exploit (loadind_ptr_correct SP (fn_retaddr_ofs f) RA (Pfreeframe (fn_stacksize f) (fn_link_ofs f) :: k) rs tm).
    rewrite <- (sp_val _ _ _ AG). simpl. eexact LRA'. congruence.
  intros (rs1 & A1 & B1 & C1).
  econstructor; econstructor; split.
  eapply exec_straight_trans. eexact A1. apply exec_straight_one. simpl.
    rewrite (C1 A10) by auto with asmgen. rewrite <- (sp_val _ _ _ AG). simpl; rewrite LP'.
    rewrite FREE'. eauto. auto.
  split. apply agree_nextinstr.
    apply agree_change_sp with (Vptr stk soff).
    apply agree_exten with rs; auto. intros; apply C1; auto with asmgen.
    eapply parent_sp_def; eauto.
  split; auto.
  repeat split; intros; Simpl.
Qed.

Lemma make_epilogue'_correct:
  forall ge0 f r m stk soff cs m' ms rs k tm,
  r <> TMP ->
  load_stack m (Vptr stk soff) Tptr f.(fn_link_ofs) = Some (parent_sp cs) ->
  load_stack m (Vptr stk soff) Tptr f.(fn_retaddr_ofs) = Some (parent_ra cs) ->
  Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
  agree ms (Vptr stk soff) rs ->
  Mem.extends m tm ->
  match_stack ge0 cs ->
  exists rs', exists tm',
     exec_straight ge fn (make_epilogue' f r k) rs tm k rs' tm'
  /\ agree ms (parent_sp cs) rs'
  /\ Mem.extends m' tm'
  /\ rs'#RA = parent_ra cs
  /\ rs'#SP = parent_sp cs
  /\ rs'#TMPA = rs#r
  /\ (forall r, r <> PC -> r <> RA -> r <> SP -> r <> TMP -> r <> TMPA -> rs'#r = rs#r).
Proof.
  intros until tm; intros NOTT LP LRA FREE AG MEXT MCS.
  exploit Mem.loadv_extends. eauto. eexact LP. auto. simpl. intros (parent' & LP' & LDP').
  exploit Mem.loadv_extends. eauto. eexact LRA. auto. simpl. intros (ra' & LRA' & LDRA').
  exploit lessdef_parent_sp; eauto. intros EQ; subst parent'; clear LDP'.
  exploit lessdef_parent_ra; eauto. intros EQ; subst ra'; clear LDRA'.
  exploit Mem.free_parallel_extends; eauto. intros (tm' & FREE' & MEXT').
  unfold make_epilogue'.
  exploit (loadind_ptr_correct SP (fn_retaddr_ofs f) RA (Pfreeframe (fn_stacksize f) (fn_link_ofs f) :: Pmov_a A14 r :: k) rs tm).
  Simpl. rewrite <- (sp_val _ _ _ AG). simpl. eexact LRA'. congruence.
  intros (rs1 & A1 & B1 & C1).
  econstructor; econstructor; split.
  eapply exec_straight_trans. eexact A1. eapply exec_straight_two; simpl; eauto.
  rewrite (C1 A10) by auto with asmgen. Simpl. rewrite <- (sp_val _ _ _ AG). simpl; rewrite LP'.
  rewrite FREE'. eauto. auto.
  split. apply agree_nextinstr.
  apply agree_set_other; auto with asmgen.
  apply agree_nextinstr.
  apply agree_change_sp with (Vptr stk soff).
  apply agree_exten with rs; auto. intros. rewrite C1; auto with asmgen.
  eapply parent_sp_def; eauto.
  split. auto.
  repeat split; intros; Simpl.
Qed.


End CONSTRUCTORS.
