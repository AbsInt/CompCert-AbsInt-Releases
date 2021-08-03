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

(** Correctness proof for Peaktop generation: auxiliary results. *)

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
Require Import Asm.
Require Import Asmgen.
Require Import Conventions.
Require Import Asmgenproof0.

Local Transparent Archi.ptr64.

(** * Properties of low half/high half decomposition *)

Lemma low_high_u_14_18:
  forall n, Int.or (Int.shl (high_u_18 n) (Int.repr 14)) (low_u_14 n) = n.
Proof.
  intros. unfold high_u_18, low_u_14.
  rewrite Int.shl_rolm. rewrite Int.shru_rolm.
  rewrite Int.rolm_rolm.
  rewrite Int.rolm_zero. rewrite <- Int.and_or_distrib.
  exact (Int.and_mone n).
  apply int_wordsize_divides_modulus. reflexivity. reflexivity.
Qed.

Lemma low_high_s_14_18:
  forall n, Int.add (Int.shl (high_s_18 n) (Int.repr 14)) (low_s_14 n) = n.
Proof.
  intros.
  rewrite Int.shl_mul_two_p.
  unfold high_s_18.
  rewrite <- (Int.divu_pow2 (Int.sub n (low_s_14 n)) (Int.repr 16384) (Int.repr 14)).
  2: reflexivity.
  change (two_p (Int.unsigned (Int.repr 14))) with 16384.
  set (x := Int.sub n (low_s_14 n)).
  assert (x = Int.add (Int.mul (Int.divu x (Int.repr 16384)) (Int.repr 16384))
                      (Int.modu x (Int.repr 16384))).
  { apply Int.modu_divu_Euclid. vm_compute; congruence. }
  assert (Int.modu x (Int.repr 16384) = Int.zero).
  { unfold Int.modu, Int.zero. decEq.
    change 0 with (0 mod 16384).
    change (Int.unsigned (Int.repr 16384)) with 16384.
    apply eqmod_mod_eq. lia.
    unfold x, low_s_14. eapply eqmod_trans.
    apply  eqmod_divides with Int.modulus.
    unfold Int.sub. apply Int.eqm_unsigned_repr_l. apply Int.eqm_refl.
    exists 262144. compute. auto.
    replace 0 with (Int.unsigned n - Int.unsigned n) by lia.
    apply eqmod_sub. apply eqmod_refl. apply Int.eqmod_sign_ext'.
    compute; auto. }
  rewrite H0 in H. rewrite Int.add_zero in H.
  rewrite <- H. unfold x. rewrite Int.sub_add_opp. rewrite Int.add_assoc.
  rewrite (Int.add_commut (Int.neg (low_s_14 n))). rewrite <- Int.sub_add_opp.
  rewrite Int.sub_idem. apply Int.add_zero.
Qed.

Lemma low_high_s_18_14:
  forall n, Int.add (Int.shl (high_s_14 n) (Int.repr 18)) (low_s_18 n) = n.
Proof.
  intros.
  rewrite Int.shl_mul_two_p.
  unfold high_s_14.
  rewrite <- (Int.divu_pow2 (Int.sub n (low_s_18 n)) (Int.repr 262144) (Int.repr 18)).
  2: reflexivity.
  change (two_p (Int.unsigned (Int.repr 18))) with 262144.
  set (x := Int.sub n (low_s_18 n)).
  assert (x = Int.add (Int.mul (Int.divu x (Int.repr 262144)) (Int.repr 262144))
                      (Int.modu x (Int.repr 262144))).
  { apply Int.modu_divu_Euclid. vm_compute; congruence. }
  assert (Int.modu x (Int.repr 262144) = Int.zero).
  { unfold Int.modu, Int.zero. decEq.
    change 0 with (0 mod 262144).
    change (Int.unsigned (Int.repr 262144)) with 262144.
    apply eqmod_mod_eq. lia.
    unfold x, low_s_18. eapply eqmod_trans.
    apply  eqmod_divides with Int.modulus.
    unfold Int.sub. apply Int.eqm_unsigned_repr_l. apply Int.eqm_refl.
    exists 16384. compute. auto.
    replace 0 with (Int.unsigned n - Int.unsigned n) by lia.
    apply eqmod_sub. apply eqmod_refl. apply Int.eqmod_sign_ext'.
    compute; auto. }
  rewrite H0 in H. rewrite Int.add_zero in H.
  rewrite <- H. unfold x. rewrite Int.sub_add_opp. rewrite Int.add_assoc.
  rewrite (Int.add_commut (Int.neg (low_s_18 n))). rewrite <- Int.sub_add_opp.
  rewrite Int.sub_idem. apply Int.add_zero.
Qed.


(** Properties of registers *)

Lemma preg_of_not_TMP: forall r, preg_of r <> TMP.
Proof.
  destruct r; simpl; congruence.
Qed.
Global Hint Resolve preg_of_not_TMP: asmgen.

Lemma preg_of_not_SP: forall r, GPR SP <> preg_of r.
Proof.
  destruct r; simpl; congruence.
Qed.
Global Hint Resolve preg_of_not_SP: asmgen.

Lemma reg_of_eq:
  forall r r', reg_of r = OK r' -> preg_of r = r'.
Proof.
  unfold reg_of; intros. destruct (preg_of r); inv H; auto.
Qed.
Global Hint Resolve reg_of_eq: asmgen.

Lemma reg_of_not_TMP:
  forall m r, reg_of m = OK r -> r <> TMP.
Proof.
  unfold reg_of; intros. destruct (preg_of m) eqn:E; inv H.
  red; intros; subst r. elim (preg_of_not_TMP m); auto.
Qed.
Global Hint Resolve reg_of_not_TMP: asmgen.

Lemma reg_of_not_SP:
  forall m r, reg_of m = OK r -> SP <> r.
Proof.
  unfold reg_of; intros. destruct (preg_of m) eqn:E; inv H.
  red; intros; subst r. elim (preg_of_not_SP m); auto.
Qed.
Global Hint Resolve reg_of_not_SP: asmgen.

Lemma reg_of_not_SP':
  forall m r, reg_of m = OK r -> GPR SP <> GPR r.
Proof.
  intros. apply reg_of_not_SP in H. congruence.
Qed.
Global Hint Resolve reg_of_not_SP': asmgen.

Lemma reg_of_data_preg:
  forall m r, reg_of m = OK r -> data_preg r = true.
Proof.
  unfold reg_of; intros. destruct (preg_of m) eqn:E; inv H.
  destruct r, m; simpl in *; try (auto || discriminate E).
Qed.
Global Hint Resolve reg_of_data_preg: asmgen.

Lemma not_TMP_data_preg:
  forall r, r <> TMP -> data_preg (GPR r) = true.
Proof.
  destruct r; auto.
Qed.
Global Hint Resolve not_TMP_data_preg : asmgen.

Lemma data_preg_not_TMP:
  forall r, data_preg r = true -> r <> TMP.
Proof.
  destruct r; simpl; auto; try congruence.
  destruct r; intros H; inv H; congruence.
Qed.
Global Hint Resolve data_preg_not_TMP : asmgen.


(** [undef_flags] and [nextinstr_nf] *)

(** Useful simplification tactic *)

Ltac Simplif :=
  ((rewrite nextinstr_inv by eauto with asmgen)
  || (rewrite nextinstr_inv1 by eauto with asmgen)
  || (rewrite Pregmap.gss)
  || (rewrite nextinstr_pc)
  || (rewrite Pregmap.gso by eauto with asmgen)); auto with asmgen.

Ltac Simpl := repeat Simplif.

(** * Correctness of PEAKTOP constructor functions *)

Section CONSTRUCTORS.

Variable ge: genv.
Variable fn: function.

(** 32-bit integer constants and arithmetic *)

Lemma loadimm_correct:
  forall rd n k rs m,
  exists rs',
     exec_straight ge fn (loadimm rd n k) rs m k rs' m
  /\ rs'#rd = Vint n
  /\ forall r': preg, data_preg r' = true ->  r' <> rd -> rs'#r' = rs#r'.
Proof.
  intros. unfold loadimm.
  case (Int.eq (high_s_14 n) Int.zero).
  (* move immediate *)
  econstructor; split. apply exec_straight_one.
  simpl; eauto. auto.
  intuition Simpl.
  generalize (Int.eq_spec (low_s_18 n) Int.zero); case (Int.eq (low_s_18 n) Int.zero).
  (* move immediate + shift *)
  econstructor; split. eapply exec_straight_two; simpl; eauto.
  split; Simpl. simpl.
  replace (Int.ltu (Int.repr 18) Int.iwordsize) with true by auto.
  rewrite  <- (Int.add_zero (Int.shl (high_s_14 n) (Int.repr 18))).
  rewrite <- H. rewrite low_high_s_18_14. auto.
  intuition Simpl.
  (* move immediate + shift + add *)
  econstructor; split. eapply exec_straight_three; simpl; eauto.
  split; intros; Simpl. simpl.
  replace (Int.ltu (Int.repr 14) Int.iwordsize) with true by auto.
  simpl.
  rewrite low_high_u_14_18. auto.
Qed.

Lemma opimm_correct:
  forall (op: reg -> reg -> instruction)
    (opi: reg -> int -> instruction)
    (sem: val -> val -> val) m,
  (forall d s rs,
   exec_instr ge fn (op d s) rs m = Next (nextinstr (rs#d <- (sem rs#d rs#s))) m) ->
  (forall d n rs,
   exec_instr ge fn (opi d n) rs m = Next (nextinstr (rs#d <- (sem rs#d (Vint n)))) m) ->
  forall rd n k rs,
    rd <> TMP ->
  exists rs',
     exec_straight ge fn (opimm op opi rd n k) rs m k rs' m
  /\ rs'#rd = sem rs#rd (Vint n)
  /\ forall r' : preg, data_preg r' = true ->  r' <> rd -> rs'#r' = rs#r'.
Proof.
  intros. unfold opimm.
  destruct (Int.eq (high_s_18 n) Int.zero).
  - econstructor; split. apply exec_straight_one; eauto.
    intuition Simpl.
  - destruct (loadimm_correct TMP n (op rd TMP :: k) rs m) as (rs' & A & B & C).
    econstructor; split.
    eapply exec_straight_trans. eexact A. apply exec_straight_one; eauto.
    split; intros; Simpl. rewrite B, C; auto with asmgen.
Qed.

Lemma opuimm_correct:
  forall (op: reg -> reg -> instruction)
    (opi: reg -> int -> instruction)
    (sem: val -> val -> val) m,
  (forall d s rs,
   exec_instr ge fn (op d s) rs m = Next (nextinstr (rs#d <- (sem rs#d rs#s))) m) ->
  (forall d n rs,
   exec_instr ge fn (opi d n) rs m = Next (nextinstr (rs#d <- (sem rs#d (Vint n)))) m) ->
  forall rd n k rs,
    rd <> TMP ->
  exists rs',
     exec_straight ge fn (opuimm op opi rd n k) rs m k rs' m
  /\ rs'#rd = sem rs#rd (Vint n)
  /\ forall r' : preg, data_preg r' = true ->  r' <> rd -> rs'#r' = rs#r'.
Proof.
  intros. unfold opuimm.
  destruct (Int.eq (high_u_18 n) Int.zero).
  - econstructor; split. apply exec_straight_one; eauto.
    intuition Simpl.
  - exploit (loadimm_correct TMP n (op rd TMP :: k)). intros (rs' & A & B & C).
    econstructor; split.
    eapply exec_straight_trans. eexact A. apply exec_straight_one; eauto.
    split; intros; Simpl. rewrite B, C; auto with asmgen.
Qed.

Lemma extsb_correct:
  forall rd k rs m,
  exists rs',
    exec_straight ge fn (extsb rd k) rs m k rs' m
  /\ rs'#rd = Val.sign_ext 8 rs#rd
  /\ forall r': preg, data_preg r' = true -> r' <> rd -> rs'#r' = rs#r'.
Proof.
  econstructor; split.
  eapply exec_straight_two; simpl; eauto.
  split; intros; Simpl.
  assert (A: Int.ltu (Int.repr 24) Int.iwordsize = true) by auto.
  destruct (rs rd); auto; simpl. do 2 (rewrite A; simpl).
  f_equal. rewrite Int.sign_ext_shr_shl. simpl. reflexivity.
  split; reflexivity.
Qed.


Lemma extsh_correct:
  forall rd k rs m,
  exists rs',
    exec_straight ge fn (extsh rd k) rs m k rs' m
  /\ rs'#rd = Val.sign_ext 16 rs#rd
  /\ forall r': preg, data_preg r' = true -> r' <> rd -> rs'#r' = rs#r'.
Proof.
  econstructor; split.
  eapply exec_straight_two; simpl; eauto.
  split; intros; Simpl.
  assert (A: Int.ltu (Int.repr 16) Int.iwordsize = true) by auto.
  destruct (rs rd); auto; simpl. do 2 (rewrite A; simpl).
  f_equal. rewrite Int.sign_ext_shr_shl. simpl. reflexivity.
  split; reflexivity.
Qed.



Lemma addimm_correct:
  forall rd n k rs m,
    rd <> TMP ->
  exists rs',
     exec_straight ge fn (addimm rd n k) rs m k rs' m
  /\ rs'#rd = Val.add rs#rd (Vint n)
  /\ forall r': preg,  data_preg r' = true -> r' <> rd -> rs'#r' = rs#r'.
Proof.
  intros.
  apply (opimm_correct Padd Paddi Val.add); auto.
Qed.

Lemma loadsymbol_correct:
  forall rd s ofs k rs m,
    exists rs',
      exec_straight ge fn (Ploadsymbol rd s ofs :: k) rs m k rs' m
      /\ rs'#rd = Genv.symbol_address ge s ofs
      /\ forall r, data_preg r = true -> r <> rd -> rs'#r = rs#r.
Proof.
  intros. econstructor. split.
  eapply exec_straight_one; [simpl; eauto | reflexivity].
  intuition Simpl.
Qed.

(** Float comparisons. *)

Lemma transl_float_mask_eq_gt_lt_correct:
  forall cmp r1 r2 k c (rs: regset) m,
    data_preg (GPR r2) = true ->
    (cmp = Ceq \/ cmp = Clt \/ cmp = Cgt) ->
    transl_float_mask cmp r1 r2 k = OK c ->
    exists rs',
      exec_straight ge fn c rs m k rs' m
      /\ rs'#TMP = Val.cmpfs cmp (rs r1) (rs r2)
      /\ forall r, data_preg r = true -> rs'#r = rs#r.
Proof.
  intros.
  assert (exists mask, c = Pmov_rr TMP r1 :: Pfcmp TMP r2 :: Ptbi TMP mask :: k).
  destruct H0 as [EQ | [EQ | EQ]]; subst cmp; inv H1; eauto.
  destruct H2 as [x  EQ].
  econstructor; split. rewrite EQ.
  eapply exec_straight_three; try (econstructor; Simpl; reflexivity).
  split; intros; Simpl.
  destruct (rs r1), (rs r2); eauto.
  rewrite EQ in H1.
  unfold cmpfs_float, Val.cmpfs, Val.cmpfs_bool, Val.of_optbool.
  destruct H0 as [EQ2 | [EQ2 | EQ2]]; rewrite EQ2 in H1; inversion H1; subst cmp;
    destruct (Float32.cmp Ceq f f0) eqn:Heq1; destruct (Float32.cmp Clt f f0) eqn:Heq2; destruct (Float32.cmp Cgt f f0) eqn:Heq3; try reflexivity;
      try (destruct (Float32.cmp_lt_eq_false f f0 Heq2 Heq1)); try (destruct (Float32.cmp_lt_gt_false f f0 Heq2 Heq3)); try (destruct (Float32.cmp_gt_eq_false f f0 Heq3 Heq1)).
Qed.

Lemma transl_float_mask_ge_le_correct:
  forall cmp r1 r2 k c (rs: regset) m,
    data_preg (GPR r2) = true ->
    (cmp = Cle \/ cmp = Cge) ->
    transl_float_mask cmp r1 r2 k = OK c ->
    exists rs',
      exec_straight ge fn c rs m k rs' m
      /\ rs'#TMP = cmpfs_float (rs r1) (rs r2)
      /\ forall r, data_preg r = true -> rs'#r = rs#r.
Proof.
  intros.
  assert (c = Pmov_rr TMP r1 :: Pfcmp TMP r2 :: k).
  destruct H0; subst cmp; inv H1; eauto.
  rewrite H2.
  econstructor. split.
  eapply exec_straight_two; try (econstructor; Simpl; reflexivity).
  split; intros; Simpl.
Qed.

Lemma transl_float_mask_ne_correct:
  forall r1 r2 k c (rs: regset) m,
    data_preg (GPR r2) = true ->
    transl_float_mask Cne r1 r2 k = OK c ->
    exists rs',
      exec_straight ge fn c rs m k rs' m
      /\ rs'#TMP = Val.notbool (Val.cmpfs Cne (rs r1) (rs r2))
      /\ forall r, data_preg r = true -> rs'#r = rs#r.
Proof.
  simpl. intros. inv H0.
  econstructor. split.
  eapply exec_straight_three; try (econstructor; Simpl; reflexivity).
  split; intros; Simpl.
  destruct (rs r1), (rs r2); eauto.
  unfold cmpfs_float, Val.cmpfs, Val.cmpfs_bool, Val.of_optbool.
  rewrite Float32.cmp_ne_eq.
  destruct (Float32.cmp Ceq f f0) eqn:Heq1; destruct (Float32.cmp Clt f f0) eqn:Heq2; destruct (Float32.cmp Cgt f f0) eqn:Heq3;
      try (destruct (Float32.cmp_lt_eq_false f f0 Heq2 Heq1)); try (destruct (Float32.cmp_lt_gt_false f f0 Heq2 Heq3)); try (destruct (Float32.cmp_gt_eq_false f f0 Heq3 Heq1)); try reflexivity.
Qed.

Lemma floatcomp_correct:
  forall cmp (rd r1 r2: reg) k rs m c,
    rd <> TMP ->
    data_preg (GPR r2) = true ->
    floatcomp cmp rd r1 r2 k = OK c ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
     /\  rs'#rd =
        (match cmp with
         | Cne => Val.notbool (Val.of_optbool (eval_condition (Ccompfs cmp) (rs r1 :: rs r2 :: nil) m))
         | _ => Val.of_optbool (eval_condition (Ccompfs cmp) (rs r1 :: rs r2 :: nil) m) end)
  /\ forall r', data_preg r' = true -> GPR rd <> r' -> rs'#r' = rs#r'.
Proof.
  intros.
  assert ((cmp = Cne)
          \/ (cmp = Cle \/ cmp = Cge) \/ (cmp = Ceq \/ cmp = Clt \/ cmp = Cgt)).
  case cmp; tauto.
  destruct H2 as [H2|[H2|H2]].
  - subst cmp. simpl in H0.
    exploit (transl_float_mask_ne_correct r1 r2 (Pmov_rr rd TMP :: k)); eauto.
    intros (rs' & A & B & C).
    exists (nextinstr (rs'#rd <- (rs' TMP))).
    split. eapply exec_straight_trans. eexact A.
    eapply exec_straight_one; eauto.
    simpl. split; intros; Simpl.
  - destruct H2; subst cmp.
    + set (k' := Pmov_rr rd TMP :: Ptbi TMP (Int.repr 5) :: Ptbi rd (Int.repr 7) :: Por rd TMP :: k).
      exploit (transl_float_mask_ge_le_correct Cle r1 r2 k' c); eauto.
      intros (rs' & A & B & D).
      econstructor; split.
      eapply exec_straight_trans. eexact A.
      do 3 (eapply exec_straight_step; simpl; eauto).
      eapply exec_straight_one; simpl; eauto.
      split; intros; Simpl.
      simpl. rewrite B.
      unfold cmpfs_float, Val.cmpfs_bool, Val.of_optbool. destruct (rs r1), (rs r2); eauto.
      change (Int.ltu (Int.repr 7) Int.iwordsize) with true.
      change (Int.ltu (Int.repr 5) Int.iwordsize) with true.
      destruct (Float32.cmp Ceq f f0) eqn:Heq1; destruct (Float32.cmp Clt f f0) eqn:Heq2; destruct (Float32.cmp Cgt f f0) eqn:Heq3;
        rewrite Float32.cmp_le_lt_eq; try (destruct (Float32.cmp_lt_gt_false f f0 Heq2 Heq3));
          rewrite Heq1, Heq2; simpl; reflexivity.
    + exploit (transl_float_mask_ge_le_correct Cle r1 r2); eauto.
      intros (rs' & A & B & D).
      econstructor; split.
      eapply exec_straight_trans. eexact A.
      do 3 (eapply exec_straight_step; simpl; eauto).
      eapply exec_straight_one; simpl; eauto.
      split; intros; Simpl.
      simpl. rewrite B.
      unfold cmpfs_float, Val.cmpfs_bool, Val.of_optbool. destruct (rs r1), (rs r2); eauto.
      destruct (Float32.cmp Ceq f f0) eqn:Heq1; destruct (Float32.cmp Clt f f0) eqn:Heq2; destruct (Float32.cmp Cgt f f0) eqn:Heq3;
        rewrite Float32.cmp_ge_gt_eq; try (destruct (Float32.cmp_lt_gt_false f f0 Heq2 Heq3)); rewrite Heq1; rewrite Heq3; simpl; try reflexivity.
  - unfold floatcomp in H1.
    exploit (transl_float_mask_eq_gt_lt_correct); eauto.
    destruct H2  as [EQ | [EQ | EQ]]; subst cmp; eexact H1.
    intros (rs' & A & B & C).
    econstructor. split.
    eapply exec_straight_trans. eexact A.
    econstructor. reflexivity. Simpl.
    rewrite B. simpl.
    destruct H2 as [EQ | [EQ | EQ]]; subst cmp;
      split; intros; Simpl.
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
  | [ H: reg_of _ = OK _ |- _ ] => simpl in *; rewrite (reg_of_eq _ _ H) in *
  end).

(* Translation of arithmetic operations *)

Ltac SimplEval H :=
  match type of H with
  | Some _ = None _ => discriminate
  | None = Some _  => discriminate
  | Some _ = Some _ => inv H
  | ?a = Some ?b => let A := fresh in assert (A: Val.maketotal a = b) by (rewrite H; reflexivity)
end.

Ltac TranslOpSimpl :=
  econstructor; split;
  [ apply exec_straight_one; [simpl; eauto | reflexivity]
  | split; [ apply Val.lessdef_same; Simpl; fail | intros; Simpl; fail ] ].

Definition is_fcmp cond :=
  match cond with
  | Ccompfs cmp => true
  | Cnotcompfs cmp => true
  | _ => false
  end.

Lemma transl_integercmp_correct:
  forall c rd r1 r2 k rs m,
   exists rs' : regset,
    exec_straight ge fn (integercmp c rd r1 r2 k) rs m k rs' m /\
    rs' rd =
    (if cmp_needs_inversion c
     then Val.notbool (Val.of_optbool (Val.cmp_bool c (rs r1) (rs r2)))
     else Val.of_optbool (Val.cmp_bool c (rs r1) (rs r2)))
    /\ (forall r' : preg, data_preg r' = true -> r' <> rd -> rs' r' = rs r').
Proof.
  intros. unfold integercmp.
  destruct c; simpl.
  - (* Ceq *)
    econstructor. split.
    apply exec_straight_one; simpl; reflexivity.
    split; intros; intuition Simpl.
  - (* Cne *)
    econstructor. split.
    apply exec_straight_one; simpl; reflexivity.
    split; intros; intuition Simpl.
    replace Ceq with (negate_comparison Cne) by auto.
    rewrite Val.negate_cmp. auto.
  - (* Clt *)
    econstructor. split.
    apply exec_straight_one; simpl; reflexivity.
    split; intros; intuition Simpl.
  - (* Cle *)
    econstructor. split.
    apply exec_straight_one; simpl; reflexivity.
    split; intros; intuition Simpl.
    rewrite <- Val.swap_cmp_bool, <- Val.not_of_optbool, <- Val.negate_cmp_bool.
    simpl; reflexivity.
  - (* Cgt *)
    econstructor. split.
    apply exec_straight_one; simpl; reflexivity.
    split; intros; intuition Simpl.
    rewrite <- Val.swap_cmp_bool. simpl; reflexivity.
  - (* Cge *)
    econstructor. split.
    apply exec_straight_one; simpl; reflexivity.
    split; intros; intuition Simpl.
    rewrite <- Val.not_of_optbool, <- Val.negate_cmp_bool.
    simpl; reflexivity.
Qed.


Lemma transl_integercmpu_correct:
  forall c rd r1 r2 k rs m,
   exists rs' : regset,
    exec_straight ge fn (integercmpu c rd r1 r2 k) rs m k rs' m /\
    rs' rd =
    (if cmp_needs_inversion c
     then Val.notbool (Val.of_optbool (Val.cmpu_bool (Mem.valid_pointer m) c (rs r1) (rs r2)))
     else Val.of_optbool (Val.cmpu_bool (Mem.valid_pointer m) c (rs r1) (rs r2)))
    /\ (forall r' : preg, data_preg r' = true -> r' <> rd -> rs' r' = rs r').
Proof.
  intros. unfold integercmpu.
  destruct c; simpl.
  - (* Ceq *)
    econstructor. split.
    apply exec_straight_one; simpl; reflexivity.
    split; intros; intuition Simpl.
  - (* Cne *)
    econstructor. split.
    apply exec_straight_one; simpl; reflexivity.
    split; intros; intuition Simpl.
    replace Ceq with (negate_comparison Cne) by auto.
    rewrite Val.negate_cmpu. auto.
  - (* Clt *)
    econstructor. split.
    apply exec_straight_one; simpl; reflexivity.
    split; intros; intuition Simpl.
  - (* Cle *)
    econstructor. split.
    apply exec_straight_one; simpl; reflexivity.
    split; intros; intuition Simpl.
    rewrite <- Val.swap_cmpu_bool, <- Val.not_of_optbool, <- Val.negate_cmpu_bool.
    simpl. reflexivity.
  - (* Cgt *)
    econstructor. split.
    apply exec_straight_one; simpl; reflexivity.
    split; intros; intuition Simpl.
    rewrite <- Val.swap_cmpu_bool. simpl. reflexivity.
  - (* Cge *)
    econstructor. split.
    apply exec_straight_one; simpl; reflexivity.
    split; intros; intuition Simpl.
    rewrite <- Val.not_of_optbool, <- Val.negate_cmpu_bool.
    simpl. reflexivity.
Qed.


Lemma transl_cond_correct:
  forall cond args k rs r m c,
    (is_fcmp cond = true -> r <> TMP) ->
    transl_cond cond args r k = OK c ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#r = (if cond_needs_inversion cond
             then Val.notbool (Val.of_optbool (eval_condition cond (map rs (map preg_of args)) m))
        else Val.of_optbool (eval_condition cond (map rs (map preg_of args)) m))
  /\ forall r', data_preg r' = true -> r' <> r -> rs'#r' = rs#r'.
Proof.
  assert (CMP_INV:
            forall c, cmp_needs_inversion c = cmp_needs_inversion (swap_comparison c)) by (destruct c; reflexivity).
  intros.
  Local Opaque Int.eq.
  unfold transl_cond in H0; destruct cond; ArgsInv; simpl.
  - (* Ccomp *)
    apply transl_integercmp_correct.
  - (* Ccompu *)
    apply transl_integercmpu_correct.
  - (* Ccompimm *)
    exploit loadimm_correct. intros (rs' & A & B & C).
    exploit (transl_integercmp_correct (swap_comparison c0) r TMP x k rs'). intros (rs'' & A' & B' & C').
    exists rs''. split. eapply exec_straight_trans.
    eexact A. eexact A'. split.
    rewrite <- Val.swap_cmp_bool, <- B, <- (C x); eauto with asmgen.
    rewrite CMP_INV.
    apply B'. intros. rewrite C', C; eauto with asmgen.
  - exploit loadimm_correct. intros (rs' & A & B & C).
    exploit (transl_integercmpu_correct (swap_comparison c0) r TMP x k rs'). intros (rs'' & A' & B' & C').
    exists rs''. split. eapply exec_straight_trans.
    eexact A. eexact A'. split.
    rewrite <- Val.swap_cmpu_bool, <- B, <- (C x); eauto with asmgen.
    rewrite CMP_INV.
    apply B'. intros. rewrite C', C; eauto with asmgen.
  - (* Ccompf *)
    destruct (floatcomp_correct c0 r x x0 k rs m c) as [rs' [EX [RES OTH]]];
      eauto with asmgen.
    exists rs'. split; eauto. rewrite RES. destruct c0; auto.
  - (* Cnotcompf *)
    rewrite Val.notbool_negb_3. rewrite Val.notbool_idem4.
    destruct (floatcomp_correct c0 r x x0 k rs m c) as [rs' [EX [RES OTH]]]; eauto with asmgen.
    exists rs'. split; eauto.
    destruct c0; eauto.
Qed.

Lemma transl_op_correct:
  forall op args res k (rs: regset) m v c,
  transl_op op args res k = OK c ->
  eval_operation ge (rs#SP) op (map rs (map preg_of args)) m = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ Val.lessdef v rs'#(preg_of res)
  /\ forall r, data_preg r = true -> r <> preg_of res -> preg_notin r (destroyed_by_op op) -> rs' r = rs r.
Proof.
  Local Opaque Int.eq.
  intros until c; intros TR EV.
  unfold transl_op in TR; destruct op; ArgsInv; simpl in EV; SimplEval EV; try TranslOpSimpl.
  - (* move *)
    destruct (preg_of res), (preg_of m0); inv TR. TranslOpSimpl.
  - (* intconst *)
    exploit loadimm_correct; eauto. intros (rs' & A & B & C).
    exists rs'; split; eauto. rewrite B; auto with asmgen.
  - (* addrstack *)
    exploit (addimm_correct x (Ptrofs.to_int ofs) k (nextinstr (rs#x <- (rs#SP)))); eauto with asmgen.
    intros (rs'' & A' & B' & C'). exists rs''; split.
    eapply exec_straight_step; simpl; eauto.
    rewrite B'.
    split; intros; Simpl. destruct (rs SP); auto.
    simpl. rewrite Ptrofs.of_int_to_int; auto.
    intros. rewrite C'; Simpl; eauto with asmgen.
  - (* cast8signed *)
    exploit (extsb_correct x0 k (nextinstr (rs#x0 <- (rs#x)))).
    intros (rs' & A & B & C).
    exists rs'; split.
    eapply exec_straight_trans.
    apply exec_straight_one; simpl; reflexivity. eexact A.
    rewrite B. split; intuition Simpl. rewrite C; Simpl; auto.
  - (* cast16signed *)
    exploit (extsh_correct x0 k (nextinstr (rs#x0 <- (rs#x)))).
    intros (rs' & A & B & C).
    exists rs'; split.
    eapply exec_straight_trans.
    apply exec_straight_one; simpl; reflexivity. eexact A.
    rewrite B. split; intuition Simpl. rewrite C; Simpl; auto.
  - (* addimm *)
    exploit (addimm_correct x); eauto with asmgen.
    intros (rs' & A & B & C). exists rs'; split; eauto. rewrite B; auto with asmgen.
  - (* subimm *)
    exploit (opimm_correct Psub Psubi Val.sub); eauto with asmgen.
    intros (rs' & A & B & C). exists rs'; split; eauto. rewrite B; auto with asmgen.
  - (* mulimm *)
    exploit (opimm_correct Pmul Pmuli Val.mul); eauto with asmgen.
    intros (rs' & A & B & C). exists rs'; split; eauto. rewrite B; auto with asmgen.
  - (* orimm *)
    exploit (opimm_correct Por Pori Val.or); eauto with asmgen.
    intros (rs' & A & B & C). exists rs'; split; eauto. rewrite B; auto with asmgen.
  - (* andimm *)
    exploit (opimm_correct Pand Pandi Val.and); eauto with asmgen.
    intros (rs' & A & B & C). exists rs'; split; eauto. rewrite B; auto with asmgen.
  - (* nandimm *)
    exploit (opimm_correct Pnand Pnandi (fun x y => Val.notint (Val.and x y)));  eauto with asmgen.
    intros (rs' & A & B & C). exists rs'; split; eauto. rewrite B; auto with asmgen.
  - (* xorimm *)
    exploit (opimm_correct Pxor Pxori Val.xor); eauto with asmgen.
    intros (rs' & A & B & C). exists rs'; split; eauto. rewrite B; auto with asmgen.
  - (* srlimm *)
    exploit (opimm_correct Psra Psrai Val.shr); eauto with asmgen.
    intros (rs' & A & B & C). exists rs'; split; eauto. rewrite B; auto with asmgen.
  - (* shrximm *)
    clear H. exploit Val.shrx_shr_2; eauto. intros E; subst v; clear EV.
    destruct (Int.eq n Int.zero).
    + (* zero case *)
      econstructor; split.  apply exec_straight_one. simpl; eauto. auto.
      split; intros; Simpl.
    + (* non zero case *)
      change (Int.repr 32) with Int.iwordsize. set (n' := Int.sub Int.iwordsize n).
      econstructor; split.
      do 5 (eapply exec_straight_step; simpl; eauto with asmgen).
      apply exec_straight_one. simpl; reflexivity. auto.
      split; intros; Simpl.
      rewrite Val.add_commut.
      auto.
  - (* shlimm *)
    exploit (opimm_correct Psll Pslil Val.shl); eauto with asmgen.
    intros (rs' & A & B & C). exists rs'; split; eauto. rewrite B; auto with asmgen.
  - (* shruimm *)
    exploit (opuimm_correct Psrl Psril Val.shru); eauto with asmgen.
    intros (rs' & A & B & C). exists rs'; split; eauto. rewrite B; auto with asmgen.
  - (* rorimm *)
    exploit (opimm_correct Prr Prri Val.ror); eauto with asmgen.
    intros (rs' & A & B & C). exists rs'; split; eauto. rewrite B; auto with asmgen.
  - (* eval condition *)
    exploit transl_cond_correct; eauto with asmgen.
    intros (rs1 & EX1 & RES1 & AG1).
    destruct (cond_needs_inversion cond); econstructor.
    + (* we need to invert the result *)
      split. eapply exec_straight_trans. eexact EX1.
      apply exec_straight_one; reflexivity.
      intuition Simpl. rewrite RES1.
      destruct (eval_condition cond rs ## (preg_of ## args) m); eauto with asmgen.
      destruct b; auto.
    + (* result can be used as is *)
      split. eexact EX1. rewrite RES1. eauto with asmgen.
Qed.

Lemma transl_cond_branch_correct:
  forall cond args lbl k c rs m b,
    transl_cond_branch cond args lbl k = OK c ->
    eval_condition cond (map rs (map preg_of args)) m = Some b ->
    exists rs' insn,
      exec_straight_opt ge fn c rs m (insn :: k) rs' m
      /\ exec_instr ge fn insn rs' m =
        (if b then goto_label fn lbl rs' m else Next (nextinstr rs') m)
      /\ forall r, data_preg r = true -> rs'#r = rs#r.
Proof.
  intros until b; intros TR EV.
  assert (DFL:
            transl_cond_branch_default cond args lbl k = OK c ->
            (is_fcmp cond = false) ->
            exists rs' insn,
              exec_straight_opt ge fn c rs m (insn :: k) rs' m
              /\ exec_instr ge fn insn rs' m =
                (if b then goto_label fn lbl rs' m else Next (nextinstr rs') m)
              /\ forall r, data_preg r = true -> rs'#r = rs#r).
  {
    unfold transl_cond_branch_default; intros.
    exploit transl_cond_correct; eauto with asmgen.
    intros. congruence.
    intros (rs' & A & B & C).
    set (b0 := cond_needs_inversion cond) in *.
    exists rs', (if b0 then Pbz TMP lbl else Pbnz TMP lbl). split.
    apply exec_straight_opt_intro. destruct b0; eexact A.
    assert (H1: rs' TMP = if b0 then Val.notbool (Val.of_optbool (Some b)) else Val.of_optbool (Some b))
      by (rewrite <- EV; auto).
    destruct b; destruct b0; simpl; rewrite H1; eauto with asmgen.
  }
  Local Opaque transl_cond transl_cond_branch_default.
  destruct cond; simpl in TR; eauto with asmgen.
  - (* Ccomp *)
    destruct c0; ArgsInv; auto.
    + (* Ceq *)
      econstructor.
      exists (Pbz TMP lbl). split; simpl.
      eapply exec_straight_opt_intro. eapply exec_straight_two; simpl; reflexivity.
      intuition Simpl.
      destruct (rs x); inv EV. destruct (rs x0); inv H0. simpl.
      rewrite Int.xor_is_zero. split; eauto with asmgen.
    + (* Cne *)
      econstructor. exists (Pbnz TMP lbl). split; simpl.
      eapply exec_straight_opt_intro. eapply exec_straight_two; simpl; reflexivity.
      intuition Simpl.
      destruct (rs x); inv EV. destruct (rs x0); inv H0. simpl.
      rewrite Int.xor_is_zero. destruct (Int.eq i i0); eauto with asmgen.
  - (* Ccompimm *)
    destruct c0; ArgsInv; simpl in EV; inv EV;
      destruct (Int.eq n Int.zero) eqn:N0; try (monadInv TR); auto;
        try (try inv EQ0; apply Int.same_if_eq in N0; subst n;
             do 2 econstructor; split;
             try apply exec_straight_opt_refl;
             try rewrite (reg_of_eq m0 x EQ) in H0;
             split; auto; simpl; destruct (rs x);
             inv H0; simpl; destruct (Int.eq i Int.zero); auto).
    + inv EQ0.
      exploit (loadimm_correct TMP n). intros (rs1 & A & B & C).
      exists (nextinstr (rs1#TMP <- (Val.xor rs1#TMP rs1#x))), (Pbz TMP lbl).
      split.
      eapply exec_straight_opt_intro.
      eapply exec_straight_trans. eapply A.
      apply exec_straight_one; simpl; eauto.
      simpl. rewrite B, Val.xor_commut, C; eauto with asmgen.
      destruct (rs x); inv H0; simpl. rewrite Int.xor_is_zero.
      split; intros; Simpl; eauto with asmgen.
    + inv EQ0.
      exploit (loadimm_correct TMP n). intros (rs1 & A & B & C).
      exists (nextinstr (rs1#TMP <- (Val.xor rs1#TMP rs1#x))), (Pbnz TMP lbl).
      split.
      apply exec_straight_opt_intro.
      eapply exec_straight_trans. eapply A.
      eapply exec_straight_one; simpl; eauto.
      simpl; rewrite B, Val.xor_commut, C; eauto with asmgen.
      destruct (rs x); inv H0. simpl. rewrite Int.xor_is_zero.
      split; intros; Simpl. destruct (Int.eq i n); eauto with asmgen.
  -(* Ccompuimm *)
    destruct c0; ArgsInv; destruct (Int.eq n Int.zero) eqn:N0; eauto; monadInv TR;
      apply Int.same_if_eq in N0; subst n; simpl in EV; rewrite (reg_of_eq m0 x EQ) in EV.
    + (* Ccompuimm Ceq 0 *)
      do 2 econstructor; split.
      apply exec_straight_opt_refl.
      split; auto; simpl; rewrite EV; auto.
    + (* Ccompuimm Cne 0 *)
      do 2 econstructor; split.
      apply exec_straight_opt_refl.
      split; auto; simpl.
      rewrite (Val.negate_cmpu_bool (Mem.valid_pointer m) Cne), EV.
      destruct b; auto.
  - (* Ccompfs *)
    ArgsInv; auto; try inv EV. clear DFL.
  assert ((c0 = Cne)
          \/ (c0 = Cle \/ c0 = Cge) \/ (c0 = Ceq \/ c0 = Clt \/ c0 = Cgt)).
  case c0; tauto.
  destruct H as [H| [H | H]].
  + subst c0.
    exploit (transl_float_mask_ne_correct x x0  (Pbz Reg1 lbl :: k)); eauto with asmgen.
    intros (rs' & A & B & C).
    exists rs', (Pbz TMP lbl). split.
    eapply exec_straight_opt_intro.
    eexact A.
    split. simpl. rewrite B.
    replace (Val.cmpu_bool (Mem.valid_pointer m) Ceq
                           (Val.notbool (Val.cmpfs Cne (rs x) (rs x0)))
                           (Vint Int.zero)) with  (Val.cmpfs_bool Cne (rs x) (rs x0)).
    rewrite H0. reflexivity.
    unfold Val.cmpfs. unfold Val.notbool. unfold Val.of_optbool.
    rewrite H0. destruct b; try reflexivity.
    intros. rewrite C; eauto with asmgen.
  + destruct H; subst c0.
    exploit (transl_float_mask_ge_le_correct Cle x x0 (Pandi TMP (Int.repr 160) :: Pbnz Reg1 lbl :: k)); eauto with asmgen.
    intros (rs' & A & B & C).
    exists (nextinstr (rs'#TMP <- (Val.and rs'#TMP (Vint (Int.repr 160))))).
    exists (Pbnz TMP lbl).
    split.
    eapply exec_straight_opt_intro.
    eapply exec_straight_trans. eexact A.
    eapply exec_straight_one; simpl; reflexivity.
    split; intros; Simpl. simpl. rewrite B.
    Simpl.
    replace (Val.cmpu_bool (Mem.valid_pointer m) Ceq
                           (Val.and (cmpfs_float (rs x) (rs x0)) (Vint (Int.repr 160)))
                           (Vint Int.zero)) with (Some (negb b)). destruct b; reflexivity.
    unfold cmpfs_float. destruct (rs x), (rs x0); try inv H0.
    destruct (Float32.cmp Ceq f f0) eqn:Heq1; destruct (Float32.cmp Clt f f0) eqn:Heq2; destruct (Float32.cmp Cgt f f0) eqn:Heq3;
      rewrite Float32.cmp_le_lt_eq; try (destruct (Float32.cmp_lt_gt_false f f0 Heq2 Heq3)); rewrite Heq1; rewrite Heq2; simpl; try reflexivity.
    exploit (transl_float_mask_ge_le_correct Cge x x0 (Pandi TMP (Int.repr 96) :: Pbnz Reg1 lbl :: k)); eauto with asmgen.
    intros (rs' & A & B & C).
    exists (nextinstr (rs'#TMP <- (Val.and rs'#TMP (Vint (Int.repr 96))))).
    exists (Pbnz TMP lbl).
    split.
    eapply exec_straight_opt_intro.
    eapply exec_straight_trans. eexact A.
    eapply exec_straight_one; simpl; reflexivity.
    split; intros; Simpl. simpl. rewrite B.
    Simpl.
    replace (Val.cmpu_bool (Mem.valid_pointer m) Ceq
                           (Val.and (cmpfs_float (rs x) (rs x0)) (Vint (Int.repr 96)))
                           (Vint Int.zero)) with (Some (negb b)). destruct b; reflexivity.
    unfold cmpfs_float. destruct (rs x), (rs x0); try inv H0.
    destruct (Float32.cmp Ceq f f0) eqn:Heq1; destruct (Float32.cmp Clt f f0) eqn:Heq2; destruct (Float32.cmp Cgt f f0) eqn:Heq3;
      rewrite Float32.cmp_ge_gt_eq; try (destruct (Float32.cmp_lt_gt_false f f0 Heq2 Heq3)); rewrite Heq1; rewrite Heq3; simpl; try reflexivity.
  +  exploit (transl_float_mask_eq_gt_lt_correct c0 x x0 (Pbnz TMP lbl :: k) c rs m); eauto with asmgen.
     destruct H as [H | [H | H]]; subst c0; auto.
     intros (rs' & A & B & C).
     exists rs', (Pbnz TMP lbl). split.
     eapply exec_straight_opt_intro. eexact A.
     split. simpl. rewrite B.
     replace (Val.cmpu_bool (Mem.valid_pointer m) Ceq (Val.cmpfs c0 (rs x) (rs x0)) (Vint Int.zero)) with (Some (negb b)).
     destruct b; reflexivity.
     unfold Val.cmpfs. unfold Val.of_optbool. rewrite H0. destruct b; auto.
     intros. rewrite C; eauto with asmgen.
  - (* Cnotcompfs *)
    ArgsInv; auto; try inv EV. clear DFL.
  assert ((c0 = Cne)
          \/ (c0 = Cle \/ c0 = Cge) \/ (c0 = Ceq \/ c0 = Clt \/ c0 = Cgt)).
  case c0; tauto.
  destruct H as [H| [H | H]].
  + subst c0.
    exploit (transl_float_mask_ne_correct x x0  (Pbnz Reg1 lbl :: k)); eauto with asmgen.
    intros (rs' & A & B & C).
    exists rs', (Pbnz TMP lbl). split.
    eapply exec_straight_opt_intro.
    eexact A.
    split. simpl. rewrite B.
    replace (Val.cmpu_bool (Mem.valid_pointer m) Ceq
                           (Val.notbool (Val.cmpfs Cne (rs x) (rs x0)))
                           (Vint Int.zero)) with  (Val.cmpfs_bool Cne (rs x) (rs x0)).
    assert (Val.cmpfs_bool Cne (rs x) (rs x0) = Some (negb b)).
    destruct (Val.cmpfs_bool Cne (rs x) (rs x0)). simpl in H0. inv H0.
    rewrite negb_involutive.
    reflexivity. inv H0. rewrite H.
    destruct b; simpl; auto.
    unfold Val.cmpfs. unfold Val.notbool. unfold Val.of_optbool.
    destruct (Val.cmpfs_bool Cne (rs x) (rs x0)). inv H0. destruct b0; auto. inv H0.
    intros. rewrite C; eauto with asmgen.
  + destruct H; subst c0.
    exploit (transl_float_mask_ge_le_correct Cle x x0 (Pandi TMP (Int.repr 160) :: Pbz Reg1 lbl :: k)); eauto with asmgen.
    intros (rs' & A & B & C).
    exists (nextinstr (rs'#TMP <- (Val.and rs'#TMP (Vint (Int.repr 160))))).
    exists (Pbz TMP lbl).
    split.
    eapply exec_straight_opt_intro.
    eapply exec_straight_trans. eexact A.
    eapply exec_straight_one; simpl; reflexivity.
    split; intros; Simpl. simpl. rewrite B.
    Simpl.
    replace (Val.cmpu_bool (Mem.valid_pointer m) Ceq
                           (Val.and (cmpfs_float (rs x) (rs x0)) (Vint (Int.repr 160)))
                           (Vint Int.zero)) with (Some b). destruct b; reflexivity.
    unfold cmpfs_float. destruct (rs x), (rs x0); try inv H0.
    destruct (Float32.cmp Ceq f f0) eqn:Heq1; destruct (Float32.cmp Clt f f0) eqn:Heq2; destruct (Float32.cmp Cgt f f0) eqn:Heq3;
      rewrite Float32.cmp_le_lt_eq; try (destruct (Float32.cmp_lt_gt_false f f0 Heq2 Heq3)); rewrite Heq1; rewrite Heq2; simpl; try reflexivity.
    exploit (transl_float_mask_ge_le_correct Cge x x0 (Pandi TMP (Int.repr 96) :: Pbz Reg1 lbl :: k)); eauto with asmgen.
    intros (rs' & A & B & C).
    exists (nextinstr (rs'#TMP <- (Val.and rs'#TMP (Vint (Int.repr 96))))).
    exists (Pbz TMP lbl).
    split.
    eapply exec_straight_opt_intro.
    eapply exec_straight_trans. eexact A.
    eapply exec_straight_one; simpl; reflexivity.
    split; intros; Simpl. simpl. rewrite B.
    Simpl.
    replace (Val.cmpu_bool (Mem.valid_pointer m) Ceq
                           (Val.and (cmpfs_float (rs x) (rs x0)) (Vint (Int.repr 96)))
                           (Vint Int.zero)) with (Some b). destruct b; reflexivity.
    unfold cmpfs_float. destruct (rs x), (rs x0); try inv H0.
    destruct (Float32.cmp Ceq f f0) eqn:Heq1; destruct (Float32.cmp Clt f f0) eqn:Heq2; destruct (Float32.cmp Cgt f f0) eqn:Heq3;
      rewrite Float32.cmp_ge_gt_eq; try (destruct (Float32.cmp_lt_gt_false f f0 Heq2 Heq3)); rewrite Heq1; rewrite Heq3; simpl; try reflexivity.
  +  exploit (transl_float_mask_eq_gt_lt_correct c0 x x0 (Pbz TMP lbl :: k) c rs m); eauto with asmgen.
     destruct H as [H | [H | H]]; subst c0; auto.
     intros (rs' & A & B & C).
     exists rs', (Pbz TMP lbl). split.
     eapply exec_straight_opt_intro. eexact A.
     split. simpl. rewrite B.
     replace (Val.cmpu_bool (Mem.valid_pointer m) Ceq (Val.cmpfs c0 (rs x) (rs x0)) (Vint Int.zero)) with (Some b).
     destruct b; reflexivity.
     unfold Val.cmpfs. unfold Val.of_optbool. rewrite <- H0.
     unfold option_map. destruct (Val.cmpfs_bool c0 (rs x) (rs x0)).
     destruct b0; auto. inv H0.
     intros. rewrite C; eauto with asmgen.
Qed.

(** Translation of addressing modes, loads, stores *)

Lemma accessind_correct:
  forall insn (base: reg) ofs k (rs: regset) m b i,
    base <> TMP ->
    Val.offset_ptr rs#base ofs = Vptr b i ->
    exists ad rs',    exec_straight_opt ge fn (accessind insn base ofs k) rs m (insn ad :: k) rs' m
  /\ Asm.eval_addressing ad rs' = Vptr b i
  /\ forall r, data_preg r = true -> rs' r = rs r.
Proof.
  unfold accessind; intros.
  assert (Val.add rs#base (Vint (Ptrofs.to_int ofs)) = Vptr b i).
  { destruct (rs base); try discriminate. simpl in *. rewrite Ptrofs.of_int_to_int by auto. auto. }
  destruct (Int.eq (high_s_20 (Ptrofs.to_int ofs)) Int.zero).
  - econstructor; econstructor; split. apply exec_straight_opt_refl. auto.
  - exploit (loadimm_correct TMP). intros (rs' & A & B & C).
    econstructor. exists rs'. split. apply exec_straight_opt_intro; eexact A.
    split. simpl. rewrite B, C; eauto with asmgen.
    eauto with asmgen.
Qed.

Lemma transl_memory_access_correct:
  forall addr args (insn: Asm.addressing -> instruction) k (rs: regset) m c b o,
  transl_memory_access insn addr args k = OK c ->
  Op.eval_addressing ge (rs#SP) addr (map rs (map preg_of args)) = Some (Vptr b o) ->
  exists ad rs',
     exec_straight_opt ge fn c rs m (insn ad :: k) rs' m
  /\ Asm.eval_addressing ad rs' = Vptr b o
  /\ forall r, data_preg r = true -> rs' r = rs r.
Proof.
  intros until o; intros TR EV.
  unfold transl_memory_access in TR; destruct addr; ArgsInv; SimplEval EV.
  - (* Aindexed *)
  destruct (Int.eq (high_s_20 ofs) Int.zero); inv EQ0.
  + econstructor; econstructor; split. apply exec_straight_opt_refl.
    auto.
  + exploit (loadimm_correct TMP ofs). intros (rs' & A & B & C).
    econstructor; exists rs'. split. apply exec_straight_opt_intro. eexact A.
    split. simpl. rewrite B, C by eauto with asmgen. auto.
    intros. rewrite C; eauto with asmgen.
  - (* Aglobal *)
    inv TR.
    exploit (loadsymbol_correct TMP id ofs). auto.  intros (rs' & A & B & C).
    econstructor. exists rs'. split.
    apply exec_straight_opt_intro. eexact A.
    split. simpl. rewrite B. rewrite <- Genv.shift_symbol_address_32, Ptrofs.add_zero by auto.
    simpl in EV. congruence.
    auto with asmgen.
  - (* Astack *)
    inv TR.
    exploit accessind_correct; eauto. congruence. inv EV. auto.
Qed.

Lemma transl_load_correct:
  forall chunk addr args dst k c (rs: regset) m vaddr v,
  transl_load chunk addr args dst k = OK c ->
  Op.eval_addressing ge (rs#SP) addr (map rs (map preg_of args)) = Some vaddr ->
  Mem.loadv chunk m vaddr = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, data_preg r = true -> r <> preg_of dst -> rs' r = rs r.
Proof.
  intros. destruct vaddr; try discriminate.
  assert (A: exists insn,
             transl_memory_access insn addr args k = OK c
             /\ (forall ad rs', exec_instr ge fn (insn ad) rs' m =
                          exec_load chunk rs' m (preg_of dst) ad)).
  {
    destruct chunk; monadInv H;
      try rewrite (reg_of_eq _ _ EQ);
        do 2 econstructor; eauto.
  }
  destruct A as (insn & B & C).
  exploit transl_memory_access_correct. eexact B. eexact H0. intros (ad & rs' & P & Q & R).
  assert (X: exec_load chunk rs' m (preg_of dst) ad =
             Next (nextinstr (rs'#(preg_of dst) <- v)) m).
  { unfold exec_load. rewrite Q, H1. auto. }
  econstructor; split.
  eapply exec_straight_opt_right. eexact P.
  apply exec_straight_one. rewrite C, X; eauto. Simpl.
  split. Simpl. intros; Simpl.
Qed.


Lemma transl_store_correct:
  forall chunk addr args src k c (rs: regset) m vaddr m',
  transl_store chunk addr args src k = OK c ->
  Op.eval_addressing ge (rs#SP) addr (map rs (map preg_of args)) = Some vaddr ->
  Mem.storev chunk m vaddr rs#(preg_of src) = Some m' ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, data_preg r = true -> rs' r = rs r.
Proof.
  intros. destruct vaddr; try discriminate.
  set (chunk' := match chunk with Mint8signed => Mint8unsigned
                                | Mint16signed => Mint16unsigned
                                | _ => chunk end).
  assert (A: exists insn,
             transl_memory_access insn addr args k = OK c
             /\ (forall ad rs', exec_instr ge fn (insn ad) rs' m =
                              exec_store chunk' rs' m ad rs'#(preg_of src))).
  {
    unfold chunk'; destruct chunk; monadInv H;
    try rewrite (reg_of_eq _ _ EQ);
    do 2 econstructor; eauto.
  }
  destruct A as (insn & B & C).
  exploit transl_memory_access_correct. eexact B. eexact H0. intros (ad & rs' & P & Q & R).
  assert (X: Mem.storev chunk' m (Vptr b i) rs#(preg_of src) = Some m').
  { rewrite <- H1. unfold chunk'. destruct chunk; auto; simpl; symmetry.
    apply Mem.store_signed_unsigned_8.
    apply Mem.store_signed_unsigned_16. }
  assert (Y: exec_store chunk' rs' m ad rs'#(preg_of src) =
             Next (nextinstr rs') m').
  { unfold exec_store. rewrite Q, R, X by auto with asmgen. auto. }
  econstructor; split.
  eapply exec_straight_opt_right. eexact P.
  apply exec_straight_one. rewrite C, Y; eauto. Simpl.
  intros; Simpl.
Qed.


Lemma loadptr_correct: forall (base: reg) ofs dst k m v (rs: regset),
  Mem.loadv Mint32 m (Val.offset_ptr rs#base ofs) = Some v ->
  base <> TMP ->
  exists rs',
     exec_straight ge fn (loadptr base ofs dst k) rs m k rs' m
  /\ rs'#dst = v
  /\ forall r, data_preg r = true -> r <> dst -> rs' r = rs r.
Proof.
  intros.
  destruct (Val.offset_ptr rs#base ofs) eqn:V; try discriminate.
  exploit accessind_correct; eauto. intros (ad & rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_opt_right. eexact A.
  apply exec_straight_one;  simpl. unfold exec_load. rewrite B, H;  eauto. auto.
  intuition Simpl.
Qed.

Lemma storeptr_correct: forall (base: reg) ofs (src: reg) k m m' (rs: regset),
  Mem.storev Mint32 m (Val.offset_ptr rs#base ofs) rs#src = Some m' ->
  base <> TMP ->
  src <> TMP ->
  exists rs',
     exec_straight ge fn (storeptr src base ofs k) rs m k rs' m'
  /\ forall r, data_preg r = true -> rs' r = rs r.
Proof.
  intros.
  destruct (Val.offset_ptr rs#base ofs) eqn:V; try discriminate.
  exploit (accessind_correct (fun a => Pmov_rm a src) base); eauto.
  intros (ad & rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_opt_right. unfold storeptr. eexact A.
  apply exec_straight_one. simpl. unfold exec_store. rewrite B, C, H;
  eauto with asmgen. Simpl. intuition Simpl.
Qed.

Lemma loadind_correct: forall (base: reg) ofs ty dst k c (rs: regset) m v,
  loadind base ofs ty dst k = OK c ->
  Mem.loadv (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) = Some v ->
  base <> TMP ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, data_preg r = true -> r <> preg_of dst -> rs' r = rs r.
Proof.
  intros.
  destruct (Val.offset_ptr rs#base ofs) eqn:V; try discriminate.
  assert (X: exists insn,
                c = accessind insn base ofs k
             /\ (forall ad rs', exec_instr ge fn (insn ad) rs' m =
                             exec_load (chunk_of_type ty) rs' m (preg_of dst) ad)).
  {
    unfold loadind in H; destruct ty; destruct (preg_of dst); inv H; do 2 econstructor; eauto.
  }
  destruct X as (insn & EQ & SEM). subst c.
  exploit accessind_correct; eauto.
  intros (ad & rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_opt_right. eexact A.
  apply exec_straight_one. rewrite SEM. unfold exec_load. rewrite B, H0; eauto. Simpl.
  intuition Simpl.
Qed.

Lemma storeind_correct: forall (base: reg) ofs ty src k c (rs: regset) m m',
  storeind src base ofs ty k = OK c ->
  Mem.storev (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) rs#(preg_of src) = Some m' ->
  base <> TMP ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, data_preg r = true -> rs' r = rs r.
Proof.
  intros.
  destruct (Val.offset_ptr rs#base ofs) eqn:V; try discriminate.
  assert (X: exists insn,
                c =  accessind insn base ofs k
             /\ (forall ad rs', exec_instr ge fn (insn ad) rs' m =
                          exec_store (chunk_of_type ty) rs' m ad rs'#(preg_of src))).
  {
    unfold storeind in H; destruct ty; destruct (preg_of src); inv H; do 2 econstructor; eauto.
  }
  destruct X as (insn & EQ & SEM). subst c.
  exploit accessind_correct; eauto. intros (ad & rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_opt_right. eexact A.
  apply exec_straight_one. rewrite SEM; eauto.
  unfold exec_store. rewrite B, C, H0 by eauto with asmgen; eauto.
  Simpl. intuition Simpl.
Qed.

Lemma transl_epilogue_correct:
forall ge0 f m stk soff cs m' ms rs k tm,
  load_stack m (Vptr stk soff) Tptr f.(fn_link_ofs) = Some (parent_sp cs) ->
  load_stack m (Vptr stk soff) Tptr f.(fn_retaddr_ofs) = Some (parent_ra cs) ->
  Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
  agree ms (Vptr stk soff) rs ->
  Mem.extends m tm ->
  match_stack ge0 cs ->
  exists rs', exists tm',
     exec_straight ge fn (transl_epilogue f k) rs tm k rs' tm'
  /\ agree ms (parent_sp cs) rs'
  /\ Mem.extends m' tm'
  /\ rs'#CRP = parent_ra cs
  /\ rs'#SP = parent_sp cs
  /\ (forall r, data_preg r = true -> r <> SP -> rs'#r = rs#r).
Proof.
  intros until tm; intros LP LRA FREE AG MEXT MCS.
  exploit Mem.loadv_extends. eauto. eexact LP. auto. simpl. intros (parent' & LP' & LDP').
  exploit Mem.loadv_extends. eauto. eexact LRA. auto. simpl. intros (ra' & LRA' & LDRA').
  exploit lessdef_parent_sp; eauto. intros EQ; subst parent'; clear LDP'.
  exploit lessdef_parent_ra; eauto. intros EQ; subst ra'; clear LDRA'.
  exploit Mem.free_parallel_extends; eauto. intros (tm' & FREE' & MEXT').
  unfold transl_epilogue.
  destruct (loadptr_correct SP (fn_retaddr_ofs f) TMP ((Pmov_tcrp TMP :: Pfreeframe (fn_stacksize f) (fn_link_ofs f) :: k)) tm (parent_ra cs) rs) as (rs1 & A1 & B1 & C1); eauto with asmgen.
  rewrite <- (sp_val _ _ _ AG).  eapply LRA'.
  econstructor; econstructor. split.
  eapply exec_straight_trans. eexact A1.
  eapply exec_straight_trans. econstructor; simpl; reflexivity.
  eapply exec_straight_one; simpl.
  replace (nextinstr rs1 # CRP <- (rs1 Reg1) Reg0) with (rs1#Reg0); eauto with asmgen.
  rewrite (C1 SP); eauto with asmgen.
  rewrite <- (sp_val _ _ _ AG); eauto with asmgen. simpl; rewrite LP'.
  rewrite FREE'.  auto. auto.
  split. apply agree_nextinstr.
  apply agree_change_sp with (Vptr stk soff); try (eapply parent_sp_def; eauto).
  apply agree_exten with rs1; eauto with asmgen.
  apply agree_exten with rs; eauto with asmgen.
  intuition Simpl.
  split. auto.
  split; intuition Simpl. rewrite C1; auto with asmgen.
  apply data_preg_not_TMP; auto.
Qed.

Lemma save_lr_correct:
  forall ofs k (rs: regset) m m',
    Mem.storev Mint32 m (Val.offset_ptr rs#SP ofs) (rs#CRP) = Some m' ->
    exists rs',
      exec_straight ge fn (save_lr ofs k) rs m k rs' m'
      /\ (forall r, data_preg r = true -> r <> Reg2 -> rs' r = rs r)
      /\ (save_lr_preserves_Reg2 ofs = true -> rs'#Reg2 = rs#Reg2).
Proof.
  intros; unfold save_lr.
  set (n := Ptrofs.to_int ofs).
  assert (EQ: Val.offset_ptr rs#SP ofs = Val.add rs#SP (Vint n)).
  { destruct rs#SP; try discriminate. simpl. f_equal; f_equal. unfold n; symmetry; auto with ptrofs. }
  destruct (Int.eq (high_s_20 (n))) eqn:LARGE.
  - econstructor; split.
    eapply exec_straight_two. simpl; reflexivity.
    simpl; unfold exec_store. simpl.
    Simpl.
    rewrite <- EQ. rewrite H. reflexivity.
    eauto with asmgen.
    eauto with asmgen.
    split; intros; intuition Simpl.
  - exploit (storeptr_correct SP ofs Reg2 k m m' (nextinstr (rs#Reg2 <- (rs#CRP)))); try congruence.
    eapply H.
    intros (rs' & A & B).
    exists rs'; split.
    eapply exec_straight_trans. econstructor; simpl; reflexivity.
    eexact A.
    split. intros. rewrite B; eauto with asmgen. Simpl.
    unfold save_lr_preserves_Reg2. unfold n in LARGE.
    rewrite LARGE. congruence.
Qed.

End CONSTRUCTORS.
