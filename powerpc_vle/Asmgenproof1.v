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

(** Correctness proof for PPC generation: auxiliary results. *)

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

Lemma low_high_u:
  forall n, Int.or (Int.shl (high_u n) (Int.repr 16)) (low_u n) = n.
Proof.
  intros. unfold high_u, low_u.
  rewrite Int.shl_rolm. rewrite Int.shru_rolm.
  rewrite Int.rolm_rolm.
  change (Int.modu (Int.add (Int.sub (Int.repr (Z.of_nat Int.wordsize)) (Int.repr 16))
                            (Int.repr 16))
                   (Int.repr (Z.of_nat Int.wordsize)))
    with (Int.zero).
  rewrite Int.rolm_zero. rewrite <- Int.and_or_distrib.
  exact (Int.and_mone n).
  apply int_wordsize_divides_modulus. reflexivity. reflexivity.
Qed.

Lemma low_high_u_xor:
  forall n, Int.xor (Int.shl (high_u n) (Int.repr 16)) (low_u n) = n.
Proof.
  intros. unfold high_u, low_u.
  rewrite Int.shl_rolm. rewrite Int.shru_rolm.
  rewrite Int.rolm_rolm.
  change (Int.modu (Int.add (Int.sub (Int.repr (Z.of_nat Int.wordsize)) (Int.repr 16))
                            (Int.repr 16))
                   (Int.repr (Z.of_nat Int.wordsize)))
    with (Int.zero).
  rewrite Int.rolm_zero. rewrite <- Int.and_xor_distrib.
  exact (Int.and_mone n).
  apply int_wordsize_divides_modulus. reflexivity. reflexivity.
Qed.

Lemma low_high_s:
  forall n, Int.add (Int.shl (high_s n) (Int.repr 16)) (low_s n) = n.
Proof.
  intros.
  rewrite Int.shl_mul_two_p.
  unfold high_s.
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

Lemma add_zero_symbol_address:
  forall (ge: genv) id ofs,
  Val.add Vzero (Genv.symbol_address ge id ofs) = Genv.symbol_address ge id ofs.
Proof.
  unfold Genv.symbol_address; intros. destruct (Genv.find_symbol ge id); auto.
  simpl. rewrite Ptrofs.add_zero; auto.
Qed.

Lemma low_high_half_zero:
  forall (ge: genv) id ofs,
  Val.add (Val.add Vzero (high_half ge id ofs)) (low_half ge id ofs) =
  Genv.symbol_address ge id ofs.
Proof.
  intros. rewrite Val.add_assoc. rewrite low_high_half. apply add_zero_symbol_address.
Qed.

Lemma high_low_half_zero:
  forall (ge: genv) id ofs,
  Val.add (Val.add Vzero (low_half ge id ofs)) (high_half ge id ofs) =
  Genv.symbol_address ge id ofs.
Proof.
  intros. rewrite Val.add_assoc.
  rewrite (Val.add_commut (low_half _ _ _)).
  rewrite <- Val.add_assoc. apply low_high_half_zero.
Qed.

(** * Useful properties of registers *)

(** [important_preg] extends [data_preg] by tracking the LR register as well.
    It is used to state that a code sequence modifies no data registers
    and does not modify LR either. *)

Definition important_preg (r: preg) : bool :=
  match r with
  | LR => true
  | _ => data_preg r
  end.

Lemma important_diff:
  forall r r',
  important_preg r = true -> important_preg r' = false -> r <> r'.
Proof.
  congruence.
Qed.
Global Hint Resolve important_diff: asmgen.

Lemma important_data_preg_1:
  forall r, data_preg r = true -> important_preg r = true.    
Proof.
  destruct r; simpl; auto; discriminate.
Qed.

Lemma important_data_preg_2:
  forall r, important_preg r = false -> data_preg r = false.
Proof.
  intros. destruct (data_preg r) eqn:E; auto. apply important_data_preg_1 in E. congruence.
Qed.

Global Hint Resolve important_data_preg_1 important_data_preg_2: asmgen.

Lemma nextinstr_inv2:
  forall r rs, important_preg r = true -> (nextinstr rs)#r = rs#r.
Proof.
  intros. apply nextinstr_inv. red; intro; subst; discriminate.
Qed.

(** Useful properties of the GPR0 registers. *)

Lemma gpr_or_zero_not_zero:
  forall rs (r:ireg), r <> GPR0 -> gpr_or_zero rs r = rs#r.
Proof.
  intros. unfold gpr_or_zero. case (ireg_eq r GPR0); tauto.
Qed.
Lemma gpr_or_zero_zero:
  forall rs, gpr_or_zero rs GPR0 = Vzero.
Proof.
  intros. reflexivity.
Qed.
Global Hint Resolve gpr_or_zero_not_zero gpr_or_zero_zero: asmgen.

Lemma gpr_or_zero_l_not_zero:
  forall rs (r:ireg), r <> GPR0 -> gpr_or_zero_l rs r = rs#r.
Proof.
  intros. unfold gpr_or_zero_l. case (ireg_eq r GPR0); tauto.
Qed.
Lemma gpr_or_zero_l_zero:
  forall rs, gpr_or_zero_l rs GPR0 = Vlong Int64.zero.
Proof.
  intros. reflexivity.
Qed.
Global Hint Resolve gpr_or_zero_l_not_zero gpr_or_zero_l_zero: asmgen.

Lemma ireg_of_not_GPR0:
  forall m r, ireg_of m = OK r -> IR r <> IR GPR0.
Proof.
  intros. erewrite <- ireg_of_eq; eauto with asmgen.
Qed.
Global Hint Resolve ireg_of_not_GPR0: asmgen.

Lemma ireg_of_not_GPR0':
  forall m r, ireg_of m = OK r -> r <> GPR0.
Proof.
  intros. generalize (ireg_of_not_GPR0 _ _ H). congruence.
Qed.
Global Hint Resolve ireg_of_not_GPR0': asmgen.

(** Useful properties of the LR register *)

Lemma preg_of_not_LR:
  forall r, LR <> preg_of r.
Proof.
  intros. auto using not_eq_sym with asmgen.
Qed.

Lemma preg_notin_LR:
  forall rl, preg_notin LR rl.
Proof.
  intros. rewrite preg_notin_charact. intros. apply preg_of_not_LR. 
Qed.

Global Hint Resolve preg_of_not_LR preg_notin_LR: asmgen.
      
(** Useful simplification tactic *)

Ltac Simplif :=
  ((rewrite nextinstr_inv by eauto with asmgen)
  || (rewrite nextinstr_inv2 by eauto with asmgen)
  || (rewrite Pregmap.gss)
  || (rewrite nextinstr_pc)
  || (rewrite Pregmap.gso by eauto with asmgen)); auto with asmgen.

Ltac Simpl := repeat Simplif.

(** Useful properties of pointer addition *)

Lemma loadv_offset_ptr:
  forall chunk m a delta v,
  Mem.loadv chunk m (Val.offset_ptr a delta) = Some v ->
  Mem.loadv chunk m (Val.add a (Vint (Ptrofs.to_int delta))) = Some v.
Proof.
  intros. destruct a; try discriminate H. simpl. rewrite Ptrofs.of_int_to_int by auto. assumption.
Qed.

Lemma storev_offset_ptr:
  forall chunk m a delta v m',
  Mem.storev chunk m (Val.offset_ptr a delta) v = Some m' ->
  Mem.storev chunk m (Val.add a (Vint (Ptrofs.to_int delta))) v = Some m'.
Proof.
  intros. destruct a; try discriminate H. simpl. rewrite Ptrofs.of_int_to_int by auto. assumption.
Qed.

(** * Correctness of PowerPC constructor functions *)

Section CONSTRUCTORS.

Variable ge: genv.
Variable fn: function.

(** Properties of comparisons. *)

Lemma compare_sint_spec:
  forall rs v1 v2,
  let rs1 := nextinstr (compare_sint rs v1 v2) in
     rs1#CR0_0 = Val.cmp Clt v1 v2
  /\ rs1#CR0_1 = Val.cmp Cgt v1 v2
  /\ rs1#CR0_2 = Val.cmp Ceq v1 v2
  /\ forall r', r' <> CR0_0 -> r' <> CR0_1 -> r' <> CR0_2 -> r' <> CR0_3 -> r' <> PC -> rs1#r' = rs#r'.
Proof.
  intros. unfold rs1.
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  intros. unfold compare_sint. Simpl.
Qed.

Lemma compare_uint_spec:
  forall rs m v1 v2,
  let rs1 := nextinstr (compare_uint rs m v1 v2) in
     rs1#CR0_0 = Val.cmpu (Mem.valid_pointer m) Clt v1 v2
  /\ rs1#CR0_1 = Val.cmpu (Mem.valid_pointer m) Cgt v1 v2
  /\ rs1#CR0_2 = Val.cmpu (Mem.valid_pointer m) Ceq v1 v2
  /\ forall r', r' <> CR0_0 -> r' <> CR0_1 -> r' <> CR0_2 -> r' <> CR0_3 -> r' <> PC -> rs1#r' = rs#r'.
Proof.
  intros. unfold rs1.
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  intros. unfold compare_uint. Simpl.
Qed.

Lemma compare_slong_spec:
  forall rs v1 v2,
  let rs1 := nextinstr (compare_slong rs v1 v2) in
     rs1#CR0_0 = Val.of_optbool (Val.cmpl_bool Clt v1 v2)
  /\ rs1#CR0_1 = Val.of_optbool (Val.cmpl_bool Cgt v1 v2)
  /\ rs1#CR0_2 = Val.of_optbool (Val.cmpl_bool Ceq v1 v2)
  /\ forall r', r' <> CR0_0 -> r' <> CR0_1 -> r' <> CR0_2 -> r' <> CR0_3 -> r' <> PC -> rs1#r' = rs#r'.
Proof.
  intros. unfold rs1. split. reflexivity. split. reflexivity. split. reflexivity.
  intros. unfold compare_slong. Simpl.
Qed.

Lemma compare_ulong_spec:
  forall rs m v1 v2,
  let rs1 := nextinstr (compare_ulong rs m v1 v2) in
     rs1#CR0_0 = Val.of_optbool (Val.cmplu_bool (Mem.valid_pointer m) Clt v1 v2)
  /\ rs1#CR0_1 = Val.of_optbool (Val.cmplu_bool (Mem.valid_pointer m) Cgt v1 v2)
  /\ rs1#CR0_2 = Val.of_optbool (Val.cmplu_bool (Mem.valid_pointer m) Ceq v1 v2)
  /\ forall r', r' <> CR0_0 -> r' <> CR0_1 -> r' <> CR0_2 -> r' <> CR0_3 -> r' <> PC -> rs1#r' = rs#r'.
Proof.
  intros. unfold rs1. split. reflexivity. split. reflexivity. split. reflexivity.
  intros. unfold compare_ulong. Simpl.
Qed.

(** Move between registers. *)

Lemma move_rr_base_correct:
  forall rd r k rs m,
  exists rs',
     exec_straight ge fn (move_rr_base rd r k) rs m  k rs' m
  /\ rs'#rd = rs#r
  /\ forall r': preg, r' <> rd -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold move_rr_base.
  destruct rd, r.
  - (* se_mr *)
    econstructor. split.
    apply exec_straight_one; simpl; reflexivity.
    intuition Simpl.
  - (* se_mfar *)
    econstructor. split.
    apply exec_straight_one; simpl; reflexivity.
    intuition Simpl.
  - (* se_mtar *)
    econstructor. split.
    apply exec_straight_one; simpl; reflexivity.
    intuition Simpl.
  - (* or *)
    econstructor. split.
    apply exec_straight_one; simpl; reflexivity.
    intuition Simpl.
Qed.

Lemma move_rr_correct:
  forall rd r k rs m,
  exists rs',
     exec_straight_opt ge fn (move_rr rd r k) rs m  k rs' m
  /\ rs'#rd = rs#r
  /\ forall r': preg, r' <> rd -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold move_rr.
  destruct (ireg_eq rd r).
  exists rs. split. econstructor. rewrite e. auto with asmgen.
  destruct (move_rr_base_correct rd r k rs m) as (rs' & EX & RES & OTH).
  exists rs'. split; try econstructor; assumption.
Qed.


(** Loading a constant. *)

Lemma loadimm_default_correct:
  forall r n k rs m,
  exists rs',
     exec_straight ge fn (loadimm_default r n k) rs m  k rs' m
  /\ rs'#r = Vint n
  /\ forall r': preg, r' <> r -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold loadimm_default.
  case (Int.eq (Int.shru n (Int.repr 7)) Int.zero).
  (* se_li *)
  destruct r.
  econstructor; split. apply exec_straight_one; simpl; eauto.
  intuition Simpl.
  econstructor; split. apply exec_straight_one; simpl; eauto.
  intuition Simpl.
  (* e_li *)
  case (Int.eq (high_s_12 n) Int.zero).
  econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  intuition Simpl.
  (* e_lis *)
  generalize (Int.eq_spec (low_s n) Int.zero); case (Int.eq (low_s n) Int.zero); intro.
  econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  rewrite <- (Int.add_zero (Int.shl (high_s n) (Int.repr 16))).
  rewrite <- H. rewrite low_high_s.
  intuition Simpl.
  (* e_lis + e_or2i *)
  econstructor; split. eapply exec_straight_two;
  simpl; eauto.
  split; intros; Simpl.  unfold Val.or. rewrite low_high_u. auto.
Qed.

Lemma loadimm_correct:
  forall r n k rs m ,
  exists rs',
    exec_straight ge fn (loadimm r n k) rs m k rs' m
  /\ rs'#r = Vint n
  /\ forall r': preg, r' <> r -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold loadimm.
  destruct r, (Int.is_power2 n) eqn:?; try apply loadimm_default_correct.
  econstructor; split.
Local Opaque Val.shl.
  apply exec_straight_one; simpl; eauto.
  split; intros; Simpl.
  assert (Int.sub (Int.repr 31) (Int.sub (Int.repr 31) i) = i).
  rewrite Int.sub_add_opp, Int.sub_add_opp.
  rewrite Int.neg_add_distr. rewrite Int.neg_involutive.
  rewrite <- Int.add_assoc.
  replace (Int.add (Int.repr 31) (Int.neg (Int.repr 31))) with Int.zero.
  rewrite Int.add_commut, Int.add_zero. reflexivity.
  rewrite <- Int.sub_add_opp. auto.
  rewrite H.
  rewrite <- (Val.mul_pow2 Vone n); auto.
  simpl. rewrite Int.mul_commut, Int.mul_one.
  reflexivity.
Qed.


(** Add integer immediate. *)

Lemma addi_low_correct:
  forall (r1 r2: ireg) n k rs m,
  exists rs',
     exec_straight ge fn (addi_low r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = Val.add rs#r2 (Vint n)
  /\ forall r': preg, r' <> r1 -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold addi_low.
  assert (DEFAULT: exists rs', exec_straight ge fn (Pe_add16i r1 r2 (Cint n) :: k) rs m k rs' m
                   /\  rs'#r1 = Val.add rs#r2 (Vint n)
                   /\ forall r': preg, r' <> r1 -> r' <> PC -> rs'#r' = rs#r').
  { econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl. }
  destruct r1; eauto. destruct (ireg_eq s r2); eauto. simpl.
  destruct (is_oim5 n); eauto.
  econstructor; split.  apply exec_straight_one; simpl; eauto. rewrite e. intuition Simpl.
  destruct (is_oim5 (Int.neg n)); eauto.
  econstructor; split. apply exec_straight_one; simpl; eauto. rewrite e.
  rewrite Val.sub_add_opp. rewrite Int.neg_involutive. intuition Simpl.
Qed.

Lemma addimm_correct:
  forall (r1 r2: ireg) n k rs m,
  r1 <> GPR0 ->
  r2 <> GPR0 ->
  exists rs',
     exec_straight ge fn (addimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = Val.add rs#r2 (Vint n)
  /\ forall r': preg, r' <> r1 -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold addimm.
  (* e_add16i *)
  case (Int.eq (high_s n) Int.zero).
  eapply addi_low_correct.
  (* se_mr + e_add2is *)
  generalize (Int.eq_spec (low_s n) Int.zero); case (Int.eq (low_s n) Int.zero); intro.
  exploit (move_rr_correct r1 r2). intros [rs' [EX [RES OTH]]].
  econstructor; split.
  eapply  exec_straight_opt_right.
  eexact EX. apply exec_straight_one; simpl; reflexivity.
  rewrite RES.
  split; intros; Simpl. generalize (low_high_s n). rewrite H1.
  rewrite Int.add_zero. congruence.
  (* e_add16i + e_add2is *)
  exploit addi_low_correct. intros [rs' [EX [RES OTH]]].
  econstructor; split. eapply exec_straight_trans.  eexact EX.
  eapply exec_straight_one; simpl; eauto.
  split; intros; Simpl. rewrite RES. rewrite Val.add_assoc. simpl.
  rewrite Int.add_commut, low_high_s. auto.
Qed.

(** And integer immediate. *)

Lemma andimm_base_correct:
  forall (r1 r2:ireg) n k (rs : regset) m,
  r2 <> GPR0 ->
  let v := Val.and rs#r2 (Vint n) in
  exists rs',
     exec_straight ge fn (andimm_base r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = v
  /\ rs'#CR0_2 = Val.cmp Ceq v Vzero
  /\ forall r', important_preg r' = true -> r' <> r1 -> rs'#r' = rs#r'.
Proof.
  intros. unfold andimm_base.
  case (Int.eq (high_u n) Int.zero).
  (* se_mr + and2i_ *)
  exploit (move_rr_correct r1 r2). intros [rs' [EX [RS OTH]]].
  econstructor. split.
  eapply exec_straight_opt_right. eexact EX.
  apply exec_straight_one; simpl; reflexivity.
  rewrite RS.
  split; try split; unfold compare_sint; intros; Simpl.
  (* se_mr + and2is_ *)
  generalize (Int.eq_spec (low_u n) Int.zero);
  case (Int.eq (low_u n) Int.zero); intro.
  exploit (move_rr_correct r1 r2). intros [rs' [EX [RS OTH]]].
  econstructor. split.
  eapply exec_straight_opt_right. eexact EX.
  apply exec_straight_one; simpl; eauto.
  rewrite RS.
  generalize (low_high_u n). rewrite H0. rewrite Int.or_zero.
  intro. rewrite H1. unfold compare_sint. split; Simpl.
  split. auto. intros. Simpl.
  (* loadimm + and *)
  generalize (loadimm_correct GPR0 n (select_encoding_instr Pse_and_ Pand_ true r1 r2 GPR0 k) rs m).
  intros [rs1 [EX1 [RES1 OTHER1]]].
  exists (nextinstr (compare_sint (rs1#r1 <- v) v Vzero)).
  generalize (compare_sint_spec (rs1#r1 <- v) v Vzero).
  intros [A [B [C D]]].
  split. eapply exec_straight_trans. eexact EX1.
  assert (exec_straight ge fn (Pand_ r1 r2 GPR0 :: k) rs1 m k (nextinstr (compare_sint rs1 # r1 <- v v Vzero)) m).
  { apply exec_straight_one. simpl. rewrite RES1. rewrite (OTHER1 r2); eauto with asmgen. reflexivity. }
  unfold select_encoding_instr.
  destruct r1, r2; auto. destruct (sreg_eq s s0); auto.
  apply exec_straight_one. simpl. rewrite RES1.
  rewrite (OTHER1 s); eauto with asmgen. subst v. rewrite e.
  reflexivity. reflexivity.
  destruct (sreg_eq s GPR0); auto. simpl.
  apply exec_straight_one. simpl. rewrite e. rewrite RES1.
  rewrite (OTHER1 s0); eauto with asmgen. subst v.
  rewrite Val.and_commut. reflexivity. reflexivity.
  split. rewrite D; auto with asmgen. Simpl.
  split. auto.
  intros. rewrite D; auto with asmgen. Simpl.
Qed.

Lemma andimm_correct:
  forall (r1 r2:ireg) n k (rs : regset) m,
  r2 <> GPR0 ->
  exists rs',
     exec_straight ge fn (andimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = Val.and rs#r2 (Vint n)
  /\ forall r', important_preg r' = true -> r' <> r1 -> rs'#r' = rs#r'.
Proof.
  intros. unfold andimm. destruct (is_rlw_mask n).
  (* turned into rlw *)
  econstructor; split. eapply exec_straight_one.
  simpl. rewrite Val.rolm_zero. eauto. auto.
  intuition Simpl.
  (* andimm_base *)
  destruct (andimm_base_correct r1 r2 n k rs m) as [rs' [A [B [C D]]]]; auto.
  exists rs'; auto.
Qed.

(** Or integer immediate. *)

Lemma orimm_correct:
  forall r1 (r2: ireg) n k (rs : regset) m,
  let v := Val.or rs#r2 (Vint n) in
  exists rs',
     exec_straight ge fn (orimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = v
  /\ forall r': preg, r' <> r1 -> r' <> PC ->rs'#r' = rs#r'.
Proof.
  intros. unfold orimm.
  case (Int.eq (high_u n) Int.zero).
  (* se_mr + e_or2i *)
  exploit (move_rr_correct r1 r2). intros [rs' [EX [RS OTH]]].
  econstructor. split.
  eapply exec_straight_opt_right. eexact EX.
  apply exec_straight_one; simpl; eauto.
  rewrite RS. intuition Simpl.
  (* se_mr + e_or2is *)
  generalize (Int.eq_spec (low_u n) Int.zero);
  case (Int.eq (low_u n) Int.zero); intro.
  exploit (move_rr_correct r1 r2). intros [rs' [EX [RS OTH]]].
  econstructor. split.
  eapply exec_straight_opt_right. eexact EX.
  apply exec_straight_one; simpl; eauto. rewrite RS.
  generalize (low_high_u n). rewrite H. rewrite Int.or_zero.
  intro. rewrite H0.
  intuition Simpl.
  (* se_mr + e_or2i + e_or2i *)
  exploit (move_rr_correct r1 r2). intros [rs' [EX [RS OTH]]].
  econstructor; split.
  eapply exec_straight_opt_right. eexact EX.
  eapply exec_straight_two; simpl; reflexivity.
  intuition Simpl. rewrite RS.
  rewrite Val.or_assoc. simpl. rewrite low_high_u.  reflexivity.
Qed.

(** Xor integer immediate. *)

Lemma xorimm_correct:
  forall r1 (r2: ireg) n k (rs : regset) m,
  r2 <> GPR0 ->
  let v := Val.xor rs#r2 (Vint n) in
  exists rs',
     exec_straight ge fn (xorimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = v
  /\ forall r': preg,  important_preg r' = true -> r' <> r1 -> rs'#r' = rs#r'.
Proof. intros. unfold xorimm.
  case (Int.eq (Int.shru n (Int.repr 8)) Int.zero).
  (* e_xori *)
  exists (nextinstr rs#r1 <- v).
  split. apply exec_straight_one; simpl; eauto.
  intuition Simpl.
  (* loadimm + xor *)
  generalize (loadimm_correct GPR0 n (Pxor r1 r2 GPR0 :: k) rs m).
  intros [rs1 [EX1 [RES1 OTHER1]]].
  exists (nextinstr ((rs1#r1 <- v))).
  split. eapply exec_straight_trans. eexact EX1.
  eapply exec_straight_one; simpl; eauto. rewrite RES1.
  rewrite OTHER1; eauto with asmgen. split; intros; Simpl.
Qed.

(** Rotate and mask. *)

Lemma rolm_correct:
  forall (r1 r2:ireg) amount mask k (rs : regset) m,
  r1 <> GPR0 ->
  exists rs',
     exec_straight ge fn (rolm r1 r2 amount mask k) rs m  k rs' m
  /\ rs'#r1 = Val.rolm rs#r2 amount mask
  /\ forall r', important_preg r' = true -> r' <> r1 -> rs'#r' = rs#r'.
Proof.
  intros. unfold rolm. destruct (is_rlw_mask mask).
  - (* rlwinm *)
    econstructor; split. eapply exec_straight_one; simpl; eauto.
    intuition Simpl.
  - (* rlwinm ; andimm *)
    set (rs1 := nextinstr (rs#r1 <- (Val.rolm rs#r2 amount Int.mone))).
    destruct (andimm_base_correct r1 r1 mask k rs1 m) as [rs' [A [B [C D]]]]; auto.
    exists rs'.
    split. eapply exec_straight_step; eauto. auto. auto.
    split. rewrite B. unfold rs1. rewrite nextinstr_inv; auto with asmgen.
    rewrite Pregmap.gss. destruct (rs r2); simpl; auto.
    unfold Int.rolm. rewrite Int.and_assoc.
    decEq; decEq; decEq. rewrite Int.and_commut. apply Int.and_mone.
    intros. rewrite D; auto. unfold rs1; Simpl.
Qed.

(** Shift right immediate *)

Lemma shrimm_correct:
  forall (r1 r2:ireg) n k (rs : regset) m,
  exists rs',
     exec_straight ge fn (shrimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = Val.shr rs#r2 (Vint n)
  /\ rs'#CARRY = Val.shr_carry rs#r2 (Vint n)
  /\ forall r', important_preg r' = true -> r' <> r1 -> rs'#r' = rs#r'.
Proof.
  intros. unfold shrimm.
  assert (DF: exists rs',
           exec_straight ge fn (Psrawi r1 r2 n :: k) rs m  k rs' m
           /\ rs'#r1 = Val.shr rs#r2 (Vint n)
           /\ rs'#CARRY = Val.shr_carry rs#r2 (Vint n)
           /\ forall r', important_preg r' = true -> r' <> r1 -> rs'#r' = rs#r').
  { econstructor. split. apply exec_straight_one; simpl; reflexivity.
    intuition Simpl. }
  destruct r1, r2; eauto. destruct (sreg_eq s s0); eauto.
  econstructor. split. apply exec_straight_one; simpl; reflexivity.
  rewrite e. intuition Simpl.
Qed.

(** Indexed memory loads. *)

Lemma select_mem_access_load_correct :
  forall chunk access_size instr1 instr2 (rd base: ireg) cst rs m,
  base <> GPR0 ->
  (forall cst (r1 rd: sreg) (rs: regset),
    exec_instr ge fn (instr1 rd cst r1) rs m =
    load1_non_zero ge chunk (IR rd) (Cint cst) r1 rs m) ->
  (forall cst (r1 rd: ireg) (rs: regset),
    exec_instr ge fn (instr2 rd cst r1) rs m =
    load1 ge chunk (IR rd) cst r1 rs m) ->
  exec_instr ge fn (select_mem_access access_size instr1 instr2 rd cst base) rs m =
  load1 ge chunk rd cst base rs m.
Proof.
  unfold select_mem_access. intros.
  destruct rd; try apply H1. destruct cst; try apply H1.
  destruct base; try apply H1.
  destruct (is_sd4_const access_size i); try apply H1.
  unfold load1. rewrite gpr_or_zero_not_zero.
  apply H0. congruence.
Qed.


Lemma select_mem_access_store_correct :
  forall chunk access_size instr1 instr2 (rd base: ireg) cst rs m,
  base <> GPR0 ->
  (forall cst (r1 rd: sreg) (rs: regset),
    exec_instr ge fn (instr1 rd cst r1) rs m =
    store1_non_zero ge chunk (IR rd) (Cint cst) r1 rs m) ->
  (forall cst (r1 rd: ireg) (rs: regset),
    exec_instr ge fn (instr2 rd cst r1) rs m =
    store1 ge chunk (IR rd) cst r1 rs m) ->
  exec_instr ge fn (select_mem_access access_size instr1 instr2 rd cst base) rs m =
  store1 ge chunk rd cst base rs m.
Proof.
  unfold select_mem_access. intros.
  destruct rd; try apply H1. destruct cst; try apply H1.
  destruct base; try apply H1.
  destruct (is_sd4_const access_size i); try apply H1.
  unfold store1. rewrite gpr_or_zero_not_zero.
  apply H0. congruence.
Qed.

Lemma accessind_load_correct:
  forall (A: Type) (inj: A -> preg)
       (instr1: A -> constant -> ireg -> instruction)
       (instr2: A -> ireg -> ireg -> instruction)
       (base: ireg) ofs rx chunk v (rs: regset) m k,
  (forall rs m r1 cst (r2 : ireg),
   r2 <> GPR0 ->
   exec_instr ge fn (instr1 r1 cst r2) rs m = load1 ge chunk (inj r1) cst r2 rs m) ->
  (forall rs m r1 r2 r3,
   exec_instr ge fn (instr2 r1 r2 r3) rs m = load2 chunk (inj r1) r2 r3 rs m) ->
  Mem.loadv chunk m (Val.offset_ptr rs#base ofs) = Some v ->
  base <> GPR0 -> inj rx <> PC ->
  exists rs',
     exec_straight ge fn (accessind instr1 instr2 base ofs rx k) rs m k rs' m
  /\ rs'#(inj rx) = v
  /\ forall r, r <> PC -> r <> inj rx -> r <> GPR0 -> rs'#r = rs#r.
Proof.
  intros. unfold accessind. set (ofs' := Ptrofs.to_int ofs) in *.
  assert (LD: Mem.loadv chunk m (Val.add (rs base) (Vint ofs')) = Some v)
    by (apply loadv_offset_ptr; auto).
  destruct (Int.eq (high_s ofs') Int.zero).
  - econstructor; split. apply exec_straight_one.
    rewrite (H rs m rx (Cint ofs')); auto. unfold load1. rewrite gpr_or_zero_not_zero by auto. simpl.
    rewrite LD. eauto. unfold nextinstr. Simpl.
    split; intros; Simpl.
  - exploit (loadimm_correct GPR0 ofs'); eauto. intros [rs' [P [Q R]]].
    econstructor; split. eapply exec_straight_trans. eexact P.
    apply exec_straight_one. rewrite H0. unfold load2.
    rewrite gpr_or_zero_not_zero by auto. simpl.
    rewrite Q, R by auto with asmgen.
    rewrite LD. reflexivity. Simpl.
    split; intros; Simpl.
Qed.

Lemma loadind_correct:
  forall (base: ireg) ofs ty dst k (rs: regset) m v c,
  loadind base ofs ty dst k = OK c ->
  Mem.loadv (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) = Some v ->
  base <> GPR0 ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, r <> PC -> r <> preg_of dst -> r <> GPR0 -> rs'#r = rs#r.
Proof.
  unfold loadind; intros. destruct ty; try discriminate; destruct (preg_of dst); inv H; simpl in H0.
  - apply accessind_load_correct with (inj := IR) (chunk := Mint32); auto with asmgen.
    intros. apply select_mem_access_load_correct; auto with asmgen.
  - apply accessind_load_correct with (inj := IR) (chunk := Mfloat32); auto with asmgen.
    intros. apply select_mem_access_load_correct; auto with asmgen.
  - apply accessind_load_correct with (inj := IR) (chunk := Many32); auto with asmgen.
    intros. apply select_mem_access_load_correct; auto with asmgen.
Qed.

(** Indexed memory stores. *)

Lemma accessind_store_correct:
  forall (A: Type) (inj: A -> preg)
       (instr1: A -> constant -> ireg -> instruction)
       (instr2: A -> ireg -> ireg -> instruction)
       (base: ireg) ofs rx chunk (rs: regset) m m' k,
  (forall rs m r1 cst (r2: ireg),
    r2 <> GPR0 ->
    exec_instr ge fn (instr1 r1 cst r2) rs m = store1 ge chunk (inj r1) cst r2 rs m) ->
  (forall rs m r1 r2 r3,
   exec_instr ge fn (instr2 r1 r2 r3) rs m = store2 chunk (inj r1) r2 r3 rs m) ->
  Mem.storev chunk m (Val.offset_ptr rs#base ofs) (rs (inj rx)) = Some m' ->
  base <> GPR0 -> inj rx <> PC -> inj rx <> GPR0 ->
  exists rs',
     exec_straight ge fn (accessind instr1 instr2 base ofs rx k) rs m k rs' m'
  /\ forall r, r <> PC -> r <> GPR0 -> rs'#r = rs#r.
Proof.
  intros. unfold accessind. set (ofs' := Ptrofs.to_int ofs) in *.
  assert (ST: Mem.storev chunk m (Val.add (rs base) (Vint ofs')) (rs (inj rx)) = Some m')
    by (apply storev_offset_ptr; auto).
  destruct (Int.eq (high_s ofs') Int.zero).
  - econstructor; split. apply exec_straight_one.
    rewrite H; auto. unfold store1. rewrite gpr_or_zero_not_zero by auto. simpl.
    rewrite ST. eauto. Simpl. intuition Simpl.
  - exploit (loadimm_correct GPR0 ofs'); eauto. intros [rs' [P [Q R]]].
    econstructor; split. eapply exec_straight_trans. eexact P.
    apply exec_straight_one. rewrite H0. unfold store2.
    rewrite gpr_or_zero_not_zero by auto.
    rewrite Q. rewrite R by auto with asmgen. rewrite R by auto.
    rewrite ST. reflexivity. eauto with asmgen. intuition Simpl.
Qed.

Lemma storeind_correct:
  forall (base: ireg) ofs ty src k (rs: regset) m m' c,
  storeind src base ofs ty k = OK c ->
  Mem.storev (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) (rs#(preg_of src)) = Some m' ->
  base <> GPR0 ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, r <> PC -> r <> GPR0 -> rs'#r = rs#r.
Proof.
  unfold storeind; intros.
  assert (preg_of src <> GPR0) by auto with asmgen.
  destruct ty; try discriminate; destruct (preg_of src) ; inv H; simpl in H0.
  - apply accessind_store_correct with (inj := IR) (chunk := Mint32); auto with asmgen.
    intros. apply select_mem_access_store_correct; auto.
  - apply accessind_store_correct with (inj := IR) (chunk := Mfloat32); auto with asmgen.
    intros. apply select_mem_access_store_correct; auto.
  - apply accessind_store_correct with (inj := IR) (chunk := Many32); auto with asmgen.
    intros. apply select_mem_access_store_correct; auto.
Qed.

(** Float comparisons. *)

Lemma floatcomp_correct:
  forall cmp (r1 r2: ireg) k rs m,
  exists rs',
     exec_straight ge fn (floatcomp cmp r1 r2 k) rs m k rs' m
  /\ rs'#(reg_of_crbit (fst (crbit_for_fcmp cmp))) =
       (if snd (crbit_for_fcmp cmp)
        then Val.cmpfs cmp rs#r1 rs#r2
        else Val.notbool (Val.cmpfs cmp rs#r1 rs#r2))
  /\ forall r',
       r' <> PC -> r' <> CR0_0 -> r' <> CR0_1 ->
       r' <> CR0_2 -> r' <> CR0_3 -> r' <> CR1_1 -> r' <> CR1_2  -> rs'#r' = rs#r'.
Proof.
  intros. unfold floatcomp. destruct cmp.
  - (* Ceq *)
    econstructor; split.
    apply exec_straight_one; simpl; reflexivity.
    split; intuition Simpl.
  - (* Cne *)
    econstructor; split.
    apply exec_straight_one; simpl; reflexivity. simpl.
    split; intuition Simpl.
    rewrite Val.negate_cmpfs_eq. auto.
  - (* Clt *)
    econstructor; split.
    apply exec_straight_one; simpl; reflexivity.
    split; intuition Simpl.
  - (* Cle *)
    econstructor; split.
    eapply exec_straight_three; simpl; reflexivity.
    split; simpl;  intuition Simpl.
    rewrite Val.cmpfs_le. reflexivity.
  - (* Cgt *)
    econstructor; split.
    apply exec_straight_one; simpl; reflexivity.
    split; intuition Simpl.
  - (* Cge *)
    econstructor; split.
    eapply exec_straight_three; simpl; reflexivity.
    split; simpl;  intuition Simpl.
    rewrite Val.cmpfs_ge. reflexivity.
Qed.

(** Translation of conditions. *)

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

Lemma transl_cond_correct_1:
  forall cond args k rs m c,
  transl_cond cond args k = OK c ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(reg_of_crbit (fst (crbit_for_cond cond))) =
       (if snd (crbit_for_cond cond)
        then Val.of_optbool (eval_condition cond (map rs (map preg_of args)) m)
        else Val.notbool (Val.of_optbool (eval_condition cond (map rs (map preg_of args)) m)))
  /\ forall r, important_preg r = true -> rs'#r = rs#r.
Proof.
  intros.
Opaque Int.eq.
  unfold transl_cond in H; destruct cond; ArgsInv; simpl.
 -  (* Ccomp *)
    fold (  Val.cmp c0 (rs x) (rs x0)).
    destruct (compare_sint_spec rs (rs x) (rs x0)) as [A [B [C D]]].
    econstructor; split.
    destruct x, x0; inv EQ2;
    apply exec_straight_one; simpl; reflexivity.
    split.
    case c0; simpl; auto; rewrite <- Val.negate_cmp; simpl; auto.
    auto with asmgen.
  - (* Ccompu *)
    fold (Val.cmpu (Mem.valid_pointer m) c0 (rs x) (rs x0)).
    destruct (compare_uint_spec rs m (rs x) (rs x0)) as [A [B [C D]]].
    econstructor; split.
    destruct x, x0; inv EQ2;
    apply exec_straight_one; simpl; reflexivity.
    split.
    case c0; simpl; auto; rewrite <- Val.negate_cmpu; simpl; auto.
    auto with asmgen.
  - (* Ccompimm *)
    fold (Val.cmp c0 (rs x) (Vint i)).
    destruct (Int.eq (Int.shru i (Int.repr 5)) Int.zero);
    [|destruct (Int.eq (high_s i) Int.zero)]; inv EQ0.
    + (* Short immediate *)
      destruct (compare_sint_spec rs (rs x) (Vint i)) as [A [B [C D]]].
      econstructor; split.
      destruct x; inv H0; apply exec_straight_one; simpl; reflexivity.
      split.
      case c0; simpl; auto; rewrite <- Val.negate_cmp; simpl; auto.
      auto with asmgen.
    + (* 16 bit signed immediate*)
      destruct (compare_sint_spec rs (rs x) (Vint i)) as [A [B [C D]]].
      econstructor; split.
      apply exec_straight_one. simpl; reflexivity. reflexivity.
      split.
      case c0; simpl; auto; rewrite <- Val.negate_cmp; simpl; auto.
      auto with asmgen.
    + (* immediate too large *)
      destruct (loadimm_correct GPR0 i (Pcmpw x GPR0 :: k) rs m) as [rs1 [EX1 [RES1 OTH1]]].
      destruct (compare_sint_spec rs1 (rs x) (Vint i)) as [A [B [C D]]].
      assert (SAME: rs1 x = rs x) by (apply OTH1; eauto with asmgen).
      exists (nextinstr (compare_sint rs1 (rs1 x) (Vint i))).
      split. eapply exec_straight_trans. eexact EX1.
      apply exec_straight_one. simpl. rewrite RES1; rewrite SAME; auto.
      reflexivity.
      split. rewrite SAME.
      case c0; simpl; auto; rewrite <- Val.negate_cmp; simpl; auto.
      intros. rewrite SAME; rewrite D; auto with asmgen.
  - (* Ccompuimm *)
    fold (Val.cmpu (Mem.valid_pointer m) c0 (rs x) (Vint i)).
    destruct (Int.eq (high_u i) Int.zero); inv EQ0.
    + (* 16 bit signed immediate *)
      destruct (compare_uint_spec rs m (rs x) (Vint i)) as [A [B [C D]]].
      econstructor; split.
      apply exec_straight_one. simpl; reflexivity. reflexivity.
      split.
      case c0; simpl; auto; rewrite <- Val.negate_cmpu; simpl; auto.
      auto with asmgen.
    + (* immediate too large *)
      destruct (loadimm_correct GPR0 i (Pcmplw x GPR0 :: k) rs m) as [rs1 [EX1 [RES1 OTH1]]].
      destruct (compare_uint_spec rs1 m (rs x) (Vint i)) as [A [B [C D]]].
      assert (SAME: rs1 x = rs x) by (apply OTH1; eauto with asmgen).
      exists (nextinstr (compare_uint rs1 m (rs1 x) (Vint i))).
      split. eapply exec_straight_trans. eexact EX1.
      apply exec_straight_one. simpl. rewrite RES1; rewrite SAME; auto.
      reflexivity.
      split. rewrite SAME.
      case c0; simpl; auto; rewrite <- Val.negate_cmpu; simpl; auto.
      intros. rewrite SAME; rewrite D; auto with asmgen.
  - (* Ccompfs *)
    fold (Val.cmpfs c0 (rs x) (rs x0)).
    destruct (floatcomp_correct c0 x x0 k rs m) as [rs' [EX [RES OTH]]].
    exists rs'. split. auto.
    split. apply RES.
    auto with asmgen.
  - (* Cnotcompfs *)
    rewrite Val.notbool_negb_3. rewrite Val.notbool_idem4.
    fold (Val.cmpfs c0 (rs x) (rs x0)).
    destruct (floatcomp_correct c0 x x0 k rs m) as [rs' [EX [RES OTH]]].
    exists rs'. split. auto.
    split. rewrite RES. destruct (snd (crbit_for_fcmp c0)); auto.
    auto with asmgen.
  - (* Cmaskzero *)
    destruct (andimm_base_correct GPR0 x i k rs m) as [rs' [A [B [C D]]]].
    eauto with asmgen.
    exists rs'. split. assumption.
    split. rewrite C. destruct (rs x); auto.
    auto with asmgen.
  - (* Cmasknotzero *)
    destruct (andimm_base_correct GPR0 x i k rs m) as [rs' [A [B [C D]]]].
    eauto with asmgen.
    exists rs'. split. assumption.
    split. rewrite C. destruct (rs x); auto.
    fold (option_map negb (Some (Int.eq (Int.and i0 i) Int.zero))).
    rewrite Val.notbool_negb_3. rewrite Val.notbool_idem4. auto.
    auto with asmgen.
Qed.

Lemma transl_cond_correct_2:
  forall cond args k rs m b c,
  transl_cond cond args k = OK c ->
  eval_condition cond (map rs (map preg_of args)) m = Some b ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(reg_of_crbit (fst (crbit_for_cond cond))) =
       (if snd (crbit_for_cond cond)
        then Val.of_bool b
        else Val.notbool (Val.of_bool b))
  /\ forall r, important_preg r = true -> rs'#r = rs#r.
Proof.
  intros.
  replace (Val.of_bool b)
  with (Val.of_optbool (eval_condition cond rs ## (preg_of ## args) m)).
  eapply transl_cond_correct_1; eauto.
  rewrite H0; auto.
Qed.

Lemma transl_cond_correct_3:
  forall cond args k ms sp rs m b m' c,
  transl_cond cond args k = OK c ->
  agree ms sp rs ->
  eval_condition cond (map ms args) m = Some b ->
  Mem.extends m m' ->
  exists rs',
     exec_straight ge fn c rs m' k rs' m'
  /\ rs'#(reg_of_crbit (fst (crbit_for_cond cond))) =
       (if snd (crbit_for_cond cond)
        then Val.of_bool b
        else Val.notbool (Val.of_bool b))
  /\ agree (Mach.undef_regs (destroyed_by_cond cond) ms) sp rs'.
Proof.
  intros.
  exploit transl_cond_correct_2. eauto.
    eapply eval_condition_lessdef. eapply preg_vals; eauto. eauto. eauto.
  intros [rs' [A [B C]]].
  exists rs'; split. eauto. split. auto.
  apply agree_undef_regs with rs; auto. intros r D E.
  apply C. apply important_data_preg_1; auto.
Qed.

(** Translation of condition operators *)

Remark add_carry_eq0:
  forall i,
  Vint (Int.add (Int.add (Int.sub Int.zero i) i)
                (Int.add_carry Int.zero (Int.xor i Int.mone) Int.one)) =
  Val.of_bool (Int.eq i Int.zero).
Proof.
  intros. rewrite <- Int.sub_add_l. rewrite Int.add_zero_l.
  rewrite Int.sub_idem. rewrite Int.add_zero_l. fold (Int.not i).
  predSpec Int.eq Int.eq_spec i Int.zero.
  subst i. reflexivity.
  unfold Val.of_bool, Vfalse. decEq.
  unfold Int.add_carry. rewrite Int.unsigned_zero. rewrite Int.unsigned_one.
  apply zlt_true.
  generalize (Int.unsigned_range (Int.not i)); intro.
  assert (Int.unsigned (Int.not i) <> Int.modulus - 1).
    red; intros.
    assert (Int.repr (Int.unsigned (Int.not i)) = Int.mone).
Local Transparent Int.repr.
      rewrite H1. apply Int.mkint_eq. reflexivity.
   rewrite Int.repr_unsigned in H2.
   assert (Int.not (Int.not i) = Int.zero).
   rewrite H2. apply Int.mkint_eq; reflexivity.
  rewrite Int.not_involutive in H3.
  congruence.
  lia.
Qed.

Remark add_carry_ne0:
  forall i,
  Vint (Int.add (Int.add i (Int.xor (Int.add i Int.mone) Int.mone))
                (Int.add_carry i Int.mone Int.zero)) =
  Val.of_bool (negb (Int.eq i Int.zero)).
Proof.
  intros. fold (Int.not (Int.add i Int.mone)). rewrite Int.not_neg.
  rewrite (Int.add_commut  (Int.neg (Int.add i Int.mone))).
  rewrite <- Int.sub_add_opp. rewrite Int.sub_add_r. rewrite Int.sub_idem.
  rewrite Int.add_zero_l. rewrite Int.add_neg_zero. rewrite Int.add_zero_l.
Transparent Int.eq.
  unfold Int.add_carry, Int.eq.
  rewrite Int.unsigned_zero.  rewrite Int.unsigned_mone.
  unfold negb, Val.of_bool, Vtrue, Vfalse.
  destruct (zeq (Int.unsigned i) 0); decEq.
  apply zlt_true. lia.
  apply zlt_false. generalize (Int.unsigned_range i). lia.
Qed.

Lemma transl_cond_op_correct:
  forall cond args r k rs m c,
  transl_cond_op cond args r k = OK c ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of r) = Val.of_optbool (eval_condition cond (map rs (map preg_of args)) m)
  /\ forall r', important_preg r' = true -> preg_notin r' (destroyed_by_cond cond) ->  r' <> preg_of r -> rs'#r' = rs#r'.
Proof.
  Proof.
  intros until args. unfold transl_cond_op.
  destruct (classify_condition cond args); intros; monadInv H; simpl;
  erewrite ! ireg_of_eq; eauto.
- (* eq 0 *)
  econstructor; split.
  eapply exec_straight_two; simpl; reflexivity.
  split. Simpl. destruct (rs x0); simpl; auto.
  apply add_carry_eq0.
  intros; Simpl.
- (* ne 0 *)
  econstructor; split.
  eapply exec_straight_two; simpl; reflexivity.
  split. Simpl. destruct (rs x0); simpl; auto.
  apply add_carry_ne0.
  intros; Simpl.
- (* ge 0 *)
  econstructor; split.
  eapply exec_straight_two; simpl; reflexivity.
  split. Simpl. rewrite Val.rolm_ge_zero. auto.
  intros; Simpl.
- (* lt 0 *)
  econstructor; split.
  apply exec_straight_one; simpl; reflexivity.
  split. Simpl. rewrite Val.rolm_lt_zero. auto.
  intros; Simpl.
- (* default *)
  set (bit := fst (crbit_for_cond c)) in *.
  set (isset := snd (crbit_for_cond c)) in *.
  set (k1 :=
        Pmfcrbit x bit ::
        (if isset
         then k
         else Pe_xori x x Int.one :: k)).
  generalize (transl_cond_correct_1 c rl k1 rs m c0 EQ0).
  fold bit; fold isset.
  intros [rs1 [EX1 [RES1 AG1]]].
  destruct isset.
  +  (* bit set *)
    econstructor; split.  eapply exec_straight_trans. eexact EX1.
    unfold k1. apply exec_straight_one; simpl; reflexivity.
    intuition Simpl.
  + (* bit clear *)
    econstructor; split.  eapply exec_straight_trans. eexact EX1.
    unfold k1. eapply exec_straight_two; simpl; reflexivity.
    intuition Simpl.
    rewrite RES1. destruct (eval_condition c rs ## (preg_of ## rl) m). destruct b; auto. auto.
Qed.

Lemma transl_select_op_correct:
  forall cond args ty r1 r2 rd k rs m c,
  transl_select_op cond args r1 r2 rd k = OK c ->
  important_preg rd = true -> important_preg r1 = true -> important_preg r2 = true ->
  exists rs',
  exec_straight ge fn c rs m k rs' m
  /\ Val.lessdef (Val.select (eval_condition cond (map rs (map preg_of args)) m) rs#r1 rs#r2 ty) rs'#rd
  /\ forall r, important_preg r = true  -> r <> rd -> rs'#r = rs#r.
Proof.
  intros until c.  intros TR IMP1 IMP2 IMP3.
  unfold transl_select_op in TR.
  destruct (ireg_eq r1 r2).
  - inv TR. exploit (move_rr_base_correct rd r2). intros [rs' [EX [RS OTH]]].
    econstructor; split; [|split]. eexact EX. rewrite RS.
    destruct (eval_condition cond rs ## (preg_of ## args) m) as [[]|]; simpl; auto using Val.lessdef_normalize.
    intros; Simpl. rewrite OTH; auto with asmgen.
  - destruct (transl_cond_correct_1 cond args _ rs m _ TR) as (rs1 & A & B & C).
    set (bit := fst (crbit_for_cond cond)) in *.
    set (dir := snd (crbit_for_cond cond)) in *.
    set (ob := eval_condition cond rs##(preg_of##args) m) in *.
    econstructor; split; [|split].
    + eapply exec_straight_trans. eexact A. apply exec_straight_one. simpl; eauto.
      reflexivity.
    + Simpl.
      rewrite <- (C r1), <- (C r2) by auto.
      rewrite B, gpr_or_zero_not_zero.
      destruct dir; destruct ob as [[]|]; simpl; auto using Val.lessdef_normalize.
      destruct dir; intros e; subst; discriminate.
    + intros. Simpl.
Qed.

Lemma select_encoding_instr_correct:
  forall (instr1: sreg -> sreg -> instruction)
    (instr2: ireg -> ireg -> ireg -> instruction)
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
  /\ forall r, important_preg r = true -> r <> rd -> rs'#r = rs#r.
Proof.
  intros. unfold select_encoding_instr.
  assert (BASE: exists rs',
           exec_straight ge fn (instr2 rd r1 r2 :: k) rs m k rs' m
           /\ rs'#rd = sem (rs r1) (rs r2)
           /\ forall r, important_preg r = true -> r <> rd -> rs'#r = rs#r).
  { econstructor. split. econstructor. apply H1. Simpl. split; intros; Simpl. }
  destruct rd, r1, r2; eauto.
  destruct (sreg_eq s s0); eauto.
  rewrite e. econstructor; split. eapply exec_straight_one; simpl; eauto. split; intros; Simpl.
  destruct commut, (sreg_eq s s1); eauto.
  simpl. econstructor; split. eapply exec_straight_one; simpl; eauto.
  rewrite e, H; eauto.  split; intros; Simpl.
Qed.

(** Translation of arithmetic operations. *)

Ltac TranslOpSimpl :=
  econstructor; split;
  [ apply exec_straight_one; [simpl; eauto | reflexivity]
  | split; [ apply Val.lessdef_same; Simpl; fail | intros; Simpl; fail ] ].

Lemma transl_op_correct_aux:
  forall op args res k (rs: regset) m v c,
  transl_op op args res k = OK c ->
  eval_operation ge (rs#GPR1) op (map rs (map preg_of args)) m = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ Val.lessdef v rs'#(preg_of res)
  /\ forall r, important_preg r = true -> r <> preg_of res -> preg_notin r (destroyed_by_op op) -> rs' r = rs r.
Proof.
    assert (SAME: forall v1 v2, v1 = v2 -> Val.lessdef v2 v1). { intros; subst; auto. }
Opaque Int.eq.
  intros. unfold transl_op in H; destruct op; ArgsInv; simpl in H0; try (inv H0); try TranslOpSimpl.
- (* Omove *)
  destruct (preg_of res) eqn:RES; destruct (preg_of m0) eqn:ARG; inv H.
  exploit (move_rr_base_correct i i0). intros [rs' [EX [RS OTH]]].
  exists rs'. split. eexact EX. split. rewrite RS. auto. intros.
  rewrite OTH; auto with asmgen.
- (* Ointconst *)
  destruct (loadimm_correct x i k rs m) as [rs' [A [B C]]].
  exists rs'. rewrite B. auto with asmgen.
- (* Oaddrsymbol *)
  set (v' := Genv.symbol_address ge i i0).
  destruct (symbol_is_small_data i i0) eqn: SD; [ | destruct (symbol_is_rel_data i i0) ].
  + (* small data *)
    Opaque Val.add.
    econstructor; split. apply exec_straight_one; simpl; reflexivity.
    split. apply SAME. Simpl. rewrite small_data_area_addressing by auto.
    auto. intuition Simpl.
  + (* relative data *)
    econstructor; split. eapply exec_straight_three; simpl; reflexivity.
    split. apply SAME. Simpl. rewrite Val.add_assoc. rewrite (Val.add_commut (low_half ge i i0)).
    rewrite low_high_half. rewrite add_zero_symbol_address. reflexivity.
    intuition Simpl.
  + (* absolute data *)
    econstructor; split. eapply exec_straight_two; simpl; reflexivity.
    split. apply SAME. Simpl. apply low_high_half.
    intuition Simpl.
- (* Oaddrstack *)
  destruct (addimm_correct x GPR1 (Ptrofs.to_int i) k rs m) as [rs' [EX [RES OTH]]]; eauto with asmgen.
  exists rs'; split. auto. split; auto with asmgen.
  rewrite RES. destruct (rs GPR1); simpl; auto.
  Transparent Val.add.
  simpl. rewrite Ptrofs.of_int_to_int; auto.
- (* Ocast8signed *)
  destruct x0; try TranslOpSimpl.
  exploit (move_rr_correct s x). intros [rs' [EX [RS OTH]]].
  econstructor. split. eapply exec_straight_opt_right. eexact EX.
  apply exec_straight_one; simpl; reflexivity. rewrite RS. split; intros; Simpl.
- (* Ocast16signed *)
  destruct x0; try TranslOpSimpl.
  exploit (move_rr_correct s x). intros [rs' [EX [RS OTH]]].
  econstructor. split. eapply exec_straight_opt_right. eexact EX.
  apply exec_straight_one; simpl; reflexivity. rewrite RS. split; intros; Simpl.
- (* Oadd *)
  destruct (select_encoding_instr_correct Pse_add Padd Val.add true x1 x x0 k rs m) as [rs' [EX [RES OTH]]]; eauto with asmgen.
  intros. apply Val.add_commut.
  exists rs'. split; auto.
- (* Oaddimm *)
  exploit (addimm_correct x0 x i k); eauto with asmgen.
  intros [rs' [EX [RES OTH]]].
  exists rs'. split; eauto. rewrite RES. split. auto.
  intros. rewrite OTH; eauto with asmgen.
- (* Oaddsymbol *)
  destruct (symbol_is_small_data i i0) eqn:SD; [ | destruct (symbol_is_rel_data i i0) ].
  + (* small data *)
    econstructor; split. eapply exec_straight_two; simpl; reflexivity.
    split; intros; Simpl. apply SAME. rewrite (Val.add_commut (rs x)).
    rewrite small_data_area_addressing by auto. reflexivity.
  + (* relative data *)
    econstructor; split.
    eapply exec_straight_trans.
    eapply exec_straight_trans.
    eapply exec_straight_trans.
    eapply exec_straight_one; reflexivity.
    eapply exec_straight_one; reflexivity.
    eapply exec_straight_one; reflexivity.
    eapply exec_straight_one; reflexivity.
    split; intros; Simpl.
    rewrite (Val.add_assoc (Vint Int.zero)).
    replace (Val.add (const_low ge (Csymbol_rel_low i i0)) (const_high ge (Csymbol_rel_high i i0))) with (Genv.symbol_address ge i i0) by
        (simpl; rewrite Val.add_commut; rewrite low_high_half; auto).
    rewrite  add_zero_symbol_address.
    auto.
  + (* absolute data *)
    econstructor; split. eapply exec_straight_two; simpl; reflexivity.
    split; intros; Simpl.
    rewrite Val.add_assoc. rewrite Val.add_commut.
    replace (Val.add (low_half ge i i0) (high_half ge i i0)) with (Genv.symbol_address ge i i0) by
        (rewrite Val.add_commut; rewrite low_high_half; auto).
    auto.
- (* Osub *)
  destruct x1, x, x0; try TranslOpSimpl.
  destruct (sreg_eq s s0); [rewrite e|]; try TranslOpSimpl.
  destruct (sreg_eq s s1); [rewrite e|]; TranslOpSimpl.
- (* Osubimm *)
  exploit (loadimm_correct GPR0 i). intros [rs' [EX [RES OTH]]].
  econstructor. split.
  eapply exec_straight_trans. eapply EX. eapply exec_straight_one; simpl; reflexivity.
  split; intros; Simpl. rewrite RES. rewrite OTH; eauto with asmgen.
- (* Omull *)
  destruct (select_encoding_instr_correct Pse_mullw Pmullw Val.mul true x1 x x0 k rs m) as [rs' [EX [RES OTH]]]; eauto with asmgen.
  intros; apply Val.mul_commut.
  exists rs'. split; auto.
- (* Omullimm *)
  exploit (loadimm_correct GPR0 i). intros [rs' [EX [RES OTH]]].
  econstructor. split.
  eapply exec_straight_trans. eexact EX. eapply exec_straight_one; simpl; reflexivity.
  split; intros; Simpl. rewrite RES. rewrite OTH; eauto with asmgen.
- (* Odiv *)
  replace v with (Val.maketotal (Val.divs (rs x) (rs x0))).
  TranslOpSimpl.
  rewrite H1; auto.
- (* Odivu *)
  replace v with (Val.maketotal (Val.divu (rs x) (rs x0))).
  TranslOpSimpl.
  rewrite H1; auto.
- (* Oand *)
  set (v' := Val.and (rs x) (rs x0)) in *.
  pose (rs1 := rs#x1 <- v').
  destruct (compare_sint_spec rs1 v' Vzero) as [A [B [C D]]].
  econstructor; split. unfold select_encoding_instr.
  destruct x1, x, x0; try (apply exec_straight_one; simpl; reflexivity).
  destruct (sreg_eq s s0); [rewrite e| simpl; destruct (sreg_eq s s1); simpl; [rewrite e; rewrite Val.and_commut|]]; try (apply exec_straight_one; simpl; reflexivity).
  split. rewrite D; auto with asmgen. unfold rs1; Simpl.
  intros. rewrite D; auto with asmgen. unfold rs1; Simpl.
- (* Oandimm *)
  destruct (andimm_correct x0 x i k rs m) as [rs' [A [B C]]]. eauto with asmgen.
  exists rs'; auto with asmgen.
- (* Oor*)
  destruct (select_encoding_instr_correct Pse_or Por Val.or true x1 x x0 k rs m) as [rs' [EX [RES OTH]]]; eauto with asmgen.
  intros; apply Val.or_commut.
  exists rs'. split; auto.
- (* Oorimm *)
  destruct (orimm_correct x0 x i k rs m) as [rs' [A [B C]]].
  exists rs'; auto with asmgen.
- (* Oxorimm *)
  destruct (xorimm_correct x0 x i k rs m) as [rs' [A [B C]]].
  apply (ireg_of_not_GPR0' m0 x EQ).
  exists rs'; auto with asmgen.
- (* Onor *)
  replace (Val.notint (rs x))
     with (Val.notint (Val.or (rs x) (rs x))).
  TranslOpSimpl.
  destruct (rs x); simpl; auto. rewrite Int.or_idem. auto.
- (* Oandc *)
  destruct (select_encoding_instr_correct Pse_andc Pandc (fun a b => Val.and a (Val.notint b)) false x1 x x0 k rs m) as [rs' [EX [RES OTH]]]; intros; try inv H; eauto with asmgen.
  exists rs'; auto.
- (* Oshl *)
  destruct (select_encoding_instr_correct Pse_slw Pslw Val.shl false x1 x x0 k rs m) as [rs' [EX [RES OTH]]]; intros; try inv H; eauto with asmgen.
  exists rs'; auto.
- (* Oshr *)
  unfold select_encoding_instr.
  destruct x1, x, x0; try TranslOpSimpl.
  destruct (sreg_eq s s0); try TranslOpSimpl.
  rewrite e. TranslOpSimpl.
- (* Oshrimm *)
  destruct (shrimm_correct x0 x i k rs m) as [rs' [A [B [C D]]]].
  exists rs'; auto with asmgen.
- (* Oshrximm *)
  destruct (shrimm_correct x0 x i (Paddze x0 x0 :: k) rs m) as [rs' [A [B [C D]]]].
  econstructor. split.
  eapply exec_straight_trans. eexact A.
  apply exec_straight_one; simpl; reflexivity.
  intuition Simpl. apply SAME. rewrite B, C. apply Val.shrx_carry. auto.
- (* Oshru *)
  destruct (select_encoding_instr_correct Pse_srw Psrw Val.shru false x1 x x0 k rs m)  as [rs' [EX [RES OTH]]]; intros; try inv H; eauto with asmgen.
  exists rs'; auto.
- destruct (rolm_correct x0 x i i0 k rs m) as [rs' [A [B C]]].
  apply (ireg_of_not_GPR0' res x0 EQ1).
  exists rs'; auto.
- (* Ointofsingle *)
  replace v with (Val.maketotal (Val.intofsingle (rs x0))).
  TranslOpSimpl.
  rewrite H1; auto.
- (* Ointuofsingle *)
  replace v with (Val.maketotal (Val.intuofsingle (rs x0))).
  TranslOpSimpl.
  rewrite H1; auto.
- (* Osingleofint *)
  replace v with (Val.maketotal (Val.singleofint (rs x0))).
  TranslOpSimpl.
  rewrite H1; auto.
- (* Osingleofintu *)
  replace v with (Val.maketotal (Val.singleofintu (rs x0))).
  TranslOpSimpl.
  rewrite H1; auto.
- (* Ocmp *)
   destruct (transl_cond_op_correct c0 args res k rs m c) as [rs' [A [B C]]]; auto.
  exists rs'; auto with asmgen.
- (* Osel *)
  assert (X: forall mr r, ireg_of mr = OK r -> important_preg r = true).
  { intros. apply ireg_of_eq in H0. apply important_data_preg_1. rewrite <- H0.
    auto with asmgen. }
  destruct (preg_of res) eqn:RES; monadInv H; rewrite <- RES.
 rewrite (ireg_of_eq _ _ EQ), (ireg_of_eq _ _ EQ0), (ireg_of_eq _ _ EQ1) in *.
 destruct (transl_select_op_correct _ _ t _ _ _ _ rs m _ EQ3) as (rs' & A & B & C); eauto.
Qed.

Lemma transl_op_correct:
  forall op args res k ms sp rs m v m' c,
  transl_op op args res k = OK c ->
  agree ms sp rs ->
  eval_operation ge sp op (map ms args) m = Some v ->
  Mem.extends m m' ->
  exists rs',
     exec_straight ge fn c rs m' k rs' m'
  /\ agree (Regmap.set res v (Mach.undef_regs (destroyed_by_op op) ms)) sp rs'
  /\ forall r, important_preg r = true -> r <> preg_of res -> preg_notin r (destroyed_by_op op) -> rs' r = rs r.
Proof.
  intros.
  exploit eval_operation_lessdef. eapply preg_vals; eauto. eauto. eauto.
  intros [v' [A B]].  rewrite (sp_val _ _ _ H0) in A.
  exploit transl_op_correct_aux; eauto. intros [rs' [P [Q R]]].
  exists rs'; split. eexact P.
  split. apply agree_set_undef_mreg with rs; auto with asmgen. eapply Val.lessdef_trans; eauto.
  auto.
Qed.

(** Translation of memory accesses *)

Lemma transl_memory_access_correct:
  forall (P: regset -> Prop) mk1 mk2 addr args temp k c (rs: regset) a m m',
  transl_memory_access mk1 mk2 addr args temp k = OK c ->
  eval_addressing ge (rs#GPR1) addr (map rs (map preg_of args)) = Some a ->
  temp <> GPR0 ->
  (forall cst (r1: ireg) (rs1: regset) k,
    r1 <> GPR0 ->
    Val.lessdef a (Val.add (gpr_or_zero rs1 r1) (const_low ge cst)) ->
    (forall r, r <> PC -> r <> temp -> r <> GPR0 -> rs1 r = rs r) ->
    exists rs',
        exec_straight ge fn (mk1 cst r1 :: k) rs1 m k rs' m' /\ P rs') ->
  (forall (r1 r2: ireg) (rs1: regset) k,
    Val.lessdef a (Val.add (gpr_or_zero rs1 r1) rs1#r2) ->
    (forall r, r <> PC -> r <> temp -> r <> GPR0 -> rs1 r = rs r) ->
    exists rs',
        exec_straight ge fn (mk2 r1 r2 :: k) rs1 m k rs' m' /\ P rs') ->
  exists rs',
      exec_straight ge fn c rs m k rs' m' /\ P rs'.
Proof.
  intros until m'; intros TR ADDR TEMP MK1 MK2.
  unfold transl_memory_access in TR; destruct addr; ArgsInv; simpl in ADDR; inv ADDR.
  - (* Aindexed *)
    destruct (Int.eq (high_s i) Int.zero).
    +  (* Aindexed short *)
      apply MK1. apply (ireg_of_not_GPR0' m0 x); auto. rewrite gpr_or_zero_not_zero; eauto with asmgen. auto.
    +  (* Aindexed long *)
      exploit (move_rr_correct temp x). intros [rs' [EX [RS OTH]]].
      set (rs1 := (nextinstr rs' # temp <- (Val.add (rs x) (Vint (Int.shl (high_s i) (Int.repr 16)))))).
      exploit (MK1 (Cint (low_s i)) temp rs1 k).
      simpl. auto. rewrite gpr_or_zero_not_zero; eauto with asmgen.  unfold rs1; Simpl.
      rewrite Val.add_assoc.
Transparent Val.add.
    simpl. rewrite low_high_s. auto.
    intros; unfold rs1; Simpl.
    intros [rs'' [EX' AG']].
    exists rs''. split. eapply exec_straight_opt_right.
    eexact EX.
    eapply exec_straight_trans.
    apply exec_straight_one; simpl; reflexivity.
    rewrite RS.
    eexact EX'. auto.
  - (* Aindexed2 *)
    apply MK2. rewrite gpr_or_zero_not_zero; eauto with asmgen. auto.
  - (* Aglobal *)
    destruct (symbol_is_small_data i i0) eqn:SISD; [ | destruct (symbol_is_rel_data i i0) ]; inv TR.
    +(* Aglobal from small data *)
      set (rs1 := nextinstr (rs#GPR0 <- Vzero)).
      set (rs2 :=nextinstr (rs1#temp <- (Val.add rs1#GPR0 (Genv.symbol_address ge i i0)))).
      exploit (MK1 (Cint Int.zero) temp rs2); auto.
      unfold rs2, rs1. Simpl. rewrite Val.add_commut. rewrite gpr_or_zero_not_zero; auto. Simpl.
      rewrite add_zero_symbol_address. rewrite add_zero_symbol_address. auto.
      intros; unfold rs2, rs1; Simpl.
      intros [rs' [EX' AG']].
      exists rs'; split. apply exec_straight_step with rs1 m; auto.
      apply exec_straight_step with rs2 m; auto.
      unfold rs2, rs1. simpl. rewrite small_data_area_addressing; auto.
      eexact EX'. auto.
    + (* Aglobal from realive data *)
      set (rs1 := nextinstr (rs#GPR0 <- Vzero)).
      set (rs2 := nextinstr (rs1#temp <- (Val.add (rs1#GPR0) (low_half ge i i0)))).
      set (rs3 := nextinstr (rs2#temp <- (Val.add (rs2#temp) (high_half ge i i0)))).
      exploit (MK1 (Cint Int.zero) temp rs3); auto.
      unfold rs3, rs2, rs1. rewrite gpr_or_zero_not_zero; auto. Simpl.
      rewrite high_low_half_zero.
      rewrite Val.add_commut. rewrite add_zero_symbol_address.
      auto.
      intros; unfold rs3, rs2, rs1; Simpl.
      intros [rs' [EX' AG']].
      exists rs'; split. eapply exec_straight_trans.
      eapply exec_straight_three; simpl; reflexivity.
      eexact EX'. apply AG'.
    +  (* Aglobal from absolute data *)
      set (rs1 := nextinstr (rs#temp <- (high_half ge i i0))).
      exploit (MK1 (Csymbol_low i i0) temp rs1).
      auto. rewrite gpr_or_zero_not_zero; eauto with asmgen.
      unfold rs1. Simpl. simpl. rewrite low_high_half. auto.
      intros; unfold rs1; Simpl.
      intros [rs' [EX' AG']].
      exists rs'. split. eapply exec_straight_step.
      reflexivity. Simpl. eexact EX'. auto.
  - (* Abased *)
    destruct (symbol_is_small_data i i0) eqn:SISD; [ | destruct (symbol_is_rel_data i i0) ].
    + (* Abased from small data *)
      set (rs1 := nextinstr (rs#GPR0 <- Vzero)).
      set (rs2 := nextinstr (rs1#GPR0 <- (Val.add rs1#GPR0 (Genv.symbol_address ge i i0)))).
      exploit (MK2 x GPR0 rs2 k).
      simpl. rewrite gpr_or_zero_not_zero; eauto with asmgen.
      unfold rs2, rs1; Simpl. rewrite Val.add_commut. rewrite add_zero_symbol_address. auto.
      intros. unfold rs2, rs1; Simpl.
      intros [rs' [EX' AG']].
      exists rs'; split. apply exec_straight_step with rs1 m; auto.
      apply exec_straight_step with rs2 m; auto.
      unfold exec_instr.  f_equal. unfold rs2, rs1. f_equal. f_equal.
      unfold const_low. rewrite small_data_area_addressing; auto.
      eexact AG'.
    + (* Abased from relative data *)
      exploit (move_rr_correct temp x
                               (Pse_li GPR0 Int.zero ::
                                Pe_add16i GPR0 GPR0 (Csymbol_rel_low i i0) ::
                                Pe_add2is GPR0 (Csymbol_rel_high i i0) ::
                                mk2 temp GPR0 :: k) rs).
      intros [rs1 [EX [RS OTH]]].
      set (rs2 := nextinstr (rs1#GPR0 <-  (Vint Int.zero))).
      set (rs3 := nextinstr (rs2#GPR0 <- (Val.add (rs2#GPR0) (low_half ge i i0)))).
      set (rs4 := nextinstr (rs3#GPR0 <- (Val.add (rs3#GPR0) (high_half ge i i0)))).
      exploit (MK2 temp GPR0 rs4).
      rewrite gpr_or_zero_not_zero; eauto with asmgen.
      unfold  rs4, rs3, rs2. Simpl.
      rewrite high_low_half_zero. rewrite Val.add_commut. rewrite RS.
      auto.
      intros; unfold rs4, rs3, rs2; Simpl.
      intros [rs' [EX' AG']].
      exists rs'. split.
      eapply exec_straight_opt_right. eexact EX.
      eapply exec_straight_step. reflexivity. Simpl.
      eapply exec_straight_step. reflexivity. Simpl.
      eapply exec_straight_step. reflexivity. Simpl.
      eexact EX'. assumption.
    + (* Abased absolute *)
      set (rs1 := nextinstr (rs#temp <- (Val.add (rs#x) (low_half ge i i0)))).
      set (rs2 := nextinstr (rs1#temp <- (Val.add (rs1#temp) (high_half ge i i0)))).
      exploit (MK1 (Cint Int.zero) temp rs2 k); auto.
      unfold rs2, rs1. rewrite gpr_or_zero_not_zero; auto. Simpl.
      rewrite Val.add_assoc.
      rewrite Val.add_assoc.
      rewrite (Val.add_commut (low_half _ _ _ )).
      rewrite (Val.add_commut _ Vzero).
      rewrite low_high_half_zero.
      rewrite Val.add_commut. auto.
      intros. unfold rs2, rs1. Simpl.
      intros [rs' [EX' AG']].
      exists rs'. split.
      eapply exec_straight_trans.
      eapply exec_straight_two; simpl; reflexivity.
      eexact EX'. assumption.
  -  (* Ainstack *)
    set (ofs := Ptrofs.to_int i) in *.
    assert (L: Val.lessdef (Val.offset_ptr (rs GPR1) i) (Val.add (rs GPR1) (Vint ofs))).
    { destruct (rs GPR1); simpl; auto. unfold ofs; rewrite Ptrofs.of_int_to_int; auto. }
   destruct (Int.eq (high_s ofs) Int.zero); inv TR.
    + (* Ainstack 16 bit offset *)
      apply MK1. congruence. eauto with asmgen. intros. auto.
     + (* Ainstack offset larger than 16 bit *)
      set (rs1 := nextinstr (rs#GPR0 <- (Vint (Int.shl (high_s ofs) (Int.repr 16))))).
      set (rs2 := nextinstr (rs1#GPR0 <- (Val.add rs1#GPR0 (Vint (low_s ofs))))).
      exploit (MK2 GPR1 GPR0 rs2 k).
      unfold rs2, rs1. Simpl.
      replace (Val.add (Vint (Int.shl (high_s ofs) (Int.repr 16))) (Vint (low_s ofs))) with (Vint ofs).
      auto.
      simpl. rewrite low_high_s. reflexivity.
      intros. unfold rs2, rs1. Simpl.
      intros [rs' [EX' AG']].
      exists rs'. split. eapply exec_straight_trans.
      eapply exec_straight_two; reflexivity.
      eexact EX'. assumption.
Qed.

(** Translation of loads *)

Lemma transl_load_correct:
  forall chunk addr args dst k c (rs: regset) m a v,
  transl_load chunk addr args dst k = OK c ->
  eval_addressing ge (rs#GPR1) addr (map rs (map preg_of args)) = Some a ->
  Mem.loadv chunk m a = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, r <> PC -> r <> GPR12 -> r <> GPR0 -> r <> preg_of dst -> rs' r = rs r.
Proof.
  intros.
  assert (LD: forall v, Val.lessdef a v -> v = a).
  { intros. inv H2; auto. discriminate H1. }
  assert (BASE: forall mk1 mk2 k' chunk' v',
           transl_memory_access mk1 mk2 addr args GPR12 k' = OK c ->
           Mem.loadv chunk' m a = Some v' ->
           (forall cst (r1: ireg) (rs1: regset),
             r1 <> GPR0 ->
             exec_instr ge fn (mk1 cst r1) rs1 m =
             load1 ge chunk' (preg_of dst) cst r1 rs1 m) ->
           (forall (r1 r2: ireg) (rs1: regset),
             exec_instr ge fn (mk2 r1 r2) rs1 m =
             load2 chunk' (preg_of dst) r1 r2 rs1 m) ->
           exists rs',
           exec_straight ge fn c rs m k' rs' m
           /\ rs'#(preg_of dst) = v'
           /\ forall r, r <> PC -> r <> GPR12 -> r <> GPR0 -> r <> preg_of dst -> rs' r = rs r).
  {
  intros. eapply transl_memory_access_correct; eauto. congruence.
  intros. econstructor; split. apply exec_straight_one.
  rewrite H4. unfold load1. apply LD in H7. simpl. rewrite H7. rewrite H3. eauto. auto.
  unfold nextinstr. rewrite Pregmap.gss. rewrite Pregmap.gso; auto with asmgen.
  intuition Simpl.
  intros. econstructor; split. apply exec_straight_one.
  rewrite H5. unfold load2. apply LD in H6. rewrite H6. rewrite H3. eauto.
  unfold nextinstr. rewrite Pregmap.gss. rewrite Pregmap.gso; auto with asmgen.
  intuition Simpl.
  }
  destruct chunk; monadInv H.
  - (* Mint8signed *)
    assert (exists v1, Mem.loadv Mint8unsigned m a = Some v1 /\ v = Val.sign_ext 8 v1).
    {
    destruct a; simpl in *; try discriminate.
    rewrite Mem.load_int8_signed_unsigned in H1.
    destruct (Mem.load Mint8unsigned m b (Ptrofs.unsigned i)); simpl in H1; inv H1.
    exists v0; auto.
    }
    destruct H as [v1 [LD' SG]]. clear H1.
    exploit BASE; eauto; erewrite ireg_of_eq by eauto; auto.
    intros. apply select_mem_access_load_correct; auto.
    intros [rs1 [A [B C]]].
    econstructor; split.
    eapply exec_straight_trans. eexact A. apply exec_straight_one. simpl; eauto. auto.
    split. Simpl. congruence. intros. Simpl.
  - (* Mint8unsigned *)
    eapply BASE; eauto; erewrite ireg_of_eq by eauto; auto.
    intros. apply select_mem_access_load_correct; auto.
  - (* Mint16signed *)
    eapply BASE; eauto; erewrite ireg_of_eq by eauto; auto.
  - (* Mint16unsigned *)
    eapply BASE; eauto; erewrite ireg_of_eq by eauto; auto.
    intros. apply select_mem_access_load_correct; auto.
  - (* Mint32 *)
    eapply BASE; eauto; erewrite ireg_of_eq by eauto; auto.
    intros. apply select_mem_access_load_correct; auto.
  - (* Mfloat32 *)
    eapply BASE; eauto; erewrite ireg_of_eq by eauto; auto.
    intros. apply select_mem_access_load_correct; auto.
Qed.

(** Translation of stores *)

Lemma transl_store_correct:
  forall chunk addr args src k c (rs: regset) m a m',
  transl_store chunk addr args src k = OK c ->
  eval_addressing ge (rs#GPR1) addr (map rs (map preg_of args)) = Some a ->
  Mem.storev chunk m a (rs (preg_of src)) = Some m' ->
  exists rs',
  exec_straight ge fn c rs m k rs' m'
  /\ forall r, r <> PC -> r <> GPR0 -> preg_notin r (destroyed_by_store chunk addr) -> rs' r = rs r.
Proof.
  Local Transparent destroyed_by_store.
  intros.
  assert (LD: forall v, Val.lessdef a v -> v = a).
  { intros. inv H2; auto. discriminate H1. }
  assert (TEMP0: int_temp_for src = GPR11 \/ int_temp_for src = GPR12).
  unfold int_temp_for. destruct (mreg_eq src R12); auto.
  assert (TEMP1: int_temp_for src <> GPR0).
  destruct TEMP0; congruence.
  assert (TEMP2: IR (int_temp_for src) <> preg_of src).
  unfold int_temp_for. destruct (mreg_eq src R12).
  subst src; simpl; congruence.
  change (IR GPR12) with (preg_of R12). red; intros; elim n.
  eapply preg_of_injective; eauto.
  assert (BASE: forall mk1 mk2  chunk',
           transl_memory_access mk1 mk2 addr args (int_temp_for src) k = OK c ->
           Mem.storev chunk' m a (rs (preg_of src)) = Some m' ->
           (forall cst (r1: ireg) (rs1: regset),
             r1 <> GPR0 ->
             exec_instr ge fn (mk1 cst r1) rs1 m =
             store1 ge chunk' (preg_of src) cst r1 rs1 m) ->
           (forall (r1 r2: ireg) (rs1: regset),
             exec_instr ge fn (mk2 r1 r2) rs1 m =
             store2 chunk' (preg_of src) r1 r2 rs1 m) ->
           exists rs',
           exec_straight ge fn c rs m k rs' m'
           /\ forall r, r <> PC -> r <> GPR0 -> r <> GPR11 /\ r <> GPR12 -> rs' r = rs r).
  {
  intros. eapply transl_memory_access_correct; eauto.
  intros. econstructor; split. apply exec_straight_one.
  rewrite H4. unfold store1. apply LD in H7. simpl. rewrite H7. rewrite H8; auto with asmgen. rewrite H3. eauto. auto. auto.
  intros; Simpl. apply H8; auto. destruct TEMP0; destruct H11; congruence.
  intros. econstructor; split. apply exec_straight_one.
  rewrite H5. unfold store2. apply LD in H6. rewrite H6. rewrite H7; auto with asmgen. rewrite H3. eauto. auto.
  intros; Simpl. apply H7; auto. destruct TEMP0; destruct H10; congruence.
  }
  destruct chunk; monadInv H.
  - (* Mint8signed *)
    assert (Mem.storev Mint8unsigned m a (rs (preg_of src)) = Some m').
    rewrite <- H1. destruct a; simpl; auto. symmetry. apply Mem.store_signed_unsigned_8.
    clear H1. eapply BASE; eauto; erewrite ireg_of_eq by eauto; auto.
    intros. apply select_mem_access_store_correct; auto.
  - (* Mint8unsigned *)
    eapply BASE; eauto; erewrite ireg_of_eq by eauto; auto.
    intros. apply select_mem_access_store_correct; auto.
  - (* Mint16signed *)
    assert (Mem.storev Mint16unsigned m a (rs (preg_of src)) = Some m').
    rewrite <- H1. destruct a; simpl; auto. symmetry. apply Mem.store_signed_unsigned_16.
    clear H1. eapply BASE; eauto; erewrite ireg_of_eq by eauto; auto.
    intros. apply select_mem_access_store_correct; auto.
  - (* Mint16unsigned *)
    eapply BASE; eauto; erewrite ireg_of_eq by eauto; auto.
    intros. apply select_mem_access_store_correct; auto.
  - (* Mint32 *)
    eapply BASE; eauto; erewrite ireg_of_eq by eauto; auto.
    intros. apply select_mem_access_store_correct; auto.
  - (* Mfloat32 *)
    eapply BASE; eauto; erewrite ireg_of_eq by eauto; auto.
    intros. apply select_mem_access_store_correct; auto.
Qed.

(** Translation of function epilogues *)

Lemma transl_epilogue_correct:
  forall ge0 f m stk soff cs m' ms rs k tm,
  load_stack m (Vptr stk soff) Tptr f.(fn_link_ofs) = Some (parent_sp cs) ->
  load_stack m (Vptr stk soff) Tptr f.(fn_retaddr_ofs) = Some (parent_ra cs) ->
  Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
  agree ms (Vptr stk soff) rs ->
  (is_leaf_function f = true -> rs#LR = parent_ra cs) ->
  Mem.extends m tm ->
  match_stack ge0 cs ->
  exists rs', exists tm',
     exec_straight ge fn (transl_epilogue f k) rs tm k rs' tm'
  /\ agree ms (parent_sp cs) rs'
  /\ Mem.extends m' tm'
  /\ rs'#LR = parent_ra cs
  /\ rs'#SP = parent_sp cs
  /\ (forall r, r <> PC -> r <> LR -> r <> SP -> r <> GPR0 -> rs'#r = rs#r).
Proof.
  intros until tm; intros LP LRA FREE AG LEAF MEXT MCS.
  exploit Mem.loadv_extends. eauto. eexact LP. auto. simpl. intros (parent' & LP' & LDP').
  exploit Mem.loadv_extends. eauto. eexact LRA. auto. simpl. intros (ra' & LRA' & LDRA').
  exploit lessdef_parent_sp; eauto. intros EQ; subst parent'; clear LDP'.
  exploit lessdef_parent_ra; eauto. intros EQ; subst ra'; clear LDRA'.
  exploit Mem.free_parallel_extends; eauto. intros (tm' & FREE' & MEXT').
  unfold transl_epilogue. destruct (is_leaf_function f).
- (* leaf function *)
  econstructor; exists tm'.
  split. apply exec_straight_one. simpl. rewrite <- (sp_val _ _ _ AG). simpl. 
  rewrite LP'. rewrite FREE'. reflexivity. reflexivity.
  split. apply agree_nextinstr. eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.
  split. auto.
  split. Simpl. 
  split. Simpl.
  intros; Simpl.
- (* regular function *)
  set (rs1 := nextinstr (rs#GPR0 <- (parent_ra cs))).
  set (rs2 := nextinstr (rs1#LR  <- (parent_ra cs))).
  set (rs3 := nextinstr (rs2#GPR1 <- (parent_sp cs))).
  exists rs3; exists tm'.
  split. apply exec_straight_three with rs1 tm rs2 tm; auto.
    simpl. unfold load1. rewrite gpr_or_zero_not_zero by congruence. 
    unfold const_low. rewrite <- (sp_val _ _ _ AG).
    erewrite loadv_offset_ptr by eexact LRA'. reflexivity.
    simpl. change (rs2#GPR1) with (rs#GPR1). rewrite <- (sp_val _ _ _ AG). simpl. 
    rewrite LP'. rewrite FREE'. reflexivity.
  split. unfold rs3. apply agree_nextinstr. apply agree_change_sp with (Vptr stk soff). 
    apply agree_nextinstr. apply agree_set_other; auto. 
    apply agree_nextinstr. apply agree_set_other; auto. 
    eapply parent_sp_def; eauto.
  split. auto.
  split. reflexivity.
  split. reflexivity.
  intros. unfold rs3, rs2, rs1; Simpl. 
Qed.

End CONSTRUCTORS.
