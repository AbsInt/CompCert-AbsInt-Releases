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
Require Import Separation.
Require Import Events.

Local Transparent Archi.ptr64.
Local Open Scope sep_scope.

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

Lemma get_uconst2_sound:
  forall n x, get_uconst2 n = Some x ->
    u_amount 2 x = n.
Proof.
  intros. unfold get_uconst2 in H.
  destruct (Int.ltu n (Int.repr 4)) eqn:?; inv H.
  apply Int.zero_ext_range_eq; auto.
  change Int.zwordsize with 32. simpl. lia.
Qed.

Lemma get_uconst4_sound:
  forall n x, get_uconst4 n = Some x ->
    u_amount 4 x = n.
Proof.
  intros. unfold get_uconst4 in H.
  destruct (Int.ltu n (Int.repr 16)) eqn:?; inv H.
  apply Int.zero_ext_range_eq; auto.
  change Int.zwordsize with 32. simpl. lia.
Qed.

Lemma get_uconst9_sound:
  forall n x, get_uconst9 n = Some x ->
    u_amount 9 x = n.
Proof.
  intros. unfold get_uconst9 in H.
  destruct (Int.ltu n (Int.repr (two_p 9))) eqn:?; inv H.
  apply Int.zero_ext_range_eq; auto.
  change Int.zwordsize with 32. simpl. lia.
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

(* Two lemmas for address registers. The respective versions for ireg & freg are in 
   the Asmgen module of each architecture, but the areg version is only needed for TriCore. *)
Lemma areg_of_eq:
  forall r r', areg_of r = OK r' -> preg_of r = r'.
Proof.
  unfold areg_of; intros. destruct (preg_of r); inv H; auto.
Qed.

Lemma preg_of_not_RA:
  forall r, AREG RA <> preg_of r.
Proof.
  intros. unfold preg_of; destruct r; cbn; congruence.
Qed.

Lemma preg_of_not_RA':
  forall r r', preg_of r = r' -> AREG RA <> r'.
Proof.
  unfold preg_of. intros. destruct r; cbn; congruence.
Qed.

Remark preg_of_not_P12:
  forall r, negb (mreg_eq r P12) = true ->
  AREG A12 <> preg_of r.
Proof.
  intros. change (AREG A12) with (preg_of P12). red; intros.
  exploit preg_of_injective; eauto. intros; subst r; discriminate.
Qed.

Remark preg_of_not_PCXI:
  forall r, PCXI <> preg_of r.
Proof.
  intros. red; intros. destruct r; cbn in H; congruence.
Qed.

Remark preg_of_not_PSW:
  forall r, PSW_C <> preg_of r.
Proof.
  intros. red; intros. destruct r; cbn in H; congruence.
Qed.

Lemma ireg_of_not_TMP:
  forall m r, ireg_of m = OK r -> DREG r <> TMP.
Proof.
  intros. erewrite <- ireg_of_eq; eauto with asmgen.
Qed.
Global Hint Resolve ireg_of_not_TMP: asmgen.

Lemma ireg_of_not_TMP':
  forall m r, ireg_of m = OK r -> r <> TMP.
Proof.
  intros. apply ireg_of_not_TMP in H. congruence.
Qed.
Global Hint Resolve ireg_of_not_TMP': asmgen.

Lemma ireg_of_not_TMP'':
  forall m r, ireg_of m = OK r -> DREG TMP <> DREG r.
Proof.
  intros. destruct m; inv H; congruence.
Qed.
Global Hint Resolve ireg_of_not_TMP'': asmgen.

Lemma ireg_of_not_TMP''':
  forall m r, ireg_of m = OK r -> TMP <> r.
Proof.
  intros. destruct m; inv H; congruence.
Qed.
Global Hint Resolve ireg_of_not_TMP''': asmgen.

Lemma ireg_rpair_of_not_TMP:
  forall m r, ireg_of_rpair m = OK r -> DREG r <> TMP.
Proof.
  intros. destruct m; simpl in *; auto with asmgen.
  unfold ireg_of in H. destruct r0; inv H; try congruence.
Qed.
Global Hint Resolve ireg_rpair_of_not_TMP: asmgen.

Lemma ireg_rpair_of_not_TMP':
  forall m r, ireg_of_rpair m = OK r -> r <> TMP.
Proof.
  intros. generalize (ireg_rpair_of_not_TMP _ _ H). congruence.
Qed.
Global Hint Resolve ireg_rpair_of_not_TMP': asmgen.

Lemma data_preg_not_TMP:
  forall r, data_preg r = true -> r <> TMP.
Proof.
  unfold data_preg. intros. destruct r; try congruence.
  destruct r; congruence.
Qed.
Global Hint Resolve data_preg_not_TMP: asmgen.

Lemma data_preg_not_TMPA:
  forall r, data_preg r = true -> r <> TMPA.
Proof.
  unfold data_preg; intros. destruct r; try congruence.
  destruct r; congruence.
Qed.

Lemma areg_of_not_TMPA:
  forall m r, areg_of m = OK r -> AREG r <> TMPA.
Proof.
  intros. erewrite <- areg_of_eq; eauto with asmgen.
Qed.

Lemma areg_of_not_TMPA':
  forall m r, areg_of m = OK r -> r <> TMPA.
Proof.
  intros. apply areg_of_not_TMPA in H. congruence.
Qed.

Lemma areg_of_not_SP:
  forall r r', areg_of r = OK r' -> r' <> SP.
Proof.
  intros.
  apply areg_of_eq in H.
  Set Printing Coercions.
  intros eq. subst.
  now apply preg_of_not_SP in H.
  Unset Printing Coercions.
Qed.

Lemma areg_of_not_RA:
  forall r r', areg_of r = OK r' -> r' <> RA.
Proof.
  intros.
  apply areg_of_eq in H.
  Set Printing Coercions.
  intros eq. subst.
  generalize (preg_of_not_RA r). congruence.
  Unset Printing Coercions.
Qed.

Lemma areg_of_not_RA':
  forall r r', areg_of r = OK r' -> AREG RA <> AREG r'.
Proof.
  intros. red; intros. destruct r; cbn in H; congruence.
Qed.

Lemma areg_of_not_SP':
  forall r r', areg_of r = OK r' -> AREG r' <> SP.
Proof.
  intros. red; intros. destruct r; cbn in H; congruence.
Qed.

Lemma data_preg_not_PC:
  forall r, data_preg r = true -> r <> PC.
Proof.
  unfold data_preg. intros. destruct r; congruence.
Qed.

Lemma preg_of_dreg_not_TMP pr mr: preg_of mr = pr -> pr <> TMP.
Proof.
  destruct mr; cbn; congruence.
Qed.

Lemma preg_of_areg_not_TMPA pr mr: preg_of mr = pr -> pr <> TMPA.
Proof.
  destruct mr; cbn; congruence.
Qed.

Lemma data_preg_not_RA:
  forall r, data_preg r = true -> r <> RA.
Proof.
  unfold data_preg. intros. destruct r; try congruence.
  destruct r; congruence.
Qed.

Lemma data_preg_not_PCXI:
  forall r, data_preg r = true -> r <> PCXI.
Proof.
  unfold data_preg. intros. destruct r; congruence.
Qed.

Global Hint Resolve ireg_of_not_TMP ireg_of_not_TMP' data_preg_not_TMP  areg_of_not_TMPA areg_of_not_TMPA' data_preg_not_TMPA
  data_preg_not_PC preg_of_dreg_not_TMP preg_of_areg_not_TMPA areg_of_not_SP areg_of_not_RA data_preg_not_RA data_preg_not_PCXI
  areg_of_not_RA' areg_of_not_SP' preg_of_not_RA preg_of_not_RA' preg_of_not_P12 preg_of_not_PCXI : asmgen.

Remark valid_index_reg_A10:
  forall rs m,
  valid_index_reg A10 rs m = true.
Proof.
  reflexivity.
Qed.

Hint Resolve valid_index_reg_A10 : asmgen.

Lemma ra_injects_flat:
  forall ge j s (rs: regset) m, 
  match_stack ge s ->
  m |= globalenv_inject ge j ->
  Val.inject j (parent_ra s) (rs RA) ->
  rs RA = parent_ra s.
Proof.
  intros.
  destruct s as [|[?????] s'].
  - simpl. inv H1. reflexivity.
  - simpl. simpl in H1. inv H. inv H9. inv H1.
    destruct H0 as (bound&_&[]).
    apply FUNCTIONS in H. apply DOMAIN in H. rewrite H in H9.
    inv H9. rewrite Ptrofs.add_zero. reflexivity.
Qed.

(** * Agreement between Mach registers and processor registers *)

(** Adapted for TriCore to use [Val.inject] instead of [Val.lessdef] in order to
    be able to use separation logic lemmas during [Asmgenproof]. *)

Record agree_inj (j : meminj) (ms : Mach.regset) (sp : val) (rs : regset) : Prop :=
  mkagree_inj {
    agree_inj_sp : Val.inject j sp (rs A10);
    agree_inj_sp_def : sp <> Vundef;
    agree_inj_mregs : forall r, Val.inject j (ms r) (rs (preg_of r))
  }.

Lemma preg_val2:
  forall j ms sp rs r,
  agree_inj j ms sp rs ->
  Val.inject j (ms r) rs#(preg_of r).
Proof.
  intros. destruct H; auto.
Qed.

Lemma preg_vals2:
  forall j ms sp rs,
  agree_inj j ms sp rs ->
  forall l, Val.inject_list j (map ms l) (map rs (map preg_of l)).
Proof.
  induction l; simpl. constructor. constructor. eapply preg_val2; eauto. auto.
Qed.

Lemma preg_rpair_val2:
  forall j ms sp rs p,
  agree_inj j ms sp rs ->
  Val.inject j (Mach.get_pair p ms) (get_pair (preg_rpair_of p) rs).
Proof.
  intros. destruct H. destruct p; simpl; auto using Val.combine_inject.
Qed.

Lemma preg_rpair_vals2:
  forall j ms sp rs,
  agree_inj j ms sp rs ->
  forall l, Val.inject_list j (Mach.get_pairs l ms) (get_pairs (map preg_rpair_of l) rs).
Proof.
  induction l; simpl. constructor. constructor. eapply preg_rpair_val2; eauto. auto.
Qed.

Lemma ireg_val:
  forall j ms sp rs r r',
  agree_inj j ms sp rs ->
  ireg_of r = OK r' ->
  Val.inject j (ms r) rs#r'.
Proof.
  intros. rewrite <- (ireg_of_eq _ _ H0). eapply preg_val2; eauto.
Qed.

Lemma areg_val:
  forall j ms sp rs r r',
  agree_inj j ms sp rs ->
  areg_of r = OK r' ->
  Val.inject j (ms r) rs#r'.
Proof.
  intros. rewrite <- (areg_of_eq _ _ H0). eapply preg_val2; eauto.
Qed.

Lemma agree_inj_exten:
  forall j ms sp rs rs',
  agree_inj j ms sp rs ->
  (forall r, data_preg r = true -> rs'#r = rs#r) ->
  agree_inj j ms sp rs'.
Proof.
  intros. destruct H. split; auto.
  rewrite H0; auto.
  intros. rewrite H0; auto. apply preg_of_data.
Qed.

(** Preservation of register agreement under various assignments. *)

Lemma agree_inj_set_mreg:
  forall j ms sp rs r v rs',
  agree_inj j ms sp rs ->
  Val.inject j v (rs'#(preg_of r)) ->
  (forall r', data_preg r' = true -> r' <> preg_of r -> rs'#r' = rs#r') ->
  agree_inj j (Regmap.set r v ms) sp rs'.
Proof.
  intros. destruct H. split; auto.
  rewrite H1; auto. apply not_eq_sym. apply preg_of_not_SP.
  intros. unfold Regmap.set. destruct (RegEq.eq r0 r). congruence.
  rewrite H1. auto. apply preg_of_data.
  red; intros; elim n. eapply preg_of_injective; eauto.
Qed.

Corollary agree_inj_set_mreg_parallel:
  forall j ms sp rs r v v',
  agree_inj j ms sp rs ->
  Val.inject j v v' ->
  agree_inj j (Regmap.set r v ms) sp (Pregmap.set (preg_of r) v' rs).
Proof.
  intros. eapply agree_inj_set_mreg; eauto. rewrite Pregmap.gss; auto. intros; apply Pregmap.gso; auto.
Qed.

Lemma agree_inj_set_other:
  forall j ms sp rs r v,
  agree_inj j ms sp rs ->
  data_preg r = false ->
  agree_inj j ms sp (rs#r <- v).
Proof.
  intros. apply agree_inj_exten with rs. auto.
  intros. apply Pregmap.gso. congruence.
Qed.

Lemma agree_inj_nextinstr:
  forall j ms sp rs,
  agree_inj j ms sp rs -> agree_inj j ms sp (nextinstr rs).
Proof.
  intros. unfold nextinstr. apply agree_inj_set_other. auto. auto.
Qed.

Lemma agree_inj_set_pair:
  forall j sp p v v' ms rs,
  agree_inj j ms sp rs ->
  Val.inject j v v' ->
  agree_inj j (Mach.set_pair p v ms) sp (set_pair (map_rpair preg_of p) v' rs).
Proof.
  intros. destruct p; simpl.
- apply agree_inj_set_mreg_parallel; auto.
- apply agree_inj_set_mreg_parallel. apply agree_inj_set_mreg_parallel; auto.
  apply Val.hiword_inject; auto. apply Val.loword_inject; auto.
Qed.

Lemma agree_inj_undef_regs:
  forall j ms sp rl rs rs',
  agree_inj j ms sp rs ->
  (forall r', data_preg r' = true -> preg_notin r' rl -> rs'#r' = rs#r') ->
  agree_inj j (Mach.undef_regs rl ms) sp rs'.
Proof.
  intros. destruct H. split; auto.
  rewrite H0; auto.
  rewrite preg_notin_charact. intros. apply not_eq_sym. apply preg_of_not_SP.
  intros. destruct (In_dec mreg_eq r rl).
  rewrite Mach.undef_regs_same; auto.
  rewrite Mach.undef_regs_other; auto. rewrite H0; auto.
  apply preg_of_data.
  rewrite preg_notin_charact. intros; red; intros. elim n.
  exploit preg_of_injective; eauto. congruence.
Qed.

Lemma agree_inj_set_undef_mreg:
  forall j ms sp rs r v rl rs',
  agree_inj j ms sp rs ->
  Val.inject j v (rs'#(preg_of r)) ->
  (forall r', data_preg r' = true -> r' <> preg_of r -> preg_notin r' rl -> rs'#r' = rs#r') ->
  agree_inj j (Regmap.set r v (Mach.undef_regs rl ms)) sp rs'.
Proof.
  intros. apply agree_inj_set_mreg with (rs'#(preg_of r) <- (rs#(preg_of r))); auto.
  apply agree_inj_undef_regs with rs; auto.
  intros. unfold Pregmap.set. destruct (PregEq.eq r' (preg_of r)).
  congruence. auto.
  intros. rewrite Pregmap.gso; auto.
Qed.

Definition inject' j (v: val) (p: rpair preg) (rs: regset) :=
  match p with
  | One r => Val.inject j v (rs r)
  | Two rhi rlo => Val.inject j (Val.hiword v) (rs rhi) /\ Val.inject j (Val.loword v) (rs rlo)
  end.

Lemma inject_lessdef'_trans:
  forall j v v' p rs,
  Val.inject j v v' -> lessdef' v' p rs -> inject' j v p rs.
Proof.
  intros.
  destruct p; unfold lessdef' in H0; unfold inject'; intros.
  eapply Mem.val_inject_lessdef_compose; eauto.
  destruct H0. split.
  eapply Mem.val_inject_lessdef_compose; [eapply Val.hiword_inject|]; eauto.
  eapply Mem.val_inject_lessdef_compose; [eapply Val.loword_inject|]; eauto.
Qed.

Lemma agree_inj_set_undef_mreg_rpair:
  forall j ms sp rs p v rl rs',
  agree_inj j ms sp rs ->
  inject' j v (preg_rpair_of p) rs' ->
  (forall r', data_preg r' = true -> forall_rpair (fun x => r' <> preg_of x) p -> preg_notin r' rl -> rs'#r' = rs#r') ->
  agree_inj j (Mach.set_pair p v (Mach.undef_regs rl ms)) sp rs'.
Proof.
  destruct p; intros.
  - eapply agree_inj_set_undef_mreg; eauto.
  - destruct (mreg_eq rhi rlo).
    + eapply agree_inj_set_mreg; eauto. eapply agree_inj_set_undef_mreg; eauto. apply H0. intros. apply H1; eauto.
      simpl. rewrite <- e. split; assumption. simpl in *. apply H0.
    + eapply agree_inj_set_mreg with (rs' # (preg_of rlo) <- (rs#(preg_of rlo))); eauto. eapply agree_inj_set_undef_mreg; eauto.
      * rewrite Pregmap.gso; auto with asmgen. apply H0. intro. apply preg_of_injective in H2. contradiction.
      * intros. destruct (preg_eq r' (preg_of rlo)).
        rewrite <- e. rewrite Pregmap.gss. reflexivity.
        simpl in H1. rewrite Pregmap.gso; auto with asmgen.
      * apply H0.
      * intros. rewrite Pregmap.gso; auto with asmgen.
Qed.

Lemma agree_inj_inject_incr:
  forall j j' ms sp rs,
  inject_incr j j' ->
  agree_inj j ms sp rs ->
  agree_inj j' ms sp rs.
Proof.
  intros. destruct H0.
  econstructor; eauto.
Qed.

(** Connection between Mach and Asm calling conventions for external
    functions. *)

Lemma extcall_arg_match2:
  forall j ms sp rs m m' l v,
  agree_inj j ms sp rs ->
  Mem.inject j m m' ->
  Mach.extcall_arg ms m sp l v ->
  exists v', Asm.extcall_arg rs m' l v' /\ Val.inject j v v'.
Proof.
  intros. inv H1.
  exists (rs#(preg_of r)); split. constructor. eapply preg_val2; eauto.
  unfold load_stack in H2.
  exploit Mem.loadv_inject; eauto.
  eapply Val.offset_ptr_inject. apply H.
  intros [v' [A B]].
  exists v'; split; auto.
  econstructor. eauto. assumption.
Qed.

Lemma extcall_arg_pair_match2:
  forall j ms sp rs m m' p v,
  agree_inj j ms sp rs ->
  Mem.inject j m m' ->
  Mach.extcall_arg_pair ms m sp p v ->
  exists v', Asm.extcall_arg_pair rs m' p v' /\ Val.inject j v v'.
Proof.
  intros. inv H1.
- exploit extcall_arg_match2; eauto. intros (v' & A & B). exists v'; split; auto. constructor; auto.
- exploit extcall_arg_match2. eauto. eauto. eexact H2. intros (v1 & A1 & B1).
  exploit extcall_arg_match2. eauto. eauto. eexact H3. intros (v2 & A2 & B2).
  exists (Val.combine v1 v2); split. constructor; auto. apply Val.combine_inject; auto.
Qed.

Lemma extcall_args_match2:
  forall j ms sp rs m m',
  agree_inj j ms sp rs -> Mem.inject j m m' ->
  forall ll vl,
  list_forall2 (Mach.extcall_arg_pair ms m sp) ll vl ->
  exists vl', list_forall2 (Asm.extcall_arg_pair rs m') ll vl' /\ Val.inject_list j vl vl'.
Proof.
  induction 3; intros.
  exists (@nil val); split. constructor. constructor.
  exploit extcall_arg_pair_match2; eauto. intros [v1' [A B]].
  destruct IHlist_forall2 as [vl' [C D]].
  exists (v1' :: vl'); split; constructor; auto.
Qed.

Lemma extcall_arguments_match2:
  forall j ms m m' sp rs sg args,
  agree_inj j ms sp rs -> Mem.inject j m m' ->
  Mach.extcall_arguments ms m sp sg args ->
  exists args', Asm.extcall_arguments rs m' sg args' /\ Val.inject_list j args args'.
Proof.
  unfold Mach.extcall_arguments, Asm.extcall_arguments; intros.
  eapply extcall_args_match2; eauto.
Qed.

(** Translation of arguments and results to builtins. *)

Lemma builtin_args_match2:
  forall (F V: Type) (ge: Genv.t F V) j ms sp rs m m', 
  agree_inj j ms sp rs ->
  Mem.inject j m m' ->
  meminj_preserves_globals ge j ->
  forall al vl, eval_builtin_args ge (fun p => Mach.get_pair p ms) sp m al vl ->
  exists vl', eval_builtin_args ge (fun p => get_pair p rs) (rs#SP) m' (map (map_builtin_arg preg_rpair_of) al) vl'
           /\ Val.inject_list j vl vl'.
Proof.
  induction 4; intros; simpl.
  exists (@nil val); split; constructor.
  exploit (@eval_builtin_arg_inject _ _ _ ge (fun p => Mach.get_pair p ms) (fun p => get_pair (preg_rpair_of p) rs)).
    apply H.
    intros; eapply preg_rpair_val2; eauto.
    assumption. eassumption. eassumption.
  intros (v1' & A & B).
  destruct IHlist_forall2 as [vl' [C D]].
  exists (v1' :: vl'); split; constructor; auto. apply builtin_arg_match; auto.
Qed.

Lemma agree_inj_set_res:
  forall j res ms sp rs v v',
  agree_inj j ms sp rs ->
  Val.inject j v v' ->
  agree_inj j (Mach.set_res res v ms) sp (Asm.set_res_pair (map_builtin_res preg_rpair_of res) v' rs).
Proof.
  induction res; simpl; intros.
- eapply agree_inj_set_pair; eauto.
- auto.
- apply IHres2. apply IHres1. auto.
  apply Val.hiwordoflong_inject; auto.
  apply Val.lowordoflong_inject; auto.
Qed.

Lemma agree_inj_change_sp:
  forall j ms sp rs sp' sp'',
  agree_inj j ms sp rs -> sp' <> Vundef ->
  Val.inject j sp' sp'' ->
  agree_inj j ms sp' (rs#SP <- sp'').
Proof.
  intros. inv H. split; auto.
  intros. rewrite Pregmap.gso; auto with asmgen.
Qed.

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

Lemma loadimm_addr_correct:
 forall rd n k rs m,
  exists rs',
     exec_straight ge fn (loadimm_addr rd n k) rs m k rs' m
  /\ rs'#rd = Vint n
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  unfold loadimm_addr; intros.
  predSpec Int.eq Int.eq_spec (low_s n) Int.zero.
  - (* movh_ao *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl. f_equal.
    rewrite <- low_high_s, H, Int.add_zero.
    reflexivity.
 - (* movh_ao + lea_sc16 *)
    econstructor; split. eapply exec_straight_two; simpl; eauto.
    split; intuition Simpl. simpl. f_equal.
    rewrite <- low_high_s. reflexivity.
Qed.

(* Lemma to show that encoding selection is correct *)

Lemma select_encoding_instr_correct':
  forall (instr1: dreg -> dreg -> instruction)
    (instr2: dreg -> dreg -> dreg -> instruction)
    (sem: val -> val -> val)
    commut rd r1 r2 k k' rs m,
  (forall v1 v2, commut = true -> sem v1 v2 = sem v2 v1) ->
  (forall rd r1 rs m,
    exec_instr ge fn (instr1 rd r1) rs m =
    Next (nextinstr (rs#rd <- (sem rs#rd rs#r1))) m) ->
  (forall rd r1 r2 rs m,
    exec_instr ge fn (instr2 rd r1 r2) rs m =
    Next (nextinstr (rs#rd <- (sem rs#r1 rs#r2))) m) ->
  exists rs',
    exec_straight ge fn (select_encoding_instr instr1 instr2 commut rd r1 r2 k ++ k') rs m (k++k') rs' m
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
  - rewrite e. econstructor; split.
    + eapply exec_straight_one; simpl; eauto.
    + split; intuition Simpl.
  - destruct commut, (dreg_eq rd r2); eauto.
    + simpl. econstructor; split.
      * apply exec_straight_one; simpl; eauto.
      * rewrite e, H; eauto. split; intuition Simpl.
    + simpl. eexists; split.
      * apply exec_straight_one; simpl; eauto.
      * split; intuition Simpl.
    + simpl. eexists; split.
      * apply exec_straight_one; simpl; eauto.
      * rewrite e. split; intuition Simpl.
    + simpl. eexists; split.
      * apply exec_straight_one; simpl; eauto.
      * split; intuition Simpl.
Qed.

        
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
  intros. exploit (select_encoding_instr_correct' instr1 instr2 sem commut rd r1 r2 k nil); eauto.
  intros (rs' & A & B & C). exists rs'. split; try eauto.
  repeat rewrite app_nil_r in A. exact A.
Qed.

Lemma select_encoding_instr_correct_aa:
  forall (instr1: areg -> areg -> instruction)
    (instr2: areg -> areg -> areg -> instruction)
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
    exec_straight ge fn (select_encoding_instr_aa instr1 instr2 commut rd r1 r2 k) rs m k rs' m
  /\ rs'#rd = sem rs#r1 rs#r2
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  intros. unfold select_encoding_instr_aa.
  assert (BASE: exists rs',
           exec_straight ge fn (instr2 rd r1 r2 :: k) rs m k rs' m
           /\ rs'#rd = sem (rs r1) (rs r2)
           /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r).
  { econstructor. split. apply exec_straight_one. apply H1. Simpl. split; intuition Simpl. }
  destruct (areg_eq rd r1).
  rewrite e. econstructor; split. eapply exec_straight_one; simpl; eauto. split; intuition Simpl.
  destruct commut, (areg_eq rd r2); eauto.
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

Lemma add_aa_correct:
  forall rd r1 r2 k rs m,
  exists rs',
  exec_straight ge fn (add_aa rd r1 r2 k) rs m k rs' m
  /\ rs'#rd = Val.add (rs#r1) (rs#r2)
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  intros. unfold add. apply select_encoding_instr_correct_aa; intros; try reflexivity.
  apply Val.add_commut.
Qed.

Lemma add_d_correct: forall (rd r1 : dreg) (r2: areg) (k : code) (rs : regset) (m : mem),
 rd <> TMP -> exists rs' : regset,
  exec_straight ge fn (add_d rd r1 r2 k) rs m k rs' m /\
  rs' rd = Val.add (rs r1) (rs r2) /\ (forall r : preg, r <> TMP -> r <> PC -> r <> rd -> rs' r = rs r).
Proof.
  intros. unfold add_d.
  destruct (dreg_eq rd r1).
  - eexists; split.
    + eapply exec_straight_two; reflexivity.
    + cbn. split.
      * Simpl.
      * intros. Simpl. 
  - eexists; split.
    + eapply exec_straight_two; reflexivity.
    + split; intros; Simpl. apply Val.add_commut.
Qed.

Lemma sub_correct':
  forall rd r1 r2 k k' rs m,
  exists rs',
  exec_straight ge fn ((sub rd r1 r2 k) ++ k') rs m (k++k') rs' m
  /\ rs'#rd = Val.sub (rs#r1) (rs#r2)
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  intros. unfold sub. apply select_encoding_instr_correct'; intros; try reflexivity. congruence.
Qed.

Lemma sub_correct:
  forall rd r1 r2 k rs m,
  exists rs',
  exec_straight ge fn ((sub rd r1 r2 k)) rs m (k) rs' m
  /\ rs'#rd = Val.sub (rs#r1) (rs#r2)
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  intros. exploit (sub_correct' rd r1 r2 k nil).
   repeat rewrite app_nil_r. eauto.
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
  exists rs',
    exec_straight ge fn (addimm rd r n k) rs m k rs' m
  /\ rs'#rd = Val.add (rs#r) (Vint n)
  /\ forall r': preg, r' <> PC -> r' <> TMP -> r' <> rd -> rs'#r' = rs#r'.
Proof.
  intros. unfold addimm, addimm_gen.
  destruct (dreg_eq rd r && is_in_signed_range 4 n) eqn:cond;
    [|clear cond; predSpec Int.eq Int.eq_spec (high_s n) Int.zero;
    [|predSpec Int.eq Int.eq_spec (low_s n) Int.zero]].
  - (* add_sc4 *)
    rewrite andb_true_iff in cond. destruct cond as (reg_eq, range).
    replace rd with r  by (destruct rd, r; try inv reg_eq; try reflexivity).
    econstructor. split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl. rewrite Int.sign_ext_range_eq; auto.
  - (* addi *)
    econstructor.  split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl. do 2 f_equal. rewrite <- low_high_s.
    rewrite H, Int.add_zero_l. reflexivity.
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

Lemma addimm_addr_correct:
  forall (rd r : areg) n k rs m,
  exists rs',
    exec_straight ge fn (addimm_addr rd r n k) rs m k rs' m
  /\ rs'#rd = Val.add (rs#r) (Vint n)
  /\ forall r': preg, r' <> PC -> r' <> rd -> rs'#r' = rs#r'.
Proof.
  intros. unfold addimm_addr, addimm_gen.
  destruct (areg_eq rd r && is_in_signed_range 4 n) eqn:cond.
  - (* add_asc4 *) rewrite andb_true_iff in cond. destruct cond as (reg_eq, range).
    replace rd with r.
    econstructor. split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl. rewrite Int.sign_ext_range_eq; auto.
    destruct r, rd; try destruct a,a0; try inv reg_eq; try reflexivity.
  - predSpec Int.eq Int.eq_spec (high_s n) Int.zero; [|predSpec Int.eq Int.eq_spec (low_s n) Int.zero].
    + (* lea_sc16 *)
      econstructor.  split. apply exec_straight_one; simpl; eauto.
      split; intuition Simpl. do 2 f_equal. rewrite <- low_high_s.
      rewrite H, Int.add_zero_l. reflexivity.
    + (* addih_a *)
      econstructor.  split. apply exec_straight_one; simpl; eauto.
      split; intuition Simpl. do 2 f_equal. rewrite <- low_high_s.
      rewrite H0, Int.add_zero. reflexivity.
    + (* addih_a + lea_sc16 *)
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
    change Int.zwordsize with 32. lia.
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
    change Int.zwordsize with 32. lia.
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
       change Int.zwordsize with 32. lia.
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
    change Int.zwordsize with 32. lia.
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


Ltac Equalizer :=
  repeat match goal with
  | [H: ireg_of_rpair ?X = _ |- _] => destruct X; inv H
  end.


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
  | _ => Equalizer
  end).

Lemma switch_A_D_via_TMP_correct:
  forall ra rd k rs m,
  exists rs',
     exec_straight ge fn (switch_A_D_via_TMP ra rd k) rs m k rs' m
  /\ rs#ra = rs'#rd /\ (rd <> TMP ->  rs#rd = rs'#ra)
  /\ forall r, r <> PC -> r <> TMP -> r <> rd -> r <> ra -> rs'#r = rs#r.
Proof.
  intros. unfold switch_A_D_via_TMP.
  eexists; split.
  - eapply exec_straight_step.
    + cbn. reflexivity.
    + Simpl.
    + eapply exec_straight_two.
      * reflexivity.
      * reflexivity. 
      * Simpl.
      * Simpl.
  - repeat split; intros; Simpl.
Qed.

Lemma switch_A_D_via_TMPA_correct:
  forall ra rd k rs m,
  exists rs',
     exec_straight ge fn (switch_A_D_via_TMPA ra rd k) rs m k rs' m
  /\ (ra <> TMPA -> rs#ra = rs'#rd) /\ rs#rd = rs'#ra
  /\ forall r, r <> PC -> r <> TMPA -> r <> rd -> r <> ra -> rs'#r = rs#r.
Proof.
  intros. unfold switch_A_D_via_TMPA.
  eexists; split.
  - eapply exec_straight_step.
    + cbn. reflexivity.
    + Simpl.
    + eapply exec_straight_two.
      * reflexivity.
      * reflexivity. 
      * Simpl.
      * Simpl.
  - Simpl. repeat split; intros; Simpl.
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

Lemma transl_cond_addr_correct:
  forall cmp rd r1 r2 k rs m,
  exists rs',
     exec_straight ge fn (transl_cond_addr cmp rd r1 r2 :: k) rs m k rs' m
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
      change Int.zwordsize with 32. lia.
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
    rewrite H3. auto. change Int.zwordsize with 32. lia.
    unfold Int.ltu. rewrite H0. apply zlt_true.
    change (Int.unsigned (Int.repr (two_p 9))) with 512. lia.
    simpl. destruct (Int.eq n Int.zero && (Mem.valid_pointer m b (Ptrofs.unsigned i) || Mem.valid_pointer m b (Ptrofs.unsigned i - 1)));
    simpl; auto.
  - (* Cge *)
    destruct (get_uconst9 n) eqn:?; auto.
    econstructor; split. apply exec_straight_one; simpl; eauto.
    rewrite (get_uconst9_sound n u Heqo). split; intuition Simpl.
Qed.

Lemma transl_condimm_addr_correct:
  forall cmp rd r n k rs m c,
  transl_condimm_addr cmp rd r n = Some c ->
  exists rs',
     exec_straight ge fn (c :: k) rs m k rs' m
  /\  rs'#rd = Val.cmpu (Mem.valid_pointer m) cmp rs#r (Vint n) 
  /\ forall r, r <> PC -> r <> rd -> r <> TMP -> rs'#r = rs#r.
Proof.
  intros * H.
  unfold transl_condimm_addr in H.
  destruct (Int.eq n Int.zero) eqn:En; inv H.
  rewrite (Int.same_if_eq _ _ En).
  destruct cmp; inv H1; cbn.
  - (* Ceq *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl.
  - (* Cne *)
    econstructor; split. apply exec_straight_one; simpl; eauto.
    split; intuition Simpl.
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
  destruct cmp; try congruence;  inv H0; simpl; rewrite !Int.zero_ext_range_eq; try (change Int.zwordsize with 32; try lia); auto;
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

Lemma translate_bin_comp_correct cmp rd a1 a2 k c get_val rs m:
  translate_bin_comp rd a1 a2 cmp k = OK c ->
  (forall a1 a2 rs k, exists rs' : regset,
    exec_straight ge fn (transl_cond_int32s cmp rd a1 a2 :: k) rs m k rs' m
    /\ Val.lessdef (get_val (rs a1) (rs a2)) (rs' rd) 
    /\ (forall r : preg, r <> PC -> r <> rd -> rs' r = rs r)) ->
  exists rs',
    exec_straight ge fn c rs m k rs' m
    /\ Val.lessdef (get_val (rs (preg_of a1))  (rs (preg_of a2))) rs'#rd
    /\ forall r, r <> PC -> r <> TMP -> r <> TMPA -> r <> rd -> rs'#r = rs#r.
Proof.
  intros H P. unfold translate_bin_comp in H.
  destruct (preg_of a1) eqn:E1, (preg_of a2) eqn:E2; inv H.
  - exploit (P r r0). intros (rs' & A & B & C). exists rs'. eauto.
  - exploit (P r D0). intros (rs' & A & B & C). exists rs'. repeat split.
    + eapply exec_straight_step.
      * reflexivity.
      * Simpl.
      * exact A.        
    + cbn in B. rewrite Pregmap.gso in B.
      * assumption.
      * eauto with asmgen.
    + intros. rewrite (C r1); eauto. Simpl. 
  - exploit (P D0 r0); intros (rs' & A & B & C). exists rs'. repeat split.
    +  eapply exec_straight_step.
        -- reflexivity.
        -- Simpl.
        -- eassumption.
    + cbn in B. rewrite Pregmap.gso in B.
      * assumption.
      * eapply preg_of_dreg_not_TMP. eassumption.
    + intros. rewrite (C r1); eauto. Simpl.
  - destruct (areg_eq r r0); inv H1.
    + exploit (P D0 D0). intros (rs' & A & B & C). exists rs'. repeat split.
      * eapply exec_straight_step.
        -- reflexivity.
        -- Simpl.
        -- eassumption.
      * cbn in B. assumption.
      * intros. rewrite (C r); eauto. Simpl.
    + exploit switch_A_D_via_TMP_correct. intros (rs' & A & B & C & D).
      exploit (P (if dreg_eq rd D2 then D3 else D2) D0). intros (rs'' & A' & B' & C').
      exploit switch_A_D_via_TMPA_correct. intros (rs''' & A'' & B'' & C'' & D'').
      exists rs'''. repeat split.
      *  eapply exec_straight_trans.           
         -- exact A.
         -- eapply exec_straight_step.
            ++ reflexivity.
            ++ Simpl.
            ++ eapply exec_straight_trans; eassumption.
      * rewrite D''; eauto with asmgen.
        -- cbn in B'. rewrite <- (D r0); eauto with asmgen.
           rewrite Pregmap.gso in B'.
           ++ rewrite B. assumption.
           ++ destruct (dreg_eq rd D2); congruence.
        -- destruct (dreg_eq rd D2); congruence.          
      * intros. Set Printing Coercions.
        destruct (preg_eq r1 (AREG r)).
        -- subst. rewrite <- C''. rewrite C'; eauto with asmgen.
           ++ Simpl. rewrite Pregmap.gso.
              ** auto.
              ** destruct (dreg_eq rd D2); congruence.
           ++ destruct (dreg_eq rd D2); congruence.
        -- destruct (preg_eq r1 (DREG (if dreg_eq rd D2 then D3 else D2))).
           ++ subst. rewrite <- B''; auto with asmgen.
              ** rewrite C'; auto with asmgen. Simpl.
                 rewrite C; eauto with asmgen.
              ** intros eq. rewrite eq in E1. eapply preg_of_areg_not_TMPA in E1.
                 congruence.
           ++ rewrite D''; auto with asmgen.
              rewrite C'; auto with asmgen. Simpl.
              Unset Printing Coercions.
Qed.

Lemma translate_bin_compu_correct cmp rd a1 a2 k c get_val rs m:
  translate_bin_compu rd a1 a2 cmp k = OK c ->
  (forall a1 a2 rs k, exists rs' : regset,
  exec_straight ge fn (transl_cond_int32u cmp rd a1 a2 :: k) rs m k rs' m /\
  Val.lessdef (get_val (rs a1) (rs a2)) (rs' rd) /\
  (forall r : preg, r <> PC -> r <> rd -> rs' r = rs r)) ->
  (forall a1 a2 rs k, exists rs' : regset,
  exec_straight ge fn (transl_cond_addr cmp rd a1 a2 :: k) rs m k rs' m /\
  Val.lessdef (get_val (rs a1) (rs a2)) (rs' rd) /\
  (forall r : preg, r <> PC -> r <> rd -> rs' r = rs r)) ->
  exists rs',
    exec_straight ge fn c rs m k rs' m
    /\ Val.lessdef (get_val (rs (preg_of a1))  (rs (preg_of a2))) rs'#rd
  /\ forall r, r <> PC -> r <> TMP -> r <> TMPA -> r <> rd -> rs'#r = rs#r.
Proof.
  intros H P Pa. unfold translate_bin_compu in H.
  destruct (preg_of a1) eqn:E1, (preg_of a2) eqn:E2; inv H.
  - exploit (P r r0). intros (rs' & A & B & C). exists rs'. eauto.
  - exploit (P r D0). intros (rs' & A & B & C). exists rs'. repeat split.
    + eapply exec_straight_step.
      * reflexivity.
      * Simpl.
      * exact A.        
    + cbn in B. rewrite Pregmap.gso in B.
      * assumption.
      * eauto with asmgen.
    + intros. rewrite (C r1); eauto. Simpl. 
  - exploit (P D0 r0); intros (rs' & A & B & C). exists rs'. repeat split.
    +  eapply exec_straight_step.
        -- reflexivity.
        -- Simpl.
        -- eassumption.
    + cbn in B. rewrite Pregmap.gso in B.
      * assumption.
      * eapply preg_of_dreg_not_TMP. eassumption.
    + intros. rewrite (C r1); eauto. Simpl.
  - exploit (Pa r r0). intros (rs' & A & B & C). exists rs'. eauto.
Qed.

Lemma translate_imm_comp_correct cond rd a1 k c n get_val rs m:
  translate_imm_comp rd a1 cond n k = OK c ->
  (forall a1 rs k, a1 <> TMP -> exists rs' : regset,
  exec_straight ge fn (transl_condimm_int32s cond rd a1 n k) rs m k rs' m /\
  Val.lessdef (get_val (rs a1) (Vint n)) (rs' rd) /\
  (forall r : preg, r <> PC -> r <> rd -> r <> TMP -> rs' r = rs r)) ->
  exists rs',
    exec_straight ge fn c rs m k rs' m
    /\ Val.lessdef (get_val (rs (preg_of a1))  (Vint n)) rs'#rd
    /\ forall r, r <> PC -> r <> TMP -> r <> TMPA -> r <> rd -> rs'#r = rs#r.
Proof.
  unfold translate_imm_comp. intros H P. destruct (preg_of a1) eqn:E; inv H.
  - destruct (P r rs k) as (rs' & A & B & C).
    + apply preg_of_dreg_not_TMP in E; congruence.
    + exists rs'; eauto.
  - destruct (dreg_eq rd TMP); inv H1.
    + subst.
      exploit switch_A_D_via_TMP_correct. intros (rs' & A & B & C & D).
      exploit (P D2).
      * congruence.
      * intros (rs'' & A' & B' & C').
        exploit switch_A_D_via_TMPA_correct. intros (rs''' & A'' & B'' & C'' & D'').
        exists rs'''. repeat split.
        -- eapply exec_straight_trans.
            ++ eassumption.
            ++ eapply exec_straight_trans; eassumption.
        -- rewrite D''; eauto with asmgen. rewrite B. assumption.
        -- intros. Set Printing Coercions.
           destruct (preg_eq r0 (DREG D2)).
           ++ subst. rewrite <- B''.
              ** rewrite C'; eauto with asmgen. rewrite C; auto with asmgen.
              ** apply preg_of_areg_not_TMPA in E; congruence.                
           ++ destruct (preg_eq r0 (AREG r)).
              ** subst. rewrite <- C''. rewrite C'; auto with asmgen.
              ** rewrite D''; auto with asmgen. rewrite C'; auto with asmgen.
                 Unset Printing Coercions.
    + exploit (P rd); auto. intros (rs' & A & B & C).
      exists rs'. repeat split.
      * eapply exec_straight_step.
        -- reflexivity.
        -- Simpl.
        -- eassumption.
      * cbn in B. rewrite Pregmap.gss in B. assumption.        
      * intros. rewrite C; auto. Simpl.
Qed.          

Lemma translate_imm_compu_correct cmp rd a1 k c n get_val rs m:
  translate_imm_compu rd a1 cmp n k = OK c ->
  (forall a1 rs k, a1 <> TMP -> exists rs' : regset,
  exec_straight ge fn (transl_condimm_int32u cmp rd a1 n k) rs m k rs' m /\
  Val.lessdef (get_val (rs a1) (Vint n)) (rs' rd) /\
  (forall r : preg, r <> PC -> r <> rd -> r <> TMP -> rs' r = rs r)) ->
  (forall a1 rs k c,
   transl_condimm_addr cmp rd a1 n = Some c ->
    exists rs' : regset,
    exec_straight ge fn (c :: k) rs m k rs' m /\
    Val.lessdef (get_val (rs a1) (Vint n)) (rs' rd) /\
    (forall r : preg, r <> PC -> r <> rd -> r <> TMP -> rs' r = rs r)) ->
  exists rs',
    exec_straight ge fn c rs m k rs' m
    /\ Val.lessdef (get_val (rs (preg_of a1))  (Vint n)) rs'#rd
    /\ forall r, r <> PC -> r <> TMP -> r <> TMPA -> r <> rd -> rs'#r = rs#r.
Proof.
  unfold translate_imm_compu. intros H P Pza. destruct (preg_of a1) eqn:E; inv H.
  - destruct (P r rs k) as (rs' & A & B & C).
    + apply preg_of_dreg_not_TMP in E; congruence.
    + exists rs'; eauto.
  - destruct (transl_condimm_addr cmp rd r n) eqn:Hz; inv H1.
    {
      exploit (Pza r). eassumption. intros (rs' & A & B & C). exists rs'. eauto.
    }
    destruct (dreg_eq rd TMP); inv H0.
    + subst.
      exploit switch_A_D_via_TMP_correct. intros (rs' & A & B & C & D).
      exploit (P D2).
      * congruence.
      * intros (rs'' & A' & B' & C').
        exploit switch_A_D_via_TMPA_correct. intros (rs''' & A'' & B'' & C'' & D'').
        exists rs'''. repeat split.
        -- eapply exec_straight_trans.
            ++ eassumption.
            ++ eapply exec_straight_trans; eassumption.
        -- rewrite D''; eauto with asmgen. rewrite B. assumption.
        -- intros. Set Printing Coercions.
           destruct (preg_eq r0 (DREG D2)).
           ++ subst. rewrite <- B''.
              ** rewrite C'; eauto with asmgen. rewrite C; auto with asmgen.
              ** apply preg_of_areg_not_TMPA in E; congruence.                
           ++ destruct (preg_eq r0 (AREG r)).
              ** subst. rewrite <- C''. rewrite C'; auto with asmgen.
              ** rewrite D''; auto with asmgen. rewrite C'; auto with asmgen.
                 Unset Printing Coercions.
    + exploit (P rd); auto. intros (rs' & A & B & C).
      exists rs'. repeat split.
      * eapply exec_straight_step.
        -- reflexivity.
        -- Simpl.
        -- eassumption.
      * cbn in B. rewrite Pregmap.gss in B. assumption.        
      * intros. rewrite C; auto. Simpl.
Qed.          
  
Lemma transl_cond_op_correct:
  forall cond rd args k c rs m,
  transl_cond_op cond rd args k = OK c ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ Val.lessdef (Val.of_optbool (eval_condition cond (map rs (map preg_of args)) m)) rs'#rd
  /\ forall r, r <> PC -> r <> TMP -> r <> TMPA -> r <> rd -> rs'#r = rs#r.
Proof.
  assert (MKTOT: forall ob, Val.of_optbool ob = Val.maketotal (option_map Val.of_bool ob)).
  { destruct ob as [[]|]; reflexivity. }
  intros until m; intros TR.
  destruct cond; simpl in TR; ArgsInv.
  - (* cmp *)
    exploit translate_bin_comp_correct; eauto.
    + intros.
      exploit transl_cond_int32s_correct; intros (rs' & A & B & C).
      exists rs'. eauto. 
    + intros (rs' & A & B & C). exists rs'. eauto.
  - (* cmpu *)
     exploit translate_bin_compu_correct; eauto.
    + intros.
      exploit transl_cond_int32u_correct; intros (rs' & A & B & C).
      exists rs'. split.
      * eassumption.
      * split.
        --  rewrite B. eauto.
        -- eauto.
    + intros.
      exploit transl_cond_addr_correct; intros (rs' & A & B & C).
      exists rs'. split.
      * eassumption.
      * split.
        --  rewrite B. eauto.
        -- eauto.
    + intros (rs' & A & B & C). exists rs'. eauto.
  - (* cmpimm *)
    exploit translate_imm_comp_correct; eauto.
    + intros. exploit transl_condimm_int32s_correct; cycle 1.
      * intros (rs' & A & B & C). exists rs'; eauto.
      * assumption.
    + intros (rs' & A & B & C). exists rs'. eauto.
  - (* cmpuimm *)
    exploit translate_imm_compu_correct; eauto.
    + intros. exploit transl_condimm_int32u_correct; cycle 1.
      * intros (rs' & A & B & C). exists rs'; eauto.
      * assumption.
    + intros. exploit transl_condimm_addr_correct; [eassumption|].
      intros (rs' & A & B & C). exists rs'; split.
      eassumption.
      split; [|assumption].
      eapply Val.lessdef_same. symmetry. eassumption.
    + intros (rs' & A & B & C). exists rs'. eauto.
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

Lemma translate_bin_cbranch_correct r1 r2 cond transl_f lbl k c f (rs: regset) m:
  translate_bin_cbranch r1 r2 cond transl_f lbl k = OK c ->
 ( forall (r1 r2 : dreg) (lbl : label) 
  (rs : regset) (m : mem) (b : bool),
     f m (rs r1) (rs r2) = Some b ->
exec_instr ge fn (transl_f r1 r2 lbl) rs m =
  eval_branch fn lbl rs m (Some b))
 ->  f m (rs (preg_of r1)) (rs (preg_of r2)) = eval_condition cond ((rs (preg_of r1))::(rs (preg_of r2))::nil) m ->
   forall b, f m (rs (preg_of r1)) (rs (preg_of r2)) = Some b -> exists rs', exists insn,
     exec_straight_opt ge fn c rs m (insn :: k) rs' m
  /\ exec_instr ge fn insn rs' m = eval_branch fn lbl rs' m (Some b)
  /\ forall r, r <> PC -> r <> TMP -> r <> TMPA -> rs'#r = rs#r.
Proof.
  unfold translate_bin_cbranch; intros H P. destruct (preg_of r1) eqn:E1, (preg_of r2) eqn:E2; inv H.
  - intros. specialize (P r r0 lbl rs m b H0). do 2 eexists; split.
    + constructor.
    + intros. split; auto with asmgen.
  - intros. specialize (P r TMP lbl). do 2 eexists; split.
    + eapply exec_straight_opt_intro. eapply exec_straight_one.
      * reflexivity.
      * Simpl.
    + split.
      * apply P. Simpl.
      * intros. Simpl.
  - intros. do 2 eexists; split.
    + eapply exec_straight_opt_step_opt.
      * reflexivity.
      * Simpl.
      * constructor.
    + split.
      * apply P. Simpl.
      * intros. Simpl.
  - intros. destruct (areg_eq r r0); inv H1.
    + do 2 eexists. split.
      * eapply exec_straight_opt_step_opt.
        -- reflexivity.
        -- Simpl.
        -- constructor.          
      * split.
        -- apply P. Simpl.
        -- intros. Simpl.          
    + exploit transl_cond_op_correct; eauto. intros (rs' & A & B & C).
      eexists. exists (Pjne_sc4 D0 (mk_sconst4 Int.zero) lbl). split.
      * eapply exec_straight_opt_intro. eassumption.
      * split.
        -- cbn in B. rewrite E1 in *; rewrite E2 in *. rewrite <- H in B. unfold exec_instr.
           f_equal. 
           eapply Val.cmpu_bool_lessdef.
           ++ eauto.
           ++ eassumption.
           ++ apply Val.lessdef_refl.
           ++ rewrite H0. cbn. destruct b; cbn; f_equal.
        -- intros. rewrite C; auto with asmgen.
Qed.            

Lemma transl_cbranch_correct_1:
  forall cond args lbl k c m ms b sp rs j m',
  transl_cbranch cond args lbl k = OK c ->
  eval_condition cond (List.map ms args) m = Some b ->
  agree_inj j ms sp rs ->
  Mem.inject j m m' ->
  exists rs', exists insn,
     exec_straight_opt ge fn c rs m' (insn :: k) rs' m'
  /\ exec_instr ge fn insn rs' m' = eval_branch fn lbl rs' m' (Some b)
  /\ forall r, r <> PC -> r <> TMP -> r <> TMPA -> rs'#r = rs#r.
Proof.
  intros until m'; intros TRANSL EVAL AG MEXT.
  set (vl' := map rs (map preg_of args)).
  assert (EVAL': eval_condition cond vl' m' = Some b).
  { apply eval_condition_inject with j (map ms args) m; auto. eapply preg_vals2; eauto. }
  clear EVAL MEXT AG.
  destruct cond; simpl in TRANSL; ArgsInv.
  - (* branch signed int *)
    cbn in *. eapply translate_bin_cbranch_correct; eauto.
    + intros. cbn in EVAL'. pose proof transl_cbranch_int32s_correct as H'.
      apply H'. rewrite <- H.
      instantiate (1 := (fun m => Val.cmp_bool c0)). reflexivity.
    + reflexivity.
    + cbn. assumption. 
  - (* branch unsigned int *)
     cbn in *; eapply translate_bin_cbranch_correct; eauto.
     + intros. apply transl_cbranch_int32u_correct.
       rewrite <- H. instantiate (1 := (fun m => Val.cmpu_bool (Mem.valid_pointer m) c0)).
       reflexivity.
    + reflexivity.
    + assumption.
  - (* branch signed int with immediate *)
    destruct (preg_of m0) eqn:E; inv TRANSL.
    + cbn in *. rewrite E in *.
      exploit transl_cbranch_int32s_imm_correct; eauto with asmgen.
      apply preg_of_dreg_not_TMP in E.  congruence.
      intros  (rs' & inst & A & B & C); eauto with asmgen.
      exists rs', inst. eauto with asmgen.
    + exploit translate_imm_comp_correct; eauto with asmgen.
      intros. eapply transl_condimm_int32s_correct; eauto.
      intros (rs' &  A & B & C).
      exists rs'. eexists. split.
      constructor; eauto.
      split; eauto. simpl in EVAL'. rewrite E in *.
      simpl. unfold Val.cmp in B. rewrite EVAL' in B.
      destruct b; inv B; auto.
  - (* branch unsigned int with immediate *)
    destruct (preg_of m0) eqn:E; inv TRANSL.
    + cbn in *. rewrite E in *.
      exploit transl_cbranch_int32u_imm_correct; eauto with asmgen. apply preg_of_dreg_not_TMP in E. congruence.
      intros (rs' & inst & A & B & C).
      exists rs', inst; eauto with asmgen.
    + exploit translate_imm_compu_correct; eauto with asmgen.
      intros. eapply transl_condimm_int32u_correct; eauto.
      intros. exploit (transl_condimm_addr_correct c0 D0 a1 n). eassumption.
      intros (rs' & A & B & C).
      exists rs'; repeat split; eauto.
      eapply Val.lessdef_same. symmetry. eassumption.
      intros (rs' & A & B & C).
      exists rs'. econstructor. split. constructor. eexact A.
      split. simpl in EVAL'.
      unfold Val.cmpu in B. rewrite EVAL' in B. simpl in B. simpl exec_instr.
      f_equal. eapply Val.cmpu_bool_lessdef. eauto. eexact B. apply Val.lessdef_refl.
      destruct b; auto. intros. rewrite C; auto.
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
  forall cond args lbl k c m ms sp rs j m',
  transl_cbranch cond args lbl k = OK c ->
  eval_condition cond (List.map ms args) m = Some true ->
  agree_inj j ms sp rs ->
  Mem.inject j m m' ->
  exists rs', exists insn,
     exec_straight_opt ge fn c rs m' (insn :: k) rs' m'
  /\ exec_instr ge fn insn rs' m' = goto_label fn lbl rs' m'
  /\ forall r, r <> PC -> r <> TMP -> r <> TMPA -> rs'#r = rs#r.
Proof.
  intros. eapply transl_cbranch_correct_1 with (b := true); eauto.
Qed.

Lemma transl_cbranch_correct_false:
  forall cond args lbl k c m ms sp rs j m',
  transl_cbranch cond args lbl k = OK c ->
  eval_condition cond (List.map ms args) m = Some false ->
  agree_inj j ms sp rs ->
  Mem.inject j m m' ->
  exists rs',
     exec_straight ge fn c rs m' k rs' m'
  /\ forall r, r <> PC -> r <> TMP -> r <> TMPA -> rs'#r = rs#r.
Proof.
  intros. exploit transl_cbranch_correct_1; eauto. simpl.
  intros (rs' & insn & A & B & C).
  exists (nextinstr rs').
  split. eapply exec_straight_opt_right; eauto. apply exec_straight_one; auto.
  intros; Simpl.
Qed.


(* Translation of arithmetic operations *)

Ltac Splitter' :=
  match goal with
  | [H: iregs_of_rpair ?X = _ |- _] => destruct X; [unfold iregs_of_rpair in H; discriminate|];
                                         pose proof (iregs_of_rpair_eq' _ _ _ H) as [? ?];
                                         apply iregs_of_rpair_eq in H as [? ?]
  | [H: ireg_of_rpair ?X = _ |- _] => destruct X; inv H
  | [H: ireg_of _ = _ |- _ ] => rewrite (ireg_of_eq _ _ H) in *
  | [|-_ /\ _ ] => split
  | [H: _ /\ _ |- _] => destruct H
  | [H: (preg_of _) = _ |- _] => rewrite H in *
  | [H: forall_rpair _ (Two _ _) |- _] => destruct H
  | _ => simpl in *; try Simpl; auto with asmgen
  end.

Ltac Splitter :=
  repeat match goal with
  | [|- Val.lessdef _ _] => apply Val.lessdef_same
  | _ => Splitter'
  end.


Ltac SimplEval H :=
  match type of H with
  | Some _ = None _ => discriminate
  | Some _ = Some _ => inv H
  | ?a = Some ?b => let A := fresh in assert (A: Val.maketotal a = b) by (rewrite H; reflexivity)
end.

Ltac TranslOpSimpl :=
  econstructor; split;
  [ apply exec_straight_one; [simpl; eauto | reflexivity]
  | split; [ apply Val.lessdef_same; Simpl; fail
  | split; [ intros; Simpl; fail | Simpl; fail ] ] ].

Ltac TranslOpSplitter :=
  econstructor; split;
  [ apply exec_straight_one; [simpl; eauto | reflexivity ]
  | split; [|split]; [Splitter|intros; Splitter|Simpl] ].

Lemma ptrofs_of_int_neg_push i: Ptrofs.unsigned (Ptrofs.neg (Ptrofs.of_int i)) = Ptrofs.unsigned (Ptrofs.of_int (Int.neg i)).
Proof.
  erewrite (Ptrofs.agree32_of_int_eq _ (Int.neg i)).
  - reflexivity.
  - apply Ptrofs.agree32_neg; auto. apply Ptrofs.agree32_of_int; auto.
Qed.

Lemma sub_same_lessdef_zero v: Val.lessdef (Val.sub v v) Vzero.
Proof.
  destruct v; cbn; try constructor.
  - rewrite (Int.sub_idem i). constructor.
  - rewrite Ptrofs.sub_idem.
    unfold eq_block. rewrite peq_true. constructor.
Qed.    

Lemma shl_zero_is_zero: (Vint (Int.shl (mk_uconst16 Int.zero) (Int.repr 16))) = Vzero.
Proof.
  rewrite Int.shl_mul_two_p.
  Set Printing Coercions.
  cbn.
  Unset Printing Coercions.
  rewrite Int.zero_ext_range_eq; cycle 1.
  - unfold Int.ltu. change Int.zwordsize with 32. lia.
  - unfold Int.ltu. rewrite Int.unsigned_zero.  unfold two_p. unfold two_power_pos. cbn.
    rewrite Int.unsigned_repr_eq. cbn. reflexivity.
  - rewrite Int.mul_commut. rewrite Int.mul_zero. reflexivity.
Qed.
  
Lemma transl_op_correct:
  forall op args res k (rs: regset) m v c,
  transl_op op args res k = OK c ->
  eval_operation ge (rs#SP) op (get_pairs preg_rpair_of ## args rs) m = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ lessdef' v (preg_rpair_of res) rs'
  /\ (forall r, data_preg r = true -> forall_rpair (fun x => r <> (preg_of x)) res -> preg_notin r (destroyed_by_op op) -> rs' r = rs r)
  /\ rs' RA = rs RA
  /\ rs' PCXI = rs PCXI.
Proof.
  assert (SAME: forall v1 v2, v1 = v2 -> Val.lessdef v2 v1). { intros; subst; auto. }
Opaque Int.eq.   Opaque preg_eq.

  intros. unfold transl_op in H; destruct op; ArgsInv; simpl in H0; try (inv H0); try (TranslOpSplitter; fail).
  - (* move *)
    destruct res; inv H.
    destruct (preg_of r0) eqn:RES; inv H1;
    destruct r; inv H0;  destruct (preg_of r) eqn:ARG; inv H1; TranslOpSplitter.
  - (* intconst *)
    destruct res; inv H.
    destruct (preg_of r) eqn:?; inv H1.
    + exploit loadimm_correct; eauto.  intros (rs' & A & B & C).
     exists rs'; split; eauto. Splitter.
    + exploit loadimm_addr_correct; eauto. intros (rs' & A & B & C).
     exists rs'; split; eauto. Splitter.
     rewrite C; eauto with asmgen.
  - (* addrsymbol *)
    destruct res; inv H.
    destruct (preg_of r) eqn:?; inv H1.
    + econstructor. split. eapply exec_straight_two; simpl; eauto.
      Splitter. rewrite low_high_half. auto.
      intuition Simpl.
    + econstructor. split. eapply exec_straight_two; simpl; eauto.
      Splitter. rewrite low_high_half. auto.
      intuition Simpl.
  - (* addrstack *)
    destruct res; inv H.
    destruct (preg_of r) eqn:RES; inv H1.
    + exploit (addimm_addr_correct TMPA A10 (Ptrofs.to_int ofs) (Pmov_d r0 TMPA:: k) rs); eauto with asmgen.
      intros (rs'' & A & B & C).
      econstructor; split ; eauto.
      eapply exec_straight_trans. eexact A. apply exec_straight_one; simpl; reflexivity.
      repeat Splitter'. rewrite B.  destruct (rs A10); auto. simpl. rewrite Ptrofs.of_int_to_int;  auto.
      intros. Simpl.
    + exploit (addimm_addr_correct r0 A10 (Ptrofs.to_int ofs) k rs); eauto with asmgen.
      intros (rs'' & A & B & C).
      exists rs''; split; eauto. repeat Splitter'.
      rewrite B. destruct (rs A10); auto. simpl. rewrite Ptrofs.of_int_to_int; auto.
      rewrite C; eauto with asmgen.
  - (* opcast *)
    destruct r; inv EQ0.
    destruct (preg_of r) eqn:RES; inv H0.
    + econstructor. split. apply exec_straight_one; simpl; reflexivity.
      destruct res; inv EQ. simpl. rewrite (areg_of_eq _ _ H0).
      repeat Splitter'. destruct (rs r0); auto. intuition Simpl.
    + econstructor. split. apply exec_straight_one; simpl; reflexivity.
      destruct res; inv EQ. simpl. rewrite (areg_of_eq _ _ H0).
      repeat Splitter'. destruct (rs r0); auto. intuition Simpl.
  - (* add *)
    destruct res; inv H.
    destruct (preg_of r1) eqn:RES; inv H1; monadInv H0; simpl.
    + exploit add_correct; eauto. intros (rs' & A & B & C).
      exists rs'; split; eauto. split.
      destruct r, r0; inv EQ; inv EQ1; simpl.
      rewrite (ireg_of_eq _ _ H0); auto.
      rewrite (ireg_of_eq _ _ H1); auto.
      rewrite RES, B. auto. intros. rewrite C; auto with asmgen.
    + TranslOpSplitter.
      destruct r; inv EQ. simpl.
      rewrite (areg_of_eq _ _ H1). auto.
  - (* addl *)
    monadInv H.
    generalize Val.addl_hiword_lessdef. generalize Val.addl_loword_lessdef. intros.
    assert (x <> x0) by (destruct x, x0; try congruence; inv Heqb).
    destruct (dreg_eq x0 x1 || dreg_eq x0 x3) eqn:?; inv EQ3.
    + econstructor; split.
      eapply exec_straight_three; simpl; eauto.
      repeat Splitter'. intuition Simpl.
    + econstructor; split.
      eapply exec_straight_two; simpl; eauto.
      rewrite orb_false_iff in Heqb1. destruct Heqb1.
      assert (x0 <> x1) by (destruct x0, x1; try congruence; inv H2).
      assert (x0 <> x3) by (destruct x0, x3; try congruence; inv H3).
      repeat Splitter'. intuition Simpl.
  - (* addimm *)
    destruct res; inv H.
    destruct (preg_of r0) eqn:RES; inv H1; monadInv H0.
    + destruct r; inv EQ. simpl.
      rewrite (ireg_of_eq _ _ H0). rewrite RES.
      exploit (addimm_correct r1 x n); eauto with asmgen.
      intros (rs' & A & B & C).
      exists rs'; split. eauto with asmgen. simpl. rewrite B; auto with asmgen.
    + destruct r; inv EQ. simpl.
      rewrite (areg_of_eq _ _ H0). rewrite RES.
      exploit (addimm_addr_correct r1 x n); eauto with asmgen.
      intros (rs' & A & B & C).
      exists rs'; split; eauto with asmgen. split. rewrite B; auto with asmgen.
      split; eauto with asmgen.
  - (* and *)
    exploit and_correct; eauto.  intros (rs' & A & B & C).
    exists rs'; split; [eauto| Splitter].
  - (* andimm *)
    destruct r; inv EQ0.
    destruct (preg_of r) eqn:RES; inv H0; simpl; rewrite RES.
    + exploit (andimm_correct x r1 n); eauto with asmgen.
      destruct r; inv RES; try congruence.
      intros (rs' & A & B & C).
      exists rs'; split; eauto. rewrite B. split; auto.
      split. intros. rewrite C; eauto with asmgen.
      rewrite C; eauto with asmgen.
    + exploit (andimm_correct x x n); eauto with asmgen.
      intros (rs' & A & B & C).
      exists rs'; split. eapply exec_straight_trans.
      eapply exec_straight_one; simpl; reflexivity.
      eexact A. rewrite B.
      split; [Splitter|split].
      intros. rewrite C; eauto with asmgen. Simpl.
      rewrite C; eauto with asmgen.
  - (* select *)
     destruct r0, r1; inv EQ2;
     destruct (preg_of r0) eqn:?; try destruct (preg_of r1) eqn:?; inv H0.
    + econstructor; split.
      apply exec_straight_one; simpl; auto. split. Simpl.
      destruct (rs x0); auto. simpl. rewrite Heqp0, Heqp.
      destruct (Int.eq i Int.zero); simpl; apply Val.lessdef_normalize.
      intuition Simpl.
    + econstructor; split.
      eapply exec_straight_two; simpl; auto. split; [|split]; intros; Simpl.
      destruct (rs x0); auto. simpl. rewrite Heqp0, Heqp.
      destruct (Int.eq i Int.zero); simpl; apply Val.lessdef_normalize.
    + econstructor; split.
      eapply exec_straight_two; simpl; auto. split; [|split]; intros; Simpl.
      destruct (rs x0); auto. simpl. rewrite Heqp0, Heqp.
      destruct (Int.eq i Int.zero); simpl; apply Val.lessdef_normalize.
    + destruct (areg_eq r3 r4);[|destruct (dreg_eq x x0)]; subst; inv H3.
      * econstructor; split. apply exec_straight_one; simpl; auto.
        split; [|split]; intros; Simpl.
        destruct (rs x0); auto. simpl. rewrite Heqp0, Heqp.
        destruct (Int.eq i Int.zero); simpl; apply Val.lessdef_normalize.
      * exploit switch_A_D_via_TMP_correct. intros (rs' & A' & B' & C' & D').
        exploit switch_A_D_via_TMP_correct. intros (rs'' & A'' & B'' & C'' & D'').
        exists rs''. split.
        eapply exec_straight_trans. eexact A'.
        eapply exec_straight_step; simpl. reflexivity. Simpl. eapply exec_straight_step. reflexivity.
        Simpl. eexact A''. split.
        rewrite D''; eauto with asmgen.
        Simpl. rewrite D'; eauto with asmgen.
        simpl. rewrite Heqp, Heqp0.
        destruct (rs x0); auto. simpl.
        destruct (Int.eq i Int.zero); auto. simpl. rewrite D'; eauto with asmgen. apply Val.lessdef_normalize.
        simpl. rewrite B'. destruct (dreg_eq x0 D2); Simpl; apply Val.lessdef_normalize.
        destruct (dreg_eq x0 D2); congruence.
        destruct (dreg_eq x0 D2); congruence.
        split.
        intros; Simpl.
        destruct (preg_eq r5 (DREG (if dreg_eq x0 D2 then D3 else D2))).
        subst. rewrite <- B''; eauto with asmgen. Simpl. rewrite <- C'; eauto with asmgen.
        destruct (dreg_eq x0 D2); congruence.
        destruct (preg_eq r5 r3). rewrite e; rewrite <- C''. Simpl.
        destruct (dreg_eq x0 D2) eqn:?; eauto with asmgen. Simpl.
        rewrite Pregmap.gso; eauto with asmgen. destruct (dreg_eq x0 D2); congruence.
        rewrite D''; eauto with asmgen. Simpl.
        rewrite D''; eauto with asmgen. Simpl.
        rewrite D''; eauto with asmgen. Simpl.
        rewrite D'; eauto with asmgen.
      * econstructor. split. eapply exec_straight_three; simpl; reflexivity.
        split; [|split]; intros; Simpl.
        destruct (rs x0); auto. simpl. rewrite Heqp0, Heqp.
        destruct (Int.eq i Int.zero); simpl; apply Val.lessdef_normalize.
  - (* cadd *)
    econstructor; split. apply exec_straight_one; simpl; auto.
    split; [|split]; intros; Simpl. destruct (rs x0); auto. simpl.
    destruct (Int.eq i Int.zero); simpl.
    destruct (rs x1); auto. destruct (rs x1), (rs x2); auto.
  - (* csub *)
    econstructor; split. apply exec_straight_one; simpl; auto.
    split; [|split]; intros; Simpl. destruct (rs x0); auto. simpl.
    destruct (Int.eq i Int.zero); simpl.
    destruct (rs x1); auto. destruct (rs x1), (rs x2); auto. simpl.
    destruct (eq_block b b0); auto.
  - (* cond *)
    exploit transl_cond_op_correct; eauto. intros (rs' & A & B & C).
    exists rs'; split. eexact A. repeat Splitter'.
    erewrite get_pairs_singles; eauto.
  - (* divs *)
    replace v with (Val.maketotal (Val.divs (rs x) (rs x0))).
    Local Transparent destroyed_by_op.
    TranslOpSplitter. rewrite H4; auto.
  - (* divu *)
    replace v with (Val.maketotal (Val.divu (rs x) (rs x0))).
    TranslOpSplitter. rewrite H4; auto.
  - (* mods *)
    replace v with (Val.maketotal (Val.mods (rs x) (rs x0))).
    TranslOpSplitter. rewrite H4; auto.
  - (* modu *)
    replace v with (Val.maketotal (Val.modu (rs x) (rs x0))).
    TranslOpSplitter. rewrite H4; auto.
  - (* extr *)
    econstructor; split.
    apply exec_straight_one; simpl; eauto.
    Splitter.
    destruct pos, width. simpl.
    rewrite !Int.zero_ext_range_eq; change Int.zwordsize with 32; try lia; auto.
    intuition Simpl.
  - (* extru *)
    econstructor; split.
    apply exec_straight_one; simpl; eauto.
    Splitter.
    destruct pos, width. simpl.
    rewrite !Int.zero_ext_range_eq; change Int.zwordsize with 32; try lia; auto.
    intuition Simpl.
  - (* insert *)
    econstructor; split.
    apply exec_straight_one; simpl; eauto.
    Splitter.
    destruct pos, width. simpl.
    rewrite !Int.zero_ext_range_eq; change Int.zwordsize with 32; try lia; auto.
    intuition Simpl.
  - (* madd *)
    destruct r; inv EQ3.
    destruct (preg_of r) eqn:Eres; inv H0.
    + TranslOpSplitter.
    + econstructor; split.
      eapply exec_straight_two; simpl; eauto.
      Splitter. intros. Simpl.
  - (* maddimm *)
    destruct res; inv H.
    destruct (preg_of r1) eqn:Eres; monadInv H1.
    + exploit (maddimm_correct r2 x x0 n); eauto with asmgen. intros (rs' & A & B & C).
      exists rs'; split. eexact A.
      Splitter.
    + destruct (Int.is_power2 n) eqn:En.
      destruct (get_uconst2 i) eqn:Ei; inv EQ2.
      econstructor; split. apply exec_straight_one; simpl; reflexivity.
      repeat Splitter'. destruct r; inv EQ. simpl.
      rewrite (areg_of_eq _ _ H1).
      destruct (Int.eq_dec (u_amount 2 u) Int.zero) as [Heq|Hneq].
      destruct  (rs x), (rs x0); auto; simpl; rewrite (Int.mul_pow2 _ _ _ En);
        rewrite <- (get_uconst2_sound _ _ Ei); rewrite Heq;
        rewrite Int.shl_zero; auto.
      assert (Int.ltu u Int.iwordsize = true) as Hltu.
      { rewrite (get_uconst2_sound _ _ Ei).
        eapply Int.is_power2_range; eassumption. }
      destruct  (rs x), (rs x0); auto; simpl; rewrite (Int.mul_pow2 _ _ _ En), Hltu;
        rewrite <- (get_uconst2_sound _ _ Ei); auto.
      intuition Simpl.
      exploit (mulimm_correct TMP x0 n); eauto with asmgen.
      intros (rs' & A & B & C).
      eexists; split.
      eapply exec_straight_trans. exact A.
      apply exec_straight_one; reflexivity.
      Splitter. rewrite B.
      destruct r; inv EQ. simpl.
      rewrite (areg_of_eq _ _ H1). rewrite C; auto with asmgen.
      intros. Simpl.
      inv EQ2.
      exploit (mulimm_correct TMP x0 n); eauto with asmgen.
      intros (rs' & A & B & C).
      eexists; split.
      eapply exec_straight_trans. exact A.
      apply exec_straight_one; reflexivity.
      Splitter. rewrite B.
      destruct r; inv EQ. simpl.
      rewrite (areg_of_eq _ _ H1). rewrite C; auto with asmgen.
      intros. Simpl.
  - (* msub *)
    destruct r; inv EQ3.
    destruct (preg_of r) eqn:Eres; inv H0.
    + TranslOpSplitter.
    + econstructor; split.
      eapply exec_straight_two; simpl; eauto.
      Splitter. intros. Simpl.
  - (* msubimm *)
    destruct r; inv EQ2.
    destruct (preg_of r) eqn:Eres; inv H0.
    + exploit (msubimm_correct x0 r2); eauto with asmgen.
      apply preg_of_dreg_not_TMP in Eres. congruence.
      intros (rs' & A & B & C).
      exists rs'; split. eexact A. Splitter.
    + destruct (dreg_eq x0 x); inv H3.
      exploit (mulimm_correct TMP x n); eauto with asmgen. intros (rs' & A & B & C).
      econstructor; split. eapply exec_straight_trans. eexact A.
      eapply exec_straight_two; simpl; reflexivity.
      Splitter. rewrite B. rewrite C; eauto with asmgen.
      intros. Simpl.
      exploit (msubimm_correct x0 x0 x n); eauto with asmgen.
      intros (rs' & A & B & C). exists rs'. split.
      eapply exec_straight_trans. apply exec_straight_one; reflexivity.
      eexact A. rewrite B. split.
      simpl. rewrite Eres. Simpl.
      split. intros. rewrite C; eauto with asmgen. Simpl. 
      rewrite C; eauto with asmgen.
  - (* mul *)
    exploit mul_correct; eauto with asmgen. intros (rs' & A & B & C).
    exists rs'; split; [eauto| Splitter].
  - (* mulimm *)
    exploit (mulimm_correct x0 x n); eauto with asmgen. intros (rs' & A & B & C).
    exists rs'; split; [eauto| Splitter].
  - (* mulhs *)
    econstructor; split.
    apply exec_straight_one; simpl; eauto.
    Splitter. intuition Simpl.
  - (* mulhu *)
    econstructor; split.
    apply exec_straight_one; simpl; eauto.
    Splitter. intuition Simpl.
  - (* mulu *)
    econstructor; split.
    apply exec_straight_one; simpl; eauto. rewrite Val.mull'_mulhu.
    Splitter.
    destruct (rs x), (rs x0); auto. simpl. f_equal. apply Int64.hi_ofwords.
    destruct (rs x), (rs x0); auto. simpl. f_equal. apply Int64.lo_ofwords.
    intuition Simpl.
  - (* nandimm *)
    exploit (nandimm_correct x0 x n); eauto with asmgen. intros (rs' & A & B & C).
    exists rs'; split; [eauto| Splitter].
  - (* neg *)
    exploit (move_rr_correct x0 x); eauto with asmgen. intros (rs' & A & B & C).
    econstructor; split. eapply exec_straight_opt_right. eexact A.
    apply exec_straight_one; simpl; eauto. rewrite B.
    Splitter. intros; Simpl.
  - (* negl  *)
    monadInv H.
    assert (forall y, Int.eq y Int.zero = Int.eq (Int.neg y) Int.zero).
    {
      Local Transparent Int.eq.
      unfold Int.eq, Int.neg; intros. rewrite Int.unsigned_zero.
      destruct (zeq (Int.unsigned y) 0); symmetry. rewrite e.
      apply zeq_true. apply zeq_false. red. intros.
      rewrite Int.unsigned_repr_eq in H. apply Z_mod_zero_opp_full in H.
      replace (- - Int.unsigned y) with (Int.unsigned y) in H by lia.
      rewrite Zmod_small in H by apply Int.unsigned_range. congruence.
    }
    assert (x <> x0) by (destruct x, x0; try congruence; inv Heqb).
    destruct (dreg_eq x0 x1); inv EQ2.
    + econstructor; split.
      eapply exec_straight_trans. eapply exec_straight_three; simpl; reflexivity.
      eapply exec_straight_one; simpl; reflexivity.
      repeat Splitter'.
      rewrite ! Int.sign_ext_range_eq; auto.
      destruct (rs x1), (rs x2); auto. simpl.
      rewrite Int64.decompose_neg, Int64.hi_ofwords.
      rewrite <- H. unfold Int.sub_borrow.
      destruct (Int.eq i0 Int.zero) eqn:?.
      unfold Int.sub_borrow. rewrite (Int.same_if_eq _ _ Heqb1).
      rewrite ! Int.unsigned_zero. simpl. rewrite Int.sub_zero_l. rewrite <- Int.sub_zero_r. auto.
      unfold Int.sub_borrow. rewrite zlt_true, Int.sub_add_opp.
      unfold Int.neg. rewrite Int.unsigned_one. auto. unfold Int.eq in Heqb1.
      rewrite Int.unsigned_zero in *.
      destruct (zeq (Int.unsigned i0) 0); inv Heqb1.
      generalize (Int.unsigned_range i0). lia.
      destruct (rs x1), (rs x2); auto. simpl.
      rewrite Int64.decompose_neg, Int64.lo_ofwords, Int.sign_ext_range_eq; auto.
      intuition Simpl.
    + econstructor; split.
      eapply exec_straight_three; simpl; reflexivity.
      repeat Splitter'.
      rewrite ! Int.sign_ext_range_eq; auto.
      destruct (rs x1), (rs x2); auto. simpl.
      rewrite Int64.decompose_neg, Int64.hi_ofwords.
      rewrite <- H.
      unfold Int.eq. rewrite Int.unsigned_zero.
      destruct (zeq (Int.unsigned i0) 0). unfold Int.sub_borrow. rewrite e.
      rewrite ! Int.unsigned_zero. simpl. rewrite Int.sub_zero_l. rewrite <- Int.sub_zero_r.
      auto.
      unfold Int.sub_borrow. rewrite zlt_true, Int.sub_add_opp.
      unfold Int.neg. rewrite Int.unsigned_one. auto.
      rewrite Int.unsigned_zero. generalize (Int.unsigned_range i0). lia.
      destruct (rs x1), (rs x2); auto. simpl.
      rewrite Int64.decompose_neg, Int64.lo_ofwords, Int.sign_ext_range_eq; auto.
      intuition Simpl.
  - (* norimm *)
    exploit (norimm_correct x0 x n); eauto with asmgen. intros(rs' & A & B & C).
    exists rs'; split; [eauto| Splitter].
  - (* not *)
    exploit (move_rr_correct x0 x); eauto with asmgen. intros (rs' & A & B & C).
    econstructor; split. eapply exec_straight_opt_right. eexact A.
    apply exec_straight_one; simpl; eauto. rewrite B. Splitter.
    intros; Simpl.
  - (* or *)
    exploit or_correct; eauto with asmgen. intros (rs' & A & B & C).
    exists rs'; split; [eauto| Splitter].
  - (* orimm *)
    destruct r; inv EQ0.
    destruct (preg_of r) eqn:E; monadInv H0.
    exploit (orimm_correct x r1 n); eauto with asmgen. apply preg_of_dreg_not_TMP in E; congruence.
    intros (rs' & A & B & C). exists rs'; split. eexact A. Splitter.
    exploit (orimm_correct x x n); eauto with asmgen.
    intros (rs' & A & B & C). exists rs'; split. eapply exec_straight_trans.
    apply exec_straight_one; reflexivity. eexact A. rewrite B. Splitter.
    intros. rewrite C; eauto with asmgen. Simpl.
  - (* rsubimm *)
    exploit (rsubimm_correct x0 x n); eauto with asmgen. intros (rs' & A & B & C).
    exists rs'; split; [eauto| Splitter].
  - (* shl *)
    econstructor; split.
    apply exec_straight_one; simpl; eauto. repeat Splitter'.
     unfold Val.shl.
    destruct (rs x), (rs x0); auto.
    destruct (Int.ltu i0 Int.iwordsize) eqn:?; auto.
    rewrite sh_shl; auto. simpl. rewrite Heqb. auto.
    intros; Simpl.
  - (* slimm *)
    exploit (slimm_correct x0 x a); eauto with asmgen. intros (rs' & A & B & C).
    exists rs'; split; [eauto| Splitter].
  - (* shr *)
    econstructor; split. eapply exec_straight_two; simpl; auto.
    repeat Splitter'.
    rewrite Int.sign_ext_range_eq; auto.
    destruct (rs x), (rs x0); auto. rewrite Int.sub_zero_r.
    unfold Val.shr. destruct (Int.ltu i0 Int.iwordsize) eqn:?; auto.
    rewrite sha_shr; auto. simpl. rewrite Heqb. auto.
    intros; Simpl.
  - (* asrimm *)
    exploit (asrimm_correct x0 x a); eauto  with asmgen. intros (rs' & A & B & C).
    exists rs'; split; [eauto| Splitter].
  - (* shru *)
    econstructor; split. eapply exec_straight_two; simpl; auto.
    repeat Splitter'.
    rewrite Int.sign_ext_range_eq; auto.
    destruct (rs x), (rs x0); auto. rewrite Int.sub_zero_r.
    unfold Val.shru. destruct (Int.ltu i0 Int.iwordsize) eqn:?; auto.
    rewrite sh_shru; auto. simpl. rewrite Heqb. auto.
    intros; Simpl.
  - (* lsrimm *)
    exploit (lsrimm_correct x0 x a); eauto  with asmgen. intros (rs' & A & B & C).
    exists rs'; split; [eauto| Splitter].
  - (* shrx *)
    exploit Val.shrx_shr_2; eauto. intros E; subst v.
    destruct (Int.eq n Int.zero) eqn:?.
    + econstructor; split. apply exec_straight_one; simpl; eauto.
      Splitter. intuition Simpl.
    + destruct n as [n Range]; simpl in *.
      econstructor; split.
      eapply exec_straight_step. simpl; reflexivity. auto.
      eapply exec_straight_step. simpl; reflexivity. auto.
      eapply exec_straight_step. simpl; reflexivity. auto.
      apply exec_straight_one. simpl; reflexivity. auto.
      repeat Splitter'.
      rewrite (Int.sign_ext_range_eq (Int.neg (Int.repr 31))) by auto.
      assert (Int.ltu (Int.sub Int.iwordsize n) Int.iwordsize  = true).
      { apply Int.ltu_inv in Range.
        unfold Int.sub.
        change (Int.unsigned Int.iwordsize) with 32 in *.
        apply zlt_true.
        rewrite Int.unsigned_repr.
        change (Int.unsigned Int.iwordsize) with 32.
        assert (Int.unsigned n <> 0).
        Local Transparent Int.eq.
        unfold Int.eq in Heqb.
        rewrite Int.unsigned_zero in Heqb.
        destruct (zeq (Int.unsigned n) 0) eqn:?; auto; inv Heqb.
        lia. change (Int.max_unsigned) with 4294967295. lia.
      }
      rewrite !shift_sc9_eq'; auto.
      rewrite !sha_shr; auto.
      rewrite sh_shru; auto.
      intuition Simpl.
  - (* sub *)
    destruct r; inv EQ0.
    destruct (preg_of r) eqn:Er; monadInv H0; simpl; rewrite Er.
    + destruct r0; inv EQ. simpl. rewrite (ireg_of_eq _ _ H0).
      exploit sub_correct; eauto with asmgen. intros (rs' & A & B & C).
      exists rs'; split. eexact A. rewrite B. Splitter.
    +  destruct r0; inv EQ. simpl. rewrite (areg_of_eq _ _ H0).
       econstructor; split. eapply exec_straight_two; reflexivity.
       Splitter. intuition Simpl.
  - monadInv H.
    assert (x <> x0) by (destruct x, x0; try congruence; inv Heqb).
    generalize Val.subl_loword_lessdef. intros.
    destruct (dreg_eq x0 x1 || dreg_eq x0 x3) eqn:?; inv EQ3.
    + econstructor; split.
      eapply exec_straight_three; simpl; eauto.
      repeat Splitter'.
      destruct (rs x1), (rs x2), (rs x3), (rs x4); auto. simpl.
      rewrite Int64.decompose_sub', Int64.hi_ofwords, Int.sub_add_l.
      rewrite Int.sub_add_not_3; auto. rewrite Int.xor_idem, Int.add_zero. auto.
      intuition Simpl.
    + rewrite orb_false_iff in Heqb1. destruct Heqb1.
      assert (x0 <> x1) by (destruct x0, x1; try congruence; inv H1).
      assert (x0 <> x3) by (destruct x0, x3; try congruence; inv H2).
      econstructor; split.
      eapply exec_straight_two; simpl; eauto.
      repeat Splitter'.
      destruct (rs x1), (rs x2), (rs x3), (rs x4); auto. simpl.
      rewrite Int64.decompose_sub', Int64.hi_ofwords, Int.sub_add_l.
      rewrite Int.sub_add_not_3, Int.xor_idem, Int.add_zero; auto.
      intuition Simpl.
  - (* xnorimm *)
     exploit (xnorimm_correct x0 x n); eauto  with asmgen. intros (rs' & A & B & C).
     exists rs'; split; [eauto| Splitter].
  - (* xor *)
    exploit xor_correct;  eauto  with asmgen. intros (rs' & A & B & C).
    exists rs'; split; [eauto| Splitter].
  - (* xorimm *)
     exploit (xorimm_correct x0 x n); eauto  with asmgen. intros (rs' & A & B & C).
     exists rs'; split; [eauto| Splitter].
  - (* ftoiz *)
    replace v with (Val.maketotal (Val.intofsingle (rs x))).
    TranslOpSplitter. rewrite H3; auto.
  - (* ftouz *)
    replace v with (Val.maketotal (Val.intuofsingle (rs x))).
    TranslOpSplitter. rewrite H3; auto.
  - (* itof  *)
    replace v with (Val.maketotal (Val.singleofint (rs x))).
    TranslOpSplitter. rewrite H3; auto.
  - (* utof *)
    replace v with (Val.maketotal (Val.singleofintu (rs x))).
    TranslOpSplitter. rewrite H3; auto.
Qed.

(** Memory accesses *)

Lemma indexed_memory_access_correct:
  forall mk1 mk2 (base : index_reg) ofs k (rs: regset) m,
    valid_index_reg base rs m = true ->
  (exists base' ofs' rs',
      valid_index_reg base' rs' m = true
     /\ exec_straight_opt ge fn (indexed_memory_access mk1 mk2 base ofs k) rs m
         (mk2 base' ofs' :: k) rs' m
     /\ Val.offset_ptr rs'#base' (Ptrofs.of_int ofs') = Val.offset_ptr rs#base ofs
     /\ forall r, r <> PC -> r <> TMPA -> rs'#r = rs#r)
  \/ (exists base' rs',
        exec_straight_opt ge fn (indexed_memory_access mk1 mk2 base ofs k) rs m (mk1 base' :: k) rs' m
        /\ Val.offset_ptr (rs'#base') (Ptrofs.zero) = Val.offset_ptr rs#base ofs
  /\ forall r, r <> PC -> r <> TMPA -> rs'#r = rs#r).
Proof.
  intros.
  unfold indexed_memory_access.
  destruct (Ptrofs.eq ofs Ptrofs.zero) eqn:?;
           [|destruct (get_sconst16 (Ptrofs.to_int ofs)) eqn:?].
  - right. exists base. econstructor. split.
    constructor.
    rewrite (Ptrofs.same_if_eq ofs Ptrofs.zero); auto.
  - left.
    exists base, s, rs; split; auto. split.
    constructor. simpl. rewrite (get_sconst16_sound (Ptrofs.to_int ofs) s); auto.
    rewrite Ptrofs.of_int_to_int; auto.
  - right.
    generalize (low_high_s (Ptrofs.to_int ofs)). intros.
    exploit (addimm_addr_correct TMPA base).
    intros (rs' & EX & RES & OTH).
    exists TMPA, rs'. split.
    constructor. eexact EX. split.
    rewrite RES. simpl. unfold Val.offset_ptr.
    destruct (rs base); auto.
    simpl. rewrite Ptrofs.add_zero. rewrite Ptrofs.of_int_to_int; auto.
    intuition Simpl.
Qed.

Lemma indexed_load_access_correct:
  forall chunk
    (mk1: areg -> instruction)
    (mk2: index_reg -> sconst16 -> instruction) rd m,
  (forall base rs,
     exec_instr ge fn (mk1 base) rs m = exec_load chunk rs m rd base sconst16_zero) ->
  (forall base ofs rs,
      valid_index_reg base rs m = true ->
      exec_instr ge fn (mk2 base ofs) rs m = exec_load chunk rs m rd base ofs) ->
  forall (base: index_reg) ofs k (rs: regset) v,
  valid_index_reg base rs m = true ->
  Mem.loadv chunk m (Val.offset_ptr rs#base ofs) = Some v ->
  rd <> PC ->
  exists rs',
     exec_straight ge fn (indexed_memory_access mk1 mk2 base ofs k) rs m k rs' m
  /\ rs'#rd = v
  /\ forall r, r <> PC -> r <> TMPA -> r <> rd -> rs'#r = rs#r.
Proof.
  intros until m; intros EXEC1 EXEC2; intros until v; intros IR LOAD NOTPC.
  exploit indexed_memory_access_correct; eauto.
  intros. destruct H.
  - destruct H as (base' & ofs' & rs' & IV & EX & BP & OTH).
    econstructor; split.
    eapply exec_straight_opt_right. eexact EX.
    apply exec_straight_one. rewrite EXEC2.
    unfold exec_load. rewrite BP. rewrite LOAD. reflexivity. auto.
    Simpl. intuition Simpl.
  - destruct H as (base' & rs' & EX & BP & OTH).
    econstructor; split.
    eapply exec_straight_opt_right. eexact EX.
    eapply exec_straight_one. rewrite EXEC1.
    unfold exec_load. change (Ptrofs.of_int sconst16_zero) with Ptrofs.zero. rewrite BP.
    rewrite LOAD. reflexivity.
    Simpl. intuition Simpl.
Qed.

Lemma indexed_store_access_correct:
  forall chunk
    (mk1: areg -> instruction)
    (mk2: index_reg -> sconst16 -> instruction) r1 m,
  (forall base rs,
     exec_instr ge fn (mk1 base) rs m = exec_store chunk rs m r1 base sconst16_zero) ->
  (forall base ofs rs,
      valid_index_reg base rs m = true ->
     exec_instr ge fn (mk2 base ofs) rs m = exec_store chunk rs m r1 base ofs) ->
  forall (base: index_reg) ofs k (rs: regset) m',
    valid_index_reg base rs m = true ->
  Mem.storev chunk m (Val.offset_ptr rs#base ofs) (rs#r1) = Some m' ->
  r1 <> TMPA -> r1 <> PC ->
  exists rs',
     exec_straight ge fn (indexed_memory_access mk1 mk2 base ofs k) rs m k rs' m'
  /\ forall r, r <> PC -> r <> TMPA -> rs'#r = rs#r.
Proof.
  intros until m; intros EXEC1 EXEC2; intros until m'; intros IR STORE NOT31' NOTPC.
  exploit indexed_memory_access_correct; eauto.
  intros. destruct H.
  - destruct H as (base' & ofs' & rs' & IV & EX & BP & OTH).
    econstructor; split.
    eapply exec_straight_opt_right. eexact EX.
    apply exec_straight_one. rewrite EXEC2.
    unfold exec_store. rewrite BP. rewrite OTH; eauto with asmgen.
    rewrite STORE. reflexivity. auto.
    Simpl. intuition Simpl.
  - destruct H as (base' & rs' & EX & BP & OTH).
    econstructor; split.
    eapply exec_straight_opt_right. eexact EX.
    eapply exec_straight_one. rewrite EXEC1.
    unfold exec_store. change (Ptrofs.of_int sconst16_zero) with Ptrofs.zero.
    rewrite BP. rewrite OTH; eauto with asmgen.  rewrite STORE; auto.
    Simpl. intuition Simpl.
Qed.

Lemma loadind_correct:
  forall base ofs ty dst k c (rs: regset) m v,
  valid_index_reg base rs m = true ->
  loadind base ofs ty dst k = OK c ->
  Mem.loadv (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, r <> PC -> r <> TMPA -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  unfold loadind.
  intros until v; intros IR TR LOAD.
  destruct ty, (preg_of dst); inv TR; eapply indexed_load_access_correct; simpl;
    eauto with asmgen; intros; rewrite H; auto.
Qed.

Lemma storeind_correct:
  forall base ofs ty src k c (rs: regset) m m',
  valid_index_reg base rs m = true ->
  storeind src base ofs ty k = OK c ->
  Mem.storev (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) rs#(preg_of src) = Some m' ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, r <> PC -> r <> TMPA -> rs'#r = rs#r.
Proof.
  unfold storeind.
  intros until m'; intros IR TR STORE.
  destruct ty, (preg_of src) eqn:?; inv TR; eapply indexed_store_access_correct; simpl;
    eauto with asmgen; intros; rewrite H; auto.
Qed.


Lemma loadind_ptr_correct:
  forall (base: index_reg) ofs (dst: areg) k (rs: regset) m v,
  valid_index_reg base rs m = true ->
  Mem.loadv Mptr m (Val.offset_ptr rs#base ofs) = Some v ->
  exists rs',
     exec_straight ge fn (loadind_ptr base ofs dst k) rs m k rs' m
  /\ rs'#dst = v
  /\ forall r, r <> PC -> r <> TMPA -> r <> dst -> rs'#r = rs#r.
Proof.
  unfold Mptr. simpl. intros.
  eapply indexed_load_access_correct; intros; simpl; eauto with asmgen. rewrite H1.
  auto.
Qed.

Lemma storeind_ptr_correct:
  forall (base: index_reg) ofs (src: areg) k (rs: regset) m m',
  valid_index_reg base rs m = true ->
  Mem.storev Mptr m (Val.offset_ptr rs#base ofs) rs#src = Some m' ->
  src <> TMPA ->
  exists rs',
     exec_straight ge fn (storeind_ptr src base ofs k) rs m k rs' m'
  /\ forall r, r <> PC -> r <> TMPA -> rs'#r = rs#r.
Proof.
  unfold Mptr. simpl. intros.
  eapply indexed_store_access_correct; intros; simpl; eauto with asmgen. rewrite H2.
  auto.
Qed.

Lemma lea_correct:
  forall rd id ofs k rs m,
  exists rs',
  exec_straight ge fn (lea rd id ofs k) rs m k rs' m
  /\ rs'#rd = Genv.symbol_address ge id ofs
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
    (mk2: index_reg -> sconst16 -> instruction)
    (mk3: areg -> ident -> ptrofs -> instruction)
    addr args k c rd (rs: regset) m v v',
  (forall base rs,
     exec_instr ge fn (mk1 base) rs m = exec_load chunk rs m rd base sconst16_zero) ->
  (forall ofs rs,
     exec_instr ge fn (mk2 SP ofs) rs m = exec_load chunk rs m rd SP ofs) ->
  (forall (base: areg) id ofs (rs : regset),
     exec_instr ge fn (mk3 base id ofs) rs m = exec_load2 chunk rs m rd base (low_half ge id ofs)) ->
  transl_memory_access mk1 mk2 mk3 addr args k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some v ->
  Mem.loadv chunk m v = Some v' ->
  rd <> PC ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#rd = v'
  /\ forall r, r <> PC -> r <> TMPA -> r <> rd -> rs'#r = rs#r.
Proof.
  assert (forall chunk m v v',
             Mem.loadv chunk m v = Some v' ->
             Mem.loadv chunk m (Val.offset_ptr v (Ptrofs.of_int Int.zero)) = Some v').
  { intros. destruct v; inv H.  simpl.  rewrite Ptrofs.add_zero. auto. }
  intros until v'; intros INSTR1 INSTR2 INSTR3 TR EV LOAD NOTPC.
  unfold transl_memory_access in TR; destruct addr; ArgsInv.
  - (* Aindexed *)
    inv EV.
    destruct (Int.eq ofs Int.zero) eqn:?; inv EQ0.
    + econstructor; split.
      apply exec_straight_one. rewrite INSTR1. unfold exec_load.
      rewrite (areg_of_eq _ _ EQ), (Int.same_if_eq _ _ Heqb) in *.
      unfold Val.offset_ptr. unfold Mem.loadv in *.
      destruct (rs x); inv LOAD. simpl.  rewrite H1. reflexivity. Simpl.
      intuition Simpl.
    + exploit (addimm_addr_correct TMPA x); eauto with asmgen.
      intros (rs' & EX & RES & OTH).
      econstructor; split.
      eapply exec_straight_trans; eauto.
      eapply exec_straight_one. rewrite INSTR1. unfold exec_load. rewrite RES.
      rewrite (areg_of_eq _ _ EQ) in *. simpl.
      erewrite H; eauto. Simpl. intuition Simpl.
  - (* Aglobal *)
    inv EV.
    destruct (symbol_bol id ofs); inv TR.
    + (* bol *)
      econstructor; split.
      eapply exec_straight_two; simpl; auto.
      rewrite INSTR3; Simpl. unfold exec_load2.
      Simpl. rewrite low_high_half. rewrite LOAD; auto.
      Simpl. intuition Simpl.
    + (* non bol *)
      exploit (lea_correct TMPA id ofs (mk1 TMPA :: k)).
      intros (rs' & EX & RES & OTH).
      econstructor; split.
      eapply exec_straight_trans. eexact EX.
      eapply exec_straight_one. rewrite INSTR1.
      unfold exec_load. rewrite RES. simpl. erewrite H; eauto.
      Simpl.
      intuition Simpl.
  - (* Ainstack *)
    inv EV. inv TR. unfold indexed_memory_access.
    destruct (Ptrofs.eq ofs Ptrofs.zero) eqn:?.
    rewrite (Ptrofs.same_if_eq ofs Ptrofs.zero Heqb) in LOAD.
    econstructor; split. apply exec_straight_one.
    rewrite INSTR1. unfold exec_load. simpl.
    change (Ptrofs.of_int Int.zero) with Ptrofs.zero.
    rewrite LOAD. reflexivity. Simpl. intuition Simpl.
    destruct (get_sconst16 (Ptrofs.to_int ofs)) eqn:?.
    econstructor; split. apply exec_straight_one.
    rewrite INSTR2. unfold exec_load.
    rewrite (get_sconst16_sound (Ptrofs.to_int ofs) s Heqo).
    rewrite Ptrofs.of_int_to_int by auto. rewrite LOAD. reflexivity.
    Simpl. intuition Simpl.
    exploit (addimm_addr_correct TMPA A10).
    intros (rs' & EX & RES & OTH).
    econstructor. split.
    eapply exec_straight_trans. eexact EX.
    eapply exec_straight_one. rewrite INSTR1.
    unfold exec_load. simpl. change (Ptrofs.of_int Int.zero) with Ptrofs.zero.
    rewrite RES. destruct (rs A10); inv LOAD. simpl.
    rewrite Ptrofs.add_zero. rewrite Ptrofs.of_int_to_int by auto.
    rewrite H1. reflexivity. Simpl. intuition Simpl.
Qed.

Lemma transl_store_access_correct:
  forall chunk
    (mk1: areg -> instruction)
    (mk2: index_reg -> sconst16 -> instruction)
    (mk3: areg -> ident -> ptrofs -> instruction)
    addr args k c r1 (rs: regset) m v m',
  (forall base rs,
     exec_instr ge fn (mk1 base) rs m = exec_store chunk rs m r1 base sconst16_zero) ->
  (forall ofs rs,
     exec_instr ge fn (mk2 SP ofs) rs m = exec_store chunk rs m r1 SP ofs) ->
  (forall (base: areg) id ofs (rs: regset),
     exec_instr ge fn (mk3 base id ofs) rs m = exec_store2 chunk rs m r1 base (low_half ge id ofs)) ->
  transl_memory_access mk1 mk2 mk3 addr args k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some v ->
  Mem.storev chunk m v rs#r1 = Some m' ->
  r1 <> PC -> r1 <> TMPA ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, r <> PC -> r <>TMPA -> rs'#r = rs#r.
Proof.
  assert (forall chunk m a v m',
             Mem.storev chunk m a v = Some m' ->
             Mem.storev chunk m (Val.offset_ptr a (Ptrofs.of_int Int.zero)) v = Some m').
  { intros. destruct a; inv H.  simpl.  rewrite Ptrofs.add_zero. auto. }
  intros until m'; intros INSTR1 INSTR2 INSTR3 TR EV STORE NOTPC NOTTMPA.
  unfold transl_memory_access in TR; destruct addr; ArgsInv.
  - (* Aindexed *)
    inv EV.
    destruct (Int.eq ofs Int.zero) eqn:?; inv EQ0.
    + econstructor; split.
      apply exec_straight_one. rewrite INSTR1. unfold exec_store.
      rewrite (areg_of_eq _ _ EQ), (Int.same_if_eq _ _ Heqb) in *.
      simpl.
      unfold Val.offset_ptr. unfold Mem.storev in *.
      destruct (rs x); inv STORE. rewrite H1. reflexivity. Simpl.
      intuition Simpl.
    +  exploit (addimm_addr_correct TMPA x); eauto with asmgen.
       intros (rs' & EX & RES & OTH).
       econstructor; split.
       eapply exec_straight_trans. eexact EX.
       eapply exec_straight_one. rewrite INSTR1. unfold exec_store. rewrite RES.
       rewrite (areg_of_eq _ _ EQ) in *. erewrite H; eauto.
       rewrite OTH; eauto with asmgen. Simpl.
       intuition Simpl.
  - (* Aglobal *)
    inv EV.
    destruct (symbol_bol id ofs); inv TR.
    + (* bol *)
      econstructor; split.
      eapply exec_straight_two; simpl; auto.
      rewrite INSTR3. unfold exec_store2. Simpl.
      rewrite low_high_half. rewrite STORE.
      reflexivity.
      Simpl. Simpl.
      intuition Simpl.
    + (* non bol *)
      exploit (lea_correct TMPA id ofs (mk1 TMPA :: k)).
      intros (rs' & EX & RES & OTH).
      econstructor; split.
      eapply exec_straight_trans. eexact EX.
      eapply exec_straight_one. rewrite INSTR1.
      unfold exec_store. rewrite RES. simpl. rewrite OTH; eauto with asmgen.
      erewrite H; eauto with asmgen. Simpl. intuition Simpl.
  - (* Ainstack *)
    inv EV. inv TR.
    unfold indexed_memory_access.
    destruct (Ptrofs.eq ofs Ptrofs.zero) eqn:?.
    rewrite (Ptrofs.same_if_eq ofs Ptrofs.zero Heqb) in STORE.
    econstructor; split. apply exec_straight_one.
    rewrite INSTR1. unfold exec_store. simpl.
    change (Ptrofs.of_int Int.zero) with Ptrofs.zero.
    rewrite STORE. reflexivity. Simpl. intuition Simpl.
    destruct (get_sconst16 (Ptrofs.to_int ofs)) eqn:?.
    econstructor; split. apply exec_straight_one.
    rewrite INSTR2. unfold exec_store.
    rewrite (get_sconst16_sound (Ptrofs.to_int ofs) s Heqo).
    rewrite Ptrofs.of_int_to_int by auto. rewrite STORE. reflexivity.
    Simpl. intuition Simpl.
    exploit (addimm_addr_correct TMPA A10).
    intros (rs' & EX & RES & OTH).
    econstructor. split.
    eapply exec_straight_trans. eexact EX.
    eapply exec_straight_one. rewrite INSTR1.
    unfold exec_store. simpl. change (Ptrofs.of_int Int.zero) with Ptrofs.zero.
    rewrite RES. destruct (rs A10); inv STORE. simpl.
    rewrite Ptrofs.add_zero. rewrite Ptrofs.of_int_to_int by auto.
    rewrite OTH; eauto with asmgen.
    rewrite H1. reflexivity. Simpl. intuition Simpl.
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
  unfold transl_load.
  intros until v; intros TR EV LOAD.
  destruct chunk; inv TR; try monadInv H0.
  5: destruct (preg_of dst); inv H0.
  all: eapply transl_load_access_correct; eauto with asmgen; ArgsInv; intros; simpl; auto.
  all: unfold valid_reg_high; rewrite H; eauto with asmgen.
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
  destruct chunk; inv TR; try monadInv H0.
  3: destruct (preg_of src) eqn:?; inv H0.
  all: eapply transl_store_access_correct; eauto with asmgen; ArgsInv; intros; simpl; auto.
Qed.

(** Function epilogues *)

Lemma free_frame_correct:
  forall ge0 f m stk soff cs m1 ms rs k j P tm,
  load_stack m (Vptr stk soff) Tptr f.(fn_link_ofs) = Some (parent_sp cs) ->
  Mem.free m stk 0 f.(fn_stacksize) = Some m1 ->
  agree_inj j ms (Vptr stk soff) rs ->
  (exists stk', j stk = Some (stk', 0)) ->
  match_stack ge0 cs ->
  tm |= minjection j m ** globalenv_inject ge0 j ** P ->
  exists rs1, exists m1',
     exec_straight ge fn (Pfreeframe f.(fn_stacksize) f.(fn_link_ofs) :: k) rs tm k rs1 m1'
  /\ agree_inj j ms (parent_sp cs) rs1
  /\ (forall r, r <> PC -> r <> SP -> r <> TMP -> r <> TMPA -> rs1#r = rs#r)
  /\ m1' |= minjection j m1 ** globalenv_inject ge0 j ** P.
Proof.
  intros until tm; intros LP FREE AG STKINJ MCS SEP.
  exploit loadv_parallel_rule. eapply sep_proj1. exact SEP. eexact LP.
  apply Val.offset_ptr_inject. apply AG.
  intros (parent' & LP' & IP').
  destruct STKINJ as (stk' & ?).
  exploit free_parallel_rule_0; eauto.
  intros (m1' & FREE' & MEXT').
  assert (rs A10 = Vptr stk' soff).
  { destruct AG. inv agree_inj_sp0.
    rewrite H in H3. inv H3.
    rewrite Ptrofs.add_zero. reflexivity. }
  econstructor; econstructor; split.
  apply exec_straight_one. simpl.
    change (chunk_of_type Tptr) with Mint32 in LP'. rewrite LP'.
    rewrite H0.
    rewrite FREE'. eauto. auto.
  split. apply agree_inj_nextinstr.
    apply agree_inj_change_sp with (Vptr stk soff).
    apply agree_inj_exten with rs; auto.
    eapply parent_sp_def; eauto.
    assumption.
  split. intros; Simpl.
  assumption.
Qed.

End CONSTRUCTORS.

Section UPPER_CTX.

Remark upper_ctx_mr_norepet:
  list_norepet upper_ctx_mr.
Proof.
  unfold upper_ctx_mr. simpl.
  econstructor; [unfold not; simpl; intuition congruence|].
  econstructor; [unfold not; simpl; intuition congruence|].
  econstructor; [unfold not; simpl; intuition congruence|].
  econstructor; [unfold not; simpl; intuition congruence|].
  econstructor; [unfold not; simpl; intuition congruence|].
  econstructor; [unfold not; simpl; intuition congruence|].
  econstructor; [unfold not; simpl; intuition congruence|].
  econstructor; [unfold not; simpl; intuition congruence|].
  econstructor; [unfold not; simpl; intuition congruence|].
  econstructor; [unfold not; simpl; intuition congruence|].
  econstructor; [unfold not; simpl; intuition congruence|].
  econstructor; [unfold not; simpl; intuition congruence|].
  constructor.
Qed.

Lemma upper_ctx_mr_regs:
  List.map preg_of upper_ctx_mr = DREG D8 :: DREG D9 :: DREG D10 :: DREG D11 :: AREG A12 :: AREG A13 :: AREG A14 :: AREG A15 :: DREG D12 :: DREG D13 :: DREG D14 :: DREG D15 :: nil.
Proof.
  unfold upper_ctx, is_auto_save, all_mregs. unfold reg_cc. reflexivity.
Qed.

Lemma upper_ctx_regs:
  upper_ctx = (PCXI :: PSW_C :: AREG SP :: AREG RA :: DREG D8 :: DREG D9 :: DREG D10 :: DREG D11 :: AREG A12 :: AREG A13 :: AREG A14 :: AREG A15 :: DREG D12 :: DREG D13 :: DREG D14 :: DREG D15 :: nil).
Proof.
  unfold upper_ctx, is_auto_save, all_mregs. unfold reg_cc. reflexivity.
Qed.

Lemma upper_ctx_regs_split:
  upper_ctx = (PCXI :: PSW_C :: AREG SP :: AREG RA :: List.map preg_of upper_ctx_mr).
Proof.
  reflexivity.
Qed.

Lemma auto_save_regs_in_upper_ctx:
  forall r, is_auto_save r = true <-> In (preg_of r) upper_ctx.
Proof.
  split; intros.
  - rewrite upper_ctx_regs.
    unfold is_auto_save in H. destruct r; simpl; (discriminate || intuition).
  - rewrite upper_ctx_regs in H. cbn in H. decompose sum H; destruct r; (discriminate || reflexivity).
Qed.

Lemma not_auto_save_regs_not_in_upper_ctx:
  forall r, is_auto_save r = false <-> ~In (preg_of r) upper_ctx.
Proof.
  unfold not. split; intros.
  - apply auto_save_regs_in_upper_ctx in H0. congruence.
  - destruct (is_auto_save r) eqn:E; auto. exfalso. apply H, auto_save_regs_in_upper_ctx; auto.
Qed.

Lemma upper_ctx_mr_size:
  Datatypes.length upper_ctx_mr = 12%nat.
Proof.
  reflexivity.
Qed.

Lemma upper_ctx_mr_not_err:
  ~ In Machregs.ErrorReg upper_ctx_mr.
Proof.
  unfold upper_ctx_mr. simpl. intuition discriminate.
Qed.

Global Opaque upper_ctx_mr.

End UPPER_CTX.
