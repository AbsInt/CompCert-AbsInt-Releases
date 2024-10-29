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

(** Machine- and ABI-dependent layout information for activation records. *)

Require Import Coqlib.
Require Import Memory Separation.
Require Import Bounds.
Require Import AST Machregs.
Require Import Ordered OrderedType.
Require Import Conventions1.
Require Import FunInd.

(** The general shape of activation records is as follows,
  from bottom (lowest offsets) to top:
- Space for outgoing arguments to function calls.
- Pointer to activation record of the caller.
- Saved return address into caller.
- Local stack slots.
- Saved values of callee-save registers used by the function.
- Space for the stack-allocated data declared in Cminor.

The [frame_env] compilation environment records the positions of
the boundaries between areas in the frame part.
*)
Open Scope Z.

Definition fe_ofs_arg := 0.

(** Computation of the frame environment from the bounds of the current
  function. *)

Module RegOrd := OrderedIndexed(IndexedMreg).
Module RegOrdFacts := OrderedTypeFacts(RegOrd).

Definition valid_pair (r1 r2: mreg) :=
  match r1, r2 with
  | F17, F16 | F19, F18 | F21, F20
  | F23, F22 | F25, F24 | F27, F26
  | F29, F28 | F31, F30 => true
  | _, _ => false
  end.

Function split_floats (acc: list (list (rpair mreg))) (l: list mreg) {measure length l}: list (list (rpair mreg)) :=
  match l with
  | r1 :: r2 :: l => if valid_pair r2 r1
                    then match acc with
                         | (Two a2 a1 :: al) :: acc => if  Pos.eq_dec (Pos.succ(IndexedMreg.index a2)) (IndexedMreg.index r1)
                                                      then split_floats (((Two r2 r1) :: (Two a2 a1) :: al) :: acc) l
                                                      else split_floats ((Two r2 r1 :: nil) :: (Two a2 a1 :: al) :: acc) l
                         | _ => split_floats ((Two r2 r1 :: nil) :: acc) l
                         end
                    else split_floats ((One r1 :: nil) :: acc) (r2 :: l)
  | r :: nil => rev (map (@rev (rpair mreg)) ((One r :: nil) :: acc))
  | nil => rev (map (@rev (rpair mreg)) acc)
  end.
Proof.
  all: intros; simpl; lia.
Qed.



Definition length_sufficient (len: nat) := lt_dec (if Archi.thumb2_support then 3 else 2) len.

Definition consecutive_exec_constraint (il: list mreg) (fl: list mreg_group) ofs:=
  match fl with
  | (Multiple rl) :: nil => length_sufficient (length rl + 1) && length_sufficient (length il) && Z.eq_dec ofs (align ofs 8)
  | _ => false
  end.

Fixpoint reg_list_offset l ofs :=
  match l with
  | r :: l => let sz := typesize (mreg_type r) in reg_list_offset l ((align ofs sz) + sz)
  | nil => ofs
  end.

Definition unroll_floats (l: list (rpair mreg)) : list mreg_group :=
  let spl := fun p => match p with
                   | One r => Single r
                   | p => Multiple (p :: nil)
                   end in
  map spl l.

Fixpoint collect_floats (l: list (list (rpair mreg))) : (list mreg_group) :=
  match l with
  | hd :: l => if length_sufficient (length hd) then Multiple hd :: collect_floats l else unroll_floats hd ++ collect_floats l
  | _ => nil
  end.

Definition split_used_callee_save (rl: list mreg) (ofs: Z) :=
  let (mfl, mil) := partition Conventions1.is_float_reg rl in
  let fl := collect_floats (split_floats nil mfl) in
  if consecutive_exec_constraint mil fl (reg_list_offset mil ofs) then
    default_callee_save mil ++ fl
  else
    let int_regs := if length_sufficient (length mil) then Multiple (map (fun r => One r) mil) :: nil else default_callee_save mil in
    int_regs ++ fl.

Remark unroll_floats_correspond:
  forall l, flatten_group_list (unroll_floats l) = l.
Proof.
  induction l; simpl; auto.
  destruct a; simpl; rewrite IHl; auto.
Qed.

Remark split_floats_correspond:
  forall l r acc,
    In r (regs_of_rpairs (concat (split_floats acc l))) <-> In r l \/ In r (regs_of_rpairs (concat acc)).
Proof.
  intros. functional induction (split_floats acc l); simpl; try (rewrite IHl0; simpl; intuition auto with datatypes).
  - simpl. rewrite !in_regs_of_rpairs. split.
    + intros (p & A & B). rewrite in_concat in A. destruct A as (x & A1 & A2).
      rewrite in_app in A1.
      destruct A1.
      * right. exists p. split; auto. apply in_concat. rewrite <- in_rev in H. rewrite in_map_iff in H. destruct H as (x' & H & H').
        exists x'. inv H. split; auto. apply in_rev; auto.
      * left. simpl in H. inv H; auto. inv A2; auto.
    + intros [A | (p & A & B)].
      * destruct A; try contradiction. subst r. exists (One r0).
        simpl. split; auto. apply in_concat. exists (One r0 :: nil). split; simpl; auto with datatypes.
      * exists p. split; auto. apply in_concat in A as (l' & A & A'). apply in_concat. exists (rev l'). split. rewrite in_app. left.
        rewrite <- in_rev. rewrite in_map_iff. exists l'. split; auto. rewrite <- in_rev; auto.
  - rewrite !in_regs_of_rpairs. split.
    + intros (p & A & B). right. exists p.
      rewrite in_concat in *. destruct A as (l' & A & A'). rewrite <- in_rev in A. rewrite in_map_iff in A.
      destruct A as (l'' & A & A''). split; auto. exists l''. subst l'. split; auto. apply in_rev; auto.
    + intros [|(p & A & B)]; try contradiction. rewrite in_concat in A. destruct A as (l & A & A').
      exists p. split; auto. apply in_concat. exists (rev l); split. rewrite <- in_rev. apply in_map_iff. exists l; auto.
      rewrite <- in_rev; auto.
Qed.

Remark collect_floats_correspond:
  forall l r,
    In r (regs_of_rpairs (flatten_group_list (collect_floats l))) <-> In r (regs_of_rpairs (concat l)).
Proof.
  induction l; intros; simpl; try tauto.
  destruct (length_sufficient); simpl.
  - rewrite !regs_of_rpairs_app, !in_app. rewrite IHl; intuition.
  - rewrite flatten_group_app, !regs_of_rpairs_app, !in_app. rewrite IHl. rewrite unroll_floats_correspond. intuition.
Qed.

Lemma simple_correspond:
  forall (l: list mreg), (regs_of_rpairs (map (fun r0 => One r0) l)) = l.
Proof.
  induction l; intros; simpl; auto; rewrite IHl; auto.
Qed.

Remark valid_pair_wf:
  forall r1 r2,
    valid_pair r1 r2 = true -> pair_wf (Two r1 r2).
Proof.
  destruct r1, r2; simpl; intuition congruence.
Qed.

Lemma split_floats_wellformed:
  forall l p acc,
  In p (concat (split_floats acc l)) -> pair_wf p \/ In p (concat acc).
Proof.
  intros. functional induction (split_floats acc l).
  - apply IHl0 in H; auto. destruct H; auto. simpl in H. destruct H; auto. subst p. left. apply valid_pair_wf; auto.
  - apply IHl0 in H; auto. destruct H; auto. simpl in H. destruct H; auto. subst p. left. apply valid_pair_wf; auto.
  - apply IHl0 in H; auto. destruct H; auto. simpl in H. destruct H; auto. subst p. left. apply valid_pair_wf; auto.
  - apply IHl0 in H; auto. destruct H; auto. simpl in H. destruct H; auto. subst p. left. simpl; auto.
  - simpl in H. apply in_concat in H as (l' & A & B). rewrite in_app in A.
    destruct A. rewrite <- in_rev in H. apply in_map_iff in H as (l'' & A & A''). subst l'. right.
    apply in_concat. exists l''. split; auto. apply in_rev; auto.
    simpl in H. destruct H; try contradiction. subst l'. simpl in B. intuition. subst p. simpl. left; auto.
  - right. rewrite in_concat in *. destruct H as (l & A & B). rewrite <- in_rev in A. apply in_map_iff in A as (l' & A & A').
    exists l'; split; auto. subst l. apply in_rev; auto.
Qed.

Lemma collect_floats_wellformed:
  forall l p,
    (In p (concat l) -> pair_wf p) ->
    In p (flatten_group_list (collect_floats l)) -> pair_wf p.
Proof.
  induction l; intros; simpl; try contradiction.
  simpl in H, H0.
  repeat match goal with
  | [H:context [if ?X then _ else _] |- _ ] => let E := fresh "E" in destruct X eqn:E
  end; destruct (in_dec (@rpair_eq _ mreg_eq) p a); simpl in H0.
  - rewrite in_app in H0. apply H; auto with datatypes.
  - rewrite in_app in H0. destruct H0. contradiction. apply IHl; intuition auto with datatypes.
  - apply H; auto with datatypes.
  - rewrite flatten_group_app, in_app, unroll_floats_correspond in H0. destruct H0. contradiction.
    apply IHl; intuition auto with datatypes.
Qed.

Lemma trivial_map_wellformed:
  forall l p, In p (map (fun r => One r) l) -> pair_wf p.
Proof.
  induction l; simpl; intros. inv H. intuition auto.
  subst p; simpl; auto.
Qed.

Lemma callee_save_wellformed:
  forall p l ofs, In p (flatten_group_list (split_used_callee_save l ofs)) -> pair_wf p.
Proof.
  unfold split_used_callee_save; intros. destruct (partition) eqn:E.
  repeat match goal with
  | [H:context [if ?X then _ else _] |- _ ] => let E := fresh "E" in destruct X eqn:E
  | [H: context [flatten_group_list (_ ++ _)] |- _ ] => rewrite flatten_group_app in H
  | [H: context [In _ (_ ++ _)] |- _ ] => rewrite in_app in H
  | [H: _ \/ _ |- _] => simpl in H; destruct H
  end; try contradiction.
  - eapply default_callee_save_wellformed; eauto.
  - eapply collect_floats_wellformed. intros. exploit (split_floats_wellformed l0); eauto. intros.
    destruct H1; auto. instantiate (1:= nil) in H1. contradiction. auto.
  - eapply trivial_map_wellformed; eauto.
  - eapply collect_floats_wellformed. intros. exploit (split_floats_wellformed l0); eauto. intros.
    destruct H1; auto. instantiate (1:= nil) in H1. contradiction. auto.
  - eapply default_callee_save_wellformed; eauto.
  - eapply collect_floats_wellformed. intros. exploit (split_floats_wellformed l0); eauto. intros.
    destruct H1; auto. instantiate (1:= nil) in H1. contradiction. auto.
Qed.

Lemma callee_save_correspond:
  forall l r ofs, In r (regs_of_rpairs (flatten_group_list (split_used_callee_save l ofs))) <-> In r l.
Proof.
  intros. unfold split_used_callee_save. destruct (partition) eqn:E.
  repeat match goal with
  | [|-context [if ?X then _ else _]] => let E := fresh "E" in destruct X eqn:E
  end; rewrite flatten_group_app, regs_of_rpairs_app, in_app; rewrite elements_in_partition with (l := l); eauto.
  - rewrite default_callee_save_correspond. rewrite collect_floats_correspond, split_floats_correspond. intuition contradiction.
  - simpl. rewrite app_nil_r. rewrite simple_correspond. rewrite collect_floats_correspond, split_floats_correspond. intuition contradiction.
  - rewrite default_callee_save_correspond. rewrite collect_floats_correspond, split_floats_correspond. intuition contradiction.
Qed.

Definition make_env (b: bounds) :=
  let olink := 4 * b.(bound_outgoing) in  (* back link*)
  let ora := olink + 4 in (* return address *)
  let ol := align (ora + 4) 8 in    (* locals *)
  let ocs := ol + 4 * b.(bound_local) in (* callee-saves *)
  let ostkdata := align (size_callee_save_area_rec (flatten_group_list (split_used_callee_save (b.(used_callee_save)) ocs)) ocs) 8 in (* retaddr *)
  let sz := align (ostkdata + b.(bound_stack_data)) 8 in
  {| fe_size := sz;
     fe_ofs_link := olink;
     fe_ofs_retaddr := ora;
     fe_ofs_local := ol;
     fe_ofs_callee_save := ocs;
     fe_stack_data := ostkdata;
     fe_used_callee_save := split_used_callee_save (b.(used_callee_save)) ocs |}.

(** Separation property *)

Local Open Scope sep_scope.

Lemma frame_env_separated:
  forall b sp m P,
  let fe := make_env b in
  m |= range sp 0 (fe_stack_data fe) ** range sp (fe_stack_data fe + bound_stack_data b) (fe_size fe) ** P ->
  m |= range sp (fe_ofs_local fe) (fe_ofs_local fe + 4 * bound_local b)
       ** range sp fe_ofs_arg (fe_ofs_arg + 4 * bound_outgoing b)
       ** range sp (fe_ofs_link fe) (fe_ofs_link fe + 4)
       ** range sp (fe_ofs_retaddr fe) (fe_ofs_retaddr fe + 4)
       ** range sp (fe_ofs_callee_save fe) (size_callee_save_area fe (fe_ofs_callee_save fe))
       ** P.
Proof.
Local Opaque Z.add Z.mul sepconj range.
  intros; simpl.
  set (olink := 4 * b.(bound_outgoing));
  set (ora := olink + 4);
  set (ol := align (ora + 4) 8);
  set (ocs := ol + 4 * b.(bound_local));
  set (ostkdata := align (size_callee_save_area fe ocs) 8).
  generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
  assert (0 <= olink) by (unfold olink; lia).
  assert (olink <= ora) by (unfold ora; lia).
  assert (ora + 4 <= ol) by (apply align_le; lia).
  assert (ol + 4 * b.(bound_local) <= ocs) by (unfold ocs; lia).
  assert (ocs <= size_callee_save_area fe ocs) by apply size_callee_save_area_incr.
  assert (size_callee_save_area fe ocs <= ostkdata) by (apply align_le; lia).
(* Reorder as:
     outgoing
     back link
     retaddr
     local
     callee-save *)
  rewrite sep_swap12.
  rewrite sep_swap23.
  rewrite sep_swap34.
(* Apply range_split and range_split2 repeatedly *)
  unfold fe_ofs_arg.
  apply range_split. lia.
  apply range_split. lia.
  apply range_split_2. fold ol; lia. lia.
  apply range_split. lia.
  apply range_drop_right with ostkdata. lia.
  eapply sep_drop2. eexact H.
Qed.

Lemma frame_env_range:
  forall b,
  let fe := make_env b in
  0 <= fe_stack_data fe /\ fe_stack_data fe + bound_stack_data b <= fe_size fe.
Proof.
  intros; simpl.
  set (olink := 4 * b.(bound_outgoing));
  set (ora := olink + 4);
  set (ol := align (ora + 4) 8);
  set (ocs := ol + 4 * b.(bound_local)).
  set (ostkdata := align (size_callee_save_area fe ocs) 8).
  generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
  assert (0 <= olink) by (unfold olink; lia).
  assert (olink <= ora) by (unfold ora; lia).
  assert (ora + 4 <= ol) by (apply align_le; lia).
  assert (ol + 4 * b.(bound_local) <= ocs) by (unfold ocs; lia).
  assert (ocs <= size_callee_save_area fe ocs) by apply size_callee_save_area_incr.
  assert (size_callee_save_area fe ocs <= ostkdata) by (apply align_le; lia).
  split. unfold size_callee_save_area in *.
  repeat (lia || eapply Z.le_trans; eauto).
  apply align_le; lia.
Qed.

Lemma frame_env_aligned:
  forall b,
  let fe := make_env b in
     (8 | fe_ofs_arg)
  /\ (8 | fe_ofs_local fe)
  /\ (8 | fe_stack_data fe)
  /\ (4 | fe_ofs_link fe)
  /\ (4 | fe_ofs_retaddr fe).
Proof.
  intros; simpl.
  set (olink := 4 * b.(bound_outgoing));
  set (ora := olink + 4);
  set (ol := align (ora + 4) 8);
  set (ocs := ol + 4 * b.(bound_local));
  set (ostkdata := align (size_callee_save_area fe ocs) 8).
  split. apply Z.divide_0_r.
  split. apply align_divides; lia.
  split. apply align_divides; lia.
  unfold ora, olink; auto using Z.divide_mul_l, Z.divide_add_r, Z.divide_refl.
Qed.
