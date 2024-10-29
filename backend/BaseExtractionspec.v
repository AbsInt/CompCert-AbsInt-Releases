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

(** RTL base extraction: relational specification *)

Require Import Coqlib Wfsimpl Maps Errors Integers.
Require Import AST Linking.
Require Import Op Registers RTL.
Require Import BaseExtraction.

(** ** Working with the state monad *)

Remark bind_inversion:
  forall (A B: Type) (f: mon A) (g: A -> mon B)
         (y: B) (s1 s3: state) (i: sincr s1 s3),
  bind f g s1 = R y s3 i ->
  exists x, exists s2, exists i1, exists i2,
  f s1 = R x s2 i1 /\ g x s2 = R y s3 i2.
Proof.
  unfold bind; intros. destruct (f s1). exists x; exists s'; exists I.
  destruct (g x s'). inv H. exists I0; auto.
Qed.

Ltac monadInv1 H :=
  match type of H with
  | (R _ _ _ = R _ _ _) =>
      inversion H; clear H; try subst
  | (ret _ _ = R _ _ _) =>
      inversion H; clear H; try subst
  | (bind ?F ?G ?S = R ?X ?S' ?I) =>
      let x := fresh "x" in (
      let s := fresh "s" in (
      let i1 := fresh "INCR" in (
      let i2 := fresh "INCR" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion _ _ F G X S S' I H) as [x [s [i1 [i2 [EQ1 EQ2]]]]];
      clear H;
      try (monadInv1 EQ2)))))))
  end.

Ltac monadInv H :=
  match type of H with
  | (ret _ _ = R _ _ _) => monadInv1 H
  | (bind ?F ?G ?S = R ?X ?S' ?I) => monadInv1 H
  | (?F _ _ _ _ _ _ _ _ = R _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ _ = R _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ = R _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ = R _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ = R _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ = R _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ = R _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ = R _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  end.

Fixpoint mlist_iter2 {A B: Type} (f: A -> B -> mon unit) (l: list (A*B)): mon unit :=
  match l with
  | nil => ret tt
  | (x,y) :: l' => do z <- f x y; mlist_iter2 f l'
  end.

Remark mlist_iter2_fold:
  forall (A B: Type) (f: A -> B -> mon unit) l s,
  exists i,
  mlist_iter2 f l s =
  R tt (fold_left (fun a p => match f (fst p) (snd p) a with R _ s2 _ => s2 end) l s) i.
Proof.
  induction l; simpl; intros.
  exists (sincr_refl s); auto.
  destruct a as [x y]. unfold bind. simpl. destruct (f x y s) as [xx s1 i1].
  destruct (IHl s1) as [i2 EQ]. rewrite EQ. econstructor; eauto.
Qed.

Lemma ptree_mfold_spec:
  forall (A: Type) (f: positive -> A -> mon unit) t s x s' i,
  ptree_mfold f t s = R x s' i ->
  exists i', mlist_iter2 f (PTree.elements t) s = R tt s' i'.
Proof.
  intros.
  destruct (mlist_iter2_fold _ _ f (PTree.elements t) s) as [i' EQ].
  unfold ptree_mfold in H. inv H. rewrite PTree.fold_spec.
  econstructor. eexact EQ.
Qed.

(** * Properties of basic operations over the state *)

(** Properties of [add_instr]. *)

Lemma add_instr_at:
  forall s1 s2 incr i n,
  add_instr i s1 = R n s2 incr -> s2.(st_code)!n = Some i.
Proof.
  intros. monadInv H. simpl. apply PTree.gss.
Qed.

Lemma add_instr_other:
  forall s1 s2 incr i n pc,
  Plt pc s1.(st_nextnode) \/ Ple s2.(st_nextnode) pc ->
  add_instr i s1 = R n s2 incr ->
  s2.(st_code)!pc = s1.(st_code)!pc.
Proof.
  intros. monadInv H0. simpl.
  rewrite PTree.gso. reflexivity.
  destruct H.
  extlia.  simpl in H. extlia.
Qed.

Lemma set_instr_at:
  forall n i s1 s2 incr u,
  set_instr n i s1 = R u s2 incr -> s2.(st_code)!n = Some i.
Proof.
  intros. unfold set_instr in H.
  inv H. simpl. apply PTree.gss.
Qed.

Remark set_instr_other:
  forall pc instr s x s' i pc',
  set_instr pc instr s = R x s' i ->
  pc' <> pc ->
  s'.(st_code)!pc' = s.(st_code)!pc'.
Proof.
  intros. monadInv H; simpl. apply PTree.gso; auto.
Qed.


Remark set_instr_same:
  forall pc instr s x s' i c,
  set_instr pc instr s = R x s' i ->
  c!(pc) = s'.(st_code)!pc ->
  c!(pc) = Some instr.
Proof.
  intros. rewrite H0. monadInv H; simpl. apply PTree.gss.
Qed.

Section BASEEXTRACTION_SPEC.

Inductive ros_ple: positive -> (reg + ident) -> Prop :=
  | ros_inl: forall max ros r,
    ros = inl r ->
    Ple r max ->
    ros_ple max ros
  | ros_inr: forall max ros r,
    ros = inr r ->
    ros_ple max ros.

Inductive tr_instr: positive -> node -> instruction -> code -> Prop :=
  | tr_nop: forall max pc c s,
    c!pc = Some (Inop s) ->
    tr_instr max pc (Inop s) c
  | tr_op: forall max pc c op args res s,
    c!pc = Some (Iop op args res s) ->
    (forall r, In r args -> Ple r max) ->
    Ple res max ->
    tr_instr max pc (Iop op args res s) c
  | tr_load: forall max pc c chunk addr args res s,
    c!pc = Some (Iload chunk addr args res s) ->
    (forall r, In r args -> Ple r max) ->
    Ple res max ->
    tr_instr max pc (Iload chunk addr args res s) c
  | tr_load_extr: forall max pc pc1 op c chunk addr addr' args dst id r ofs s,
    Some (id, ofs) = symbol_addressing addr ->
    args = nil ->
    op = symbol_op id ->
    addr' = aindexed_addr ofs ->
    c!pc = Some (Iop op nil r pc1) ->
    c!pc1 = Some (Iload chunk addr' (r :: nil) dst s) ->
    Ple dst max ->
    Plt max r ->
    tr_instr max pc (Iload chunk addr args dst s) c
  | tr_store: forall max pc c chunk addr args src s,
    c!pc = Some (Istore chunk addr args src s) ->
    (forall r, In r args -> Ple r max) ->
    Ple src max ->
    tr_instr max pc (Istore chunk addr args src s) c
  | tr_store_extr: forall max pc pc1 op c chunk addr addr' args src id r ofs s,
    Some (id, ofs) = symbol_addressing addr ->
    args = nil ->
    op = symbol_op id ->
    addr' = aindexed_addr ofs ->
    c!pc = Some (Iop op nil r pc1) ->
    c!pc1 = Some (Istore chunk addr' (r :: nil) src s) ->
    Ple src max ->
    Plt max r ->
    tr_instr max pc (Istore chunk addr args src s) c
  | tr_call: forall max pc c sg ros args res s,
    c!pc = Some (Icall sg ros args res s) ->
    ros_ple max ros ->
    (forall r, In r args -> Ple r max) ->
    Ple res max ->
    tr_instr max pc (Icall sg ros args res s) c
  | tr_tailcall: forall max pc c sg ros args,
    c!pc = Some (Itailcall sg ros args) ->
    ros_ple max ros ->
    (forall r, In r args -> Ple r max) ->
    tr_instr max pc (Itailcall sg ros args) c
  | tr_builtin: forall max pc c ef args res s,
    c!pc = Some (Ibuiltin ef args res s) ->
    (forall r, In r (params_of_builtin_args args) -> Ple r max) ->
    match res with BR r => Ple r max | _ => True end ->
    tr_instr max pc (Ibuiltin ef args res s) c
  | tr_cond: forall max pc cond args s1 s2 c,
    c!pc = Some (Icond cond args s1 s2) ->
    (forall r, In r args -> Ple r max) ->
    tr_instr max pc (Icond cond args s1 s2) c
  | tr_jumptable: forall max pc r tbl c,
    c!pc = Some (Ijumptable r tbl) ->
    Ple r max ->
    tr_instr max pc (Ijumptable r tbl) c
  | tr_return: forall max pc or c,
    match or with Some r => Ple r max | _ => True end ->
    c!pc = Some (Ireturn or) ->
    tr_instr max pc (Ireturn or) c.

Inductive tr_funbody: function -> code -> Prop :=
  | tr_funbody_intro: forall f c,
    (forall pc i, f.(fn_code)!pc = Some i -> tr_instr (max_reg_function f) pc i c) ->
    tr_funbody f c.

Lemma expand_instr_unchanged:
  forall io pc instr s x s' i pc',
  expand_instr io pc instr s = R x s' i ->
  Plt pc' s.(st_nextnode) ->
  pc' <> pc ->
  s'.(st_code)!pc' = s.(st_code)!pc'.
Proof.
  generalize set_instr_other; intros A.
  intros. unfold expand_instr in H; destruct instr; eauto.
  destruct (can_extract io a l); auto.
  monadInv H. simpl. rewrite PTree.gsspec.
  destruct (peq pc' pc); auto. extlia.
  monadInv H.
  transitivity (st_code s1)!pc'.
  eapply set_instr_other; eauto.
  transitivity (st_code s0)!pc'.
  eapply add_instr_other; eauto. left.
  monadInv EQ2. monadInv EQ1. monadInv EQ. simpl. extlia.
  monadInv EQ. simpl. auto.
  destruct (can_extract io a l); auto.
  monadInv H. simpl. rewrite PTree.gsspec.
  destruct (peq pc' pc); auto. extlia.
  monadInv H.
  transitivity (st_code s1)!pc'.
  eapply set_instr_other; eauto.
  transitivity (st_code s0)!pc'.
  eapply add_instr_other; eauto. left.
  monadInv EQ2. monadInv EQ1. monadInv EQ. simpl. extlia.
  monadInv EQ. simpl. auto.
Qed.

Lemma iter_expand_instr_unchanged:
  forall io pc l s x s' i,
  mlist_iter2 (expand_instr io ) l s = R x s' i ->
  Plt pc s.(st_nextnode) ->
  ~In pc  (List.map (@fst _ _) l) ->
  list_norepet (List.map (@fst _ _) l) ->
  s'.(st_code)!pc = s.(st_code)!pc.
Proof.
  induction l; simpl; intros.
  - (* base case *)
    monadInv H. auto.
  - (* inductive case*)
    destruct a as [pc1 instr1]; simpl in *.
    monadInv H. inv H2.
    transitivity ((st_code s0)!pc).
    eapply IHl; eauto. destruct INCR; extlia.
    eapply expand_instr_unchanged; eauto.
Qed.

Ltac inv_incr :=
  match goal with
  | [ H: sincr _ _ |- _ ] => destruct H; inv_incr
  | _ => idtac
  end.

Lemma expand_instr_spec:
  forall io max pc instr s x s' i c,
  (forall r, In r (instr_uses instr) -> Ple r max) ->
  (forall r, instr_defs instr = Some r -> Ple r max) ->
  Plt max s.(st_nextreg)  ->
  expand_instr io pc instr s = R x s' i ->
  Plt pc s.(st_nextnode) ->
  (forall pc', Ple s.(st_nextnode) pc' -> Plt pc' s'.(st_nextnode) -> c!pc' = s'.(st_code)!pc') ->
  c!pc = s'.(st_code)!pc ->
  tr_instr max pc instr c.
Proof.
  intros until c; intros LT_U LT_DE LT_NR EXP.
  generalize set_instr_same; intros BASE.
  unfold expand_instr in EXP; destruct instr eqn:?; simpl in LT_U, LT_DE.
  - econstructor. eapply BASE; eauto.
  - econstructor. eapply BASE; eauto. intros. generalize (LT_U r0 H2); intros. extlia.
    assert (Ple r max) by (apply LT_DE; auto). extlia.
  - destruct (can_extract io a l) eqn:?.
    + econstructor. eapply BASE; eauto.
      intros. generalize (LT_U r0 H2); intros. extlia.
      assert (Ple r max) by (apply LT_DE; auto). extlia.
    + monadInv EXP. inv_incr.
      intros.
      monadInv EQ1; monadInv EQ2; monadInv EQ; simpl in *.
      eapply tr_load_extr; eauto. rewrite H1. apply PTree.gss.
      rewrite H0. rewrite PTree.gsspec. destruct (peq (st_nextnode s) pc).
      subst pc. extlia.  rewrite PTree.gss; try extlia.  reflexivity. extlia. extlia.
  - destruct (can_extract io a l) eqn:?.
    + econstructor. eapply BASE; eauto. intros. apply LT_U; auto. apply LT_U. auto.
    + monadInv EXP. inv_incr.
      intros.
      monadInv EQ1; monadInv EQ2; monadInv EQ; simpl in *.
      eapply tr_store_extr; eauto. rewrite H1. apply PTree.gss.
      rewrite H0. rewrite PTree.gsspec. destruct (peq (st_nextnode s) pc).
      subst pc. extlia.  rewrite PTree.gss; try extlia.  reflexivity. extlia. extlia.
  - destruct s1 eqn:?.
    econstructor. eapply BASE; eauto.  econstructor; eauto.
    apply LT_U. simpl.  auto.
    intros. apply LT_U. simpl.  right. auto.
    apply LT_DE. auto.
    intros.
    econstructor. eapply BASE; eauto. eapply ros_inr. reflexivity.
    intros. apply LT_U. auto.
    apply LT_DE. auto.
  - destruct s1 eqn:?.
    econstructor. eapply BASE; eauto.  econstructor; eauto.
    apply LT_U. simpl.  auto.
    intros. apply LT_U. simpl.  right. auto.
    intros.
    econstructor. eapply BASE; eauto. eapply ros_inr. reflexivity.
    intros. apply LT_U. auto.
  - econstructor. eapply BASE; eauto. auto. destruct b; auto.
  - econstructor. eapply BASE; eauto. apply LT_U.
  - econstructor. eapply BASE; eauto. apply LT_U. auto.
  - destruct o. econstructor. apply LT_U. simpl. auto. eapply BASE; eauto.
    econstructor. auto. eapply BASE; eauto.
Qed.

Lemma iter_expand_instr_spec:
  forall io max l s x s' i c,
  mlist_iter2 (expand_instr io) l s = R x s' i ->
  list_norepet (List.map (@fst _ _) l) ->
  (forall pc instr, In (pc, instr) l -> Plt pc s.(st_nextnode)) ->
  (forall pc', Ple s.(st_nextnode) pc' -> Plt pc' s'.(st_nextnode) -> c!pc' = s'.(st_code)!pc') ->
  (forall pc instr, In (pc, instr) l -> c!pc = s'.(st_code)!pc) ->
  (forall pc instr, In (pc, instr) l -> (forall r, In r (instr_uses instr) -> Ple r max)) ->
  (forall pc instr, In (pc, instr) l -> (forall r, instr_defs instr = Some r -> Ple r max)) ->
  Plt max s.(st_nextreg)  ->
  forall pc instr, In (pc, instr) l -> tr_instr max pc instr c.
Proof.
  induction l; simpl; intros.
  - (* base case *)
    contradiction.
  - (* inductive case *)
  destruct a as [pc1 instr1]; simpl in *. inv H0. monadInv H. inv_incr.
  destruct H7. inv H.
  (* same pc *)
  eapply expand_instr_spec; eauto.
  intros.
    transitivity ((st_code s')!pc').
    apply H2. auto. extlia.
    eapply iter_expand_instr_unchanged; eauto. 
    red; intros.  exploit list_in_map_inv; eauto.
    intros [[pc0 instr0] [P Q]]. simpl in P.
    assert (Plt pc0 (st_nextnode s)) by eauto. extlia.
  transitivity ((st_code s')!pc).
    eapply H3; eauto.
    eapply iter_expand_instr_unchanged; eauto. 
    assert (Plt  pc (st_nextnode s)) by eauto. extlia.
  (* older pc *)
  inv_incr. eapply IHl; eauto.
  intros. eapply Pos.lt_le_trans. eapply H1. right; eauto. extlia.
  intros. apply H2; auto. extlia. extlia.
Qed.


Lemma expand_function_spec:
  forall f s x s' i c,
  expand_function f s = R x s' i ->
  (forall pc', Plt pc' s'.(st_nextnode) -> c!pc' = s'.(st_code)!pc') ->
  tr_funbody f c.
Proof.
  intros. unfold expand_function in H. monadInv H.
  econstructor. intros.
  inversion EQ.
  exploit ptree_mfold_spec; eauto. intros [INCR' ITER].
  eapply iter_expand_instr_spec; eauto.
  apply PTree.elements_keys_norepet.
  intros.
  assert (Ple pc0 (max_pc_function f)).
  eapply max_pc_function_sound. eapply PTree.elements_complete; eauto.
  inversion EQ1. simpl. monadInv EQ1. simpl. extlia.
  intros. apply H0.
    assert (Ple pc0 (max_pc_function f)).
    eapply max_pc_function_sound. eapply PTree.elements_complete; eauto.
  inv_incr.  monadInv EQ. simpl in *. extlia.
  intros.
  exploit PTree.elements_complete; eauto.  intros.
  eapply  max_reg_function_use; eauto.
  intros.
  exploit PTree.elements_complete; eauto.  intros.
  eapply max_reg_function_def; eauto.
  monadInv EQ1.
  simpl. extlia.
 apply PTree.elements_correct; auto.
Qed.

End BASEEXTRACTION_SPEC.

Inductive tr_function: function -> function -> Prop :=
  | tr_function_intro: forall f f', 
    tr_funbody f f'.(fn_code) ->
    f'.(fn_sig) = f.(fn_sig) ->
    f'.(fn_params) = f.(fn_params) ->
    f'.(fn_entrypoint) = f.(fn_entrypoint) ->
    tr_function f f'.

Lemma transf_function_spec:
  forall f,
  tr_function f (transf_function f).
Proof.
  intros.
  unfold transf_function.
  destruct (expand_function f initstate) eqn:?.
  apply tr_function_intro; simpl; auto.
  eapply expand_function_spec; eauto.
Qed.
