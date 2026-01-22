(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*             AbsInt Angewandte Informatik GmbH                       *)
(*                                                                     *)
(*  AbsInt Angewandte Informatik GmbH. All rights reserved. This file  *)
(*  is distributed under the terms of the INRIA Non-Commercial         *)
(*  License Agreement.                                                 *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib Maps Errors Integers.
Require Import AST Linking Globalenvs Values Memory.
Require Import Op Registers RTL PointerCasts1 Smallstep.
Require Compopts Machregs.
Require Import Values Builtins Events.


(* Two programs match if they agree on the names of main, public
   variables and global definitions and they agree on global variables
   and global functions of the second program are those we get from
   the first program by applying the transformation that inserts
   explicit casts for uses of pointer types. *)
Definition match_prog (prog tprog: program) :=
  match_program (fun czx f tf => tf = transf_fundef f) eq prog tprog.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. eapply match_transform_program; eauto.
Qed.

Lemma match_prog_equiv:
  forall f f', match_prog f f' <-> f' = transf_program f.
Proof.
  split; intros.
  - inv H. destruct H1 as [eq1 eq2].
    destruct f, f'; simpl in *. subst.
    unfold transf_program, transform_program.
    simpl in *. f_equal.
    induction H0; try reflexivity.
    simpl in *. unfold match_ident_globdef in H. destruct H as [eq H].
    rewrite (surjective_pairing a1), (surjective_pairing b1). rewrite <- eq in *.
    inv  H; inv H3; reflexivity.
  - rewrite H. apply transf_program_match.
Qed.

(** ** Working with the state monad *)

Remark bind_inversion:
  forall (A B: Type) (f: mon A) (g: A -> mon B)
         (y: B) (s1 s3: PointerCasts1.state) (i: sincr s1 s3),
  bind f g s1 = R y s3 i ->
  exists x, exists s2, exists i1, exists i2,
  f s1 = R x s2 i1 /\ g x s2 = R y s3 i2.
Proof.
  unfold bind; intros. destruct (f s1). exists x; exists s'; exists I.
  destruct (g x s'). inv H. exists I0; auto.
Qed.

(** Tactic to invert hypotheses containing equations between monadic expressions, i.e. 
   - the final state
   - a return expression
   - (possibly nested) binds *)
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

(** A variation of the above tactic to invert equations possibly behind a function application F. *)
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

(* All instructions other than the one at the insertion point remain unchanged. *)
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

(* All instructions other than the one that was set remain unchanged. *)
Remark set_instr_other:
  forall pc instr s x s' i pc',
  set_instr pc instr s = R x s' i ->
  pc' <> pc ->
  s'.(st_code)!pc' = s.(st_code)!pc'.
Proof.
  intros. monadInv H; simpl. apply PTree.gso; auto.
Qed.

(* Setting the same instructions results in the same code. *)
Remark set_instr_same:
  forall pc instr s x s' i c,
  set_instr pc instr s = R x s' i ->
  c!(pc) = s'.(st_code)!pc ->
  c!(pc) = Some instr.
Proof.
  intros. rewrite H0. monadInv H; simpl. apply PTree.gss.
Qed.

Section SPEC.

(* Asserts that 
   either the code at pc in the code arguments is identical to the instruction
   and does not contain any registers larger than max,
   or ensures that those instructions changed by the translation are the
   translated version.

   max designates the largest register before the program transformation.
   This is the invariant that is maintained through the transformation. *)
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
  | tr_load_extr: forall max pc pc1 c chunk n args dst r s,
    c!pc = Some (Iop Opcast args r pc1) ->
    c!pc1 = Some (Iload chunk (Aindexed n) (r :: nil) dst s) ->
    (forall r, In r args -> Ple r max) ->
    Ple dst max ->
    Plt max r ->
    tr_instr max pc (Iload chunk (Aindexed n) args dst s) c
  | tr_store: forall max pc c chunk addr args src s,
    c!pc = Some (Istore chunk addr args src s) ->
    (forall r, In r args -> Ple r max) ->
    Ple src max ->
    tr_instr max pc (Istore chunk addr args src s) c
  | tr_store_extr: forall max pc pc1 c chunk n args src r s,
    c!pc = Some (Iop Opcast args r pc1) ->
    c!pc1 = Some (Istore chunk (Aindexed n) (r :: nil) src s) ->
    (forall r, In r args -> Ple r max) ->
    Ple src max ->
    Plt max r ->
    tr_instr max pc (Istore chunk (Aindexed n) args src s) c
  | tr_call_l: forall max pc c sg r r' args res s pc'',
    c!pc = Some (Iop Opcast (r::nil) r' pc'') ->
    c!pc'' = Some (Icall sg (inl r') args res s) ->
    Ple r max ->
    (forall r, In r args -> Ple r max) ->
    Ple res max ->
    Plt max r' ->
    tr_instr max pc (Icall sg (inl r) args res s) c
  | tr_call_r: forall max pc c sg name args res s pc'',
    c!pc = Some (Inop pc'') ->
    c!pc'' = Some (Icall sg (inr name) args res s) ->
    (forall r, In r args -> Ple r max) ->
    Ple res max ->
    tr_instr max pc (Icall sg (inr name) args res s) c
  | tr_tailcall_l: forall max pc pc' c sg r r' args,
    c!pc = Some (Iop Opcast (r::nil) r' pc') ->
    c!pc' = Some (Itailcall sg (inl r') args) ->
    Ple r max ->
    Plt max r' ->
    (forall r, In r args -> Ple r max) ->
    tr_instr max pc (Itailcall sg (inl r) args) c
  | tr_tailcall_r: forall max pc pc' c sg name args,
    c!pc = Some (Inop pc') ->
    c!pc' = Some (Itailcall sg (inr name) args) ->
    (forall r, In r args -> Ple r max) ->
    tr_instr max pc (Itailcall sg (inr name) args) c
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


(* Two functions f, f' are in the tr_funbody relation 
    if we know what happens to each instruction of f after being translated (tr_instr). *)
Inductive tr_funbody: function -> function -> Prop :=
  | tr_funbody_intro: forall f f',
    (forall pc i, f.(fn_code)!pc = Some i -> tr_instr (max_reg_function f) pc i f'.(fn_code)) ->
    tr_funbody f f'.


Inductive tr_function: function -> function -> Prop :=
  | tr_function_intro: forall f f', 
    tr_funbody f f' ->
    f'.(fn_sig) = f.(fn_sig) ->
    f'.(fn_params) = f.(fn_params) ->
    f'.(fn_entrypoint) = f.(fn_entrypoint) ->
    tr_function f f'.


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

Ltac inv_incr :=
  match goal with
  | [ H: sincr _ _ |- _ ] => destruct H; inv_incr
  | _ => idtac
  end.

(* The predicate tr_instr holds for an instruction if it is transformed via add_pcast. *)
Lemma add_pcast_spec:
  (* c is the final translated code. *)
  forall max pc instr s x s' i c,
  (* all registers read (used) by the instruction are less than max *)
  (forall r, In r (instr_uses instr) -> Ple r max) ->
  (* all registers written (defined) by the instruction are less than max *)
  (forall r, instr_defs instr = Some r -> Ple r max) ->
  (* max < nextreg just means max is defined sensibly as the initial value of nextreg is max + 1. *)
  Plt max s.(st_nextreg)  ->
  (* possible insertion of pointer casts. *)
  add_pcast pc instr s = R x s' i ->
  (* pc is defined sensibly and points to something in the original code. *)
  Plt pc s.(st_nextnode) ->
  (* All instructions that were additionally inserted by the add_pcast (i.e. s.nextnode <= pc < s'.nextnode)
     stay the same from the intermediate state s' until the final transformed output c. *)
  (forall pc', Ple s.(st_nextnode) pc' -> Plt pc' s'.(st_nextnode) -> c!pc' = s'.(st_code)!pc') ->
  (* The position pc that was (possibly) overwritten by pcast 
     stays the same from the intermediate state s' until the final transformed output c. *)
  c!pc = s'.(st_code)!pc ->
  (* Finally all this means that the translation invariant holds. *)
  tr_instr max pc instr c.
Proof.
  intros until c; intros LT_U LT_DE LT_NR PCAST.
  generalize set_instr_same; intros BASE.
  unfold add_pcast in PCAST; destruct instr eqn:?; simpl in LT_U, LT_DE.
  - econstructor; eauto.
  - econstructor; eauto.
  - destruct a; intros; [ | econstructor; eauto| econstructor; eauto].
    monadInv PCAST.
    eapply tr_load_extr; eauto.
    inv_incr; cbn in *.
    monadInv EQ1. monadInv EQ. simpl in *. monadInv EQ2. simpl in *.
    erewrite H0 by extlia.
    rewrite PTree.gso by extlia.
    apply PTree.gss.
    monadInv EQ; simpl in *; inv_incr;  extlia.
  - intros. destruct a; [| econstructor; eauto| econstructor; eauto].
    monadInv PCAST.
    eapply tr_store_extr; auto; [> idtac | monadInv EQ1; monadInv EQ;  inv_incr; cbn in * ..].
    eapply BASE; try eassumption.
    monadInv EQ2; cbn in *. erewrite H0 by extlia.
    rewrite PTree.gso by extlia.
    apply PTree.gss; extlia.
    extlia.
  - destruct s1 eqn:?; monadInv PCAST; intros.
    + monadInv EQ1. monadInv EQ. inv_incr; cbn in *.
      eapply (tr_call_l _ _ _ _ _ _  _ _ _ (st_nextnode s)) ; auto.
      eapply BASE; eassumption.
      erewrite H0 by extlia.
      monadInv EQ2. inv_incr; cbn in *. rewrite PTree.gso by extlia.
      apply PTree.gss.
      extlia.
    + monadInv EQ. inv_incr; cbn in *. eapply (tr_call_r); auto.
      eapply BASE; eassumption.
      erewrite H0 by extlia.
      monadInv EQ0. inv_incr; cbn in *. rewrite PTree.gso by extlia.
      apply PTree.gss.
  - destruct s1 eqn:?; monadInv PCAST; inv_incr; simpl in *; intros.
    + monadInv EQ1. monadInv EQ; inv_incr; simpl in *.
      eapply tr_tailcall_l; eauto.
      rewrite H0 by extlia ; try assumption.
      monadInv EQ2; inv_incr; cbn in *.
      rewrite PTree.gso by extlia.
      apply PTree.gss.
    + monadInv EQ; inv_incr; cbn in *. eapply tr_tailcall_r; auto.
      eapply BASE; eassumption.
      erewrite H0 by extlia.
      monadInv EQ0; inv_incr; cbn in *.
      rewrite PTree.gso by extlia. apply PTree.gss.
  - econstructor; eauto.
    destruct b; auto.
  - econstructor; eauto.
  - econstructor; eauto.
  - destruct o; econstructor; eauto.
    apply LT_U; simpl; auto.
Qed.

(* add pcast leaves all program locations pc' that existed before the
   transformation unchanged. *)
Lemma add_pcast_unchanged:
  forall pc instr s x s' i pc',
  add_pcast pc instr s = R x s' i ->
  Plt pc' s.(st_nextnode) ->
  pc' <> pc ->
  s'.(st_code)!pc' = s.(st_code)!pc'.
Proof.
  generalize set_instr_other; intros A.
  intros. unfold add_pcast in H; destruct instr; eauto.
  - destruct a; eauto.
    monadInv H.
    transitivity (st_code s1)!pc'.
    eapply A; eauto.
    transitivity (st_code s0)!pc'.
    eapply add_instr_other; eauto. left.
    monadInv EQ. simpl. extlia.
    monadInv EQ. simpl. auto.
  - destruct a; eauto.
    monadInv H. transitivity (st_code s1)!pc'; eauto.
    transitivity (st_code s0)!pc'.
    eapply add_instr_other; eauto. left.
    monadInv EQ2. monadInv EQ1. monadInv EQ. simpl. extlia.
    monadInv EQ. simpl. auto.
  - destruct s1; monadInv H.
    monadInv EQ1; monadInv EQ2; monadInv EQ. inv_incr; simpl in *.
    rewrite PTree.gso by extlia. apply PTree.gso; extlia.
    monadInv EQ; monadInv EQ0; inv_incr; cbn in *.
    rewrite PTree.gso by extlia. apply PTree.gso; extlia.
  - destruct s1; monadInv H.
    + monadInv EQ1; monadInv EQ2; monadInv EQ; inv_incr; cbn in *.
      rewrite PTree.gso by extlia. apply PTree.gso; extlia.
    + monadInv EQ; monadInv EQ0; inv_incr; cbn in *.
      rewrite PTree.gso by extlia. apply PTree.gso; extlia.
Qed.

Lemma iter_add_pcast_unchanged:
  forall pc (l: list (node * instruction)) s x s' i,
  (* If I repeatedly apply add_pcast to a list of pc * instr pairs. *)
  mlist_iter2 (add_pcast) l s = R x s' i ->
  (* and the pc is valid for the code *)
  Plt pc s.(st_nextnode) ->
  (* and it does not appear in the list of instructions to be transformed. *)
  ~ In pc (List.map (@fst _ _) l) ->
  list_norepet (List.map (@fst _ _) l) ->
  (* Then the instruction stays unchanged. *)
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
    eapply add_pcast_unchanged; eauto.
Qed.

Lemma iter_add_pcast_spec:
  forall max (l: list (node * instruction)) s x s' i c,
  (* When applying add_pcast iteratively on a list of node * instruction pairs *)
  mlist_iter2 add_pcast l s = R x s' i ->
  (* no node is processed twice *)
  list_norepet (List.map (@fst _ _) l) ->
  (* we only transform instructions present in the initial state *)
  (forall pc instr, In (pc, instr) l -> Plt pc s.(st_nextnode)) ->
  (* all instructions added by the calls to add_pcast stay unchanged until the final transformed output c *)
  (forall pc', Ple s.(st_nextnode) pc' -> Plt pc' s'.(st_nextnode) -> c!pc' = s'.(st_code)!pc') ->
  (* all instructions set by calls to add_pcast stay unchanged until the final transformed output c *)
  (forall pc instr, In (pc, instr) l -> c!pc = s'.(st_code)!pc) ->
  (* all registers read by any instruction are below max *)
  (forall pc instr, In (pc, instr) l -> (forall r, In r (instr_uses instr) -> Ple r max)) ->
  (* all registers written to by any instruction are below max *)
  (forall pc instr, In (pc, instr) l -> (forall r, instr_defs instr = Some r -> Ple r max)) ->
  (* max is sensibly defined *)
  Plt max s.(st_nextreg)  ->
  (* for each of those the translation invariant is upheld *)
  forall pc instr, In (pc, instr) l -> tr_instr max pc instr c.
Proof.
  induction l; simpl; intros; try contradiction.
  destruct a as [pc1 instr1]; simpl in *. inv H0. monadInv H. inv_incr.
  destruct H7.
  - (* same pc *)
    inv H.
    eapply add_pcast_spec; eauto.
    + intros.
      transitivity ((st_code s')!pc').
      apply H2. auto. extlia.
      eapply iter_add_pcast_unchanged; eauto.
      red; intros.
      exploit list_in_map_inv; eauto.
      intros [[pc0 instr0] [P Q]]. simpl in P.
      assert (Plt pc0 (st_nextnode s)) by eauto. extlia.
    + transitivity ((st_code s')!pc).
      eapply H3; eauto.      
      eapply iter_add_pcast_unchanged; eauto.
      assert (Plt  pc (st_nextnode s)) by eauto. extlia.
  - (* older pc *)
    eapply IHl; eauto; try extlia.
    intros. eapply Pos.lt_le_trans. eapply H1. right; eauto. extlia.
    intros. apply H2; auto. extlia.
Qed.

(* relating a function f with its transformation f' if the code of f'
 matches the code of the final state of the transformation. *)
Lemma add_pcasts_spec:
  forall f x s' i f',
  add_pcasts f (function_state f) = R x s' i ->
  (forall pc', Plt pc' s'.(st_nextnode) -> f'.(fn_code)!pc' = s'.(st_code)!pc') ->
  tr_funbody f f'.
Proof.
  intros.
  assert (forall pc instr,
             In (pc, instr) (PTree.elements (fn_code f)) ->
             Ple pc (max_pc_function f)).
  { intros. eapply max_pc_function_sound.
    eapply PTree.elements_complete; eauto. }
  unfold add_pcasts in H.
  exploit ptree_mfold_spec; eauto. intros [INCR' ITER].
  constructor. intros.
  eapply iter_add_pcast_spec; eauto.
  - apply PTree.elements_keys_norepet.
  - intros. generalize (H1 pc0 instr H3). intros.
    simpl. extlia.
  - intros.
    generalize (H1 pc0 instr H3). intros.
    apply H0.
    inv_incr.  cbn in *. extlia.
  - intros.
    exploit PTree.elements_complete; eauto. intros.
    eapply  max_reg_function_use; eauto.
  - intros.
    exploit PTree.elements_complete; eauto. intros.
    eapply max_reg_function_def; eauto.
  - simpl. extlia.
  - apply PTree.elements_correct; auto.    
Qed.

Lemma transf_function_spec:
  forall f,
  tr_function f (transf_function f).
Proof.
  intros.
  unfold transf_function. cbn.
  apply tr_function_intro; cbn; auto.
  eapply add_pcasts_spec. reflexivity.
  cbn. reflexivity.
Qed.

End SPEC.

Section PRESERVATION.

Variable prog: program.
Variable tprog : program.
Hypothesis TRANSF: match_prog prog tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall s, Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSF).

Lemma symbols_preserved':
  forall (id: ident), (Genv.symbol_address tge id Ptrofs.zero = Genv.symbol_address ge id Ptrofs.zero).
Proof.
  intros. unfold Genv.symbol_address. rewrite symbols_preserved. reflexivity.
Qed.

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSF).

(** ** Agreement between register sets before and after type casting. *)

Definition agree_regs (max: positive) (rs rs': regset) :=
  (forall r, Ple r max -> rs#r = rs'#r)
  /\ (forall r, Plt max r -> rs#r = Vundef).

Remark Plt_Ple_dec:
  forall p q, {Plt p q} + {Ple q p}.
Proof.
  intros. destruct (plt p q). left; auto. right; extlia.
Qed.

(** ** Forward simulation *)

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
   match_stackframe_intro:
      forall res sp pc rs f rs',
      agree_regs (max_reg_function f) rs rs' ->
      Ple res (max_reg_function f) ->
      tr_funbody f (transf_function f) ->
      match_stackframes
        (Stackframe res f sp pc rs)
        (Stackframe res (transf_function f) sp pc rs').

Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_states_intro:
      forall s sp pc rs m f s' rs'
           (FB: tr_funbody f (transf_function f))
           (STACKS: list_forall2 match_stackframes s s')
           (AG: agree_regs (max_reg_function f) rs rs'),
      match_states (State s f sp pc rs m)
                    (State s' (transf_function f) sp pc rs' m)
  | match_states_call:
    forall s f args m s'
      (STACKS: list_forall2 match_stackframes s s'),
      match_states (Callstate s f args m)
                     (Callstate s' (transf_fundef f) args m)
  | match_states_return:
      forall s v m s'
        (STACKS: list_forall2 match_stackframes s s'),
      match_states (Returnstate s v m)
        (Returnstate s' v m).

Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f -> Genv.find_funct_ptr tge b = Some (transf_fundef f).
Proof.
  intros. exploit (Genv.find_funct_ptr_match TRANSF); eauto.
  intros (cu & tf & A & B & C). subst tf. assumption.
Qed.

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = funsig f.
Proof.
  destruct f; reflexivity.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state (RTL.semantics prog) st1 -> exists st2, initial_state (RTL.semantics tprog) st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated; eauto.  intros FIND.
  exists (Callstate nil (transf_fundef f) nil m0); split.
  - econstructor; eauto.
    eapply (Genv.init_mem_match TRANSF); auto.
    replace (prog_main tprog) with (prog_main prog).
    rewrite symbols_preserved. eauto.
    symmetry; eapply match_program_main; eauto.
    rewrite <- H3. apply sig_preserved.
  - eapply match_states_call. constructor.     
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state (RTL.semantics prog) st1 r -> final_state (RTL.semantics tprog )st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS.
  constructor.
Qed.

Lemma tr_funbody_inv:
  forall  f f' pc i,
  tr_funbody f f' -> f.(fn_code)!pc = Some i -> tr_instr (max_reg_function f) pc i f'.(fn_code).
Proof.
  intros. inv H. eauto.
Qed.

Lemma agree_set_reg:
  forall max rs rs' r v ,
  agree_regs max rs rs' ->
  Ple r max ->
  agree_regs max (rs#r <- v) (rs'#r <- v).
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  repeat rewrite Regmap.gsspec.
  destruct (peq r0 r); auto.
  rewrite Regmap.gso. auto. extlia.
Qed.

Lemma agree_set_reg_other:
  forall max rs rs' r v,
  agree_regs max rs rs' ->
  Plt max r ->
  agree_regs max rs (rs'#r <- v).
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  rewrite Regmap.gsspec. destruct (peq r0 r); try extlia.
  apply H. auto. rewrite H1; auto.
Qed.

Lemma lookup_arg_eq(rs rs': regset) r max: Ple r max -> agree_regs max rs rs' -> rs' # r = rs # r.
Proof.
  intros H AG. destruct AG as [AG _]. symmetry. now apply AG.
Qed.

Lemma lookup_args_eq  (rs rs': Regmap.t val) (args: list reg) max:  (forall r : reg, List.In r args -> Ple r max) ->  agree_regs max rs rs' ->  rs' ## args = rs ## args.
Proof.
  intros H AG.
  eapply map_ext_in.
  intros p IN. eapply lookup_arg_eq; eauto.
Qed.

Lemma functions_translated:
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof.
  intros. exploit (Genv.find_funct_match TRANSF); eauto.
  intros (cu & tf & A & B & C). now subst tf.
Qed.

Lemma find_function_eq_l:
  forall r r' rs rs' f,
  rs # r = rs' # r' -> 
  find_function ge (inl r) rs = Some f ->
  find_function tge (inl r') rs' = Some (transf_fundef f).
Proof.
  intros. eapply functions_translated.
  fold fundef in *.
  rewrite <- H. auto.
Qed.

Lemma find_function_eq_r:
  forall name rs rs' f,
  find_function ge (inr name) rs = Some f -> 
  find_function tge (inr name) rs' = Some (transf_fundef f).
Proof.
  intros. simpl in *. rewrite symbols_preserved.
  fold fundef in *.
  destruct (Genv.find_symbol ge name); try discriminate.
  apply function_ptr_translated; auto.
Qed.

Lemma find_function_exists_pcast_eq:
  forall r rs fd,
  find_function ge (inl r) rs = Some fd -> 
  Val.pcast (rs # r) = (rs # r).
Proof.
  simpl. unfold Genv.find_funct, Val.pcast. intros. destruct (rs # r); congruence.
Qed.

Lemma eval_builtin_arg_preserved':
  forall max rs rs' v v' m arg,
    (forall r, In r (params_of_builtin_arg arg) -> Ple r max) ->
    agree_regs max rs rs'  ->
    eval_builtin_arg ge (fun r => rs # r) v m arg v' ->
    eval_builtin_arg ge (fun r => rs' # r) v m arg v'.
Proof.
  intros. destruct H0 as [H0 H'0]. induction H1; try now constructor; cbn in *.
  - rewrite H0; cbn in H;  eauto. constructor.
  - simpl in *. constructor; auto using in_or_app.
  - simpl in *. constructor; auto using in_or_app.
Qed.

Lemma in_params_of_builtin_args:
  forall A p arg args,
    In arg args ->
    In p (params_of_builtin_arg arg) ->
    In p (@params_of_builtin_args A args).
Proof.
  intros. unfold params_of_builtin_args. induction args; cbn in *; auto.
  apply in_or_app. inv H; auto.
Qed.    
  
Lemma eval_builtin_args_preserved':
  forall max rs rs' v m args vals,
    (forall r, In r (params_of_builtin_args args) -> Ple r max) ->
    agree_regs max rs rs' ->
    eval_builtin_args ge (fun r => rs # r) v m args vals ->
    eval_builtin_args tge (fun r => rs' # r) v m args vals.
Proof.
  intros. eapply eval_builtin_args_preserved.
  exact symbols_preserved.
  unfold eval_builtin_args in *. eapply list_forall2_imply; try eassumption.
  intros. eapply eval_builtin_arg_preserved'; try eassumption. intros. apply H.
  eapply in_params_of_builtin_args; eassumption.
Qed.

Lemma notin_init_regs:
  forall r vals regs,
  ~ In r regs -> 
  (init_regs vals regs) # r = Vundef.
Proof.
  intros. revert vals. induction regs; auto.
  - cbn in *. destruct vals; auto.
    rewrite PMap.gso by auto.
    auto.
Qed.
  
Theorem step_simulation:
  forall S1 t S2,
  step (RTL.semantics prog) ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  (exists S2', plus (step (RTL.semantics tprog)) tge S1' t S2' /\ match_states S2 S2').
Proof.
  intros S1 t S2 H. simpl in *. inv H; intros; inv MS.
  - (* nop *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  eexists; split. eapply plus_one. eapply exec_Inop; eauto.
  eapply match_states_intro; eauto.
- (* op *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  assert (EV: eval_operation ge sp op rs'##args m = Some v).
  { erewrite eval_operation_vals_ext; eauto. eapply lookup_args_eq; eassumption. }
  eexists; split.
  eapply plus_one. eapply exec_Iop; eauto.
  erewrite eval_operation_preserved by exact symbols_preserved. eassumption.
  eapply match_states_intro; eauto.
  eapply agree_set_reg; eauto.
- (* load *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  + (* no changes *)
    eexists; split.
    eapply plus_one. eapply exec_Iload; eauto.
    erewrite eval_addressing_preserved.
    erewrite eval_addressing_values_ext; try eassumption.
    eapply lookup_args_eq; try eassumption.
    exact symbols_preserved.
    eapply match_states_intro; eauto. eapply agree_set_reg; eauto.
  + (* pointer cast *)
    apply eval_addressing_indexed_inv in H1 as (v' & eq1 & eq2).
    eexists; split.
    eapply plus_two.
    eapply exec_Iop; eauto. apply (lookup_args_eq _ _ args) in AG; auto.
    rewrite AG. simpl. rewrite eq2. reflexivity.
    eapply exec_Iload; eauto.
    erewrite eval_addressing_preserved by exact symbols_preserved.
    simpl. rewrite Regmap.gss. rewrite eq1. f_equal.
    unfold Val.pcast. destruct v'; reflexivity.
    reflexivity.
    eapply match_states_intro; eauto.
    eapply agree_set_reg; eauto.
    eapply agree_set_reg_other; eauto.
- (* store *)
   exploit tr_funbody_inv; eauto. intros TR; inv TR.
   + (* no changes *)
     eexists; split.
     eapply plus_one.
     eapply exec_Istore; eauto.
     erewrite eval_addressing_preserved.
     erewrite eval_addressing_values_ext; try eassumption.
     eapply lookup_args_eq; eassumption.
     exact symbols_preserved.
     erewrite <- H2. destruct AG as [AG AG']. f_equal. rewrite AG; auto.
     eapply match_states_intro; eauto.
   + (* pointer cast *)
     eapply eval_addressing_indexed_inv in H1 as (v1 & eq1 & eq2).
     eexists; split.
     eapply plus_two.
     eapply exec_Iop with (op := Opcast); try eassumption.
     apply (lookup_args_eq _ _ args) in AG; auto.
     rewrite AG. cbn. rewrite eq2. reflexivity.
     eapply exec_Istore; eauto.
     erewrite eval_addressing_preserved by exact symbols_preserved.
     simpl.  rewrite Regmap.gss. reflexivity.
     rewrite <- H2. f_equal.
     rewrite eq1. destruct v1; reflexivity.
     rewrite Regmap.gso by extlia.
     eapply lookup_arg_eq; eassumption.
     reflexivity.
     eapply match_states_intro; eauto.
     eapply agree_set_reg_other; eauto.
- (* call *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  + eexists; split.
    eapply plus_left'.
    eapply exec_Iop; try eassumption.
    reflexivity.
    eapply plus_one.
    eapply exec_Icall; try eassumption.
    eapply find_function_eq_l; try eassumption.
    rewrite PMap.gss.
    erewrite (lookup_arg_eq rs rs'); try eassumption.
    symmetry. eapply find_function_exists_pcast_eq; eassumption.
    eapply sig_preserved.
    reflexivity.
    replace (rs ## args) with (rs' # r' <- (Val.pcast rs' # r) ## args).
    eapply match_states_call. eapply list_forall2_cons; auto.
    constructor; try assumption.
    eapply agree_set_reg_other; auto.
    eapply lookup_args_eq; eauto.
    eapply agree_set_reg_other; assumption.
  + eexists. split.
    eapply plus_left'.
    eapply exec_Inop. eassumption.
    eapply plus_one. eapply exec_Icall; try eassumption.
    eapply find_function_eq_r; eauto.
    apply sig_preserved.
    reflexivity.
    erewrite <- lookup_args_eq; eauto.
    eapply match_states_call. eapply list_forall2_cons; eauto.
    constructor; assumption.
-  (* tailcall *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  + eexists; split.
    eapply plus_left'.
    eapply exec_Iop; try eassumption.
    reflexivity.
    eapply plus_one. eapply exec_Itailcall; try eassumption.
    eapply find_function_eq_l; try eassumption.
    rewrite PMap.gss. erewrite (lookup_arg_eq rs rs'); try eassumption.
    symmetry. eapply find_function_exists_pcast_eq; eassumption.
    eapply sig_preserved.
    reflexivity.
    replace (rs ## args) with (rs' # r' <- (Val.pcast rs' # r) ## args).
    eapply match_states_call. assumption.
    eapply lookup_args_eq; eauto. eapply agree_set_reg_other; auto.
  + eexists; split.
    eapply plus_left'.
    eapply exec_Inop; eauto.
    eapply plus_one. eapply exec_Itailcall; try eassumption.
    eapply find_function_eq_r; try eassumption.
    apply sig_preserved.
    reflexivity.
    erewrite <- lookup_args_eq; try eassumption.
    eapply match_states_call. assumption.
- (* Ibuiltin *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  eexists; split.
  eapply plus_one.
  eapply exec_Ibuiltin; eauto.
  eapply eval_builtin_args_preserved'; eassumption.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  eapply match_states_intro; eauto.
  destruct res; simpl; eauto.
  eapply agree_set_reg; eauto.
-  (* Icond *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  eexists; split.
  eapply plus_one. eapply exec_Icond; eauto.
  erewrite lookup_args_eq; eauto.
  econstructor; eauto.
- (* Ijumptable *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  econstructor; split.
  eapply plus_one. eapply exec_Ijumptable; eauto.
  erewrite lookup_arg_eq; eauto.
  econstructor; eauto.
- (* Ireturn *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exists (Returnstate s' (regmap_optget or Vundef rs') m'); split.
  eapply plus_one.
  eapply exec_Ireturn; eauto. destruct or.
  simpl. erewrite <- lookup_arg_eq; eauto.
  constructor; assumption.
  constructor. assumption.
- (* internal function *)
  eexists; split.
  eapply plus_one.
  eapply exec_function_internal; simpl; eauto.
  simpl. econstructor; eauto.
  generalize (transf_function_spec f). intros.
  inv H; auto.
  unfold agree_regs. split. intros; auto.
  intros. apply notin_init_regs. red. intros.
  apply max_reg_function_params in H2. extlia.
- (* external function *)
  simpl. econstructor; split. eapply plus_one.
  eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constructor; auto.
- (* return *)
  inversion STACKS. inv H1.
  eexists; split. 
  eapply plus_one.
  eapply exec_return; eauto.
  econstructor; eauto.
  apply agree_set_reg; auto.
Qed.

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_plus.
  - apply senv_preserved.
  - eexact transf_initial_states.
  - eexact transf_final_states.
  - eexact step_simulation.
Qed.

End PRESERVATION.

