(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(* A solver for subtyping constraints. *)

From Coq Require Import Recdef.
Require Import Coqlib Maps Errors.
Require Import Integers AST.

Local Open Scope nat_scope.
Local Open Scope error_monad_scope.

(** This module provides a solver for sets of subtyping constraints of the
  following kinds: [base-type <: T(x)] or [T(x) <: base-type] or [T(x) <: T(y)].
  The unknowns are the types [T(x)] of every identifier [x]. *)

(** The interface for base types and the subtyping relation. *)

(** The constraint solver. *)
Module S.

Definition default: ptype := Ptyp Tint.

(* The current set of constraints is represented by a record with two components:
- [te_typ]: a partial map from variables to pairs [tlo, thi]
  of types, representing the low and high bounds for this variable.
- [te_sub]: a list of pairs [(x,y)] of variables, indicating that
  the type of [x] must be a subtype of the type of [y].
 *)
(* Atm the preferred one is always the lower bound so sometimes we use ptr even
   though it is not necessary. *)
Inductive bound_type : ptype -> ptype -> Type :=
  | bound_refl : forall (t: ptype), bound_type t t
  | bound_ptr: bound_type Pptr (Ptyp Tptr).

Lemma bound_type_sub:
  forall ty1 ty2, bound_type ty1 ty2 -> subptype ty1 ty2.
Proof.
  intros.
  destruct ty1, ty2; inv H.
  apply subptype_refl.
  apply subptype_pptr_tptr.
  apply subptype_refl.
Qed.

Lemma sub_bound_type:
  forall ty1 ty2, subptype ty1 ty2 -> bound_type ty1 ty2.
Proof.
  intros.
  destruct ty1, ty2; inv H.
  destruct (typ_eq t t0) as [->|]; [|discriminate].
  apply bound_refl.
  generalize bound_ptr. unfold Tptr.
  destruct t, Archi.ptr64 eqn:SF; cbn in *; try discriminate; auto.
  apply bound_refl.
Qed.

Lemma bound_type_low:
  forall ty, bound_type (low_bound ty) ty.
Proof.
  intros. apply sub_bound_type.
  apply low_bound_subptype.
Qed.

Lemma bound_type_high:
  forall ty, bound_type ty (high_bound ty).
Proof.
  intros. apply sub_bound_type.
  apply high_bound_subptype.
Qed.

Lemma bound_type_trans:
  forall ty1 ty2 ty3, bound_type ty1 ty2 -> bound_type ty2 ty3 -> bound_type ty1 ty3.
Proof.
  intros. inv H; inv H0; constructor.
Qed.

Inductive bounds := B (lo hi: ptype) (SUB: bound_type lo hi).

Definition brefl (t: ptype) : bounds := B t t (bound_refl t).
Definition bptr : bounds := B Pptr (Ptyp Tptr) bound_ptr.
Definition blow (t: ptype): bounds := B t (high_bound t) (bound_type_high t).
Definition bhigh (t: ptype): bounds := B (low_bound t) t (bound_type_low t).

Definition proj_lo (b: bounds) := 
  let '(B lo hi _) := b in lo.

Definition proj_hi (b: bounds) := 
  let '(B lo hi _) := b in hi.

Definition match_bounds_bool (ty: ptype) (b: bounds) := subptype_dec (proj_lo b) ty && subptype_dec ty (proj_hi b).
Definition match_bounds (ty: ptype) (b: bounds) := subptype (proj_lo b) ty /\ subptype ty (proj_hi b).

(** Some technical lemmas about the relationship of match_bounds, bounds projections and ptype projections. *)

Lemma eq_lo_blow:
  forall ty, S.proj_lo (S.blow ty) = ty.
Proof.
  reflexivity.
Qed.

Lemma eq_hi_blow:
  forall ty, S.proj_hi (S.blow ty) = high_bound ty.
Proof.
  destruct_ptype ty; reflexivity.
Qed.

Lemma eq_hi_bhigh:
  forall ty, S.proj_hi (S.bhigh ty) = ty.
Proof.
  reflexivity.
Qed.

Lemma eq_lo_bhigh:
  forall ty, S.proj_lo (S.bhigh ty) = low_bound ty.
Proof.
  destruct_ptype ty; reflexivity.
Qed.

Lemma eq_lo_brefl:
  forall ty, S.proj_lo (S.brefl ty) = ty.
Proof.
  reflexivity.
Qed.

Lemma eq_hi_brefl:
  forall ty, S.proj_hi (S.brefl ty) = ty.
Proof.
  reflexivity.
Qed.

Lemma list_forall2_match_blow_lo:
  forall xs ys, 
  list_forall2 S.match_bounds xs (map S.blow ys) ->
  list_forall2 subptype xs (map high_bound ys).
Proof.
  induction xs; destruct ys; cbn; intros; inv H.
  - constructor.
  - destruct H3.
    constructor.
    rewrite eq_hi_blow in H0. assumption.
    auto.
Qed.

Lemma list_forall2_match_blow_hi:
  forall xs ys, 
  list_forall2 S.match_bounds xs (map S.blow ys) ->
  list_forall2 subptype ys xs.
Proof.
  induction xs; destruct ys; cbn; intros; inv H.
  - constructor.
  - destruct H3.
    constructor.
    rewrite eq_lo_blow in H. assumption.
    auto.
Qed.

Global Hint Resolve list_forall2_match_blow_lo list_forall2_match_blow_hi : ty.

Lemma match_lo:
  forall ty b, S.match_bounds ty b -> subptype (S.proj_lo b) ty.
Proof. intros. apply H. Qed.

Lemma match_hi:
  forall ty b, S.match_bounds ty b -> subptype ty (S.proj_hi b).
Proof. intros. apply H. Qed.

Lemma match_brefl:
  forall ty1 ty2,
  S.match_bounds ty1 (S.brefl ty2) -> ty1 = ty2.
Proof.
  intros. unfold S.brefl, S.match_bounds in H.
  cbn in H. destruct H.
  apply subptype_antisymmetric; assumption.
Qed.

Lemma match_brefl_lo:
  forall ty1 ty2,
  S.match_bounds ty1 (S.brefl ty2) ->
  subptype ty2 ty1.
Proof.
  intros. rewrite (match_brefl _ _ H). apply subptype_refl.
Qed.

Lemma match_brefl_hi:
  forall ty1 ty2,
  S.match_bounds ty1 (S.brefl ty2) ->
  subptype ty1 ty2.
Proof.
  intros. rewrite (match_brefl _ _ H). apply subptype_refl.
Qed.

Lemma match_blow_hi:
  forall ty1 ty2, 
  S.match_bounds ty1 (S.blow ty2) ->
  subptype ty1 (high_bound ty2).
Proof.
  intros.
  destruct H.
  rewrite eq_hi_blow in H0. assumption.
Qed.

Lemma match_blow_lo:
  forall ty1 ty2, 
  S.match_bounds ty1 (S.blow ty2) ->
  subptype ty2 ty1.
Proof.
  intros.
  destruct H.
  rewrite eq_lo_blow in H. assumption.
Qed.

Lemma match_bhigh_lo:
  forall ty1 ty2, 
  S.match_bounds ty1 (S.bhigh ty2) ->
  subptype (low_bound ty2) ty1.
Proof.
  intros.
  destruct H.
  rewrite eq_lo_bhigh in H. assumption.
Qed.

Lemma match_bhigh_hi:
  forall ty1 ty2, 
  S.match_bounds ty1 (S.bhigh ty2) ->
  subptype ty1 ty2.
Proof.
  intros.
  destruct H.
  rewrite eq_hi_bhigh in H0. assumption.
Qed.

Global Hint Resolve match_brefl_hi match_brefl_lo match_brefl match_bhigh_hi match_bhigh_lo match_blow_hi match_blow_lo : ty.
Global Hint Extern 2 (subptype (S.proj_lo ?ty1) ?ty2) => simple apply match_lo : ty.
Global Hint Extern 2 (subptype ?ty1 (S.proj_hi ?ty2)) => simple apply match_hi : ty.

Definition constraint : Type := (positive * positive)%type.

Record typenv : Type := Typenv {
  te_typ: PTree.t bounds;    (**r mapping var -> low & high bounds *)
  te_sub: list constraint    (**r additional subtyping constraints *)
}.

Definition initial : typenv := {| te_typ := PTree.empty _; te_sub := nil |}.


Definition add_bound (e: typenv) (x: positive) (b: bounds): res typenv.
  refine (
      match e.(te_typ)!x with
      | None =>
          OK {| te_typ := PTree.set x b e.(te_typ);
                te_sub := e.(te_sub) |}
      | Some (B lo1 hi1 bt1) => 
          let '(B lo hi bt) := b in
          _ 
      end).
  destruct bt1 eqn:E1, bt eqn:E. 
  - destruct (ptype_eq t t0).
    exact (OK e). 
    exact (Error (MSG "add_bound: refl/refl inconsistent" :: nil)).
  - destruct (ptype_eq t Pptr).
    exact (OK e). 
    destruct (ptype_eq t (Ptyp Tptr)).
    exact (OK e).
    exact (Error (MSG "add_bound: refl/ptr inconsistent" :: nil)).
  - destruct (ptype_eq t Pptr).
    exact (OK {| te_typ := PTree.set x b e.(te_typ); 
                 te_sub := e.(te_sub) |}).
    destruct (ptype_eq t (Ptyp Tptr)).
    exact (OK {| te_typ := PTree.set x b e.(te_typ); 
                 te_sub := e.(te_sub) |}).
    exact (Error (MSG "add_bound: ptr/refl inconsistent" :: nil)).
  - exact (OK e).
Defined.

Fixpoint add_bounds (e: typenv) (rl: list positive) (bl: list bounds) {struct rl}: res typenv :=
  match rl, bl with
  | nil, nil => OK e
  | r::rs, b::bs => do e1 <- add_bound e r b; add_bounds e1 rs bs
  | _, _ => Error (msg "arity mismatch")
  end.   

Definition type_move (e: typenv) (r1 r2: positive) : res (bool * typenv).
Proof.
  refine(
  if peq r1 r2 then OK (false, e) else
  match e.(te_typ)!r1, e.(te_typ)!r2 with
  | None, None =>
      OK (false, {| te_typ := e.(te_typ); te_sub := (r1, r2) :: e.(te_sub) |})
  | Some(B lo1 hi1 bt1), None =>
  (* Technically we could just use "high_bound lo1" here since "high_bound lo = high_bound hi"
     in the current design of subtyping. But we use it just to be safe if we change subtyping in the future. *)
      let bt2 := bound_type_trans _ _ _ bt1 (bound_type_high hi1) in
      let b2 := B lo1 (high_bound hi1) bt2 in
      OK (true, {| te_typ := PTree.set r2 b2 e.(te_typ);
                   te_sub := if subptype_dec hi1 lo1 then e.(te_sub)
                             else (r1, r2) :: e.(te_sub) |})
  | None, Some(B lo2 hi2 bt2) =>
      let bt1 := bound_type_trans _ _ _ (bound_type_low lo2) bt2 in
      let b1 := B (low_bound lo2) hi2 bt1 in
      OK (true, {| te_typ := PTree.set r1 b1 e.(te_typ);
                   te_sub := if subptype_dec hi2 lo2 then e.(te_sub)
                             else (r1, r2) :: e.(te_sub) |})
  | Some(B lo1 hi1 bt1), Some(B lo2 hi2 bt2) => _
  end).
  destruct bt1 eqn:E1, bt2 eqn:E2.
  - (* Both are restricted to a single type. Check if they are equal. *)
    destruct (ptype_eq t t0).
    exact (OK (false, e)).
    exact (Error (MSG "type_move: refl/refl inconsistent" :: nil)).
  - (* 1. is restricted, 2. is between ptr and int.
      If first is ptr there is nothing left to do,
      if first is int, restrict second to int.
      otherwise error. *) 
    destruct (ptype_eq t Pptr).
    exact (OK (false, e)).
    destruct (ptype_eq t (Ptyp Tptr)).
    exact (OK (true, {| te_typ := PTree.set r2 (brefl (Ptyp Tptr)) e.(te_typ); 
                         te_sub := e.(te_sub) |})).
    exact (Error (MSG "type_move: refl/ptr inconsistent" :: nil)).
  - (* 1. is between ptr and int, 2. is restricted.
      If second is ptr, restrict first to ptr
      if second is int, nothing to do
      otherwise error. *)
    destruct (ptype_eq t Pptr).
    exact (OK (true, {| te_typ := PTree.set r1 (brefl Pptr) e.(te_typ); 
                         te_sub := e.(te_sub) |})).
    destruct (ptype_eq t (Ptyp Tptr)).
    exact (OK (false, e)).
    exact (Error (MSG "type_move: ptr/refl inconsistent" :: nil)).
  - (* 1. and 2. are between ptr and int. nothing to do but put constraint back into list. *)
    exact (OK (false, {| te_typ := e.(te_typ); te_sub := (r1, r2) :: e.(te_sub) |})).
Defined.
    
Fixpoint type_subs_rr (e: typenv) (rrs: list (positive * positive)): res typenv :=
  match rrs with
  | nil => OK e
  | (r1, r2)::rrs => do (changed, e1) <- type_move e r1 r2; 
                     type_subs_rr e1 rrs
  end. 

(** Solve the remaining subtyping constraints by iteration. *)

Fixpoint solve_rec (e: typenv) (changed: bool) (q: list constraint) : res (typenv * bool) :=
  match q with
  | nil =>
      OK (e, changed)
  | (r1, r2) :: q' =>
      do (changed1, e1) <- type_move e r1 r2; solve_rec e1 (changed || changed1) q'
  end. 

(** Measuring the state *)

(* Define a simple measure over bounds that gets smaller the more specific they get.
   We later show that type_move will always either return changed = false, or decrease 
   the measure of one of the bounds to argue that the solve algorithm terminates. *)
Definition weight_bounds (ob: option bounds) : nat :=
  match ob with 
  | None => 2
  | Some(B lo hi bt) => 
    match bt with
    | bound_refl _ => 0
    | bound_ptr => 1
    end
  end.

Lemma weight_bounds_1:
  forall b, weight_bounds (Some b) < weight_bounds None.
Proof.
  intros. destruct b as [?? []]; cbn; lia. 
Qed.

Lemma weight_type_move:
  forall e r1 r2 changed e',
  type_move e r1 r2 = OK (changed, e') ->
  (* We add at most one constraint *)
  (e'.(te_sub) = e.(te_sub) \/ e'.(te_sub) = (r1, r2) :: e.(te_sub))
  (* We make the bounds monotonically stricter.  *)
  /\ (forall r, weight_bounds e'.(te_typ)!r <= weight_bounds e.(te_typ)!r)
  (* If one of the bounds was made stricted, then the weight strictly monotonically decreases. *)
  /\ (changed = true ->
        weight_bounds e'.(te_typ)!r1 + weight_bounds e'.(te_typ)!r2
        < weight_bounds e.(te_typ)!r1 + weight_bounds e.(te_typ)!r2).
Proof.
  unfold type_move; intros. 
  destruct (peq r1 r2) as [->|]. 
  inv H. split; auto. split; intros. lia. discriminate.
  destruct (te_typ e)!r1 as [[lo1 hi1 s1]|] eqn:E1;
  destruct (te_typ e)!r2 as [[lo2 hi2 s2]|] eqn:E2.
  - destruct s1 eqn:Es1, s2 eqn:Es2.
    + destruct (ptype_eq t t0); inv H.
      split; auto. split; intros. lia. discriminate.
    + destruct (ptype_eq t Pptr); [|destruct (ptype_eq t (Ptyp Tptr))]; inv H.
      * split; auto. split; intros. lia. discriminate.
      * split; auto. split; intros. 
        cbn. destruct (peq r2 r) as [->|].
        rewrite PTree.gss, E2. cbn. lia. rewrite PTree.gso; auto.
        cbn. rewrite (@PTree.gso _ r1), (@PTree.gss _ r2); auto.
        rewrite E1. cbn. lia.
    + destruct (ptype_eq t Pptr); [|destruct (ptype_eq t (Ptyp Tptr))]; inv H.
      * split; auto. split; intros; cbn.
        destruct (peq r1 r) as [->|].
        rewrite PTree.gss, E1.
        cbn. lia.
        rewrite PTree.gso; auto.
        rewrite (@PTree.gso _ r2), (@PTree.gss _ r1); auto.
        rewrite E2. cbn. lia.
      * split; auto. split; intros. lia. discriminate.
    + inv H.
      split; auto. split; intros; cbn; try lia.
  - inv H. simpl.
    split; auto.
    destruct (subptype_dec hi1 lo1); auto.
    split; intros.
    + destruct (peq r2 r) as [->|].
      * rewrite E2, PTree.gss.
        specialize (weight_bounds_1 (B lo1 (high_bound hi1) (bound_type_trans _ _ _ s1 (bound_type_high hi1)))).
        lia.
      * rewrite PTree.gso; auto.
    + rewrite (@PTree.gso _ r1), (@PTree.gss _ r2); auto.
      rewrite E1.
      specialize (weight_bounds_1 (B lo1 (high_bound hi1) (bound_type_trans _ _ _ s1 (bound_type_high hi1)))).
      simpl.
      lia.
  - inv H. cbn [te_typ te_sub].
    split; auto.
    destruct (subptype_dec hi2 lo2); auto.
    split; intros.
    + destruct (peq r1 r) as [->|].
      * rewrite E1, PTree.gss.
        specialize (weight_bounds_1 (B (low_bound lo2) hi2 (bound_type_trans _ _ _ (bound_type_low lo2) s2))).
        lia.
      * rewrite PTree.gso; auto.
    + rewrite (@PTree.gso _ r2), (@PTree.gss _ r1); auto.
      rewrite E2.
      specialize (weight_bounds_1 (B (low_bound lo2) hi2 (bound_type_trans _ _ _ (bound_type_low lo2) s2))).
      lia.
  - inv H. cbn [te_typ te_sub].
    split; auto.
    split; intros; lia.
Qed.

Definition weight_constraints (b: PTree.t bounds) (cstr: list constraint) : nat :=
  List.fold_right (fun xy n => n + weight_bounds b!(fst xy) + weight_bounds b!(snd xy)) 0 cstr.

Remark weight_constraints_tighter:
  forall b1 b2, (forall r, weight_bounds b1!r <= weight_bounds b2!r) ->
  forall q, weight_constraints b1 q <= weight_constraints b2 q.
Proof.
  induction q; simpl. lia. generalize (H (fst a)) (H (snd a)); lia.
Qed.

Lemma weight_solve_rec:
  forall q e changed e' changed',
  solve_rec e changed q = OK (e', changed') ->
  (forall r, weight_bounds e'.(te_typ)!r <= weight_bounds e.(te_typ)!r) 
   /\ weight_constraints e'.(te_typ) e'.(te_sub) + (if changed' && negb changed then 1 else 0)
      <= weight_constraints e.(te_typ) e.(te_sub) + weight_constraints e.(te_typ) q.
Proof.
  induction q; simpl; intros.
- inv H. split. intros; lia. replace (changed' && negb changed') with false.
  lia. destruct changed'; auto.
- destruct a as [r1 r2]; monadInv H; simpl.
  rename x into changed1. rename x0 into e1.
  exploit weight_type_move; eauto. intros [A [B C]].
  exploit IHq; eauto. intros [D E].
  split. 
  + intros. eapply Nat.le_trans. eapply D. eapply B.
  + assert (P: weight_constraints (te_typ e1) (te_sub e) <= weight_constraints (te_typ e) (te_sub e))
      by (apply weight_constraints_tighter; auto).
    assert (Q: weight_constraints (te_typ e1) (te_sub e1) <=
                weight_constraints (te_typ e1) (te_sub e) +
                weight_bounds (te_typ e1)!r1 + weight_bounds (te_typ e1)!r2).
    { destruct A as [Q|Q]; rewrite Q. lia. simpl. lia. }
    assert (R: weight_constraints (te_typ e1) q <= weight_constraints (te_typ e) q)
    by (apply weight_constraints_tighter; auto).
    set (ch1 := if changed' && negb (changed || changed1) then 1 else 0) in *.
    set (ch2 := if changed' && negb changed then 1 else 0) in *.
    destruct changed1.
    assert (ch2 <= ch1 + 1).
    { unfold ch2, ch1. rewrite orb_true_r. simpl. rewrite andb_false_r.
      destruct (changed' && negb changed); lia. }
    exploit C; eauto. lia.
    assert (ch2 <= ch1).
    { unfold ch2, ch1. rewrite orb_false_r. lia. }
    generalize (B r1) (B r2); lia.
Qed.

Definition weight_typenv (e: typenv) : nat :=
  weight_constraints e.(te_typ) e.(te_sub).

(** Iterative solving of the remaining constraints *)
Function solve_constraints (e: typenv) {measure weight_typenv e}: res typenv :=
  match solve_rec {| te_typ := e.(te_typ); te_sub := nil |} false e.(te_sub) with
  | OK(e', false) => OK e                   (**r no more changes, fixpoint reached *)
  | OK(e', true)  => solve_constraints e'   (**r one more iteration *)
  | Error msg => Error msg
  end.
Proof.
  intros. exploit weight_solve_rec; eauto. simpl. intros [A B].
  unfold weight_typenv. lia.
Qed. 

Definition typassign := positive -> ptype.

Definition makeassign (e: typenv) : typassign :=
   fun x => match e.(te_typ)!x with 
            | Some(B lo hi _) => lo
            | None => default end.

Definition solve (e: typenv) : res typassign :=
  do e' <- solve_constraints e; OK(makeassign e').

                                
(** What it means to be a solution *)

Definition satisf (te: typassign) (e: typenv) : Prop :=
   (forall x lo hi s, e.(te_typ)!x = Some(B lo hi s) -> subptype lo (te x) /\ subptype (te x) hi)
/\ (forall x y, In (x, y) e.(te_sub) -> subptype (te x) (te y)).

Lemma satisf_initial: forall te, satisf te initial.
Proof.
  unfold initial; intros; split; simpl; intros.
  rewrite PTree.gempty in H; discriminate.
  contradiction.
Qed.

(** Soundness proof *)
Lemma add_bound_incr:
  forall te x b e e', add_bound e x b = OK e' -> satisf te e' -> satisf te e.
Proof.
  unfold add_bound; intros. 
  destruct (te_typ e)!x as [[lo1 hi1 s1]|] eqn:E.
  - destruct b as [lo hi s].
    destruct s1 eqn:Es1, s eqn:Es.
    destruct (ptype_eq t t0); inv H; auto.
    destruct (ptype_eq t Pptr); inv H; auto.
    destruct (ptype_eq t (Ptyp Tptr)); inv H2; auto.
    destruct (ptype_eq t Pptr);
      [|destruct (ptype_eq t (Ptyp Tptr))]; inv H.
    + destruct H0 as [P Q]; split; auto; intros.
      destruct (peq x x0).
      subst x0. rewrite E in H. inv H.
      edestruct (P x) as [P1 P2]. cbn.
      rewrite PTree.gss. reflexivity.
      split. assumption.
      eapply subptype_trans. eassumption.
      apply subptype_pptr_tptr.
      eapply P. cbn.
      rewrite PTree.gso; auto.
      eassumption.
    + destruct H0 as [P Q]; split; auto; intros.
      destruct (peq x x0).
      subst x0. rewrite E in H. inv H.
      edestruct (P x) as [P1 P2]. cbn.
      rewrite PTree.gss. reflexivity.
      split.
      eapply subptype_trans; [apply subptype_pptr_tptr|]; auto.
      auto. eapply P. cbn.
      rewrite PTree.gso; auto.
      eassumption.
    + inv H. exact H0.
  - monadInv H.
    destruct H0 as [P Q]; split; auto; intros.
    destruct (peq x x0).
    + subst x0. congruence.
    + eapply P. cbn.
      rewrite PTree.gso. eassumption.
      congruence.
Qed.

Global Hint Resolve add_bound_incr: ty.

Lemma add_bounds_incr:
  forall te xl bl e e', S.add_bounds e xl bl = OK e' -> S.satisf te e' -> S.satisf te e.
Proof.
  induction xl; destruct bl; simpl; intros; monadInv H; eauto with ty.
Qed.

Global Hint Resolve add_bounds_incr: ty.

Lemma add_bound_sound:
  forall te x b e e', add_bound e x b = OK e' -> satisf te e' -> match_bounds (te x) b.
Proof.
  unfold add_bound; intros. 
  destruct b as [lo hi s]; cbn. destruct H0 as [P Q].
  destruct (te_typ e)!x as [[lo1 hi1 s1]|] eqn:E.
  - destruct s1 eqn:Es1, s eqn:Es.
    + destruct (ptype_eq t t0); inv H.
      eapply (P x); eauto.
    + destruct (ptype_eq t Pptr);
      [|destruct (ptype_eq t (Ptyp Tptr))]; inv H.
      edestruct (P x) as [Hlo Hhi]. eassumption.
      split; eauto with ty.
      edestruct (P x) as [Hlo Hhi]. eassumption.
      split; eauto with ty.
    + destruct (ptype_eq t Pptr); 
      [|destruct (ptype_eq t (Ptyp Tptr))]; inv H; cbn in *.
      edestruct (P x) as [Hlo Hhi].
      apply PTree.gss.
      split; eauto with ty.
      edestruct (P x) as [Hlo Hhi].
      apply PTree.gss.
      split; eauto with ty.
    + inv H. 
      edestruct (P x) as [Hlo Hhi]. eassumption.
      split; eauto with ty.
  - inv H. cbn in *.
    edestruct (P x) as [Hlo Hhi].
    apply PTree.gss.
    split; eauto with ty.
Qed.

Lemma add_bound_sound_lo:
  forall te x b e e', add_bound e x b = OK e' -> satisf te e' -> subptype (proj_lo b) (te x).
Proof.
  apply add_bound_sound.
Qed. 

Lemma add_bound_sound_hi:
  forall te x b e e', add_bound e x b = OK e' -> satisf te e' -> subptype (te x) (proj_hi b).
Proof.
  apply add_bound_sound.
Qed.

Lemma add_bounds_sound:
  forall te xl bl e e', add_bounds e xl bl = OK e' -> satisf te e' -> list_forall2 match_bounds (map te xl) bl.
Proof.
  induction xl; destruct bl; simpl; intros; monadInv H; constructor; eauto.
  eapply add_bound_sound; eauto with ty.
Qed.

Global Hint Resolve add_bound_sound add_bounds_sound : ty.


Lemma type_move_incr:
  forall te e r1 r2 e' changed,
  type_move e r1 r2 = OK (changed, e') -> satisf te e' -> satisf te e.
Proof.
  unfold type_move; intros. destruct H0 as [P Q].
  destruct (peq r1 r2). inv H; split; auto.
  destruct (te_typ e)!r1 as [[lo1 hi1 s1]|] eqn:E1;
  destruct (te_typ e)!r2 as [[lo2 hi2 s2]|] eqn:E2.
  - destruct s1 eqn:Es1, s2 eqn:Es2.
    + destruct (ptype_eq t t0); inv H.
      split; auto.
    + destruct (ptype_eq t Pptr); [|destruct (ptype_eq t (Ptyp Tptr))]; inv H.
      * split; auto.
      * split; auto; intros.
        destruct (peq r2 x) as [->|].
        rewrite H in E2. inv E2.
        edestruct (P x). cbn.
        apply PTree.gss. split; eauto.
        eapply subptype_trans. apply subptype_pptr_tptr.
        assumption.
        eapply (P x). cbn.
        rewrite PTree.gso; auto.
        eassumption.
    + destruct (ptype_eq t Pptr); [|destruct (ptype_eq t (Ptyp Tptr))]; inv H.
      * split; auto; intros.
        destruct (peq r1 x) as [->|].
        rewrite H in E1. inv E1.
        edestruct (P x). cbn.
        apply PTree.gss. split; auto.
        eapply subptype_trans. eassumption. apply subptype_pptr_tptr.
        eapply (P x). cbn.
        rewrite PTree.gso; auto.
        eassumption.
      * split; auto.
    + inv H. split; auto; intros.
      eapply (Q x y). cbn. right. assumption.
  - inv H.
    split; auto; intros.
    + destruct (peq r2 x) as [->|].
      congruence.
      eapply (P x). cbn.
      rewrite PTree.gso; auto.
      eassumption.
    + eapply (Q x y). cbn.
      destruct (subptype_dec hi1 lo1).
      assumption.
      right. assumption.
  - inv H.
    split; auto; intros.
    + destruct (peq r1 x) as [->|].
      congruence.
      eapply (P x). cbn.
      rewrite PTree.gso; auto.
      eassumption.
    + eapply (Q x y). cbn.
      destruct (subptype_dec hi2 lo2).
      assumption.
      right. assumption.
  - inv H. split; auto; intros.
    eapply (Q x y). cbn.
    right. assumption.
Qed.

Global Hint Resolve type_move_incr: ty.

Lemma type_move_sound:
  forall te e r1 r2 e' changed,
  type_move e r1 r2 = OK (changed, e') -> satisf te e' -> subptype (te r1) (te r2).
Proof.
  unfold type_move; intros. destruct H0 as [P Q].
  destruct (peq r1 r2) as [->|]. 
  apply subptype_refl.
  destruct (te_typ e)!r1 as [[lo1 hi1 s1]|] eqn:E1;
  destruct (te_typ e)!r2 as [[lo2 hi2 s2]|] eqn:E2.
  - destruct s1 eqn:Es1, s2 eqn:Es2.
    + destruct (ptype_eq t t0); inv H.
      edestruct (P r1 _ _ _ E1) as [P11 P12].
      edestruct (P r2 _ _ _ E2) as [P21 P22].
      eapply subptype_trans; eauto.
    + destruct (ptype_eq t Pptr); [|destruct (ptype_eq t (Ptyp Tptr))]; inv H.
      * edestruct (P r1 _ _ _ E1) as [P11 P12].
        edestruct (P r2 _ _ _ E2) as [P21 P22].
        eapply subptype_trans; eauto.
      * edestruct (P r1) as [P11 P12].
        cbn. rewrite PTree.gso; auto. eassumption.
        edestruct (P r2) as [P21 P22].
        cbn. apply PTree.gss.
        eapply subptype_trans; eauto.
    + destruct (ptype_eq t Pptr); [|destruct (ptype_eq t (Ptyp Tptr))]; inv H.
      * edestruct (P r1) as [P11 P12].
        cbn. apply PTree.gss.
        edestruct (P r2) as [P21 P22].
        cbn. rewrite PTree.gso; auto. eassumption.
        eapply subptype_trans; eauto.
      * edestruct (P r1 _ _ _ E1) as [P11 P12].
        edestruct (P r2 _ _ _ E2) as [P21 P22].
        eapply subptype_trans; eauto.
    + inv H.
      eapply Q. left. reflexivity.
  - inv H.
    destruct (subptype_dec hi1 lo1) as [H|H].
    + edestruct (P r1) as [P11 P12].
      cbn. rewrite PTree.gso; auto. eassumption.
      edestruct (P r2) as [P21 P22].
      cbn. apply PTree.gss.
      eapply subptype_trans; eauto.
      eapply subptype_trans; eauto.
    + eapply Q. cbn. left. reflexivity.
  - inv H.
    destruct (subptype_dec hi2 lo2) as [H|H].
    + edestruct (P r1) as [P11 P12].
      cbn. apply PTree.gss.
      edestruct (P r2) as [P21 P22].
      cbn. rewrite PTree.gso; auto. eassumption.
      eapply subptype_trans; eauto.
      eapply subptype_trans; eauto.
    + eapply Q. cbn. left. reflexivity.
  - inv H. 
    eapply Q. cbn. left. reflexivity.
Qed.

Lemma type_subs_rr_incr:
  forall te rrs e e',
  type_subs_rr e rrs = OK e' -> satisf te e' -> satisf te e.
Proof.
  induction rrs as [|[r1 r2] rrs]; simpl; intros; monadInv H; eauto with ty.
Qed.

Global Hint Resolve type_subs_rr_incr: ty.

Lemma type_subs_rr_sound:
  forall te rrs e e',
  type_subs_rr e rrs = OK e' -> satisf te e' -> Forall (fun '(r1, r2) => subptype (te r1) (te r2)) rrs.
Proof.
  induction rrs as [|[r1 r2] rrs]; simpl; intros; monadInv H.
  constructor.
  constructor; eauto. eapply type_move_sound; eauto with ty.
Qed.

Global Hint Resolve type_move_sound type_subs_rr_sound : ty.

Lemma solve_rec_incr:
  forall te q e changed e' changed',
  solve_rec e changed q = OK(e', changed') -> satisf te e' -> satisf te e.
Proof.
  induction q; simpl; intros.
- inv H. auto.
- destruct a as [r1 r2]; monadInv H. eauto with ty.
Qed.

Lemma solve_rec_sound:
  forall te r1 r2 q e changed e' changed',
  solve_rec e changed q = OK(e', changed') -> In (r1, r2) q -> satisf te e' ->
  subptype (te r1) (te r2).
Proof.
  induction q; simpl; intros.
- contradiction.
- destruct a as [r3 r4]; monadInv H. destruct H0.
  + inv H. eapply type_move_sound; eauto. eapply solve_rec_incr; eauto.
  + eapply IHq; eauto with ty.
Qed.

Lemma type_move_false:
  forall e r1 r2 e',
  type_move e r1 r2 = OK (false, e') ->
  te_typ e' = te_typ e /\ subptype (makeassign e r1) (makeassign e r2).
Proof.
  unfold type_move; intros.
  destruct (peq r1 r2). inv H. split. reflexivity. apply subptype_refl.
  destruct (te_typ e)!r1 as [[lo1 hi1 s1]|] eqn:E1;
  destruct (te_typ e)!r2 as [[lo2 hi2 s2]|] eqn:E2.
  - destruct s1 eqn:Es1, s2 eqn:Es2.
    + destruct (ptype_eq t t0); inv H.
      split. reflexivity.
      unfold makeassign. rewrite E1, E2. apply subptype_refl.
    + destruct (ptype_eq t Pptr); [|destruct (ptype_eq t (Ptyp Tptr))]; inv H.
      split. reflexivity.
      unfold makeassign. rewrite E1, E2. apply subptype_refl.
    + destruct (ptype_eq t Pptr); [|destruct (ptype_eq t (Ptyp Tptr))]; inv H.
      split. reflexivity.
      unfold makeassign. rewrite E1, E2. apply subptype_pptr_tptr.
    + inv H.
      split. reflexivity.
      unfold makeassign. rewrite E1, E2. apply subptype_refl.
  - inv H.
  - inv H.
  - inv H.
    split. reflexivity.
    unfold makeassign. rewrite E1, E2. apply subptype_refl.
Qed.

Lemma solve_rec_false:
  forall r1 r2 q e changed e',
  solve_rec e changed q = OK(e', false) ->
  changed = false /\
  (In (r1, r2) q -> subptype (makeassign e r1) (makeassign e r2)).
Proof.
  induction q; simpl; intros.
- inv H. tauto.
- destruct a as [r3 r4]; monadInv H.
  exploit IHq; eauto. intros [P Q].
  destruct changed; try discriminate. destruct x; try discriminate.
  exploit type_move_false; eauto. intros [U V].
  split. auto. intros [A|A]. inv A. auto. exploit Q; auto.
  unfold makeassign; rewrite U; auto.
Qed.

Lemma solve_constraints_incr:
  forall te e e', solve_constraints e = OK e' -> satisf te e' -> satisf te e.
Proof.
  intros te e; functional induction (solve_constraints e); intros.
- inv H. auto.
- exploit solve_rec_incr; eauto. intros [A B].
  split; auto. intros; eapply solve_rec_sound; eauto.
- discriminate.
Qed.

Lemma solve_constraints_sound:
  forall e e', solve_constraints e = OK e' -> satisf (makeassign e') e'.
Proof.
  intros e0; functional induction (solve_constraints e0); intros.
- inv H. split; intros.
  + unfold makeassign; rewrite H. split.
    apply subptype_refl.
    apply bound_type_sub. assumption.
  + exploit solve_rec_false. eauto. intros [A B]. eapply B; eauto.
- eauto.
- discriminate.
Qed.

Theorem solve_sound:
  forall e te, solve e = OK te -> satisf te e.
Proof.
  unfold solve; intros. monadInv H.
  eapply solve_constraints_incr. eauto. eapply solve_constraints_sound; eauto.
Qed.

Definition type_expect (e: typenv) (ty: ptype) (b: bounds): res typenv :=
  if match_bounds_bool ty b then OK e else Error(msg "unexpected type").

Remark type_expect_incr:
  forall e b ty e' te, type_expect e ty b = OK e' -> satisf te e' -> satisf te e.
Proof.
  unfold type_expect; intros. destruct (match_bounds_bool ty b); inv H. auto.
Qed.

Global Hint Resolve type_expect_incr: ty.

Lemma type_expect_sound:
  forall e b ty e', type_expect e ty b = OK e' -> match_bounds ty b.
Proof.
  unfold type_expect; intros. destruct (match_bounds_bool ty b) eqn:E; inv H.
  unfold match_bounds, match_bounds_bool in *.
  rewrite andb_true_iff in E. destruct E. split.
  eapply proj_sumbool_true; eauto.
  eapply proj_sumbool_true; eauto.
Qed.

End S.

