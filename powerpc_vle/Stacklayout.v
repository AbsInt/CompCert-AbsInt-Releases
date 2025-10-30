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

Require Import Coqlib Integers.
Require Import Memory Separation.
Require Import Bounds.
Require Import AST Machregs.
(** In the PowerPC/EABI application binary interface,
  the general shape of activation records is as follows,
  from bottom (lowest offsets) to top:
- 8 reserved bytes.  The first 4 bytes hold the back pointer to the
  activation record of the caller.  The next 4 bytes are reserved
  for called functions to store their return addresses.
  Since we would rather store our return address in our own
  frame, we will not use these 4 bytes, and just reserve them.
- Space for outgoing arguments to function calls.
- Local stack slots.
- Saved values of callee-save registers used by the function.
- Space for the stack-allocated data declared in Cminor.

The [frame_env] compilation environment records the positions of
the boundaries between areas in the frame part.
*)
Open Scope Z.

(*- E_COMPCERT_FTR_Function_Stacklayout_fe_ofs_arg_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_EABI_001 *)
Definition fe_ofs_arg := 8.
(*- #End *)

Definition low_s_8 (n: int) := Int.sign_ext 8 n.
Definition high_s_24 (n: int) := Int.shru (Int.sub n (low_s_8 n)) (Int.repr 8).

Definition compute_mreg_list (r : mreg) :=
  Pos.peano_rect (fun _ => list mreg) (R31 :: nil)
    (fun p l => (IndexedMreg.reverse_index (28 - p)) :: l) (29 - (IndexedMreg.index r)).

Definition load_store_multiple_condition l ofs :=
  match l with
  | m1 :: _ :: _ => list_eq_dec mreg_eq l (compute_mreg_list m1)
                     && Int.eq (high_s_24 (Int.repr (align ofs 4))) Int.zero
  | _ => false
  end.

Fixpoint split_by_type l :=
  match l with
  | r :: l' => if typ_eq (mreg_type r) Tany32 then
               let (il, fl) := split_by_type l' in (r::il, fl)
             else (nil, r::l')
  | nil => (nil, nil)
  end.

Definition split_used_callee_save (rl: list mreg) (ofs: Z) :=
  let (mil, mfl) := split_by_type rl in
  let il := if load_store_multiple_condition mil ofs then Multiple (map (fun r => One r) mil) :: nil else default_callee_save mil in
  il ++ default_callee_save mfl.

Lemma split_by_type_same:
  forall l il fl,
    split_by_type l = (il, fl) ->
    il ++ fl = l.
Proof.
  induction l as [| r l]; simpl; intros.
  inversion H. reflexivity.
  destruct (typ_eq (mreg_type r) Tany32).
  destruct (split_by_type l). inversion H. simpl. f_equal. apply IHl. inversion H. reflexivity.
  inversion H. reflexivity.
Qed.

Remark simple_map_correspond:
  forall (l: list mreg), regs_of_rpairs (map (fun r => One r) l) = l.
Proof.
  induction l; simpl; intros; f_equal; auto.
Qed.

Lemma callee_save_correspond:
  forall l r ofs, In r (regs_of_rpairs (flatten_group_list (split_used_callee_save l ofs))) <-> In r l.
Proof.
  intros; unfold split_used_callee_save; simpl.
  destruct (split_by_type l) eqn:E.
  repeat match goal with
  | [|- context [if ?X then _ else _]] => let E := fresh "E" in destruct X eqn:E
  end; simpl;
    repeat rewrite default_callee_save_correspond || rewrite flatten_group_app || rewrite regs_of_rpairs_app || simpl || rewrite in_app
    || rewrite app_nil_r || rewrite simple_map_correspond || (erewrite <-(split_by_type_same l); eauto); intuition auto.
Qed.

Remark simple_map_wellformed:
  forall (l: list mreg) p, In p (map (fun r => One r) l) -> pair_wf p.
Proof.
  induction l; simpl; intros; intuition. subst p. simpl; auto.
Qed.

Lemma callee_save_wellformed:
  forall l p ofs, In p (flatten_group_list (split_used_callee_save l ofs)) -> pair_wf p.
Proof.
  unfold split_used_callee_save. intros. destruct (split_by_type) eqn:E. apply split_by_type_same in E.
  subst l.
  Destructor; rewrite flatten_group_app, in_app in H; destruct H; try (eapply default_callee_save_wellformed; eauto; fail).
  simpl in H. rewrite app_nil_r in H.  eapply simple_map_wellformed; eauto.
Qed.

(** Computation of the frame environment from the bounds of the current
  function. *)

Definition make_env (b: bounds) :=
  let ol := align (8 + 4 * b.(bound_outgoing)) 8 in    (* locals *)
  let ora := ol + 4 * b.(bound_local) in (* saved return address *)
  let ocs := ora + 4 in            (* callee-saves *)
  let calleepairs := split_used_callee_save (b.(used_callee_save)) ocs in
  let oendcs := size_callee_save_area_rec (flatten_group_list calleepairs) ocs in
  let ostkdata := align oendcs 8 in (* stack data *)
  let sz := align (ostkdata + b.(bound_stack_data)) 16 in
  {| fe_size := sz;
     fe_ofs_link := 0;
     fe_ofs_retaddr := ora;
     fe_ofs_local := ol;
     fe_ofs_callee_save := ocs;
     fe_stack_data := ostkdata;
     fe_used_callee_save := calleepairs |}.

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
  set (ol := align (8 + 4 * b.(bound_outgoing)) 8).
  set (ora := ol + 4 * b.(bound_local)).
  set (ocs := ora + 4).
  set (oendcs := size_callee_save_area fe ocs).
  set (ostkdata := align oendcs 8).
  generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
  unfold fe_ofs_arg.
  assert (8 + 4 * b.(bound_outgoing) <= ol) by (apply align_le; lia).
  assert (ol <= ora) by (unfold ora; lia).
  assert (ora <= ocs) by (unfold ocs; lia).
  assert (ocs <= oendcs) by (apply size_callee_save_area_incr).
  assert (oendcs <= ostkdata) by (apply align_le; lia).
(* Reorder as:
     back link
     outgoing
     locals
     retaddr
     callee-save *)
  rewrite sep_swap3.
(* Apply range_split and range_split2 repeatedly *)
  apply range_drop_right with 8. lia.
  apply range_split. lia.
  apply range_split_2. fold ol; lia. lia.
  apply range_split. lia.
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
  set (ol := align (8 + 4 * b.(bound_outgoing)) 8).
  set (ora := ol + 4 * b.(bound_local)).
  set (ocs := ora + 4).
  set (oendcs := size_callee_save_area fe ocs).
  set (ostkdata := align oendcs 8).
  generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
  unfold fe_ofs_arg.
  assert (8 + 4 * b.(bound_outgoing) <= ol) by (apply align_le; lia).
  assert (ol <= ora) by (unfold ora; lia).
  assert (ora <= ocs) by (unfold ocs; lia).
  assert (ocs <= oendcs) by (apply size_callee_save_area_incr).
  assert (oendcs <= ostkdata) by (apply align_le; lia).
  change (size_callee_save_area_rec (flatten_group_list (split_used_callee_save (used_callee_save b) ocs)) ocs) with oendcs.
  split. lia. apply align_le. lia.
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
  set (ol := align (8 + 4 * b.(bound_outgoing)) 8).
  set (ora := ol + 4 * b.(bound_local)).
  set (ocs := ora + 4).
  set (oendcs := size_callee_save_area fe ocs).
  set (ostkdata := align oendcs 8).
  split. exists (fe_ofs_arg / 8); reflexivity.
  split. apply align_divides; lia.
  split. apply align_divides; lia.
  split. apply Z.divide_0_r.
  apply Z.divide_add_r.
    apply Z.divide_trans with 8. exists 2; auto. apply align_divides; lia.
    apply Z.divide_factor_l.
Qed.
