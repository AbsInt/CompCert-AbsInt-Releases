(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*            Adrian Dapprich, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  AbsInt Angewandte Informatik GmbH. All rights reserved. This file  *)
(*  is distributed under the terms of the INRIA Non-Commercial         *)
(*  License Agreement.                                                 *)
(*                                                                     *)
(* *********************************************************************)

(** Type-checking Mach code. *)

(** This file copies a subset of backend/Lineartyping.v.

    We need a wt_regset proposition during [Asmgenproof] for TriCore in order to use
    the separation logic assertions when register values are written to the CSA.

    Alternatively one could prove that the [Stacking] pass preserves the well-typedness
    of functions, but a check is simpler. *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Globalenvs.
Require Import Memory.
Require Import Events.
Require Import Op.
Require Import Machregs.
Require Import Locations.
Require Import Conventions.
Require Import Mach.
Require Import Errors.
Require Subtyping.

(** The rules are presented as boolean-valued functions so that we
  get an executable type-checker for free. *)

Section WT.

Fixpoint wt_builtin_res (ty: typ) (res: builtin_res (rpair mreg)) : bool :=
  match res with
  | BR p => subtype ty (mreg_pair_type p)
  | BR_none => true
  | BR_splitlong hi lo => wt_builtin_res Tint hi && wt_builtin_res Tint lo
  end.

Definition wt_instr (i: instruction) : bool :=
  match i with
  | Mgetstack ofs ty r =>
      subtype ty (mreg_pair_type r)
  | Mgetparam ofs ty r =>
      subtype ty (mreg_pair_type r)
  | Mop op args res =>
      match is_move_operation op args with
      | Some arg =>
          subtype (mreg_pair_type arg) (mreg_pair_type res)
      | None =>
          match type_of_operation op args res with
          | Error _ => false
          | OK ((targs, tres), _) =>
            subtype (proj_ptype_typ (Subtyping.S.proj_lo tres)) (mreg_pair_type res)
          end
      end
  | Mload chunk addr args dst =>
      subtype (type_of_chunk chunk) (mreg_pair_type dst)
  | Mbuiltin ef args res =>
      wt_builtin_res (proj_sig_res (ef_sig ef)) res
  | _ =>
      true
  end.

Definition wt_code (f: function) (c: code) : bool :=
  forallb (wt_instr) c.

Definition wt_function (f: function) : bool :=
  wt_code f f.(fn_code).

(** Typing the run-time state. *)

Definition wt_regset (rs: regset) : Prop :=
  forall r, Val.has_type (rs r) (mreg_type r).

Lemma wt_setreg:
  forall rs r v,
  Val.has_type v (mreg_type r) -> wt_regset rs -> wt_regset (rs # r <- v).
Proof.
  intros; red; intros.
  unfold Regmap.set.
  destruct (mreg_eq r0 r).
  - subst r0. rewrite dec_eq_true; auto.
  - rewrite dec_eq_false; auto.
Qed.

Lemma wt_setreg_undef:
  forall rs r,
  wt_regset rs -> wt_regset (rs # r <- Vundef).
Proof.
  intros; red; intros.
  unfold Regmap.set.
  destruct (mreg_eq r0 r).
  - subst r0. rewrite dec_eq_true; auto. exact I.
  - rewrite dec_eq_false; auto.
Qed.

Lemma wt_setpair1:
  forall rs p v,
  Val.has_type v (mreg_pair_type p) -> wt_regset rs -> wt_regset (set_pair p v rs).
Proof.
  intros; red; intros.
  destruct p.
  - apply wt_setreg; auto.
  - simpl. eapply wt_setreg. eapply pair_words_type; eauto.
    apply wt_setreg. eapply pair_words_type; eauto. assumption.
Qed.

Lemma wt_undef_regs:
  forall rl rs, wt_regset rs -> wt_regset (undef_regs rl rs).
Proof.
  induction rl; simpl; intros. auto. apply wt_setreg; auto. red; auto.
Qed.

Lemma wt_return_regs:
  forall caller callee,
  wt_regset caller -> wt_regset callee -> wt_regset (restore_auto_save_regs caller callee).
Proof.
  intros; red; intros.
  unfold restore_auto_save_regs.
  destruct (is_auto_save r); auto.
Qed.

Lemma wt_init:
  wt_regset (Regmap.init Vundef).
Proof.
  red; intros. unfold Regmap.init. red; auto.
Qed.

Lemma wt_setpair2:
  forall sg v rs,
  Val.has_type v (proj_sig_res sg) ->
  wt_regset rs ->
  wt_regset (set_pair (loc_result sg) v rs).
Proof.
  intros. generalize (loc_result_pair sg) (loc_result_type sg).
  destruct (loc_result sg); simpl Locmap.setpair.
- intros. apply wt_setreg; auto. eapply Val.has_subtype; eauto.
- intros A B. decompose [and or] A. simpl.
  rewrite H3 in H.
  (* set loword *)
  apply wt_setreg. eapply Val.has_subtype; eauto.
  destruct v; try inversion H; exact I.
  (* set hiword *)
  apply wt_setreg. eapply Val.has_subtype; eauto.
  destruct v; try inversion H; exact I.
  assumption.
Qed.

Lemma wt_setres:
  forall res ty v rs,
  wt_builtin_res ty res = true ->
  Val.has_type v ty ->
  wt_regset rs ->
  wt_regset (set_res res v rs).
Proof.
  induction res; simpl; intros.
- apply wt_setpair1; auto. eapply Val.has_subtype; eauto.
- auto.
- InvBooleans. eapply IHres2; eauto. destruct v; exact I.
  eapply IHres1; eauto. destruct v; exact I.
Qed.

Lemma wt_find_label:
  forall f lbl c,
  wt_function f = true ->
  Mach.find_label lbl f.(fn_code) = Some c ->
  wt_code f c = true.
Proof.
  unfold wt_function; intros until c. generalize (fn_code f). induction c0; simpl; intros.
  discriminate.
  InvBooleans. destruct (is_label lbl a).
  congruence.
  auto.
Qed.

(** Soundness of the type system *)

Definition wt_fundef (fd: fundef) :=
  match fd with
  | Internal f => wt_function f = true
  | External ef => True
  end.

Variable ge: genv.

Inductive wt_callstack: list stackframe -> Prop :=
  | wt_callstack_nil:
      wt_callstack nil
  | wt_callstack_cons: forall f fb sp ra rs c s
        (FND: Genv.find_funct_ptr ge fb = Some(Internal f))
        (WTSTK: wt_callstack s)
        (WTF: wt_function f = true)
        (WTC: wt_code f c = true)
        (WTRS: wt_regset rs),
      wt_callstack (Stackframe fb sp ra rs c :: s).

Lemma wt_parent_regset:
  forall s, wt_callstack s -> wt_regset (parent_regset s).
Proof.
  induction 1; simpl.
- apply wt_init.
- auto.
Qed.

Lemma wt_external_call_regs:
  forall s rs, wt_regset (parent_regset s) -> wt_regset rs -> wt_regset (external_call_regs (parent_regset s) rs).
Proof.
  intros. red; intros. unfold external_call_regs, restore_auto_save_regs, undef_callee_may_modify_regs.
  reg_cc_all r; rewrite HrAuto, ? HrModify; auto. constructor.
Qed.

Remark type_of_chunk_of_type:
  forall ty, type_of_chunk (chunk_of_type ty) = ty.
Proof.
  destruct ty; reflexivity.
Qed.

Lemma wt_load_stack_rpairs:
  forall l m sp ofs rs rs',
  load_stack_rpairs m sp ofs l rs = Some rs' ->
  wt_regset rs ->
  wt_regset rs'.
Proof.
  induction l; intros; simpl in H.
  - inv H. assumption.
  - destruct (restore_callee_pair m sp (align ofs (Bounds.compute_size a)) a rs) as [rs0|] eqn:Er; [|now discriminate].
    eapply IHl. exact H.
    unfold restore_callee_pair in Er. destruct a.
    + destruct (load_stack m sp) eqn:El; [|now discriminate].
      inv Er. unfold load_stack in El. apply Mem.loadv_type in El. rewrite type_of_chunk_of_type in El.
      apply wt_setreg; eauto.
    + destruct (load_stack m sp (mreg_type (if Archi.big_endian then rhi else rlo))) eqn:El1; [|now discriminate].
      destruct (load_stack m sp (mreg_type (if Archi.big_endian then rlo else rhi))) eqn:El2; [|now discriminate].
      inv Er. unfold load_stack in El1, El2. apply Mem.loadv_type in El1, El2. rewrite type_of_chunk_of_type in El1, El2.
      apply wt_setreg; eauto.
      apply wt_setreg; eauto.
Qed.

Inductive wt_state: state -> Prop :=
  | wt_regular_state: forall s f fb sp c rs m
        (WTSTK: wt_callstack s)
        (FND: Genv.find_funct_ptr ge fb = Some(Internal f))
        (WTF: wt_function f = true)
        (WTC: wt_code f c = true)
        (WTRS: wt_regset rs),
      wt_state (State s fb sp c rs m)
  | wt_call_state: forall s ros fd fb rs m
        (WTSTK: wt_callstack s)
        (FND0: find_function_ptr ge ros rs = Some(fb))
        (FND1: Genv.find_funct_ptr ge fb = Some(fd))
        (WTFD: wt_fundef fd)
        (WTRS: wt_regset rs),
      wt_state (Callstate s fb rs m)
  | wt_return_state: forall s rs m
        (WTSTK: wt_callstack s)
        (WTRS: wt_regset rs),
      wt_state (Returnstate s rs m).

End WT.

(** Preservation of state typing by transitions *)

Section SOUNDNESS.

Variable prog: program.
Variable return_address_offset : function -> code -> ptrofs -> Prop.
Let ge := Genv.globalenv prog.

Hypothesis wt_prog:
  forall i fd, In (i, Gfun fd) prog.(prog_defs) -> wt_fundef fd.

Lemma wt_find_function:
  forall f fb, Genv.find_funct_ptr ge fb = Some f -> wt_fundef f.
Proof.
  intros.
  assert (X: exists i, In (i, Gfun f) prog.(prog_defs)).
  {
    eapply Genv.find_funct_ptr_inversion; eauto.
  }
  destruct X as [i IN]. eapply wt_prog; eauto.
Qed.

Theorem step_type_preservation:
  forall S1 t S2, step return_address_offset ge S1 t S2 -> wt_state ge S1 -> wt_state ge S2.
Proof.
Local Opaque mreg_type.
  induction 1; intros WTS; inv WTS.
- (* label *)
  simpl in *. econstructor; eauto.
- (* getstack *)
  simpl in *; InvBooleans.
  econstructor; eauto.
  eapply wt_setpair1; eauto. eapply Val.has_subtype; [eauto|].
  apply Mem.loadv_type in H. destruct ty; assumption.
- (* setstack *)
  simpl in *; InvBooleans.
  econstructor; eauto.
- (* restorecallee *)
  simpl in *; InvBooleans.
  econstructor; eauto.
  eapply wt_load_stack_rpairs; eauto.
- (* savecallee *)
  simpl in *; InvBooleans.
  econstructor; eauto.
  apply wt_undef_regs; auto.
- (* getparam *)
  simpl in *; InvBooleans.
  econstructor; eauto.
  eapply wt_setpair1; eauto. eapply Val.has_subtype; [eauto|].
  apply Mem.loadv_type in H1. destruct ty; assumption.
  apply wt_setreg_undef; auto.
- (* op *)
  simpl in *. destruct (is_move_operation op args) as [src | ] eqn:ISMOVE.
  + (* move *)
    InvBooleans. exploit is_move_operation_correct; eauto. intros [EQ1 EQ2]; subst.
    simpl in H. inv H.
    econstructor; eauto. apply wt_setpair1. eapply Val.has_subtype; eauto.
    unfold get_pair. destruct src.
    simpl. eapply Val.has_subtype; auto. simpl. destruct (mreg_type r); auto.
    apply (words_pair_type rlo rhi); apply WTRS.
    apply wt_undef_regs; auto.
  + (* other ops *)
    destruct (type_of_operation op args res) as [[[ty_args ty_res] eti]|] eqn:TYOP.
    InvBooleans.
    econstructor; eauto.
    destruct ty_res as [ty_res_lo ??] eqn:TYRES.
    apply wt_setpair1. eapply Val.has_subtype; eauto with ty.
    exploit (type_of_operation_sound); eauto.
    red; intros; subst op. simpl in ISMOVE.
    destruct args; try discriminate. destruct args; discriminate.
    apply wt_undef_regs; auto.
    InvBooleans; discriminate.
- (* load *)
  simpl in *; InvBooleans.
  econstructor; eauto.
  apply wt_setpair1. eapply Val.has_subtype; eauto.
  destruct a; simpl in H0; try discriminate. eapply Mem.load_type; eauto.
  apply wt_undef_regs; auto.
- (* store *)
  simpl in *; InvBooleans.
  econstructor. auto. eauto. eauto. eauto.
  apply wt_undef_regs; auto.
- (* call *)
  simpl in *; InvBooleans.
  rewrite FND in H1; inv H1.
  econstructor; eauto.
  econstructor; eauto.
  eapply wt_find_function; eauto.
- (* tailcall *)
  simpl in *; InvBooleans.
  rewrite FND in H2; inv H2.
  econstructor; eauto.
  eapply wt_find_function; eauto.
- (* builtin *)
  simpl in *; InvBooleans.
  econstructor; eauto.
  eapply wt_setres; eauto. eapply external_call_well_typed; eauto.
  apply wt_undef_regs; auto.
- (* goto *)
  simpl in *. rewrite FND in H; inv H.
  econstructor; eauto. eapply wt_find_label; eauto.
- (* cond branch, taken *)
  simpl in *. rewrite FND in H0; inv H0.
  econstructor. auto. eauto. auto. eapply wt_find_label; eauto.
  apply wt_undef_regs; auto.
- (* cond branch, not taken *)
  simpl in *. econstructor. auto. eauto. auto. auto.
  apply wt_undef_regs; auto.
- (* jumptable *)
  simpl in *. rewrite FND in H1; inv H1.
  econstructor. auto. eauto. auto. eapply wt_find_label; eauto.
  apply wt_undef_regs; auto.
- (* return *)
  simpl in *. InvBooleans.
  econstructor; eauto.
  apply wt_return_regs; auto. eapply wt_parent_regset; eauto.
- (* internal function *)
  rewrite FND1 in H; inv H.
  simpl in WTFD.
  econstructor. auto. eauto. eauto. eauto.
  apply wt_undef_regs. auto.
- (* external function *)
  econstructor. auto. apply wt_setpair2.
  eapply external_call_well_typed; eauto.
  apply wt_external_call_regs; auto. eapply wt_parent_regset; eauto.
- (* return *)
  inv WTSTK. econstructor; eauto.
Qed.

Theorem wt_initial_state:
  forall S, initial_state prog S -> wt_state ge S.
Proof.
  induction 1. econstructor.
  constructor.
  instantiate (1:=inr (prog_main prog)). simpl. eauto. eauto.
  unfold ge0 in H1. exploit Genv.find_funct_ptr_inversion; eauto.
  intros [id IN]. eapply wt_prog; eauto.
  apply wt_init.
Qed.

End SOUNDNESS.
