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

(** Correctness proof for base extraction. *)

Require Import Coqlib Maps Errors Integers Floats.
Require Import AST Linking.
Require Import Values Builtins Events Memory Globalenvs Smallstep.
Require Compopts Machregs.
Require Import Op Registers RTL.
Require Import BaseExtraction BaseExtractionspec.

Definition match_prog (prog tprog: program) :=
  match_program (fun czx f tf => tf = transf_fundef f) eq prog tprog.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. eapply match_transform_program; eauto.
Qed.


(** ** Agreement between register sets before and after inlining. *)

Definition agree_regs (max: positive) (rs rs': regset) :=
  (forall r, Ple r max -> Val.lessdef rs#r rs'#r)
  /\ (forall r, Plt max r -> rs#r = Vundef).

Remark Plt_Ple_dec:
  forall p q, {Plt p q} + {Ple q p}.
Proof.
  intros. destruct (plt p q). left; auto. right; extlia.
Qed.

Lemma agree_val_reg:
  forall max rs rs' r,
  agree_regs max rs rs' ->
  Val.lessdef rs # r rs' # r.
Proof.
  intros. destruct H. destruct (Plt_Ple_dec max r).
  rewrite H0; auto. apply  H; auto.
Qed.

Lemma agree_val_regs:
  forall max rs rs' l,
  agree_regs max rs rs' ->
  Val.lessdef_list rs ## l rs'## l.
Proof.
  induction l; auto.
  intros. simpl.
  constructor. apply (agree_val_reg max rs rs' a); auto.
  apply IHl; auto.
Qed.

Lemma agree_set_reg:
  forall max rs rs' r v v',
  agree_regs max rs rs' ->
  Val.lessdef v v' ->
  Ple r max ->
  agree_regs max (rs#r <- v) (rs'#r <- v').
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  repeat rewrite Regmap.gsspec.
  destruct (peq r0 r). auto. auto.
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


Lemma agree_regs_invariant:
  forall max rs rs1 rs2,
  agree_regs max rs rs1 ->
  (forall r, Ple r max -> rs2#r = rs1#r) ->
  agree_regs max rs rs2.
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  rewrite H0. auto. auto.
  apply H1; auto.
Qed.


Remark agree_regs_init:
  forall max rs, agree_regs max (Regmap.init Vundef) rs.
Proof.
  intros; split; intros. rewrite Regmap.gi; auto. rewrite Regmap.gi; auto.
Qed.


Lemma agree_regs_init_regs:
  forall max rl vl vl',
  Val.lessdef_list vl vl' ->
  (forall r, In r rl -> Ple r max) ->
  agree_regs max (init_regs vl rl) (init_regs vl' rl).
Proof.
  induction rl; simpl; intros.
  apply agree_regs_init.
  inv H. apply agree_regs_init.
  apply agree_set_reg; auto.
Qed.

(** * Semantic preservation *)

Section PRESERVATION.

Variable prog: program.
Variable tprog : program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSF).

Lemma symbols_preserved':
  forall (id: ident), (Genv.symbol_address tge id Ptrofs.zero = Genv.symbol_address ge id Ptrofs.zero).
Proof.
  intros. unfold Genv.symbol_address. rewrite symbols_preserved. reflexivity.
Qed.

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSF).


Lemma functions_translated:
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  exists cunit, Genv.find_funct tge v = Some (transf_fundef f) /\ linkorder cunit prog.
Proof.
  intros. exploit (Genv.find_funct_match TRANSF); eauto.
  intros (cu & tf & A & B & C). subst tf. exists cu; auto.
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists cunit, Genv.find_funct_ptr tge b = Some (transf_fundef f) /\ linkorder cunit prog.
Proof.
  intros. exploit (Genv.find_funct_ptr_match TRANSF); eauto.
  intros (cu & tf & A & B & C). subst tf. exists cu; auto.
Qed.

Lemma transf_ros_correct:
  forall max rs ros f rs',
  find_function ge ros rs = Some f ->
  ros_ple max ros ->
  agree_regs max rs rs' ->
  exists cunit,
     find_function tge ros rs' = Some (transf_fundef f)
  /\ linkorder cunit prog.
 intros until rs'; intros EF ROL RLD. destruct ros eqn:?; simpl in *.
- (* function pointer *)
  assert (Ple r max). inv ROL; inv H; auto. destruct RLD.
  generalize (H0 r H); intro LD.
   simpl. inv LD. apply functions_translated; auto. rewrite <- H3 in EF; discriminate.
- (* function symbol *)
  rewrite symbols_preserved.
  destruct (Genv.find_symbol ge i) as [b|]; try discriminate.
  apply function_ptr_translated; auto.
Qed.

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = funsig f.
Proof.
  destruct f; reflexivity.
Qed.


(** ** Forward simulation *)

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
   match_stackframe_intro:
      forall res sp pc rs f rs' cu,
      linkorder cu prog ->
      agree_regs (max_reg_function f) rs rs' ->
      Ple res (max_reg_function f) ->
      tr_funbody f (transf_function f).(fn_code) ->
      match_stackframes
        (Stackframe res f sp pc rs)
        (Stackframe res (transf_function f) sp pc rs').

Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_states_intro:
      forall s sp pc rs m f s' rs' m' cu
           (LINK: linkorder cu prog)
           (FB: tr_funbody f (transf_function f).(fn_code))
           (STACKS: list_forall2 match_stackframes s s')
           (AG: agree_regs (max_reg_function f) rs rs')
           (MEM: Mem.extends m m'),
      match_states (State s f sp pc rs m)
                    (State s' (transf_function f) sp pc rs' m')
  | match_states_call:
      forall s f args m s' args' m' cu
           (LINK: linkorder cu prog)
           (STACKS: list_forall2 match_stackframes s s')
           (ARGS: Val.lessdef_list args args')
           (MEM: Mem.extends m m'),
      match_states (Callstate s f args m)
                     (Callstate s' (transf_fundef f) args' m')
  | match_states_return:
      forall s v m s' v' m'
        (STACKS: list_forall2 match_stackframes s s')
        (VINJ: Val.lessdef  v v')
        (MEM: Mem.extends m m'),
      match_states (Returnstate s v m)
                     (Returnstate s' v' m').

Definition measure (S: RTL.state) : nat :=
  match S with
  | State _ _ _ _ _ _ => 1%nat
  | Callstate _ _ _ _ => 0%nat
  | Returnstate _ _ _ => 0%nat
  end.

Lemma tr_funbody_inv:
  forall  f c pc i,
  tr_funbody f c -> f.(fn_code)!pc = Some i -> tr_instr (max_reg_function f) pc i c.
Proof.
  intros. inv H. eauto.
Qed.

Theorem step_simulation:
  forall S1 t S2,
  step ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  (exists S2', plus step tge S1' t S2' /\ match_states S2 S2').
Proof.
  induction 1; intros; inv MS.

- (* nop *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  econstructor; split.
  eapply plus_one. eapply exec_Inop; eauto.
  eapply match_states_intro; eauto.
- (* op *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  assert (EV: exists v', eval_operation ge sp op rs'##args m' = Some v' /\ Val.lessdef v v').
  { eapply eval_operation_lessdef; eauto.
    eapply agree_val_regs; eauto.
  }
  destruct EV as [v' [EV' LD']].
  econstructor; split.
  eapply plus_one. eapply exec_Iop; eauto.
  erewrite eval_operation_preserved by exact symbols_preserved.
  eexact EV'.
  eapply match_states_intro; eauto.
  eapply agree_set_reg; eauto.
- (* load *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  + (* no extraction *)
    exploit eval_addressing_lessdef.
    eapply agree_val_regs; eauto.
    eexact H0.
    intros (a' & U & V).
    assert (W: eval_addressing tge sp addr rs'##args = Some a').
    { rewrite <- U. apply eval_addressing_preserved. exact symbols_preserved. }
    exploit Mem.loadv_extends. eexact MEM. eexact H1. eexact V.
    intros (v' & X & Y).
    econstructor; split. eapply plus_one.
    eapply exec_Iload; eauto.
    eapply match_states_intro; eauto.
    eapply agree_set_reg; eauto.
  + (* extraction *)
    exploit Mem.loadv_extends. eexact MEM. eexact H1.
    exploit symbol_addressing_correct. symmetry. eexact H7.
    intros. simpl in H0. rewrite H0 in H2. inv H2. auto.
    intros (v' & X & Y).
     econstructor; split. eapply plus_two.
    eapply exec_Iop; eauto.
    eapply symbol_op_correct.
    eapply exec_Iload; eauto.
    erewrite eval_addressing_preserved by exact symbols_preserved.
    simpl. rewrite Regmap.gss.
    rewrite symbols_preserved'.
    eapply aindexed_addr_correct with (sp := sp). constructor.
    eapply match_states_intro; eauto.
    eapply agree_set_reg; eauto.
    eapply agree_set_reg_other; eauto.
- (* store *)
   exploit tr_funbody_inv; eauto. intros TR; inv TR.
  + (* no extraction *)
    exploit eval_addressing_lessdef.
    eapply agree_val_regs; eauto.
    eexact H0.
    intros (a' & U & V).
    assert (W: eval_addressing tge sp addr rs'##args = Some a').
    { rewrite <- U. apply eval_addressing_preserved. exact symbols_preserved. }
    exploit Mem.storev_extends. eauto. eauto. apply Val.lessdef_trans with a'; eauto.
    eapply agree_val_reg; eauto.
    intros (v' & X & Y).
    econstructor; split. eapply plus_one.
    eapply exec_Istore; eauto.
    eapply match_states_intro; eauto.
  + (* extraction *)
    exploit Mem.storev_extends. eexact MEM. eexact H1.
    exploit symbol_addressing_correct. symmetry. eexact H7.
    intros. simpl in H0. rewrite H0 in H2. inv H2. auto.
    eapply agree_val_reg; eauto.
    intros (v' & X & Y).
     econstructor; split. eapply plus_two.
    eapply exec_Iop with (op := symbol_op id). eexact H14.
    eapply symbol_op_correct.
    eapply exec_Istore; eauto.
    erewrite eval_addressing_preserved by exact symbols_preserved.
    simpl. rewrite Regmap.gss.
    rewrite symbols_preserved'.
    eapply aindexed_addr_correct with (sp:= sp). rewrite Regmap.gso; try extlia.
    eexact X. constructor.
    eapply match_states_intro; eauto.
    eapply agree_set_reg_other; eauto.
- (* call *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit transf_ros_correct; eauto. intros (cu' & FIND & LINK').
  econstructor; split.
  eapply plus_one. eapply exec_Icall; eauto. apply sig_preserved.
  econstructor; eauto. constructor; auto.
  econstructor; eauto.
  eapply agree_val_regs; eauto.
-  (* tailcall *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
  exploit transf_ros_correct; eauto. intros (cu' & FIND & LINK').
  econstructor; split.
  eapply plus_one. eapply exec_Itailcall; eauto. apply sig_preserved.
  econstructor; eauto.
  eapply agree_val_regs; eauto.
- exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit (@eval_builtin_args_lessdef _ ge (fun r => rs#r) (fun r => rs'#r)); eauto.
  intros. eapply agree_val_reg; eauto.
  intros (vargs' & U & V).
  exploit external_call_mem_extends; eauto.
  intros (v' & m2' & A & B & C & D).
  econstructor; split.
  eapply plus_one.
  eapply exec_Ibuiltin; eauto.
  eapply eval_builtin_args_preserved. eexact symbols_preserved. eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  eapply match_states_intro; eauto.
  destruct res; simpl; eauto.
  eapply agree_set_reg; eauto.
- (* Icond *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  econstructor; split.
  eapply plus_one. eapply exec_Icond; eauto.
  eapply eval_condition_lessdef with (vl1 := rs##args); eauto.
  eapply agree_val_regs; eauto.
  econstructor; eauto.
- (* Ijumptale *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  econstructor; split.
  eapply plus_one. eapply exec_Ijumptable; eauto.
  assert (Val.lessdef (rs# arg) (rs'#arg)).
  eapply agree_val_reg; eauto.
  rewrite H0 in H2. inv H2. reflexivity.
  econstructor; eauto.
- (* Ireturn *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
  exists (Returnstate s' (regmap_optget or Vundef rs') m2'); split.
  eapply plus_one.
  eapply exec_Ireturn; eauto.
  econstructor; auto.
  destruct or; simpl; auto.
  eapply agree_val_reg; eauto.
- (* internal function *)
  exploit Mem.alloc_extends. eauto. eauto. apply Z.le_refl. apply Z.le_refl.
  intros [m2' [A B]].
  simpl. unfold transf_function.
  econstructor; split. eapply plus_one.
  eapply exec_function_internal; simpl; eauto using Val.has_argtype_list_lessdef.
  simpl. econstructor; eauto.
  generalize (transf_function_spec f). intros.
  inv H1; auto.
  apply agree_regs_init_regs; auto.
  apply max_reg_function_params.
- (* external function *)
  exploit external_call_mem_extends; eauto.
  intros [v' [m2' [A [B [C D]]]]].
  simpl. econstructor; split. eapply plus_one.
  eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constructor; auto.
- (* return *)
  inversion STACKS. inv H1.
  econstructor; split. eapply plus_one.
  eapply exec_return; eauto.
  econstructor; eauto.
  apply agree_set_reg; auto.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 -> exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated; eauto.  intros (cu & FIND & LINK).
  exists (Callstate nil (transf_fundef f) nil m0); split.
  econstructor; eauto.
  eapply (Genv.init_mem_match TRANSF); auto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  symmetry; eapply match_program_main; eauto.
  rewrite <- H3. apply sig_preserved.
  eapply match_states_call; eauto. constructor.
  apply Mem.extends_refl.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. inv VINJ.
  constructor.
Qed.

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_plus.
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  eexact step_simulation.
Qed.

End PRESERVATION.
