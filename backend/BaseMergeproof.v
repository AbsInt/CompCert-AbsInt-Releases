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

(** Correctness proof for base merging. *)

Require Import Coqlib Maps Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Values Builtins Events Memory Globalenvs Smallstep.
Require Compopts Machregs.
Require Import Op Registers RTL.
Require Import Liveness ValueDomain ValueAOp ValueAnalysis.
Require Import ConstpropOp ConstpropOpproof BaseMerge.

Definition match_prog (prog tprog: program) :=
  match_program (fun cu f tf => tf = transf_fundef (romem_for cu) f) eq prog tprog.

Lemma transf_program_match:
  forall prog, match_prog prog (transf_program prog).
Proof.
  intros. eapply match_transform_program_contextual. auto.
Qed.

Section PRESERVATION.

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

(** * Correctness of the code transformation *)

(** We now show that the transformed code after constant propagation
  has the same semantics as the original code. *)

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSL).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSL).

Lemma functions_translated:
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  exists cunit, Genv.find_funct tge v = Some (transf_fundef (romem_for cunit) f) /\ linkorder cunit prog.
Proof.
  intros. exploit (Genv.find_funct_match TRANSL); eauto.
  intros (cu & tf & A & B & C). subst tf. exists cu; auto.
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists cunit, Genv.find_funct_ptr tge b = Some (transf_fundef (romem_for cunit) f) /\ linkorder cunit prog.
Proof.
  intros. exploit (Genv.find_funct_ptr_match TRANSL); eauto.
  intros (cu & tf & A & B & C). subst tf. exists cu; auto.
Qed.

Lemma transf_ros_correct:
  forall bc rs ae ros f rs',
  genv_match bc ge ->
  ematch bc rs ae ->
  find_function ge ros rs = Some f ->
  regs_lessdef rs rs' ->
  exists cunit,
     find_function tge ros rs' = Some (transf_fundef (romem_for cunit) f)
  /\ linkorder cunit prog.
 intros until rs'; intros GE EM FF RLD. destruct ros; simpl in *.
- (* function pointer *)
  generalize (EM r);  intro VM. generalize (RLD r); intro LD.
  simpl. inv LD. apply functions_translated; auto. rewrite <- H0 in FF; discriminate.
- (* function symbol *)
  rewrite symbols_preserved.
  fold fundef in FF.
  destruct (Genv.find_symbol ge i) as [b|]; try discriminate.
  apply function_ptr_translated; auto.
Qed.

Lemma sig_function_translated:
  forall rm f,
  funsig (transf_fundef rm f) = funsig f.
Proof.
  intros. destruct f; reflexivity.
Qed.

Lemma init_regs_lessdef:
  forall rl vl1 vl2,
  Val.lessdef_list vl1 vl2 ->
  regs_lessdef (init_regs vl1 rl) (init_regs vl2 rl).
Proof.
  induction rl; simpl; intros.
  red; intros. rewrite Regmap.gi. auto.
  inv H. red; intros. rewrite Regmap.gi. auto.
  apply set_reg_lessdef; auto.
Qed.

(** The proof of semantic preservation is a simulation argument
  based on "option" diagrams of the following form:
<<
                 n
       st1 --------------- st2
        |                   |
       t|                   |t or (? and n' < n)
        |                   |
        v                   v
       st1'--------------- st2'
                 n'
>>
  The left vertical arrow represents a transition in the
  original RTL code.  The top horizontal bar is the [match_states]
  invariant between the initial state [st1] in the original RTL code
  and an initial state [st2] in the transformed code.
  This invariant expresses that all code fragments appearing in [st2]
  are obtained by [transf_code] transformation of the corresponding
  fragments in [st1].  Moreover, the state [st1] must match its compile-time
  approximations at the current program point.
  These two parts of the diagram are the hypotheses.  In conclusions,
  we want to prove the other two parts: the right vertical arrow,
  which is a transition in the transformed RTL code, and the bottom
  horizontal bar, which means that the [match_state] predicate holds
  between the final states [st1'] and [st2']. *)

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
   match_stackframe_intro:
      forall res sp pc rs f rs' cu,
      linkorder cu prog ->
      regs_lessdef rs rs' ->
    match_stackframes
        (Stackframe res f sp pc rs)
        (Stackframe res (transf_function (romem_for cu) f) sp pc rs').

Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
      forall s sp pc rs m f s' rs' m' cu
           (LINK: linkorder cu prog)
           (STACKS: list_forall2 match_stackframes s s')
           (REGS: regs_lessdef rs rs')
           (MEM: Mem.extends m m'),
      match_states (State s f sp pc rs m)
                    (State s' (transf_function (romem_for cu) f) sp pc rs' m')
  | match_states_call:
      forall s f args m s' args' m' cu
           (LINK: linkorder cu prog)
           (STACKS: list_forall2 match_stackframes s s')
           (ARGS: Val.lessdef_list args args')
           (MEM: Mem.extends m m'),
      match_states (Callstate s f args m)
                     (Callstate s' (transf_fundef (romem_for cu) f) args' m')
  | match_states_return:
      forall s v m s' v' m'
           (STACKS: list_forall2 match_stackframes s s')
           (RES: Val.lessdef v v')
           (MEM: Mem.extends m m'),
      list_forall2 match_stackframes s s' ->
      match_states (Returnstate s v m)
                     (Returnstate s' v' m').

Lemma transf_instr_at:
  forall rm f pc i,
  f.(fn_code)!pc = Some i ->
  (transf_function rm f).(fn_code)!pc = Some(transf_instr f (analyze rm f) (usage_analysis f) rm pc i).
Proof.
  intros. simpl. rewrite PTree.gmap. rewrite H. auto.
Qed.

Ltac TransfInstr :=
  match goal with
  | H1: (PTree.get ?pc (fn_code ?f) = Some ?instr),
    H2: (analyze ?rm ?f)#?pc = VA.State ?ae ?am |- _ =>
      generalize (transf_instr_at rm _ _ _ H1); unfold transf_instr; rewrite H2
  end.

(** The proof of simulation proceeds by case analysis on the transition
  taken in the source code. *)

Lemma transf_step_correct:
  forall s1 t s2,
  step ge s1 t s2 ->
  forall s1' (SS: sound_state prog s1) (MS: match_states s1 s1'),
  (exists s2', step tge s1' t s2' /\ match_states s2 s2').
Proof.
  induction 1; intros; inv MS; try InvSoundState; try (inv PC; try congruence).
- (* Inop *)
  TransfInstr; intros.
  econstructor; split.
  eapply exec_Inop; eauto.
  eapply match_states_intro; auto.
- (* Iop *)
  TransfInstr; intros.
  assert (EV: exists v', eval_operation ge (Vptr sp0 Ptrofs.zero) op rs'##args m' = Some v' /\ Val.lessdef v v').
  { eapply eval_operation_lessdef; eauto. eapply regs_lessdef_regs; eauto. }
  destruct EV as [v' [EV' LD']].
  econstructor; split.
  eapply exec_Iop; eauto.
  erewrite eval_operation_preserved by exact symbols_preserved. eexact EV'.
  eapply match_states_intro; auto. apply set_reg_lessdef; auto.
- (* Iload *)
  TransfInstr. intros.
  destruct (should_reduce (usage_analysis f) addr args).
  + (* Case for reducing the addressing*)
    set (aa := eval_static_addressing addr (aregs ae args)) in *.
     assert (VM1: vmatch bc a aa) by (eapply eval_static_addressing_sound; eauto with va).
     set (av := loadv chunk (romem_for cu) am aa) in *.
     assert (VM2: vmatch bc v av) by (eapply loadv_sound; eauto).
     destruct (const_for_result av) as [cop|] eqn:?; intros.
     * (* constant-propagated *)
       exploit const_for_result_correct. eexact GE.
       eexact SP. eexact Heqo. eexact VM2. intros (v' & A & B).
       econstructor; split.
       eapply exec_Iop; eauto. simpl.
       erewrite eval_operation_preserved by exact symbols_preserved.
       eapply A. eapply match_states_intro; eauto.
       apply set_reg_lessdef; auto.
     * (* strength-reduced *)
       assert (ADDR:
                let (addr', args') := addr_strength_reduction addr args (aregs ae args) in
                exists a',
                eval_addressing ge (Vptr sp0 Ptrofs.zero) addr' rs ## args' = Some a' /\
                  Val.lessdef a a').
       { eapply addr_strength_reduction_correct with (ae := ae); eauto with va. }
       destruct (addr_strength_reduction addr args (aregs ae args)) as [addr' args'].
       destruct ADDR as (a' & P & Q).
       exploit eval_addressing_lessdef. eapply regs_lessdef_regs; eauto. eexact P.
       intros (a'' & U & V).
       assert (W: eval_addressing tge (Vptr sp0 Ptrofs.zero) addr' rs'##args' = Some a'').
       { rewrite <- U. apply eval_addressing_preserved. exact symbols_preserved. }
       exploit Mem.loadv_extends. eauto. eauto. apply Val.lessdef_trans with a'; eauto.
       intros (v' & X & Y).
       econstructor; split.
       eapply exec_Iload; eauto.
       eapply match_states_intro; eauto. apply set_reg_lessdef; auto.
  + (* Load should not be strength reduced *)
    exploit eval_addressing_lessdef.
    eapply regs_lessdef_regs; eexact REGS. eexact H0.
    exploit eval_addressing_lessdef. eapply regs_lessdef_regs; eauto. eexact H0.
    intros (a' & U & V).
    assert (W: eval_addressing tge (Vptr sp0 Ptrofs.zero) addr rs'##args = Some a').
    { rewrite <- U. apply eval_addressing_preserved. exact symbols_preserved. }
    exploit Mem.loadv_extends. eauto. eauto. apply Val.lessdef_trans with a'; eauto.
    intros (v' & X & Y).
    econstructor; split.
    eapply exec_Iload; eauto.
    eapply match_states_intro; auto. apply set_reg_lessdef; auto.
- (* Istore *)
  TransfInstr. intros.
  destruct (should_reduce (usage_analysis f) addr args).
  + (* Case for reducing the addressing*)
    assert (ADDR:
             let (addr', args') := addr_strength_reduction addr args (aregs ae args) in
             exists a',
             eval_addressing ge (Vptr sp0 Ptrofs.zero) addr' rs ## args' = Some a' /\
               Val.lessdef a a').
    { eapply addr_strength_reduction_correct with (ae := ae); eauto with va. }
    destruct (addr_strength_reduction addr args (aregs ae args)) as [addr' args'].
    destruct ADDR as (a' & P & Q).
    exploit eval_addressing_lessdef. eapply regs_lessdef_regs; eauto. eexact P.
    intros (a'' & U & V).
    assert (W: eval_addressing tge (Vptr sp0 Ptrofs.zero) addr' rs'##args' = Some a'').
    { rewrite <- U. apply eval_addressing_preserved. exact symbols_preserved. }
    exploit Mem.storev_extends. eauto. eauto. apply Val.lessdef_trans with a'; eauto. apply REGS.
    intros (m2' & X & Y).
    econstructor; split.
    eapply exec_Istore; eauto.
    eapply match_states_intro; eauto.
  + (* Store addressing should not be strength reduced *)
    exploit eval_addressing_lessdef.
    eapply regs_lessdef_regs; eexact REGS. eexact H0.
    exploit eval_addressing_lessdef. eapply regs_lessdef_regs; eauto. eexact H0.
    intros (a' & U & V).
    assert (W: eval_addressing tge (Vptr sp0 Ptrofs.zero) addr rs'##args = Some a').
    { rewrite <- U. apply eval_addressing_preserved. exact symbols_preserved. }
    exploit Mem.storev_extends. eauto. eauto. apply Val.lessdef_trans with a'; eauto.  apply REGS.
    intros (v' & X & Y).
    econstructor; split.
    eapply exec_Istore; eauto.
    eapply match_states_intro; auto.
- (* Icall *)
  exploit transf_ros_correct; eauto. intros (cu' & FIND & LINK').
  TransfInstr; intros.
  econstructor; split.
  eapply exec_Icall; eauto. apply sig_function_translated; auto.
  constructor; auto. constructor; auto.
  econstructor; eauto.
  apply regs_lessdef_regs; auto.
- (* Itailcall *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
  exploit transf_ros_correct; eauto. intros (cu' & FIND & LINK').
  TransfInstr; intros.
  econstructor; split.
  eapply exec_Itailcall; eauto. apply sig_function_translated; auto.
  constructor; auto.
  apply regs_lessdef_regs; auto.
- (* Ibuiltin *)
  TransfInstr; intros.
  exploit (@eval_builtin_args_lessdef _ ge (fun r => rs#r) (fun r => rs'#r)).
  apply REGS. eauto. exact H0.
  intros (varsg' & U & V).
  exploit external_call_mem_extends; eauto.
  intros (v' & m2' & A & B & C & D).
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  eapply eval_builtin_args_preserved. eexact symbols_preserved. eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  eapply match_states_intro; eauto.
  apply set_res_lessdef; auto.
- (* Icond *)
  TransfInstr; intros.
  econstructor; split.
  eapply exec_Icond; eauto.
  eapply eval_condition_lessdef with (vl1 := rs##args); eauto. eapply regs_lessdef_regs; eauto.
  eapply match_states_intro; eauto.
- (* Ijumptable *)
  TransfInstr; intros.
  econstructor; split.
  eapply exec_Ijumptable; eauto.
  assert (Val.lessdef (rs# arg) (rs'#arg)) by auto.
  rewrite H0 in H3. inv H3. reflexivity.
  eapply match_states_intro; eauto.
- (* Ireturn *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
  exists (Returnstate s' (regmap_optget or Vundef rs') m2'); split.
  eapply exec_Ireturn; eauto. TransfInstr; auto.
  constructor; auto.
  destruct or; simpl; auto.
- (* internal function *)
  exploit Mem.alloc_extends. eauto. eauto. apply Z.le_refl. apply Z.le_refl.
  intros [m2' [A B]].
  simpl. unfold transf_function.
  econstructor; split.
  eapply exec_function_internal; simpl; eauto using Val.has_argtype_list_lessdef.
  simpl. econstructor; eauto.
  apply init_regs_lessdef; auto.
- (* external function *)
  exploit external_call_mem_extends; eauto.
  intros [v' [m2' [A [B [C D]]]]].
  simpl. econstructor; split.
  eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constructor; auto.
- (* return *)
  inv H3. inv H1.
  econstructor; split.
  eapply exec_return; eauto.
  econstructor; eauto. apply set_reg_lessdef; auto.
Qed.


Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated; eauto. intros (cu & FIND & LINK).
  exists (Callstate nil (transf_fundef (romem_for cu) f) nil m0); split.
  econstructor; eauto.
  apply (Genv.init_mem_match TRANSL); auto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  symmetry; eapply match_program_main; eauto.
  rewrite <- H3. apply sig_function_translated.
  constructor. auto. constructor. constructor. apply Mem.extends_refl.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. inv RES. constructor.
Qed.


(** The preservation of the observable behavior of the program then
  follows. *)

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_step with
    (match_states := fun s1 s2 => sound_state prog s1 /\ match_states s1 s2).
- apply senv_preserved.
- intros. exploit transf_initial_states; eauto. intros [s2 [A B]].
  exists s2. split. auto. split. apply sound_initial; auto. auto.
- intros. destruct H. eapply transf_final_states; eauto.
- intros. destruct H0. exploit transf_step_correct; eauto.
  intros [s2' [A B]]. exists s2'; split. auto. split. eapply sound_step; eauto. auto.
Qed.

End PRESERVATION.
