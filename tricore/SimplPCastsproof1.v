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

Require Import Coqlib Maps AST Linking Globalenvs Smallstep RTL RTLtyping SimplPCasts1 Subtyping.
Require Import Values Memory.

Definition match_prog (prog tprog: program) :=
  match_program (fun czx f tf => tf = simplify_fundef f) eq prog tprog.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. eapply match_transform_program; eauto.
Qed.

Lemma match_prog_equiv:
  forall f f', match_prog f f' <-> f' = transf_program f.
Proof.
  intros; split; intros.
  - inv H. destruct H1 as [eq1 eq2].
    destruct f, f'; cbn in *. subst; cbn.
    unfold transf_program.  unfold AST.transform_program; cbn.
    f_equal. induction H0; try reflexivity.
    simpl in *. unfold match_ident_globdef in H. destruct H as [eq H].
    rewrite (surjective_pairing a1). rewrite (surjective_pairing b1). rewrite <- eq in *.
    inv  H; simpl in *; try reflexivity.
    f_equal. f_equal.
    inv H3. reflexivity.
  - rewrite H. apply transf_program_match.
Qed.

Section PRESERVATION.
  
Variable prog: program.
Variable tprog : program.
Hypothesis TRANSF: match_prog prog tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  exact (Genv.find_symbol_match TRANSF).
Qed.

Lemma symbols_preserved2:
  forall s,
    Genv.find_symbol (untype_genv tge) s = Genv.find_symbol (untype_genv ge) s.
Proof.
 repeat rewrite symbols_preserved'. apply symbols_preserved.
Qed.
  
Lemma senv_preserved:
  Senv.equiv ge tge.
Proof.
  exact (Genv.senv_match TRANSF).
Qed.

Lemma senv_preserved2:
  Senv.equiv (untype_genv ge) (untype_genv tge).
Proof.
  eapply Senv.equiv_trans.
  - eapply Senv.equiv_symmetric. eapply senv_preserved'. 
  - eapply Senv.equiv_trans.
    + eapply senv_preserved.
    + eapply senv_preserved'.
Qed.

Inductive match_stackframes: list stackframe -> list stackframe -> ptype -> Prop :=
| match_stackframes_nil: forall t,
    match_stackframes nil nil t
| match_stackframes_cons: forall res env f sp pc rs tret sfs sfs',
    match_stackframes sfs sfs' (proj_sig_res_ptype (fn_sig f)) ->
    wt_regset env rs ->
    wt_function f env ->
    subptype tret (env res) ->
      match_stackframes
        (Stackframe res f sp pc rs::sfs)
        (Stackframe res (simplify_function env f) sp pc rs::sfs') tret.

Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_states_intro:
    forall s sp pc rs m env f s'
      (STACKS: match_stackframes s s' (proj_sig_res_ptype (fn_sig f))),
      wt_regset env rs ->
      wt_function f env ->
      match_states (State s f sp pc rs m)
        (State s' (simplify_function env f) sp pc rs m)
  | match_states_call:
    forall s f args m s'
      (STACKS: match_stackframes s s' (proj_sig_res_ptype (funsig (untype_fundef f)))),
      Val.has_ptype_list args (proj_sig_args_ptype (funsig (untype_fundef f))) ->
      match_states (Callstate s (untype_fundef f) args m)
        (Callstate s' (untype_fundef (simplify_fundef f)) args m)
  | match_states_return:
    forall s v m s' rt
      (STACKS: match_stackframes s s' rt),
      (Val.has_ptype v rt) ->
      match_states (Returnstate s v m)
        (Returnstate s' v m).

Lemma function_ptr_translated:
  forall (b: block) (f: typed_fundef),
  Genv.find_funct_ptr ge b = Some f -> Genv.find_funct_ptr tge b = Some (simplify_fundef f).
Proof.
  intros. exploit (Genv.find_funct_ptr_match TRANSF); eauto.
  intros (cu & tf & A & B & C). subst tf. assumption.
Qed.

Lemma sig_preserved:
  forall f f', untype_fundef f' = f ->  funsig (untype_fundef (simplify_fundef f')) = funsig f.
Proof.
  intros. destruct f'; cbn in *.
  - destruct t; inv H. reflexivity.
  - destruct f; inv H. reflexivity.
Qed.

Lemma some_init_mem_preserved:
  forall m,
    Genv.init_mem prog = Some m -> Genv.init_mem tprog = Some m.
Proof.
  apply (Genv.init_mem_match TRANSF).
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 -> exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inv H.
  apply funct_ptr_preserved_from_untype in H2 as (f' & eq1 & eq2).
  exists (Callstate nil (untype_fundef (simplify_fundef f')) nil m0); split.
  - econstructor; eauto.
    + apply init_mem_preserved_from_untype in H0.
      apply some_init_mem_preserved in H0.
      apply some_init_mem_preserved_to_untype; auto.
    +  replace (prog_main (transform_program untype_fundef tprog)) with (prog_main (transform_program untype_fundef prog)) at 1.
       * unfold ge0 in H1. rewrite <- untype_program_preserves_find_symbol in *.
         rewrite symbols_preserved. eauto. 
       * repeat rewrite <- transform_program_preserves_main.
         symmetry; eapply match_program_main. eassumption.
    + apply function_ptr_translated in eq1. unfold tge in eq1.
      apply find_some_funct_ptr_preserved_to_untype in eq1. assumption.
    + rewrite <- H3. now apply sig_preserved.
  - rewrite <- eq2. eapply match_states_call; try constructor.
    rewrite eq2. rewrite H3. constructor.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS.
  constructor.
Qed.

Lemma simplify_code_get:
  forall f pc env instr,
    (fn_code f) ! pc = Some instr -> (fn_code (simplify_function env f)) ! pc = Some (simplify env instr).
Proof.
  intros. simpl. rewrite PTree.gmap1. unfold option_map. rewrite H. reflexivity.
Qed.  

Lemma find_function_translated:
  forall ros rs fd,
    find_function ge ros rs = Some fd -> find_function tge ros rs = Some (simplify_fundef fd).
Proof.
  unfold find_function. intros until fd. destruct ros.
  - eapply Genv.find_funct_transf. assumption.
  - rewrite symbols_preserved. destruct (Genv.find_symbol ge i) eqn:E.
    + rewrite E at 1. apply function_ptr_translated.
    + rewrite E at 1. congruence.
Qed.          

Theorem step_simulation:
  forall S1 t S2,
  step ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  (exists S2', step tge S1' t S2' /\ match_states S2 S2').
Proof.
  intros.
  assert (Help:
           forall ros rs fd,
           find_function (untype_genv ge) ros rs = Some fd ->
           exists fd', find_function (untype_genv tge) ros rs = Some (untype_fundef (simplify_fundef fd'))
                  /\ untype_fundef fd' = fd).
  { intros.
    apply find_some_untype_function_preserve' in H0 as (fd' & eq1 & eq2).
    exists fd'. split; try assumption.  apply find_some_function_in_untype. apply find_function_translated; auto. }
  inv H ; inv MS.
  all: try (pose proof (simplify_code_get _ _ env _ H0)  as H'). 
  all: try (eexists; split; econstructor; now eassumption).
  - simpl simplify in H'. destruct (Op.eq_operation op Op.Opcast).
    + subst. destruct args; try discriminate.
      destruct args; try discriminate.
      destruct (env r) eqn: E.
      * eexists; split; econstructor; try eassumption.
        apply wt_regset_assign; try assumption.
        eapply wt_instr_at in H0; try eassumption.
        inv H0. inv H6.
        eapply Val.has_ptype_sub; eauto with ty. inv H1.
        destruct (rs !! r) eqn:Er; constructor.
      * eexists; split; econstructor; try eassumption.
        cbn in *. specialize (H8 r). rewrite E in *.
        destruct (rs !! r) eqn:E1; cbn in *; auto; tauto.
        apply wt_regset_assign; auto.
        eapply wt_instr_at in H0; eauto.
        inv H0. inv H6.
        eapply Val.has_ptype_sub; eauto with ty.  inv H1.
        destruct (rs !! r); constructor.
    + eexists. split; econstructor; try eassumption.
      * destruct op; try eassumption. congruence. 
      * rewrite <- H1. apply Op.eval_operation_preserved. apply symbols_preserved2.
      * apply wt_regset_assign; try assumption.
        eapply wt_instr_at in H0; try eassumption. inv H0. 
        eapply Val.has_ptype_sub; eauto with ty. inv H1. apply H8.
        eapply (Val.has_ptype_sub (S.proj_lo tres)); eauto with ty.
        eapply Op.type_of_operation_sound; eauto.
  - eexists; split.
    eapply exec_Iload; try eassumption.
    rewrite <- H1. eapply Op.eval_addressing_preserved. apply symbols_preserved2.
    econstructor; try eassumption.
    eapply wt_instr_at in H0; try eassumption.
    eapply wt_exec_Iload; try eassumption.
  - eexists; split; econstructor; try eassumption.
    rewrite <- H1.  eapply Op.eval_addressing_preserved. apply symbols_preserved2.
  - apply Help in H1 as (fd' & eq1 & eq2). eexists; split.
    eapply exec_Icall; try eassumption. apply sig_preserved.  exact eq2.
    rewrite <- eq2. eapply match_states_call.
    constructor; try assumption. eapply wt_instr_at in H0; try eassumption. inv H0.
    eauto with ty.
    eapply wt_instr_at in H0; try eassumption. inv H0.
    cbn in *. eapply wt_regset_list3; try eassumption.
    eauto with ty.
  - eapply Help in H1 as (fd' & eq1 & eq2). eexists; split.
    eapply exec_Itailcall; try eassumption.
    apply sig_preserved. assumption.
    rewrite <- eq2. constructor; try assumption.
    rewrite eq2. eapply wt_instr_at in H0; try eassumption. inv H0.
    unfold proj_sig_res_ptype. rewrite H6; auto.
    eapply wt_instr_at in H0; try eassumption. inv H0.
    eapply wt_regset_list3; eauto with ty.
  - eexists; split; econstructor; try eassumption.
    eapply Events.eval_builtin_args_preserved; try eassumption.
    apply symbols_preserved2.
    eapply Events.external_call_symbols_preserved; try eassumption.
    eapply senv_preserved2.
    eapply wt_exec_Ibuiltin; try eassumption.
    eapply wt_instr_at; eassumption.
  - eexists; split.
    eapply exec_Icond; try eassumption. reflexivity.
    econstructor; assumption.
  - eexists; split; econstructor; try eassumption.
    eapply wt_instr_at in H0; try eassumption. inv H0.
    unfold proj_sig_res_ptype. rewrite H2. exact I.
    eapply Val.has_ptype_sub'; eauto with ty.
  - destruct f0; cbn in H3; try discriminate. destruct t; inv H3.
    eexists; split; econstructor; try eassumption.
    eapply wt_init_regs. destruct f. simpl in *.
    inv w; eapply Val.has_ptype_sub_list; eauto with ty.
  - destruct f;  try discriminate. inv H2.
    eexists; split; econstructor; try eassumption.
    eapply Events.external_call_symbols_preserved; try eassumption.
    eapply senv_preserved2.
    unfold proj_sig_res_ptype, Val.has_ptype.
    rewrite <- proj_xtype_ptype_typ.
    eapply Events.external_call_well_typed; eauto.
  - inv STACKS. eexists; split; econstructor; try eassumption.
    eapply wt_regset_assign; try eassumption.
    eapply Val.has_ptype_sub; eauto with ty.
Qed.

Theorem transf_program_correct:
  forward_simulation (semantics prog) (semantics tprog).
Proof.
  eapply forward_simulation_step.
  - apply senv_preserved.
  - eexact transf_initial_states.
  - eexact transf_final_states.
  - eexact step_simulation.
Qed.

End PRESERVATION.
