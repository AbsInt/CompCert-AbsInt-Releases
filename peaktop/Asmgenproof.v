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

(** Correctness proof for peaktop generation: main proof. *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm.
Require Import Asmgen Asmgenproof0 Asmgenproof1.

Local Transparent Archi.ptr64.

Definition match_prog (p: Mach.program) (tp: Asm.program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.

Section PRESERVATION.

Variable prog: Mach.program.
Variable tprog: Asm.program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSF).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSF).

Lemma functions_translated:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial TRANSF).

Lemma functions_transl:
  forall fb f tf,
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transf_function f = OK tf ->
  Genv.find_funct_ptr tge fb = Some (Internal tf).
Proof.
  intros. exploit functions_translated; eauto. intros [tf' [A B]].
  monadInv B. rewrite H0 in EQ; inv EQ; auto.
Qed.

(** * Properties of control flow *)

Lemma transf_function_no_overflow:
  forall f tf,
  transf_function f = OK tf -> list_length_z (fn_code tf) <= Ptrofs.max_unsigned.
Proof.
  intros. monadInv H. destruct (zlt Ptrofs.max_unsigned (list_length_z (fn_code x))); inv EQ0. lia.
Qed.

Lemma exec_straight_exec:
  forall fb f c ep tf tc c' rs m rs' m',
  transl_code_at_pc ge (rs PC) fb f c ep tf tc ->
  exec_straight tge tf tc rs m c' rs' m' ->
  plus step tge (State rs m) E0 (State rs' m').
Proof.
  intros. inv H.
  eapply exec_straight_steps_1; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
Qed.

Lemma exec_straight_at:
  forall fb f c ep tf tc c' ep' tc' rs m rs' m',
  transl_code_at_pc ge (rs PC) fb f c ep tf tc ->
  transl_code f c' ep' = OK tc' ->
  exec_straight tge tf tc rs m tc' rs' m' ->
  transl_code_at_pc ge (rs' PC) fb f c' ep' tf tc'.
Proof.
  intros. inv H.
  exploit exec_straight_steps_2; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
  intros [ofs' [PC' CT']].
  rewrite PC'. constructor; auto.
Qed.

(** The [find_label] function returns the code tail starting at the
  given label.  A connection with [code_tail] is then established. *)

Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some c' else find_label lbl c'
  end.

Lemma label_pos_code_tail:
  forall lbl c pos c',
  find_label lbl c = Some c' ->
  exists pos',
  label_pos lbl pos c = Some pos'
  /\ code_tail (pos' - pos) c c'
  /\ pos < pos' <= pos + list_length_z c.
Proof.
  induction c.
  simpl; intros. discriminate.
  simpl; intros until c'.
  case (is_label lbl a).
  intro EQ; injection EQ; intro; subst c'.
  exists (pos + 1). split. auto. split.
  replace (pos + 1 - pos) with (0 + 1) by lia. constructor. constructor.
  rewrite list_length_z_cons. generalize (list_length_z_pos c). lia.
  intros. generalize (IHc (pos + 1) c' H). intros [pos' [A [B C]]].
  exists pos'. split. auto. split.
  replace (pos' - pos) with ((pos' - (pos + 1)) + 1) by lia.
  constructor. auto.
  rewrite list_length_z_cons. lia.
Qed.

(** The following lemmas show that the translation from Mach to Peaktop
  preserves labels, in the sense that the following diagram commutes:
<<
                          translation
        Mach code ------------------------ Peaktop instr sequence
            |                                          |
            | Mach.find_label lbl       find_label lbl |
            |                                          |
            v                                          v
        Mach code tail ------------------- Peaktop instr seq tail
                          translation
>>
  The proof demands many boring lemmas showing that Peaktop constructor
  functions do not introduce new labels.
*)

Section TRANSL_LABEL.

Remark loadimm_label:
  forall r n k, tail_nolabel k (loadimm r n k).
Proof.
  intros; unfold loadimm. destruct (Int.eq (high_s_14 n) Int.zero); TailNoLabel.
  destruct (Int.eq (low_s_18 n) Int.zero); TailNoLabel.
Qed.
Hint Resolve loadimm_label: labels.

Remark opimm_label:
  forall op1 op2 r n k,
  (forall r r1, nolabel (op1 r r1)) ->
  (forall r n, nolabel (op2 r n)) ->
  tail_nolabel k (opimm op1 op2 r n k).
Proof.
  intros. unfold opimm.
  destruct (Int.eq (high_s_18 n) Int.zero); TailNoLabel.
  unfold loadimm.  destruct (Int.eq (high_s_14 n) Int.zero); TailNoLabel.
  destruct (Int.eq (low_s_18 n) Int.zero); TailNoLabel.
Qed.
Hint Resolve opimm_label: labels.

Remark opuimm_label:
  forall op1 op2 r n k,
  (forall r r1, nolabel (op1 r r1)) ->
  (forall r n, nolabel (op2 r n)) ->
  tail_nolabel k (opuimm op1 op2 r n k).
Proof.
  intros. unfold opuimm.
  destruct (Int.eq (high_u_18 n) Int.zero); TailNoLabel.
  unfold loadimm.  destruct (Int.eq (high_s_14 n) Int.zero); TailNoLabel.
  destruct (Int.eq (low_s_18 n) Int.zero); TailNoLabel.
Qed.
Hint Resolve opuimm_label: labels.

Remark integercmp_label:
  forall c rd r1 r2 k,
  tail_nolabel k (integercmp c rd r1 r2 k).
Proof.
  intros. unfold integercmp. destruct c; TailNoLabel.
Qed.
Hint Resolve integercmp_label: labels.

Remark integercmpu_label:
  forall c rd r1 r2 k,
  tail_nolabel k (integercmpu c rd r1 r2 k).
Proof.
  intros. unfold integercmpu. destruct c; TailNoLabel.
Qed.
Hint Resolve integercmpu_label: labels.

Remark transl_cond_label:
  forall cond args k r c,
  transl_cond cond args r k = OK c -> tail_nolabel k c.
Proof.
  intros. unfold transl_cond in H.
  destruct cond; TailNoLabel.
  eapply tail_nolabel_trans. eapply loadimm_label. TailNoLabel.
  eapply tail_nolabel_trans. eapply loadimm_label. TailNoLabel.
  destruct c0; inv EQ2; TailNoLabel.
  destruct c0; inv EQ2; TailNoLabel.
Qed.

Remark transl_cond_branch_default_label: forall cond args lbl k c,
  transl_cond_branch_default cond args lbl k = OK c -> tail_nolabel k c.
Proof.
  unfold transl_cond_branch_default; intros.
  eapply tail_nolabel_trans; [eapply transl_cond_label;eauto|TailNoLabel].
  destruct (cond_needs_inversion cond); TailNoLabel.
Qed.
Hint Resolve transl_cond_branch_default_label: labels.

Remark transl_cond_branch_label: forall cond args lbl k c,
  transl_cond_branch cond args lbl k = OK c -> tail_nolabel k c.
Proof.
  unfold transl_cond_branch.
  destruct cond; eauto with labels.
  - destruct c; repeat (destruct args; eauto with labels);
    intros; monadInv H; TailNoLabel.
  - destruct c; repeat (destruct args; eauto with labels); intros; try monadInv H; TailNoLabel.
     eapply tail_nolabel_trans. eapply loadimm_label. TailNoLabel.
     eapply tail_nolabel_trans. eapply loadimm_label. TailNoLabel.
  - destruct c; repeat (destruct args; eauto with labels); destruct (Int.eq n Int.zero); eauto with labels;
      intros; monadInv H; TailNoLabel.
  - repeat (destruct args; eauto with labels).
    intros; monadInv H.
    destruct c; inv EQ2; TailNoLabel.
  - repeat (destruct args; eauto with labels).
    intros; monadInv H.
    destruct c; inv EQ2; TailNoLabel.
Qed.

Remark transl_op_label:
  forall op args r k c,
  transl_op op args r k = OK c -> tail_nolabel k c.
Proof.
  unfold transl_op; intros; destruct op; TailNoLabel; try (destruct (freg_eq x x0); TailNoLabel).
  - destruct (preg_of r); try discriminate; destruct (preg_of m); inv H; TailNoLabel.
  - unfold addimm; TailNoLabel.
  - unfold extsb; TailNoLabel.
  - unfold extsh; TailNoLabel.
  - unfold addimm; TailNoLabel.
  - unfold subimm; TailNoLabel.
  - unfold mulimm; TailNoLabel.
  - unfold orimm; TailNoLabel.
  - unfold andimm; TailNoLabel.
  - unfold nandimm; TailNoLabel.
  - unfold xorimm; TailNoLabel.
  - unfold sraimm; TailNoLabel.
  - destruct (Int.eq n Int.zero); TailNoLabel.
  - unfold sllimm; TailNoLabel.
  - unfold srlimm; TailNoLabel.
  - unfold rrimm; TailNoLabel.
  - eapply tail_nolabel_trans. eapply transl_cond_label; eauto.
    destruct (cond_needs_inversion cond); TailNoLabel.
Qed.

Remark accessind_label:
  forall instr base ofs k,
  (forall addr, nolabel (instr addr)) ->
  tail_nolabel k (accessind instr base ofs k).
Proof.
  intros. unfold accessind. destruct (Int.eq (high_s_20 (Ptrofs.to_int ofs)) Int.zero); TailNoLabel.
  eapply tail_nolabel_trans. eapply loadimm_label.
  TailNoLabel.
Qed.

Remark loadind_label:
  forall base ofs ty dst k c,
  loadind base ofs ty dst k = OK c -> tail_nolabel k c.
Proof.
  unfold loadind. intros.
  destruct ty; try discriminate;
  destruct (preg_of dst); try discriminate.
  TailNoLabel. apply accessind_label; TailNoLabel.
  TailNoLabel. apply accessind_label; TailNoLabel.
  TailNoLabel. apply accessind_label; TailNoLabel.
Qed.

Remark storeind_label:
  forall base ofs ty src k c,
  storeind src base ofs ty k = OK c -> tail_nolabel k c.
Proof.
  unfold storeind. intros.
  destruct ty; try discriminate;
  destruct (preg_of src); try discriminate.
  TailNoLabel. apply accessind_label; TailNoLabel.
  TailNoLabel. apply accessind_label; TailNoLabel.
  TailNoLabel. apply accessind_label; TailNoLabel.
Qed.

Remark storeptr_label:
  forall src base ofs k,
  tail_nolabel k (storeptr src base ofs k).
Proof.
  unfold storeptr. intros. eapply accessind_label.
  TailNoLabel.
Qed.

Remark loadptr_label:
  forall src base ofs k,
  tail_nolabel k (loadptr src base ofs k).
Proof.
  unfold loadptr. intros. eapply accessind_label.
  TailNoLabel.
Qed.

Remark transl_memory_access_label:
  forall instr addr args k c,
  (forall addr, nolabel (instr addr)) ->
  transl_memory_access instr addr args k = OK c -> tail_nolabel k c.
Proof.
  unfold transl_memory_access. intros.
  destruct addr; try discriminate;
  destruct args; try discriminate.
  destruct args; try discriminate.
  destruct (reg_of m); try discriminate.
  destruct (Int.eq (high_s_20 ofs) Int.zero).
  inv H0. TailNoLabel. inv H0.
  unfold loadimm.  destruct (Int.eq (high_s_14 ofs) Int.zero); TailNoLabel.
  destruct (Int.eq (low_s_18 ofs) Int.zero); TailNoLabel. TailNoLabel.
  TailNoLabel.
  eapply accessind_label; eauto.
Qed.


Remark transl_epilogue_label:
  forall f k, tail_nolabel k (transl_epilogue f k).
Proof.
  intros; unfold transl_epilogue.
  eapply tail_nolabel_trans. eapply loadptr_label. TailNoLabel.
Qed.


Remark save_lr_label:
  forall ofs k, tail_nolabel k (save_lr ofs k).
Proof.
  unfold save_lr; intros.
  destruct (Int.eq (high_s_20 (Ptrofs.to_int ofs))).
  TailNoLabel.
  TailNoLabel. eapply storeptr_label; eauto.
Qed.


Lemma transl_instr_label:
  forall f i ep k c,
    transl_instr f i ep k = OK c ->
    match i with Mlabel lbl => c = Plabel lbl :: k | _ => tail_nolabel k c end.
Proof.
  unfold transl_instr; intros; destruct i; TailNoLabel.
  - eapply loadind_label; eauto.
  - eapply storeind_label; eauto.
  - destruct ep. eapply loadind_label; eauto.
    eapply tail_nolabel_trans. unfold loadptr.
    eapply accessind_label. TailNoLabel.
    eapply loadind_label. TailNoLabel.
  - eapply transl_op_label; eauto.
  - destruct m; monadInv H; eapply transl_memory_access_label; eauto; TailNoLabel.
  - destruct m; monadInv H; eapply transl_memory_access_label; eauto; TailNoLabel.
  - destruct s0; monadInv H; TailNoLabel.
  - destruct s0; monadInv H; TailNoLabel; (eapply tail_nolabel_trans; [apply transl_epilogue_label | TailNoLabel]).
  - eapply transl_cond_branch_label; eauto.
  - eapply tail_nolabel_trans; [apply transl_epilogue_label | TailNoLabel].
Qed.

Lemma transl_instr_label':
  forall lbl f i ep k c,
  transl_instr f i ep k = OK c ->
  find_label lbl c = if Mach.is_label lbl i then Some k else find_label lbl k.
Proof.
  intros. exploit transl_instr_label; eauto.
  destruct i; try (intros [A B]; apply B).
  intros. subst c. simpl. auto.
Qed.

Lemma transl_code_label:
  forall lbl f c ep tc,
  transl_code f c ep = OK tc ->
  match Mach.find_label lbl c with
  | None => find_label lbl tc = None
  | Some c' => exists tc', find_label lbl tc = Some tc' /\ transl_code f c' false = OK tc'
  end.
Proof.
  induction c; simpl; intros.
  inv H. auto.
  monadInv H. rewrite (transl_instr_label' lbl _ _ _ _ _ EQ0).
  generalize (Mach.is_label_correct lbl a).
  destruct (Mach.is_label lbl a); intros.
  subst a. simpl in EQ. exists x; auto.
  eapply IHc; eauto.
Qed.

Lemma transl_find_label:
  forall lbl f tf,
  transf_function f = OK tf ->
  match Mach.find_label lbl f.(Mach.fn_code) with
  | None => find_label lbl (fn_code tf) = None
  | Some c => exists tc, find_label lbl (fn_code tf) = Some tc /\ transl_code f c false = OK tc
  end.
Proof.
  intros. monadInv H. destruct (zlt Ptrofs.max_unsigned (list_length_z (fn_code x))); inv EQ0.
  monadInv EQ. simpl. erewrite tail_nolabel_find_label by (apply save_lr_label). simpl.
  eapply transl_code_label; eauto.
  rewrite transl_code'_transl_code in EQ0.
  simpl. eauto.
Qed.

End TRANSL_LABEL.


(** A valid branch in a piece of Mach code translates to a valid ``go to''
  transition in the generated Peaktop code. *)

Lemma find_label_goto_label:
  forall f tf lbl rs m c' b ofs,
  Genv.find_funct_ptr ge b = Some (Internal f) ->
  transf_function f = OK tf ->
  rs PC = Vptr b ofs ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  exists tc', exists rs',
    goto_label tf lbl rs m = Next rs' m
  /\ transl_code_at_pc ge (rs' PC) b f c' false tf tc'
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros. exploit (transl_find_label lbl f tf); eauto. rewrite H2.
  intros [tc [A B]].
  exploit label_pos_code_tail; eauto. instantiate (1 := 0).
  intros [pos' [P [Q R]]].
  exists tc; exists (rs#PC <- (Vptr b (Ptrofs.repr pos'))).
  split. unfold goto_label. rewrite P. rewrite H1. auto.
  split. rewrite Pregmap.gss. constructor; auto.
  rewrite Ptrofs.unsigned_repr. replace (pos' - 0) with pos' in Q.
  auto. lia.
  generalize (transf_function_no_overflow _ _ H0). lia.
  intros. apply Pregmap.gso; auto.
Qed.

(** Existence of return addresses *)

Lemma return_address_exists:
  forall f sg ros c, is_tail (Mcall sg ros :: c) f.(Mach.fn_code) ->
  exists ra, return_address_offset f c ra.
Proof.
  intros. eapply Asmgenproof0.return_address_exists; eauto.
- intros. exploit transl_instr_label; eauto.
  destruct i; try (intros [A B]; apply A). intros. subst c0. repeat constructor.
- intros. monadInv H0.
  destruct (zlt Ptrofs.max_unsigned (list_length_z x.(fn_code))); inv EQ0. monadInv EQ.
  rewrite transl_code'_transl_code in EQ0.
  exists x; exists (save_lr_preserves_Reg2 (fn_retaddr_ofs f0)); split; auto. constructor. eapply is_tail_trans. 2:apply tail_nolabel_is_tail; apply save_lr_label.
  repeat constructor.
- exact transf_function_no_overflow.
Qed.

(** * Proof of semantic preservation *)

(** Semantic preservation is proved using simulation diagrams
  of the following form.
<<
           st1 --------------- st2
            |                   |
           t|                  *|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The invariant is the [match_states] predicate below, which includes:
- The Asm code pointed by the PC register is the translation of
  the current Mach code sequence.
- Mach register values and Asm register values agree.
*)

Inductive match_states: Mach.state -> Asm.state -> Prop :=
  | match_states_intro:
      forall s fb sp c ep ms m m' rs f tf tc
        (STACKS: match_stack ge s)
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
        (MEXT: Mem.extends m m')
        (AT: transl_code_at_pc ge (rs PC) fb f c ep tf tc)
        (AG: agree ms sp rs)
        (DXP: ep = true -> rs#Reg2 = parent_sp s),
      match_states (Mach.State s fb sp c ms m)
                   (Asm.State rs m')
  | match_states_call:
      forall s fb ms m m' rs
        (STACKS: match_stack ge s)
        (MEXT: Mem.extends m m')
        (AG: agree ms (parent_sp s) rs)
        (ATPC: rs PC = Vptr fb Ptrofs.zero)
        (ATLR: rs CRP = parent_ra s),
      match_states (Mach.Callstate s fb ms m)
                   (Asm.State rs m')
  | match_states_return:
      forall s ms m m' rs
        (STACKS: match_stack ge s)
        (MEXT: Mem.extends m m')
        (AG: agree ms (parent_sp s) rs)
        (ATPC: rs PC = parent_ra s),
      match_states (Mach.Returnstate s ms m)
                   (Asm.State rs m').


Lemma exec_straight_steps:
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2,
  match_stack ge s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists rs2,
       exec_straight tge tf c rs1 m1' k rs2 m2'
    /\ agree ms2 sp rs2
    /\ (it1_is_parent ep i = true -> rs2#Reg2 = parent_sp s)) ->
  exists st',
  plus step tge (State rs1 m1') E0 st' /\
  match_states (Mach.State s fb sp c ms2 m2) st'.
Proof.
  intros. inversion H2. subst. monadInv H7.
  exploit H3; eauto. intros [rs2 [A [B C]]].
  exists (State rs2 m2'); split.
  eapply exec_straight_exec; eauto.
  econstructor; eauto. eapply exec_straight_at; eauto.
Qed.

Lemma exec_straight_steps_goto:
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 lbl c',
  match_stack ge s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  it1_is_parent ep i = false ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists jmp, exists k', exists rs2,
       exec_straight tge tf c rs1 m1' (jmp :: k') rs2 m2'
    /\ agree ms2 sp rs2
    /\ exec_instr tge tf jmp rs2 m2' = goto_label tf lbl rs2 m2') ->
  exists st',
  plus step tge (State rs1 m1') E0 st' /\
  match_states (Mach.State s fb sp c' ms2 m2) st'.
Proof.
  intros. inversion H3. subst. monadInv H9.
  exploit H5; eauto. intros [jmp [k' [rs2 [A [B C]]]]].
  generalize (functions_transl _ _ _ H7 H8); intro FN.
  generalize (transf_function_no_overflow _ _ H8); intro NOOV.
  exploit exec_straight_steps_2; eauto.
  intros [ofs' [PC2 CT2]].
  exploit find_label_goto_label; eauto.
  intros [tc' [rs3 [GOTO [AT' OTH]]]].
  exists (State rs3 m2'); split.
  eapply plus_right'.
  eapply exec_straight_steps_1; eauto.
  econstructor; eauto.
  eapply find_instr_tail. eauto.
  rewrite C. eexact GOTO.
  traceEq.
  econstructor; eauto.
  apply agree_exten with rs2; auto with asmgen.
  congruence.
Qed.

Lemma exec_straight_opt_steps_goto:
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 lbl c',
  match_stack ge s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  it1_is_parent ep i = false ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists jmp, exists k', exists rs2,
       exec_straight_opt tge tf c rs1 m1' (jmp :: k') rs2 m2'
    /\ agree ms2 sp rs2
    /\ exec_instr tge tf jmp rs2 m2' = goto_label tf lbl rs2 m2') ->
  exists st',
  plus step tge (State rs1 m1') E0 st' /\
  match_states (Mach.State s fb sp c' ms2 m2) st'.
Proof.
  intros. inversion H3. subst. monadInv H9.
  exploit H5; eauto. intros [jmp [k' [rs2 [A [B C]]]]].
  generalize (functions_transl _ _ _ H7 H8); intro FN.
  generalize (transf_function_no_overflow _ _ H8); intro NOOV.
  inv A.
- exploit find_label_goto_label; eauto.
  intros [tc' [rs3 [GOTO [AT' OTH]]]].
  exists (State rs3 m2'); split.
  apply plus_one. econstructor; eauto.
  eapply find_instr_tail. eauto.
  rewrite C. eexact GOTO.
  econstructor; eauto.
  apply agree_exten with rs2; auto with asmgen.
  congruence.
- exploit exec_straight_steps_2; eauto.
  intros [ofs' [PC2 CT2]].
  exploit find_label_goto_label; eauto.
  intros [tc' [rs3 [GOTO [AT' OTH]]]].
  exists (State rs3 m2'); split.
  eapply plus_right'.
  eapply exec_straight_steps_1; eauto.
  econstructor; eauto.
  eapply find_instr_tail. eauto.
  rewrite C. eexact GOTO.
  traceEq.
  econstructor; eauto.
  apply agree_exten with rs2; auto with asmgen.
  congruence.
Qed.

(** We need to show that, in the simulation diagram, we cannot
  take infinitely many Mach transitions that correspond to zero
  transitions on the Peaktop side.  Actually, all Mach transitions
  correspond to at least one Peaktop transition, except the
  transition from [Machsem.Returnstate] to [Machsem.State].
  So, the following integer measure will suffice to rule out
  the unwanted behaviour. *)

Definition measure (s: Mach.state) : nat :=
  match s with
  | Mach.State _ _ _ _ _ _ => 0%nat
  | Mach.Callstate _ _ _ _ => 0%nat
  | Mach.Returnstate _ _ _ => 1%nat
  end.


Remark preg_of_not_Reg2: forall r, negb (mreg_eq r R2) = true -> GPR Reg2 <> preg_of r.
Proof.
  intros. change (GPR Reg2) with (preg_of R2). red; intros.
  exploit preg_of_injective; eauto. intros; subst r.
  unfold proj_sumbool in H; rewrite dec_eq_true in H; discriminate.
Qed.


Lemma reg_val:
  forall ms sp rs r r',
  agree ms sp rs ->
  reg_of r = OK r' ->
  Val.lessdef (ms r) rs#r'.
Proof.
  intros. rewrite <- (reg_of_eq _ _ H0). eapply preg_val; eauto.
Qed.

(** This is the simulation diagram.  We prove it by case analysis on the Mach transition. *)

Theorem step_simulation:
  forall S1 t S2, Mach.step return_address_offset ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  (exists S2', plus step tge S1' t S2' /\ match_states S2 S2')
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 S1')%nat.
Proof.
  induction 1; intros; inv MS.
  - (* Mlabel *)
    left; eapply exec_straight_steps; eauto; intros.
    monadInv TR. econstructor; split. apply exec_straight_one.
    simpl; eauto. eauto.
    split. apply agree_nextinstr; auto.
    simpl; congruence.
  - (* Mgetstack *)
    unfold load_stack in H.
    exploit Mem.loadv_extends; eauto. intros [v' [A B]].
    rewrite (sp_val _ _ _ AG) in A.
    left; eapply exec_straight_steps; eauto. intros. simpl in TR.
    exploit loadind_correct; eauto with asmgen. intros [rs' [P [Q R]]].
    exists rs'; split. eauto.
    split. eapply agree_set_mreg; eauto with asmgen. congruence.
    simpl; congruence.
  - (* Msetstack *)
    unfold store_stack in H.
    assert (Val.lessdef (rs src) (rs0 (preg_of src))) by (eapply preg_val; eauto).
    exploit Mem.storev_extends; eauto. intros [m2' [A B]].
    left; eapply exec_straight_steps; eauto.
    rewrite (sp_val _ _ _ AG) in A. intros. simpl in TR.
    exploit storeind_correct; eauto with asmgen. intros [rs' [P Q]].
    exists rs'; split. eauto.
    split. eapply agree_undef_regs; eauto with asmgen.
    simpl; intros. rewrite Q; auto with asmgen.
  - (* Mgetparam *)
    assert (f0 = f) by congruence; subst f0.
    unfold load_stack in *.
    exploit Mem.loadv_extends. eauto. eexact H0. auto.
    intros [parent' [A B]].
    exploit lessdef_parent_sp; eauto. clear B; intros B; subst parent'.
    exploit Mem.loadv_extends. eauto. eexact H1. auto.
    intros [v' [C D]].
    Opaque loadind.
    left; eapply exec_straight_steps; eauto; intros. monadInv TR.
    destruct ep.
    + (* Reg2 contains parent *)
      exploit loadind_correct. eexact EQ.
      instantiate (2 := rs0). simpl; rewrite DXP; eauto. simpl; congruence.
      intros [rs1 [P [Q R]]].
      exists rs1; split. eauto.
      split. eapply agree_set_mreg. eapply agree_set_mreg; eauto. congruence. auto with asmgen.
      simpl; intros. rewrite R; auto with asmgen.
      apply preg_of_not_Reg2; auto.
    + (* Reg2 does not contain parent *)
      rewrite (sp_val _ _ _ AG) in A.
      exploit loadptr_correct; eauto. congruence. intros [rs1 [P [Q R]]].
      exploit loadind_correct. eexact EQ. instantiate (2 := rs1). simpl; rewrite Q. eauto. simpl; congruence.
      intros [rs2 [S [T U]]].
      exists rs2; split. eapply exec_straight_trans; eauto.
      split. eapply agree_set_mreg. eapply agree_set_mreg. eauto. eauto.
      instantiate (1 := rs1#Reg2 <- (rs2#Reg2)). intros.
      rewrite Pregmap.gso; auto with asmgen.
      congruence.
      intros. unfold Pregmap.set. destruct (PregEq.eq r' Reg2). congruence. auto with asmgen.
      simpl; intros. rewrite U; auto with asmgen.
      apply preg_of_not_Reg2; auto.
  - (* MOP *)
    assert (eval_operation tge sp op (map rs args) m = Some v).
    { rewrite <- H. apply eval_operation_preserved. exact symbols_preserved. }
    exploit eval_operation_lessdef. eapply preg_vals; eauto. eauto. eexact H0.
    intros [v' [A B]]. rewrite (sp_val _ _ _ AG) in A.
    left; eapply exec_straight_steps; eauto; intros. simpl in TR.
    exploit transl_op_correct; eauto. intros [rs2 [P [Q R]]].
    assert (S: Val.lessdef v (rs2 (preg_of res))) by (eapply Val.lessdef_trans; eauto).
    exists rs2; split. eauto. split.
    eapply agree_set_undef_mreg; eauto with asmgen.
    simpl. destruct op; try congruence. destruct ep; simpl; try congruence. intros.
    rewrite R; auto. apply preg_of_not_Reg2; auto. exact I.
  - (* Mload *)
    assert (Op.eval_addressing tge sp addr (map rs args) = Some a).
    { rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved. }
    exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
    intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
    exploit Mem.loadv_extends; eauto. intros [v' [C D]].
    left; eapply exec_straight_steps; eauto; intros. simpl in TR.
    exploit transl_load_correct; eauto. intros [rs2 [P [Q R]]].
    exists rs2; split. eauto.
    split. eapply agree_set_undef_mreg; eauto. congruence.
    simpl; congruence.
  - (* Mstore *)
     assert (Op.eval_addressing tge sp addr (map rs args) = Some a).
     { rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved. }
     exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
     intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
     assert (Val.lessdef (rs src) (rs0 (preg_of src))) by (eapply preg_val; eauto).
     exploit Mem.storev_extends; eauto. intros [m2' [C D]].
     left; eapply exec_straight_steps; eauto.
     intros. simpl in TR. exploit transl_store_correct; eauto. intros [rs2 [P Q]].
     exists rs2; split. eauto.
     split. eapply agree_undef_regs; eauto with asmgen.
     simpl; congruence.
  - (* Mcall *)
    assert (f0 = f) by congruence.  subst f0.
    inv AT.
    assert (NOOV: list_length_z (fn_code tf) <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.
    destruct ros as [rf|fid]; simpl in H; monadInv H5.
    + (* Indirect call *)
      assert (rs rf = Vptr f' Ptrofs.zero).
      destruct (rs rf); try discriminate.
      revert H; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence.
      assert (rs0 x0 = Vptr f' Ptrofs.zero).
      exploit reg_val; eauto. rewrite H5; intros LD; inv LD; auto.
      generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT1.
      assert (TCA: transl_code_at_pc ge (Vptr fb (Ptrofs.add ofs Ptrofs.one)) fb f c false tf x).
      econstructor; eauto.
      exploit return_address_offset_correct; eauto. intros; subst ra.
      left; econstructor; split.
      apply plus_one. eapply exec_step_internal. eauto.
      eapply functions_transl; eauto. eapply find_instr_tail; eauto.
      simpl. eauto.
      econstructor; eauto.
      econstructor; eauto.
      eapply agree_sp_def; eauto.
      simpl. eapply agree_exten; eauto. intros. Simpl.
      Simpl. rewrite <- H2. auto.
    + (* Direct call *)
      generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT1.
      assert (TCA: transl_code_at_pc ge (Vptr fb (Ptrofs.add ofs Ptrofs.one)) fb f c false tf x).
      econstructor; eauto.
      exploit return_address_offset_correct; eauto. intros; subst ra.
      left; econstructor; split.
      apply plus_one. eapply exec_step_internal. eauto.
      eapply functions_transl; eauto. eapply find_instr_tail; eauto.
      simpl. unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H. eauto.
      econstructor; eauto.
      econstructor; eauto.
      eapply agree_sp_def; eauto.
      simpl. eapply agree_exten; eauto. intros. Simpl.
      Simpl. rewrite <- H2. auto.
  - (* Mtailcall *)
    assert (f0 = f) by congruence.  subst f0.
    inversion AT; subst.
    assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
    { eapply transf_function_no_overflow; eauto. }
    exploit Mem.loadv_extends. eauto. eexact H1. auto. simpl. intros [parent' [A B]].
    destruct ros as [rf|fid]; simpl in H; monadInv H7.
    + (* Indirect call *)
      assert (rs rf = Vptr f' Ptrofs.zero).
      { destruct (rs rf); try discriminate.
        revert H; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence. }
      assert (rs0 x0 = Vptr f' Ptrofs.zero).
      { exploit reg_val; eauto. rewrite H7; intros LD; inv LD; auto. }
      exploit transl_epilogue_correct; eauto. intros (rs1 & m1 & U & V & W & X & Y & Z).
      exploit exec_straight_steps_2; eauto using functions_transl.
      intros (ofs' & P & Q).
      left; econstructor; split.
      (* execution *)
      eapply plus_right'. eapply exec_straight_exec; eauto.
      econstructor. eexact P. eapply functions_transl; eauto. eapply find_instr_tail. eexact Q.
      simpl. reflexivity.
      traceEq.
      (* match states *)
      econstructor; eauto.
      apply agree_set_other; auto with asmgen.
      Simpl. rewrite Z by (rewrite <- (reg_of_eq _ _ EQ1); eauto with asmgen). assumption.
    + (* Direct call *)
      exploit transl_epilogue_correct; eauto. intros (rs1 & m1 & U & V & W & X & Y & Z).
      exploit exec_straight_steps_2; eauto using functions_transl.
      intros (ofs' & P & Q).
      left; econstructor; split.
      (* execution *)
      eapply plus_right'. eapply exec_straight_exec; eauto.
      econstructor. eexact P. eapply functions_transl; eauto. eapply find_instr_tail. eexact Q.
      simpl. reflexivity.
      traceEq.
      (* match states *)
      econstructor; eauto.
      apply agree_set_other; auto with asmgen.
      Simpl. unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H. auto.
  - (* Mbuiltin *)
    inv AT. monadInv H4.
    exploit functions_transl; eauto. intro FN.
    generalize (transf_function_no_overflow _ _ H3); intro NOOV.
    exploit builtin_args_match; eauto. intros [vargs' [P Q]].
    exploit external_call_mem_extends; eauto.
    intros [vres' [m2' [A [B [C D]]]]].
    left. econstructor; split. apply plus_one.
    eapply exec_step_builtin. eauto. eauto.
    eapply find_instr_tail; eauto.
    erewrite <- sp_val by eauto.
    eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
    eauto.
    econstructor; eauto.
    instantiate (2 := tf); instantiate (1 := x).
    unfold nextinstr. rewrite Pregmap.gss.
    rewrite set_res_other. rewrite undef_regs_other_2.
    rewrite <- H1. simpl. econstructor; eauto.
    eapply code_tail_next_int; eauto.
    rewrite preg_notin_charact. intros. auto with asmgen.
    auto with asmgen.
    apply agree_nextinstr. eapply agree_set_res; auto.
    eapply agree_undef_regs; eauto. intros; apply undef_regs_other_2; auto.
    congruence.
  - (* Mgoto *)
    assert (f0 = f) by congruence. subst f0.
    inv AT. monadInv H4.
    exploit find_label_goto_label; eauto. intros [tc' [rs' [GOTO [AT2 INV]]]].
    left; exists (State rs' m'); split.
    apply plus_one. econstructor; eauto.
    eapply functions_transl; eauto.
    eapply find_instr_tail; eauto.
    simpl; eauto.
    econstructor; eauto.
    eapply agree_exten; eauto with asmgen.
    congruence.
  - (* Mcond true *)
    assert (f0 = f) by congruence. subst f0.
    exploit eval_condition_lessdef. eapply preg_vals; eauto. eauto. eauto. intros EC.
    left; eapply exec_straight_opt_steps_goto; eauto.
    intros. simpl in TR.
    exploit transl_cond_branch_correct; eauto. intros (rs' & jmp & A & B & C).
    exists jmp; exists k; exists rs'.
    split. eexact A.
    split. apply agree_undef_regs with rs0; auto with asmgen.
    exact B.
  - (* Mcond false *)
    exploit eval_condition_lessdef. eapply preg_vals; eauto. eauto. eauto. intros EC.
    left; eapply exec_straight_steps; eauto. intros. simpl in TR.
    exploit transl_cond_branch_correct; eauto. intros (rs' & jmp & A & B & C).
    econstructor; split.
    eapply exec_straight_opt_right. eexact A. apply exec_straight_one. eexact B. auto.
    split. apply agree_undef_regs with rs0; auto. intros. Simpl.
    simpl; congruence.
  - (* Mjumptable *)
    assert (f0 = f) by congruence. subst f0.
    inv AT. monadInv H6.
    exploit functions_transl; eauto. intro FN.
    generalize (transf_function_no_overflow _ _ H5); intro NOOV.
    exploit find_label_goto_label. eauto. eauto.
    instantiate ( 2:= rs0).
    Simpl. eauto.
    eauto.
    intros [tc' [rs' [A [B C]]]].
    exploit reg_val; eauto. rewrite H. intros LD; inv LD.
    left; econstructor; split.
    apply plus_one. econstructor; eauto.
    eapply find_instr_tail; eauto.
    simpl. Simpl. rewrite <- H9. unfold Mach.label in H0; unfold label; rewrite H0. eexact A.
    econstructor; eauto.
    eapply agree_undef_regs; eauto.
    simpl. intros. rewrite C; auto with asmgen. Simpl.
    congruence.
  - (* Mreturn *)
    assert (f0 = f) by congruence. subst f0.
    inversion AT; subst.
    assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.
    monadInv H6.
    exploit transl_epilogue_correct; eauto.
    intros (rs2 & m2' & A & B & C & D & E & F).
    exploit exec_straight_steps_2; eauto using functions_transl.
    intros (ofs' & U & V).
    set (rs3 := rs2#PC <- (parent_ra s)).
    left; exists (State rs3 m2'); split.
    (* execution *)
    eapply plus_right'. eapply exec_straight_exec; eauto.
    econstructor; eauto using functions_transl, find_instr_tail.
    simpl. rewrite D; reflexivity.
    traceEq.
    (* match states *)
    econstructor; eauto. apply agree_set_other; auto.
  - (* internal function *)

    exploit functions_translated; eauto. intros [tf [A B]]. monadInv B.
    generalize EQ; intros EQ'. monadInv EQ'.
    destruct (zlt Ptrofs.max_unsigned (list_length_z (fn_code x0))); inversion EQ1. clear EQ1. subst x0.
    monadInv EQ0.
    set (ra_ofs := fn_retaddr_ofs f) in *.
    set (ra_ofs' := Ptrofs.to_int ra_ofs) in *.
    set (tfbody := Pallocframe (fn_stacksize f) (fn_link_ofs f) ::
                               save_lr ra_ofs x0) in *.
    set (tf := {| fn_sig := Mach.fn_sig f; fn_code := tfbody |}) in *.
    unfold store_stack in *.
    exploit Mem.alloc_extends. eauto. eauto. apply Z.le_refl. apply Z.le_refl.
    intros [m1' [C D]].
    exploit Mem.storev_extends. eexact D. eexact H1. eauto. eauto.
    intros [m2' [F G]].
    exploit Mem.storev_extends. eexact G. eexact H2. eauto. eauto.
    intros [m3' [P Q]].
    (* Execution of function prologue *)
    set (rs2 := nextinstr (rs0#Reg2 <- (parent_sp s) #SP <- (Vptr stk Ptrofs.zero)) # TMP <- Vundef).
    edestruct (save_lr_correct tge tf ra_ofs x0 rs2) as (rs3 & X & Y & Z).
    change (rs2 Reg2) with sp. change (rs2 CRP) with (rs0 CRP). rewrite ATLR. eexact P.
    assert (EXEC_PROLOGUE:
              exec_straight tge tf
                            (fn_code tf) rs0 m'
                            x0 rs3 m3').
    {
      change (fn_code tf) with tfbody; unfold tfbody.
      eapply exec_straight_trans with (rs2 := rs2) (m2 := m2').
      apply exec_straight_one.
      unfold exec_instr. rewrite C. fold sp.
      rewrite <- (sp_val _ _ _ AG). unfold Tptr, chunk_of_type, Archi.ptr64 in F. rewrite F. auto.
      auto. eexact X.
    }
    (* After the function prologue is the code for the function body *)
    exploit exec_straight_steps_2; eauto using functions_transl. lia. constructor.
    intros (ofsbody & U & V).
    (* Conclusions *)
    left; exists (State rs3 m3'); split.
    eapply exec_straight_steps_1; eauto. lia. constructor.
    econstructor; eauto. rewrite U. econstructor; eauto. rewrite <- transl_code'_transl_code. auto.
    apply agree_undef_regs2 with rs2; eauto.
    apply agree_nextinstr.
    apply agree_set_other; auto with asmgen.
    eapply agree_change_sp.
    apply agree_undef_regs with rs0; eauto.
    intros; Simpl.
    congruence.
  - (* external function *)
    exploit functions_translated; eauto.
    intros [tf [A B]]. simpl in B. inv B.
    exploit extcall_arguments_match; eauto.
    intros [args' [C D]].
    exploit external_call_mem_extends; eauto.
    intros [res' [m2' [P [Q [R S]]]]].
    left; econstructor; split.
    apply plus_one. eapply exec_step_external; eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
    econstructor; eauto.
    unfold loc_external_result. apply agree_set_other; auto. apply agree_set_pair; auto.
    apply agree_undef_caller_save_regs; auto.
  - (* return *)
    inv STACKS. simpl in *.
    right. split. lia. split. auto.
    rewrite <- ATPC in H5. econstructor; eauto. congruence.
Qed.

Lemma transf_initial_states:
  forall st1, Mach.initial_state prog st1 ->
  exists st2, Asm.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H. unfold ge0 in *.
  econstructor; split.
  econstructor.
  eapply (Genv.init_mem_transf_partial TRANSF); eauto.
  replace (Genv.symbol_address (Genv.globalenv tprog) (prog_main tprog) Ptrofs.zero)
     with (Vptr fb Ptrofs.zero).
  econstructor; eauto.
  constructor.
  apply Mem.extends_refl.
  split. auto. simpl. unfold Vnullptr; simpl; congruence. intros. rewrite Regmap.gi. auto.
  unfold Genv.symbol_address.
  rewrite (match_program_main TRANSF).
  rewrite symbols_preserved.
  unfold ge; rewrite H1. auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> Mach.final_state st1 r -> Asm.final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. constructor.
  auto.
  compute in H1. inv H1.
  generalize (preg_val _ _ _ R4 AG). rewrite H2. intros LD; inv LD. auto.
Qed.

Theorem transf_program_correct:
  forward_simulation (Mach.semantics return_address_offset prog) (Asm.semantics tprog).
Proof.
  eapply forward_simulation_star with (measure := measure).
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact step_simulation.
Qed.

End PRESERVATION.
