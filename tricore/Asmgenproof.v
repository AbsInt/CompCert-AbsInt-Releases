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

(** Correctness proof for TriCore generation: main proof. *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm.
Require Import Asmgen Asmgenproof0 Asmgenproof1.

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
  transf_function f = OK tf -> list_length_z tf.(fn_code) <= Ptrofs.max_unsigned.
Proof.
  intros. monadInv H. destruct (zlt Ptrofs.max_unsigned (list_length_z x.(fn_code))); inv EQ0.
  lia.
Qed.

Lemma exec_straight_exec:
  forall fb f c ep tf tc c' rs m rs' m' pcl,
  transl_code_at_pc ge (rs PC) fb f c ep tf tc ->
  exec_straight tge tf tc rs m c' rs' m' pcl ->
  plus step tge (State rs m pcl) E0 (State rs' m' pcl).
Proof.
  intros. inv H.
  eapply exec_straight_steps_1; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
Qed.

Lemma exec_straight_at:
  forall fb f c ep tf tc c' ep' tc' rs m rs' m' pcl,
  transl_code_at_pc ge (rs PC) fb f c ep tf tc ->
  transl_code f c' ep' = OK tc' ->
  exec_straight tge tf tc rs m tc' rs' m' pcl ->
  transl_code_at_pc ge (rs' PC) fb f c' ep' tf tc'.
Proof.
  intros. inv H.
  exploit exec_straight_steps_2; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
  intros [ofs' [PC' CT']].
  rewrite PC'. constructor; auto.
Qed.


(** The following lemmas show that the translation from Mach to Asm
  preserves labels, in the sense that the following diagram commutes:
<<
                          translation
        Mach code ------------------------ Asm instr sequence
            |                                          |
            | Mach.find_label lbl       find_label lbl |
            |                                          |
            v                                          v
        Mach code tail ------------------- Asm instr seq tail
                          translation
>>
  The proof demands many boring lemmas showing that Asm constructor
  functions do not introduce new labels.
*)

Section TRANSL_LABEL.

Remark move_rr_label:
  forall rd r k, tail_nolabel k (move_rr rd r k).
Proof.
  intros; unfold move_rr. destruct (dreg_eq rd r); TailNoLabel.
Qed.
Hint Resolve move_rr_label: labels.

Remark loadimm_label:
  forall r n k, tail_nolabel k (loadimm r n k).
Proof.
  intros; unfold loadimm.
  destruct (Int.eq (high_s n) Int.zero); TailNoLabel.
  destruct (Int.eq (low_s n) Int.zero); TailNoLabel.
Qed.
Hint Resolve loadimm_label: labels.


Remark loadimm_addr_label:
  forall r n k, tail_nolabel k (loadimm_addr r n k).
Proof.
  intros; unfold loadimm_addr.
  destruct (Int.eq (low_s n) Int.zero); TailNoLabel.
Qed.
Hint Resolve loadimm_addr_label: labels.

Remark select_encoding_instr_label':
  forall op1 op2 c rd r1 r2 k c',
    nolabel c' -> 
  (forall r1 r2, nolabel (op1 r1 r2)) ->
  (forall r1 r2 r3, nolabel (op2 r1 r2 r3)) ->
  tail_nolabel k (select_encoding_instr op1 op2 c rd r1 r2 (c'::k)).
Proof.
  intros; unfold select_encoding_instr.
  destruct (dreg_eq rd r1); TailNoLabel.
  destruct (c && dreg_eq rd r2); TailNoLabel.
Qed.
Hint Resolve select_encoding_instr_label': labels.

Remark select_encoding_instr_label:
  forall op1 op2 c rd r1 r2 k,
  (forall r1 r2, nolabel (op1 r1 r2)) ->
  (forall r1 r2 r3, nolabel (op2 r1 r2 r3)) ->
  tail_nolabel k (select_encoding_instr op1 op2 c rd r1 r2 k).
Proof.
  intros; unfold select_encoding_instr.
  destruct (dreg_eq rd r1); TailNoLabel.
  destruct (c && dreg_eq rd r2); TailNoLabel.
Qed.
Hint Resolve select_encoding_instr_label: labels.

Remark select_encoding_instr_aa_label:
  forall op1 op2 c rd r1 r2 k,
  (forall r1 r2, nolabel (op1 r1 r2)) ->
  (forall r1 r2 r3, nolabel (op2 r1 r2 r3)) ->
  tail_nolabel k (select_encoding_instr_aa op1 op2 c rd r1 r2 k).
Proof.
  intros; unfold select_encoding_instr_aa.
  destruct (areg_eq rd r1); TailNoLabel.
  destruct (c && areg_eq rd r2); TailNoLabel.
Qed.
Hint Resolve select_encoding_instr_aa_label: labels.

Remark add_label:
  forall rd r1 r2 k, tail_nolabel k (add rd r1 r2 k).
Proof.
  intros; unfold add. auto with labels.
Qed.
Hint Resolve add_label: labels.


Remark add_d_label:
  forall rd r1 r2 k, tail_nolabel k (add_d rd r1 r2 k).
Proof.
  intros; unfold add_d. destruct (dreg_eq rd r1); TailNoLabel.
Qed.
Hint Resolve add_d_label: labels.

Remark add_aa_label:
  forall rd r1 r2 k, tail_nolabel k (add_aa rd r1 r2 k).
Proof.
  intros; unfold add_aa. TailNoLabel.
Qed.

Hint Resolve add_aa_label: labels.

Remark sub_label':
  forall rd r1 r2 k c, nolabel c -> tail_nolabel k (sub rd r1 r2 (c::k)).
Proof.
  intros; unfold sub. auto with labels.
Qed.
Hint Resolve sub_label': labels.

Remark sub_label:
  forall rd r1 r2 k, tail_nolabel k (sub rd r1 r2 k).
Proof.
  intros; unfold sub. auto with labels.
Qed.
Hint Resolve sub_label: labels.


Remark mul_label:
  forall rd r1 r2 k, tail_nolabel k (mul rd r1 r2 k).
Proof.
  intros; unfold mul. auto with labels.
Qed.
Hint Resolve mul_label: labels.

Remark and_label:
  forall rd r1 r2 k, tail_nolabel k (and rd r1 r2 k).
Proof.
  intros; unfold and. auto with labels.
Qed.
Hint Resolve and_label: labels.

Remark or_label:
  forall rd r1 r2 k, tail_nolabel k (or rd r1 r2 k).
Proof.
  intros; unfold or. auto with labels.
Qed.
Hint Resolve or_label: labels.

Remark xor_label:
  forall rd r1 r2 k, tail_nolabel k (xor rd r1 r2 k).
Proof.
  intros; unfold xor. auto with labels.
Qed.
Hint Resolve xor_label: labels.

Remark op_sc9_label:
  forall op1 op2 n k k',
  (forall sc9, nolabel (op1 sc9)) ->
  (forall r k, tail_nolabel k (op2 r k)) ->
  tail_nolabel k k' ->
  tail_nolabel k (op_sc9 op1 op2 n k').
Proof.
  intros; unfold op_sc9.
  destruct (get_sconst9 n); TailNoLabel.
  eapply tail_nolabel_trans. eapply loadimm_label.
  eapply tail_nolabel_trans; eauto.
Qed.
Hint Resolve op_sc9_label: labels.

Remark addimm_label:
  forall rd r n k, tail_nolabel k (addimm rd r n k).
Proof.
  intros; unfold addimm, addimm_gen.
  destruct (dreg_eq rd r && is_in_signed_range 4 n); TailNoLabel.
  destruct (Int.eq (high_s n) Int.zero); TailNoLabel.
  destruct (Int.eq (low_s n) Int.zero); TailNoLabel.
Qed.
Hint Resolve addimm_label: labels.

Remark addimm_addr_label:
  forall rd r n k, tail_nolabel k (addimm_addr rd r n k).
Proof.
  intros; unfold addimm_addr, addimm_gen.
  destruct (areg_eq rd r && is_in_signed_range 4 n); TailNoLabel.
  destruct (Int.eq (high_s n) Int.zero); TailNoLabel.
  destruct (Int.eq (low_s n) Int.zero); TailNoLabel.
Qed.
Hint Resolve addimm_addr_label: labels.

Remark rsubimm_label:
  forall rd r n k, tail_nolabel k (rsubimm rd r n k).
Proof.
  intros; unfold rsubimm.
  destruct (dreg_eq rd r && Int.eq n Int.zero); TailNoLabel.
Qed.
Hint Resolve rsubimm_label: labels.

Remark mulimm_label:
  forall rd r n k k', tail_nolabel k k' -> tail_nolabel k (mulimm rd r n k').
Proof.
  intros; unfold mulimm. TailNoLabel.
Qed.
Hint Resolve mulimm_label: labels.

Remark slimm_label:
  forall rd r n k, tail_nolabel k (slimm rd r n k).
Proof.
  intros; unfold slimm.
  destruct (dreg_eq rd r && (Int.ltu n (Int.repr 8))); TailNoLabel.
Qed.
Hint Resolve slimm_label: labels.

Remark lsrimm_label:
  forall rd r n k, tail_nolabel k (lsrimm rd r n k).
Proof.
  intros; unfold lsrimm.
  destruct (dreg_eq rd r && (Int.ltu n (Int.repr 9))); TailNoLabel.
Qed.
Hint Resolve lsrimm_label: labels.

Remark asrimm_label:
  forall rd r n k, tail_nolabel k (asrimm rd r n k).
Proof.
  intros; unfold asrimm.
  destruct (dreg_eq rd r && (Int.ltu n (Int.repr 9))); TailNoLabel.
Qed.
Hint Resolve asrimm_label: labels.

Remark maddimm_label:
  forall rd r1 r2 n k, tail_nolabel k (maddimm rd r1 r2 n k).
Proof.
  intros; unfold maddimm. apply op_sc9_label; TailNoLabel. intros. TailNoLabel.
Qed.
Hint Resolve maddimm_label: labels.

Remark msubimm_label:
  forall rd r1 r2 n k, tail_nolabel k (msubimm rd r1 r2 n k).
Proof.
  intros; unfold msubimm. apply op_sc9_label; TailNoLabel. intros. TailNoLabel.
Qed.
Hint Resolve msubimm_label: labels.

Remark op_uc9_label:
  forall op1 op2 n k,
  (forall uc9, nolabel (op1 uc9)) ->
  (forall r k, tail_nolabel k (op2 r k)) ->
  tail_nolabel k (op_uc9 op1 op2 n k).
Proof.
  intros; unfold op_uc9.
  destruct (get_uconst9 n); TailNoLabel.
  eapply tail_nolabel_trans. eapply loadimm_label.
  auto.
Qed.
Hint Resolve op_uc9_label: labels.

Remark op_uc9_not_label:
  forall op1 op1n op2 n k,
  (forall uc9, nolabel (op1 uc9)) ->
  (forall uc9, nolabel (op1n uc9)) ->
  (forall r k, tail_nolabel k (op2 r k)) ->
  tail_nolabel k (op_uc9_not op1 op1n op2 n k).
Proof.
  intros; unfold op_uc9_not.
  destruct (get_uconst9 (Int.not n)); TailNoLabel.
Qed.
Hint Resolve op_uc9_not_label: labels.

Remark andimm_label:
  forall rd r n k, tail_nolabel k (andimm rd r n k).
Proof.
  intros; unfold andimm.
  destruct (dreg_eq rd r && dreg_eq rd D15 && Int.ltu n (Int.repr (two_p 8))); TailNoLabel.
Qed.
Hint Resolve andimm_label: labels.

Remark nandimm_label:
  forall rd r n k, tail_nolabel k (nandimm rd r n k).
Proof.
  intros; unfold nandimm. apply op_uc9_label; intros; TailNoLabel.
Qed.
Hint Resolve nandimm_label: labels.

Remark orimm_label:
  forall rd r n k, tail_nolabel k (orimm rd r n k).
Proof.
  intros; unfold orimm.
  destruct (dreg_eq rd r && dreg_eq rd D15 && Int.ltu n (Int.repr (two_p 8))); TailNoLabel.
Qed.
Hint Resolve orimm_label: labels.

Remark norimm_label:
  forall rd r n k, tail_nolabel k (norimm rd r n k).
Proof.
  intros; unfold norimm. apply op_uc9_label; intros; TailNoLabel.
Qed.
Hint Resolve norimm_label: labels.

Remark xorimm_label:
  forall rd r n k, tail_nolabel k (xorimm rd r n k).
Proof.
  intros; unfold xorimm; TailNoLabel.
Qed.
Hint Resolve xorimm_label: labels.

Remark xnorimm_label:
  forall rd r n k, tail_nolabel k (xnorimm rd r n k).
Proof.
  intros; unfold xnorimm. apply op_uc9_label; intros; TailNoLabel.
Qed.
Hint Resolve xnorimm_label: labels.

Remark switch_A_D_via_TMP_label ra rd k: tail_nolabel k (switch_A_D_via_TMP ra rd k).
Proof.
  unfold switch_A_D_via_TMP. TailNoLabel.
Qed.

Hint Resolve switch_A_D_via_TMP_label : labels.

Remark switch_A_D_via_TMPA_label ra rd k: tail_nolabel k (switch_A_D_via_TMPA ra rd k).
Proof.
  unfold switch_A_D_via_TMPA. TailNoLabel.
Qed.

Hint Resolve switch_A_D_via_TMPA_label : labels.


Remark translate_bin_comp_label rd r1 r2 cmp k c:  
  (forall rd r r', nolabel (transl_cond_int32s cmp rd r r')) -> 
  (translate_bin_comp rd r1 r2 cmp k) = OK c -> 
  tail_nolabel k c.
Proof.
  unfold translate_bin_comp; intros NL H.
  destruct (preg_of r1), (preg_of r2); inv H; TailNoLabel.
  eapply tail_nolabel_trans; TailNoLabel.
Qed.

Remark translate_bin_compu_label rd r1 r2 cmp k c:  
  (forall rd r r', nolabel (transl_cond_int32u cmp rd r r')) -> 
  (forall rd r r', nolabel (transl_cond_addr cmp rd r r')) -> 
  (translate_bin_compu rd r1 r2 cmp k) = OK c -> 
  tail_nolabel k c.
Proof.
  unfold translate_bin_compu; intros NL1 NL2 H.
  destruct (preg_of r1), (preg_of r2); inv H; TailNoLabel.
Qed.
Hint Resolve translate_bin_comp_label translate_bin_compu_label: labels_gen.

Remark translate_imm_comp_label rd r cmp n k c:  
  (forall rd r k, tail_nolabel k (transl_condimm_int32s cmp rd r n k)) -> 
  (translate_imm_comp rd r cmp n k) = OK c -> 
  tail_nolabel k c.
Proof.
  unfold translate_imm_comp; intros NL H.
  destruct (preg_of r); inv H; TailNoLabel.
  repeat (eapply tail_nolabel_trans; TailNoLabel).
Qed.

Remark translate_imm_compu_label rd r cmp n k c:  
  (forall rd r k, tail_nolabel k (transl_condimm_int32u cmp rd r n k)) -> 
  (forall rd r k c, 
    transl_condimm_addr cmp rd r n = Some c -> tail_nolabel k (c :: k)) -> 
  (translate_imm_compu rd r cmp n k) = OK c -> 
  tail_nolabel k c.
Proof.
  unfold translate_imm_compu; intros NL1 NL2 H.
  destruct (preg_of r); inv H; TailNoLabel.
  destruct (transl_condimm_addr cmp rd r0 n) eqn:Hz; inv H1.
  eapply NL2. eassumption.
  repeat (eapply tail_nolabel_trans; TailNoLabel).
Qed.
Hint Resolve translate_imm_comp_label translate_imm_compu_label: labels_gen.

Remark transl_cond_op_label:
  forall cond rd args k c,
  transl_cond_op cond rd args k = OK c -> tail_nolabel k c.
Proof.
  intros; unfold transl_cond_op in H.
  destruct cond; TailNoLabel.
  - eapply translate_bin_comp_label; try eassumption.
    intros. unfold transl_cond_int32s. destruct c0; TailNoLabel.
  - eapply translate_bin_compu_label; try eassumption.
    intros. unfold transl_cond_int32u. destruct c0; TailNoLabel.
    intros. unfold transl_cond_addr. destruct c0; TailNoLabel.
  - eapply  translate_imm_comp_label; try eassumption. intros.
    unfold transl_condimm_int32s.
    assert (tail_nolabel k0 (loadimm TMP n (transl_cond_int32s c0 rd0 r TMP :: k0))).
    { intros. eapply tail_nolabel_trans. eapply loadimm_label. destruct c0; TailNoLabel. }
    destruct c0, (get_sconst9 n), (Int.lt (Int.repr (-258)) n && Int.lt n (Int.repr 255)); TailNoLabel.
  - eapply  translate_imm_compu_label; try eassumption. intros.
    unfold transl_condimm_int32u.
    assert (tail_nolabel k0 (loadimm TMP n (transl_cond_int32u c0 rd0 r TMP :: k0))).
    { intros. eapply tail_nolabel_trans. eapply loadimm_label. destruct c0; TailNoLabel. }
     destruct c0, (get_sconst9 n), (get_uconst9 n), (Int.eq n Int.zero), (Int.ltu n (Int.repr 511)); TailNoLabel.
    intros.
    unfold transl_condimm_addr in H0. 
    destruct (Int.eq n Int.zero) eqn:Hn; inv H0.
    destruct c0; inv H2; TailNoLabel.
  - unfold transl_cond_single_op. destruct c0; simpl; TailNoLabel.
  - unfold transl_cond_single_op. destruct c0; simpl; TailNoLabel.
Qed.
Hint Resolve transl_cond_op_label: labels_gen.

Remark transl_op_label:
  forall op args r k c,
  transl_op op args r k = OK c -> tail_nolabel k c.
Proof.
  unfold transl_op; intros; destruct op; TailNoLabel.
  - destruct (preg_rpair_of r); try discriminate; destruct (preg_rpair_of r0); destruct r1; inv H; destruct r2; TailNoLabel.
  - destruct (preg_rpair_of r); try discriminate; destruct r0; inv H; TailNoLabel.
  - destruct (preg_rpair_of r); try discriminate; destruct r0; inv H; TailNoLabel.
  - destruct (preg_rpair_of r); try discriminate; destruct r0; inv H; TailNoLabel.
    eapply tail_nolabel_trans. eapply addimm_addr_label. TailNoLabel.
  -  destruct (preg_rpair_of r0); try discriminate; destruct r1; inv EQ0; TailNoLabel.
  - destruct (preg_rpair_of r); [|discriminate]. destruct r2; monadInv H; TailNoLabel.
  - monadInv H. destruct (dreg_eq x0 x1 || dreg_eq x0 x3); TailNoLabel.
  - destruct (preg_rpair_of r); [|discriminate]. destruct r1; monadInv H; TailNoLabel.
  - destruct (preg_rpair_of r0); [|discriminate]. destruct r1; inv EQ0; TailNoLabel.
  - destruct (preg_rpair_of r0); [|discriminate]; destruct r2; try discriminate; destruct (preg_rpair_of r1); try discriminate; destruct r3; inv EQ2.
     eapply tail_nolabel_trans. eapply transl_cond_op_label; eauto. TailNoLabel.
     destruct (dreg_eq x r2). eapply tail_nolabel_trans. eapply transl_cond_op_label; eauto.
     destruct (dreg_eq x D2); eapply tail_nolabel_trans; TailNoLabel.
     eapply tail_nolabel_trans. eapply transl_cond_op_label; eauto. TailNoLabel.
     destruct (dreg_eq x r3).  eapply tail_nolabel_trans. eapply transl_cond_op_label; eauto.
     destruct (dreg_eq x D2); eapply tail_nolabel_trans; TailNoLabel.
     eapply tail_nolabel_trans. eapply transl_cond_op_label; eauto. TailNoLabel.
     destruct (areg_eq r2 r3); inv H0; TailNoLabel.
     eapply tail_nolabel_trans. eapply transl_cond_op_label; eauto.
     destruct (dreg_eq x D2); eapply tail_nolabel_trans; TailNoLabel.
  - eapply tail_nolabel_trans. eapply transl_cond_op_label; TailNoLabel. TailNoLabel.
  - destruct (preg_rpair_of r0); [|discriminate]. destruct r3; try discriminate; inv EQ3; TailNoLabel.
  - destruct (preg_rpair_of r); [|discriminate]. destruct r2; monadInv H; TailNoLabel.
    destruct (Int.is_power2 n); TailNoLabel. destruct (get_uconst2 i); TailNoLabel.
    eapply tail_nolabel_trans. eapply mulimm_label. TailNoLabel. TailNoLabel.
    eapply tail_nolabel_trans. eapply mulimm_label. TailNoLabel. TailNoLabel.
  - destruct (preg_rpair_of r0); [|discriminate]. destruct r3; TailNoLabel.
  - destruct (preg_rpair_of r0); [|discriminate]. destruct r2; TailNoLabel.
    eapply tail_nolabel_trans. eapply mulimm_label; TailNoLabel. TailNoLabel.
  - eapply tail_nolabel_trans. eapply move_rr_label. TailNoLabel.
  - monadInv H. destruct (dreg_eq x0 x1); inv EQ2; TailNoLabel.
  - eapply tail_nolabel_trans. eapply move_rr_label. TailNoLabel.
  - destruct(preg_rpair_of r0); [|discriminate]. destruct r1; inv EQ0; TailNoLabel.
  - destruct (Int.eq n Int.zero); TailNoLabel.
  - destruct(preg_rpair_of r0); [|discriminate]. destruct r2; monadInv EQ0; TailNoLabel.
  - monadInv H. destruct (dreg_eq x0 x1 || dreg_eq x0 x3); inv EQ3; TailNoLabel.
Qed.
Hint Resolve transl_op_label: labels_gen.

Remark translate_bin_cbranch_label:
  forall m1 m2 comp f lbl k c,
  (forall r1 r2, nolabel (f r1 r2 lbl)) ->
  translate_bin_cbranch m1 m2 comp f lbl k = OK c ->
  tail_nolabel k c.
Proof.
  unfold translate_bin_cbranch. intros. destruct (preg_of m1), (preg_of m2); inv H0; TailNoLabel.
  apply transl_cond_op_label in H2. TailNoLabel. inv H2. constructor.
  - eapply is_tail_cons_left. eassumption. 
  - TailNoLabel.
Qed.
Hint Resolve translate_bin_cbranch_label : labels_gen.

Remark transl_cbranch_label:
  forall cond args lbl k c,
  transl_cbranch cond args lbl k = OK c -> tail_nolabel k c.
Proof.
  intros; unfold transl_cbranch in H.
  destruct cond; TailNoLabel.
  - eapply translate_bin_cbranch_label; TailNoLabel.
    intros. unfold transl_cbranch_int32s. destruct c0; TailNoLabel.
  - eapply translate_bin_cbranch_label; TailNoLabel.
    intros. unfold transl_cbranch_int32u. destruct c0; TailNoLabel.
  - destruct (preg_of m); inv H.
    + unfold transl_cbranch_int32s_imm.
    assert (tail_nolabel k (loadimm TMP n (transl_cbranch_int32s c0 r TMP lbl :: k))).
    { intros. eapply tail_nolabel_trans. eapply loadimm_label. destruct c0; TailNoLabel. }
    destruct c0, (get_sconst4 n), (Int.lt (Int.repr (-10)) n && Int.lt n (Int.repr 7)); TailNoLabel.
    + eapply tail_nolabel_trans.
      * eapply translate_imm_comp_label; try eassumption.
        intros. unfold transl_condimm_int32s.
        assert (tail_nolabel k0 (loadimm TMP n (transl_cond_int32s c0 rd r0 TMP :: k0))).
        { intros. eapply tail_nolabel_trans. eapply loadimm_label. destruct c0; TailNoLabel. }
        destruct c0, (get_sconst9 n), (Int.lt (Int.repr (-258)) n && Int.lt n (Int.repr 255)); TailNoLabel.
      * TailNoLabel.
  - destruct (preg_of m); inv H.
    + unfold transl_cbranch_int32u_imm.
      assert (tail_nolabel k (loadimm TMP n (transl_cbranch_int32u c0 r TMP lbl :: k))).
      { intros. eapply tail_nolabel_trans. eapply loadimm_label. destruct c0; TailNoLabel. }
      destruct c0, (get_sconst4 n), (get_uconst4 n), (Int.eq n Int.zero), (Int.ltu n (Int.repr 15)); TailNoLabel.
    + eapply tail_nolabel_trans.
      * eapply translate_imm_compu_label; try eassumption.
        unfold transl_condimm_int32u; intros.
        assert (tail_nolabel k0 (loadimm TMP n (transl_cond_int32u c0 rd r0 TMP :: k0))).
        { intros. eapply tail_nolabel_trans. eapply loadimm_label. destruct c0; TailNoLabel. }
        destruct c0, (get_sconst9 n), (get_uconst9 n), (Int.eq n Int.zero), (Int.ltu n (Int.repr 511)); TailNoLabel.
        intros. 
        unfold transl_condimm_addr in H.
        destruct (Int.eq n Int.zero); inv H.
        destruct c0; inv H2; TailNoLabel.
      * TailNoLabel.
  - destruct c0; inv EQ2; TailNoLabel.
  - destruct c0; inv EQ2; TailNoLabel.
Qed.

Remark indexed_memory_access_label:
  forall insn1 insn2 base ofs k,
  (forall ad, nolabel (insn1 ad)) ->
  (forall ad ofs, nolabel (insn2 ad ofs)) ->
  tail_nolabel k (indexed_memory_access insn1 insn2 base ofs k).
Proof.
  intros; unfold indexed_memory_access.
  destruct (Ptrofs.eq ofs Ptrofs.zero), (get_sconst16 (Ptrofs.to_int ofs)); TailNoLabel.
  eapply tail_nolabel_trans. apply addimm_addr_label. TailNoLabel.
Qed.

Remark loadind_label:
  forall base ofs ty dst k c,
  loadind base ofs ty dst k = OK c -> tail_nolabel k c.
Proof.
  unfold loadind; intros.
  destruct ty, (preg_of dst); inv H; apply indexed_memory_access_label; intros; exact I.
Qed.

Remark storeind_label:
  forall src base ofs ty k c,
  storeind src base ofs ty k = OK c -> tail_nolabel k c.
Proof.
  unfold storeind; intros.
  destruct ty, (preg_of src); inv H; apply indexed_memory_access_label; intros; exact I.
Qed.

Remark loadind_ptr_label:
  forall base ofs dst k, tail_nolabel k (loadind_ptr base ofs dst k).
Proof.
  intros. apply indexed_memory_access_label; TailNoLabel.
Qed.

Remark storeind_ptr_label:
  forall base ofs dst k, tail_nolabel k (storeind_ptr base ofs dst k).
Proof.
  intros. apply indexed_memory_access_label; TailNoLabel.
Qed.

Remark lea_label:
  forall rd id ofs k, tail_nolabel k (lea rd id ofs k).
Proof.
  intros; unfold lea; TailNoLabel.
Qed.

Remark transl_memory_access_label:
  forall mk1 mk2 mk3 addr args k c,
  (forall ad, nolabel (mk1 ad)) ->
  (forall ad ofs, nolabel (mk2 ad ofs)) ->
  (forall ad id ofs, nolabel (mk3 ad id ofs)) ->
  transl_memory_access mk1 mk2 mk3 addr args k = OK c ->
  tail_nolabel k c.
Proof.
  intros; unfold transl_memory_access in H2.
  destruct addr; TailNoLabel.
  - eapply tail_nolabel_trans. eapply addimm_addr_label; TailNoLabel.
    TailNoLabel.
  -  eapply tail_nolabel_trans. eapply lea_label. TailNoLabel.
  - apply indexed_memory_access_label; auto.
Qed.

Remark transl_load_label:
       forall chunk addr args dst k c,
       transl_load chunk addr args dst k = OK c ->
       tail_nolabel k c.
Proof.
  intros; unfold transl_load in H.
  destruct chunk; try now (monadInv H; eapply transl_memory_access_label; eauto; intros; exact I).
  destruct (preg_of dst); try discriminate.
  all: eapply transl_memory_access_label; eauto; intros; exact I.
Qed.

Remark transl_store_label:
       forall chunk addr args src k c,
       transl_store chunk addr args src k = OK c ->
       tail_nolabel k c.
Proof.
  intros; unfold transl_store in H.
  destruct chunk; try now (monadInv H; eapply transl_memory_access_label; eauto; intros; exact I).
  destruct (preg_of src); try discriminate.
  all: eapply transl_memory_access_label; eauto; intros; exact I.
Qed.

Remark make_epilogue_label:
  forall f k, tail_nolabel k (make_epilogue f k).
Proof.
  unfold make_epilogue; intros. eapply tail_nolabel_trans. apply loadind_ptr_label. TailNoLabel.
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
   eapply tail_nolabel_trans. apply loadind_ptr_label. eapply loadind_label; eauto.
 - eauto with labels_gen.
 - eapply transl_load_label. eauto.
 - eapply transl_store_label. eauto.
 - destruct s0; monadInv H; TailNoLabel.
 - destruct s0; monadInv H; TailNoLabel; (eapply tail_nolabel_trans; [eapply make_epilogue_label|TailNoLabel]).
 - eapply transl_cbranch_label; eauto.
 - eapply tail_nolabel_trans; [eapply make_epilogue_label|TailNoLabel].
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
  | None => find_label lbl tf.(fn_code) = None
  | Some c => exists tc, find_label lbl tf.(fn_code) = Some tc /\ transl_code f c false = OK tc
  end.
Proof.
  intros. monadInv H. destruct (zlt Ptrofs.max_unsigned (list_length_z x.(fn_code))); inv EQ0.
  monadInv EQ. rewrite transl_code'_transl_code in EQ0. unfold fn_code.
  simpl. set (k' := storeind_ptr A11 A10 (fn_retaddr_ofs f) x).
  destruct (storeind_ptr_label A12 A10 (fn_link_ofs f) k') as [A B]; rewrite B. unfold k'.
  destruct (storeind_ptr_label A11 A10 (fn_retaddr_ofs f) x) as [A1 B1]; rewrite B1.
  eapply transl_code_label; eauto.
Qed.

End TRANSL_LABEL.

(** A valid branch in a piece of Mach code translates to a valid ``go to''
  transition in the generated Asm code. *)

Lemma find_label_goto_label:
  forall f tf lbl rs m pcl c' b ofs,
  Genv.find_funct_ptr ge b = Some (Internal f) ->
  transf_function f = OK tf ->
  rs PC = Vptr b ofs ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  exists tc', exists rs',
    goto_label tf lbl rs m pcl = Next rs' m pcl
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

(* a.d. FIXME after Asmgenproof2 is removed. Because of Asmgenproof2, we cannot use Asmgenproof0.return_address_offset in Compiler.v, so we reexport it here. *)
Definition return_address_offset := Asmgenproof0.return_address_offset.

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
  exists x; exists true; split; auto. unfold fn_code.
  constructor.
  eapply tail_nolabel_trans. eapply (storeind_ptr_label A12 A10 (fn_link_ofs f0)).
  apply (storeind_ptr_label A11 A10 (fn_retaddr_ofs f0) x).
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

Definition csa_offset (r: mreg): ptrofs := Ptrofs.zero.

Inductive prev_ctx_list: list Mach.stackframe -> list regset -> Prop := 
  | prev_ctx_list_nil:  
      prev_ctx_list nil nil
  | prev_ctx_list_cons: forall fb sp ra ms c s csa pcl,
      (forall r, is_auto_save r = true -> Val.lessdef (ms r) (csa (preg_of r))) ->
      sp = (csa A10) ->
      prev_ctx_list s pcl ->
      prev_ctx_list (Stackframe fb sp ra ms c :: s) (csa :: pcl).

(* a.d. TODO when we add A10 to the upper context, this needs to be changed since the stack pointer will change. *)
Lemma agree_restore_auto_caller_save_regs:
  forall ms sp rs s pcl,
  agree ms sp rs ->
  prev_ctx_list s pcl ->
  agree (Mach.restore_auto_save_regs (parent_regset s) ms) sp (restore_auto_save_regs (pcl_top_csa pcl) rs).
Proof.
  intros. unfold Mach.restore_auto_save_regs, restore_auto_save_regs. destruct H.
  constructor; auto.
  - intros. destruct (is_auto_save r) eqn:Er.
    + (* auto caller-save, reg is is upper context *) 
      rewrite pred_dec_true.
      (* match on stack & pcl. In case of nil, we are returning from main *)
      destruct pcl as [|csa pcl'], s as [|sf s']; inv H0. constructor.
      simpl. apply H4; auto.
      apply auto_save_regs_in_upper_ctx; auto.
    + (* callee-save or manual caller-save, reg is not in upper context *) 
      apply not_auto_save_regs_not_in_upper_ctx in Er.
      rewrite pred_dec_false; auto.
Qed.

Lemma agree_pcl_parent_sp:
  forall ms sp s rs pcl,
    agree ms sp rs ->
    prev_ctx_list s pcl ->
    (parent_sp s) = (pcl_parent_sp pcl).
Proof.
  intros. inv H0; auto.
Qed.

(* Lemma exec_calli_correct:
  forall fb sp ra ms c s rs rs0 pc m pcl,
  agree ms sp rs ->
  prev_ctx_list s pcl ->
  rs0 = nextinstr (rs#TMPA <- pc) ->
  exists rs',
    exec_call ra pc rs0 m pcl = Next rs' m (rs0 :: pcl)
    /\ prev_ctx_list (Stackframe fb sp ra ms c :: s) (rs0 :: pcl)
    /\ (forall (r: preg), r <> RA -> r <> PC -> r <> TMPA -> rs'#r = rs#r)
    /\ rs'#PC = pc /\ rs'#RA = ra.
Proof.
  intros. eexists. 
  split. unfold exec_call. reflexivity.
  split.
  - constructor. intros. rewrite H1. Simpl. apply H. auto.
  - split. intros. rewrite H1. Simpl. Simpl.
Qed. *)

Lemma exec_call_correct:
  forall fb sp ra ms c s rs pc m pcl,
  agree ms sp rs ->
  prev_ctx_list s pcl ->
  exists rs',
    exec_call ra pc rs m pcl = Next rs' m (rs :: pcl)
    /\ prev_ctx_list (Stackframe fb sp ra ms c :: s) (rs :: pcl)
    /\ (forall (r: preg), r <> RA -> r <> PC -> rs'#r = rs#r)
    /\ rs'#PC = pc /\ rs'#RA = ra.
Proof.
  intros. eexists. 
  split. unfold exec_call. reflexivity.
  split.
  - constructor. intros. apply H. rewrite (sp_val ms sp rs); auto. apply H0.
  - split. intros. Simpl. Simpl.
Qed.

Lemma exec_ret_correct:
  forall s rs m pcl,
  prev_ctx_list s pcl ->
  exists rs',
    exec_ret rs m pcl = Next rs' m (List.tail pcl)
    /\ rs'#PC = rs#RA
    /\ (forall r, r <> PC -> ~In r upper_ctx -> rs'#r = rs#r)
    /\ match pcl, s with 
       | nil, nil => True
       | csa :: pcl', (Stackframe _ _ _ ms _)::s' => 
          prev_ctx_list (List.tail s) (List.tail pcl)
          /\ (forall r, is_auto_save r = true -> Val.lessdef (ms#r) (rs'#(preg_of r)))
       | _, _ => False
       end.
Proof.
  intros. 
  eexists _. split. unfold exec_ret. reflexivity. split; [|split].
  - reflexivity.
  - intros. unfold restore_auto_save_regs. 
    destruct (in_dec preg_eq r upper_ctx); try congruence. Simpl.
  - destruct pcl as [|csa pcl'], s as [|sf s']; inv H. constructor. split.
    simpl. assumption.
    intros. unfold restore_auto_save_regs.
    assert (In (preg_of r) upper_ctx).
    { apply auto_save_regs_in_upper_ctx; auto. }
    destruct (in_dec preg_eq (preg_of r) upper_ctx); try congruence.
    cbn. apply H4; auto.
Qed.

Inductive match_states: Mach.state -> Asm.state -> Prop :=
  | match_states_intro:
      forall s fb sp c ep ms m m' rs f tf tc pcl
        (STACKS: match_stack ge s)
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
        (MEXT: Mem.extends m m')
        (AT: transl_code_at_pc ge (rs PC) fb f c ep tf tc)
        (AG: agree ms sp rs)
        (DXP: ep = true -> rs#A12 = parent_sp s)
        (PCL: prev_ctx_list s pcl),
      match_states (Mach.State s fb sp c ms m)
                   (Asm.State rs m' pcl)
  | match_states_call:
      forall s fb ms m m' rs pcl
        (STACKS: match_stack ge s)
        (MEXT: Mem.extends m m')
        (AG: agree ms (parent_sp s) rs)
        (ATPC: rs PC = Vptr fb Ptrofs.zero)
        (ATLR: rs RA = parent_ra s)
        (PCL: prev_ctx_list s pcl),
      match_states (Mach.Callstate s fb ms m)
                   (Asm.State rs m' pcl)
  | match_states_return:
      (* the match in PCL is necessary because in ASM the upper context is already restored, so the current PCXI
         corresponds to the registers in the previous stackframe. *)
      forall s ms m m' rs pcl
        (STACKS: match_stack ge s)
        (MEXT: Mem.extends m m')
        (AG: agree ms (parent_sp s) rs)
        (ATPC: rs PC = parent_ra s)
        (PCL: match s with 
              | nil => pcl = nil
              | _::s' => prev_ctx_list s' pcl
              end),
      match_states (Mach.Returnstate s ms m)
                   (Asm.State rs m' pcl).

Lemma exec_straight_steps:
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 pcl,
  match_stack ge s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  prev_ctx_list s pcl ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists rs2,
       exec_straight tge tf c rs1 m1' k rs2 m2' pcl
    /\ agree ms2 sp rs2
    /\ (it1_is_parent ep i = true -> rs2#A12 = parent_sp s)) ->
  exists st',
  plus step tge (State rs1 m1' pcl) E0 st' /\
  match_states (Mach.State s fb sp c ms2 m2) st'.
Proof.
  intros. inversion H3. subst. monadInv H8.
  exploit H4; eauto. intros [rs2 [A [B C]]].
  exists (State rs2 m2' pcl); split.
  eapply exec_straight_exec; eauto.
  econstructor; eauto. eapply exec_straight_at; eauto.
Qed.

Lemma exec_straight_steps_goto:
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 lbl c' pcl,
  match_stack ge s ->
  prev_ctx_list s pcl ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  it1_is_parent ep i = false ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists jmp, exists k', exists rs2,
       exec_straight tge tf c rs1 m1' (jmp :: k') rs2 m2' pcl
    /\ agree ms2 sp rs2
    /\ exec_instr tge tf jmp rs2 m2' pcl = goto_label tf lbl rs2 m2' pcl) ->
  exists st',
  plus step tge (State rs1 m1' pcl) E0 st' /\
  match_states (Mach.State s fb sp c' ms2 m2) st'.
Proof.
  intros *? H'. intros. inversion H3. subst. monadInv H9.
  exploit H5; eauto. intros [jmp [k' [rs2 [A [B C]]]]].
  generalize (functions_transl _ _ _ H7 H8); intro FN.
  generalize (transf_function_no_overflow _ _ H8); intro NOOV.
  exploit exec_straight_steps_2; eauto.
  intros [ofs' [PC2 CT2]].
  exploit find_label_goto_label; eauto.
  intros [tc' [rs3 [GOTO [AT' OTH]]]].
  exists (State rs3 m2' pcl); split.
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
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 lbl c' pcl,
  match_stack ge s ->
  prev_ctx_list s pcl ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  it1_is_parent ep i = false ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists jmp, exists k', exists rs2,
       exec_straight_opt tge tf c rs1 m1' (jmp :: k') rs2 m2' pcl
    /\ agree ms2 sp rs2
    /\ exec_instr tge tf jmp rs2 m2' pcl = goto_label tf lbl rs2 m2' pcl) ->
  exists st',
  plus step tge (State rs1 m1' pcl) E0 st' /\
  match_states (Mach.State s fb sp c' ms2 m2) st'.
Proof.
  intros *? H'. intros. inversion H3. subst. monadInv H9.
  exploit H5; eauto. intros [jmp [k' [rs2 [A [B C]]]]].
  generalize (functions_transl _ _ _ H7 H8); intro FN.
  generalize (transf_function_no_overflow _ _ H8); intro NOOV.
  inv A.
- exploit find_label_goto_label; eauto.
  intros [tc' [rs3 [GOTO [AT' OTH]]]].
  exists (State rs3 m2' pcl); split.
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
  exists (State rs3 m2' pcl); split.
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
  transitions on the Asm side.  Actually, all Mach transitions
  correspond to at least one Asm transition, except the
  transition from [Machsem.Returnstate] to [Machsem.State].
  So, the following integer measure will suffice to rule out
  the unwanted behaviour. *)

Definition measure (s: Mach.state) : nat :=
  match s with
  | Mach.State _ _ _ _ _ _ => 0%nat
  | Mach.Callstate _ _ _ _ => 0%nat
  | Mach.Returnstate _ _ _ => 1%nat
  end.

Remark preg_of_not_P12: forall r, negb (mreg_eq r P12) = true -> AREG A12 <> preg_of r.
Proof.
  intros. change (AREG A12) with (preg_of P12). red; intros.
  exploit preg_of_injective; eauto. intros; subst r; discriminate.
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
  monadInv TR. econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split. apply agree_nextinstr; auto. simpl; congruence.


- (* Mgetstack *)
  unfold load_stack in H.
  exploit Mem.loadv_extends; eauto. intros [v' [A B]].
  rewrite (sp_val _ _ _ AG) in A.
  left; eapply exec_straight_steps; eauto. intros. monadInv TR. ErrorSingle.
  exploit loadind_correct; eauto with asmgen. auto. intros [rs' [P [Q R]]].
  exists rs'; split. eauto.
  split. eapply agree_set_mreg; eauto with asmgen. congruence.
  simpl; congruence.

- (* Msetstack *)
  unfold store_stack in H.
  assert (Val.lessdef (Mach.get_pair src rs) (get_pair (preg_rpair_of src) rs0)). eapply preg_rpair_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [A B]].
  left; eapply exec_straight_steps; eauto.
  rewrite (sp_val _ _ _ AG) in A. intros. monadInv TR. ErrorSingle.
  exploit storeind_correct; eauto with asmgen. auto. intros [rs' [P Q]].
  exists rs'; split. eauto.
  split. eapply agree_undef_regs; eauto with asmgen.
  simpl; intros. rewrite Q; auto with asmgen.

- (* Mrestorecallee *)
  inv AT. monadInv H3.

- (* Msavecallee *)
  inv AT. monadInv H4.

- (* Mgetparam *)
  assert (f0 = f) by congruence; subst f0.
  unfold load_stack in *.
  exploit Mem.loadv_extends. eauto. eexact H0. auto.
  intros [parent' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  exploit lessdef_parent_sp; eauto. clear B; intros B; subst parent'.
  exploit Mem.loadv_extends. eauto. eexact H1. auto.
  intros [v' [C D]].
Opaque loadind.
  left; eapply exec_straight_steps; eauto; intros. monadInv TR. ErrorSingle.
  destruct ep.
(* A12 contains parent *)
  exploit loadind_correct.
  instantiate (3:= A12). simpl. rewrite DXP; eauto. erewrite agree_pcl_parent_sp; eauto.
  instantiate (1:= pcl). destruct (Val.eq (pcl_parent_sp pcl) (pcl_parent_sp pcl)); auto. eexact EQ1.
  rewrite DXP; eauto.
  intros [rs1 [P [Q R]]].
  exists rs1; split. eauto.
  split. eapply agree_set_mreg. eapply agree_set_mreg; eauto. congruence. auto with asmgen.
  simpl; intros. rewrite R; auto with asmgen.
  apply preg_of_not_P12; auto.
(* A12 does not contain parent *)
  rewrite chunk_of_Tptr in A.
  exploit (loadind_ptr_correct tge tf SP). auto. exact A. intros [rs1 [P [Q R]]].
  exploit loadind_correct.
  instantiate (3:= A12). simpl. rewrite Q. erewrite agree_pcl_parent_sp; eauto.
  instantiate (1:= pcl). destruct (Val.eq (pcl_parent_sp pcl) (pcl_parent_sp pcl)); auto. eexact EQ1.
  rewrite Q. eexact C.
  intros [rs2 [S [T U]]].
  exists rs2; split. eapply exec_straight_trans; eauto.
  split. eapply agree_set_mreg. eapply agree_set_mreg. eauto. eauto.
  instantiate (1 := rs1#A12 <- (rs2#A12)). intros.
  rewrite Pregmap.gso; auto with asmgen.
  congruence.
  intros. unfold Pregmap.set. destruct (PregEq.eq r' A12). congruence. auto with asmgen.
  simpl; intros. rewrite U; auto with asmgen.
  apply preg_of_not_P12; auto.

- (* Mop *)
    assert (eval_operation tge sp op (Mach.get_pairs args rs) m = Some v).
    rewrite <- H. apply eval_operation_preserved. exact symbols_preserved.
  exploit eval_operation_lessdef. eapply preg_rpair_vals; eauto. eauto. eexact H0.
  intros [v' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  left; eapply exec_straight_steps; eauto; intros.
  exploit transl_op_correct; eauto. intros [rs2 [P [Q R]]].
  exists rs2; split. eauto. split.
  assert (S: lessdef' v (preg_rpair_of res) rs2) by (eapply lessdef_lessdef'_trans; eauto).
  eapply agree_set_undef_mreg_rpair; eauto with asmgen.
  simpl; intros. destruct (andb_prop _ _ H1); clear H1.
  rewrite R; auto. destruct res; [| split; simpl in H3; rewrite andb_true_iff in H3; destruct H3]; simpl; apply preg_of_not_P12; auto.
  Local Transparent destroyed_by_op destroyed_by_cond.
  destruct op; simpl; auto; split; congruence.

- (* Mload *)
  assert (eval_addressing tge sp addr (map rs args) = Some a).
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  exploit Mem.loadv_extends; eauto. intros [v' [C D]].
  left; eapply exec_straight_steps; eauto; intros. monadInv TR. ErrorSingle.
  exploit transl_load_correct; eauto. intros [rs2 [P [Q R]]].
  exists rs2; split. eauto.
  split. eapply agree_set_undef_mreg; eauto. congruence.
  intros; auto with asmgen.
  simpl; congruence.

- (* Mstore *)
  assert (eval_addressing tge sp addr (map rs args) = Some a).
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  assert (Val.lessdef (Mach.get_pair src rs) (get_pair (preg_rpair_of src) rs0)). eapply preg_rpair_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [C D]].
  left; eapply exec_straight_steps; eauto.
  intros. monadInv TR. ErrorSingle.
  exploit transl_store_correct; eauto. intros [rs2 [P Q]].
  exists rs2; split. eauto.
  split. eapply agree_undef_regs; eauto with asmgen.
  simpl; congruence.

- (* Mcall *)
  assert (f0 = f) by congruence.  subst f0.
  inv AT.
  assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
  eapply transf_function_no_overflow; eauto.
  destruct ros as [rf|fid]; simpl in H.
  + (* Indirect call *)
    simpl in H5. monadInv H5.
    assert (rs rf = Vptr f' Ptrofs.zero).
    destruct (rs rf); try discriminate.
    revert H; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence.
    assert (rs0 x0 = Vptr f' Ptrofs.zero).
    exploit areg_val; eauto. rewrite H5; intros LD; inv LD; auto.
    generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT2.
  (*  generalize (code_tail_next_int _ _ _ _ NOOV CT2). intro CT1. *)
    assert (TCA: transl_code_at_pc ge (Vptr fb  (Ptrofs.add ofs Ptrofs.one)) fb f c false tf x).
    econstructor; eauto.
    exploit return_address_offset_correct; eauto. intros; subst ra.
    exploit exec_call_correct. exact AG. eauto. intros (rs1 & A & B & C & D & E).
    left; econstructor; split.
    eapply plus_one. eapply exec_step_internal. Simpl. rewrite <- H2; simpl; eauto.
    eapply functions_transl; eauto. eapply find_instr_tail; eauto.
    simpl. exact A.
    econstructor; eauto.
    econstructor; eauto.
    eapply agree_sp_def; eauto.
    simpl. eapply agree_exten; eauto. intros. rewrite C; eauto with asmgen. 
    rewrite D. apply H7. 
    rewrite E. simpl. rewrite <- H2. auto.
    rewrite <- H2 in B. simpl in B. exact B.
  + (* Direct call *)
    simpl in H5. monadInv H5.
    generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT1.
    assert (TCA: transl_code_at_pc ge (Vptr fb (Ptrofs.add ofs Ptrofs.one)) fb f c false tf x).
    econstructor; eauto.
    exploit return_address_offset_correct; eauto. intros; subst ra.
    exploit exec_call_correct; eauto. intros (rs1 & A & B & C & D & E).
    left; econstructor; split.
    apply plus_one. eapply exec_step_internal. eauto.
    eapply functions_transl; eauto. eapply find_instr_tail; eauto.
    simpl. unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H.
    exact A.
    econstructor; eauto.
    econstructor; eauto.
    eapply agree_sp_def; eauto.
    simpl. eapply agree_exten; eauto. intros. rewrite C; eauto with asmgen. 
    rewrite E. simpl. rewrite <- H2. auto.
    rewrite <- H2 in B. simpl in B. exact B.

- (* Mtailcall *)
  assert (f0 = f) by congruence.  subst f0.
  inversion AT; subst.
  assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.  exploit Mem.loadv_extends. eauto. eexact H2. auto. simpl. intros [parent' [A B]].
  destruct ros as [rf|fid]; simpl in H0; monadInv H7.
  + (* Indirect call *)
    assert (rs rf = Vptr f' Ptrofs.zero).
    destruct (rs rf); try discriminate.
    revert H0; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence.
    assert (rs0 x0 = Vptr f' Ptrofs.zero).
    exploit areg_val; eauto. rewrite H7; intros LD; inv LD; auto.
    exploit make_epilogue_correct; eauto with asmgen. intros (rs1 & m1 & U & V & W & X & Y  & Z).
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
    Simpl.
    rewrite Z; eauto with asmgen.
    apply areg_of_not_RA in EQ1. congruence.
    apply areg_of_not_SP in EQ1. congruence.
  + (* Direct call *)
    exploit make_epilogue_correct; eauto. intros (rs1 & m1 & U & V & W & X & Y & Z).
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
    Simpl. unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H0. auto.

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
  eapply restrict_builtin_args_single; eauto.
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
  apply agree_nextinstr. erewrite restrict_builtin_res_single; eauto. eapply agree_set_res; auto.
  eapply agree_undef_regs; eauto. intros. rewrite undef_regs_other_2; auto.
  congruence.

- (* Mgoto *)
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H4.
  exploit find_label_goto_label; eauto. intros [tc' [rs' [GOTO [AT2 INV]]]].
  left; exists (State rs' m' pcl); split.
  apply plus_one. econstructor; eauto.
  eapply functions_transl; eauto.
  eapply find_instr_tail; eauto.
  simpl; eauto.
  econstructor; eauto.
  eapply agree_exten; eauto with asmgen.
  congruence.

- (* Mcond true *)
  assert (f0 = f) by congruence. subst f0.
  exploit eval_condition_lessdef. eapply preg_rpair_vals; eauto. eauto. eauto. intros EC.
  left; eapply exec_straight_opt_steps_goto; eauto.
  intros. monadInv TR. ErrorSingle.
  exploit transl_cbranch_correct_true; eauto. intros (rs' & jmp & A & B & C).
  exists jmp; exists k; exists rs'.
  split. eexact A.
  split. apply agree_exten with rs0; auto with asmgen.
  exact B.

- (* Mcond false *)
  exploit eval_condition_lessdef. eapply preg_rpair_vals; eauto. eauto. eauto. intros EC.
  left; eapply exec_straight_steps; eauto. intros. monadInv TR. ErrorSingle.
  exploit transl_cbranch_correct_false; eauto. intros (rs' & A & B).
  exists rs'.
  split. eexact A.
  split. apply agree_exten with rs0; auto with asmgen.
  simpl. congruence.

- (* Mjumptable *)
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H6.
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H5); intro NOOV.
  exploit find_label_goto_label. eauto. eauto.
  instantiate (2 := rs0#TMPA <- Vundef).
  Simpl. eauto.
  eauto.
  intros [tc' [rs' [A [B C]]]].
  exploit ireg_val; eauto. rewrite H. intros LD; inv LD.
  left; econstructor; split.
  apply plus_one. econstructor; eauto.
  eapply find_instr_tail; eauto.
  simpl. rewrite <- H9. unfold Mach.label in H0; unfold label; rewrite H0. eexact A.
  econstructor; eauto.
  eapply agree_undef_regs; eauto.
  simpl. intros. rewrite C; auto with asmgen. Simpl.
  congruence.

- (* Mreturn *)
  assert (f0 = f) by congruence. subst f0.
  inversion AT; subst. simpl in H6; monadInv H6.
  assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  exploit make_epilogue_correct; eauto. intros (rs1 & m1 & U & V & W & X & Y & Z).
  exploit exec_straight_steps_2; eauto using functions_transl.
  intros (ofs' & P & Q).
  exploit (exec_ret_correct s rs1 m1 pcl). auto.
  intros (rs2 & A & B & C & D).
  left; econstructor; split.
  (* execution *)
  eapply plus_right'. eapply exec_straight_exec; eauto.
  econstructor. eexact P. eapply functions_transl; eauto. eapply find_instr_tail. eexact Q.
  simpl. exact A. traceEq.
  (* match states *)
  destruct pcl as [|csa pcl'], s as [|[??? ms?] s']; try now contradiction D.
  + (* return from main. PCL & Stack empty *)
    econstructor; eauto. simpl. constructor.
    rewrite C; eauto with asmgen. 
    unfold not. intros. rewrite upper_ctx_regs in H6. cbn in H6. decompose sum H6; discriminate.
    unfold Vnullptr. destruct Archi.ptr64; congruence.
    intros. unfold Mach.restore_auto_save_regs. destruct (is_auto_save r) eqn:Er; auto.
    rewrite C; eauto with asmgen. apply V. apply not_auto_save_regs_not_in_upper_ctx; auto.
    rewrite B. apply X.
  + destruct D as (D & E). econstructor; eauto. simpl.
    constructor. 
    rewrite C. auto. auto with asmgen. 
    rewrite upper_ctx_regs. unfold not. intros. cbn in H6. decompose sum H6; discriminate. 
    apply V.
    intros. unfold Mach.restore_auto_save_regs. destruct (is_auto_save r) eqn:Er.
    apply E; auto.
    rewrite C. apply V. auto with asmgen. apply not_auto_save_regs_not_in_upper_ctx; auto.
    simpl. rewrite B. auto.

- (* internal function *)
  exploit functions_translated; eauto. intros [tf [A B]]. monadInv B.
  generalize EQ; intros EQ'. monadInv EQ'.
  destruct (zlt Ptrofs.max_unsigned (list_length_z x0.(fn_code))); inversion EQ1. clear EQ1. subst x0.
  unfold store_stack in *.
  exploit Mem.alloc_extends. eauto. eauto. apply Z.le_refl. apply Z.le_refl.
  intros [m1' [C D]].
  exploit Mem.storev_extends. eexact D. eexact H1. eauto. eauto.
  intros [m2' [F G]].
  simpl chunk_of_type in F.
  exploit Mem.storev_extends. eexact G. eexact H2. eauto. eauto.
  intros [m3' [P Q]].
  (* Execution of function prologue *)
  monadInv EQ0. rewrite transl_code'_transl_code in EQ1.
  set (tfbody := Pallocframe (fn_stacksize f) ::
                  storeind_ptr A12 SP (fn_link_ofs f)
                  (storeind_ptr RA SP (fn_retaddr_ofs f) x0)) in *.
  set (tf := {| fn_sig := Mach.fn_sig f; fn_code := tfbody |}) in *.
  set (rs2 := nextinstr (rs0#A12 <- (parent_sp s) #SP <- sp)).
  exploit (storeind_ptr_correct tge tf SP (fn_link_ofs f) A12); eauto with asmgen.
    rewrite chunk_of_Tptr in F. instantiate (2 := rs2).
    change (rs2 A10) with sp. eexact F.
  intros (rs3 & U & V).
  exploit (storeind_ptr_correct tge tf SP (fn_retaddr_ofs f) RA); eauto.
    rewrite chunk_of_Tptr in P. instantiate (2 := rs3).
    rewrite (V A11) by congruence.
    change (rs2 A11) with (rs0 A11). rewrite ATLR.
    rewrite (V A10) by congruence.
    change (rs3 A10) with sp. eexact P.
    congruence.
  intros (rs4 & U' & V').
  assert (EXEC_PROLOGUE:
            exec_straight tge tf
              tf.(fn_code) rs0 m'
              x0 rs4 m3' pcl).
  { change (fn_code tf) with tfbody; unfold tfbody.
    apply exec_straight_step with rs2 m1'.
    unfold exec_instr. rewrite C. fold sp.
    rewrite <- (sp_val _ _ _ AG). rewrite chunk_of_Tptr in F. change Mptr with Mint32 in F.
    unfold rs2.  reflexivity. reflexivity.
    eapply exec_straight_trans. eexact U. eexact U'.
  }
  exploit exec_straight_steps_2; eauto using functions_transl. lia. constructor.
  intros (ofs' & X & Y).
  left; exists (State rs4 m3' pcl); split.
  eapply exec_straight_steps_1; eauto. lia. constructor.
  econstructor; eauto.
  rewrite X; econstructor; eauto.
  apply agree_exten with rs2; eauto with asmgen.
  unfold rs2.
  apply agree_nextinstr.
  apply agree_change_sp with (parent_sp s).
  apply agree_undef_regs with rs0. auto.
Local Transparent destroyed_at_function_entry.
  simpl; intros; Simpl.
  unfold sp; congruence.
  intros. rewrite V', V; auto with asmgen.
  intros. rewrite V', V; auto with asmgen.
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
  eapply agree_restore_auto_caller_save_regs; auto. eapply agree_undef_caller_save_regs; eauto.
  destruct pcl as [|csa pcl'], s as [|sf s']; inv PCL; auto.

- (* return *)
  inv STACKS. simpl in *.
  right. split. lia. split. auto.
  rewrite <- ATPC in H6.
  econstructor; eauto. congruence.
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
  split. auto. simpl. unfold Vnullptr; destruct Archi.ptr64; congruence.
  intros. rewrite Regmap.gi. auto.
  constructor.
  unfold Genv.symbol_address.
  rewrite (match_program_main TRANSF).
  rewrite symbols_preserved.
  unfold ge; rewrite H1. auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> Mach.final_state st1 r -> Asm.final_state st2 r.
Proof.
  intros. inv H0. inv H. econstructor. assumption.
  compute in H1. inv H1.
  generalize (preg_val _ _ _ R2 AG). rewrite H2. intros LD; inv LD. auto.
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
