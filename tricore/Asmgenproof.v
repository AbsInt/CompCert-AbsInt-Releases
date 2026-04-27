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
Require Import Values Memory Separation Events Globalenvs Smallstep.
Require Import Op Locations Mach Machtyping Conventions Asm.
Require Import Asmgen Asmgenproof0 Asmgenproof1.

Local Transparent Archi.ptr64.
Local Open Scope sep_scope.

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

Lemma transf_function_well_typed:
  forall f tf,
  transf_function f = OK tf -> wt_function f = true.
Proof.
  intros. unfold transf_function in H.
  destruct (wt_function f); inv H. reflexivity.
Qed.

Lemma transf_function_no_overflow:
  forall f tf,
  transf_function f = OK tf -> list_length_z tf.(fn_code) <= Ptrofs.max_unsigned.
Proof.
  intros. unfold transf_function in H.
  destruct (wt_function f); inv H.
  monadInv H1. destruct (zlt Ptrofs.max_unsigned (list_length_z x.(fn_code))); inv EQ0.
  lia.
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
  - destruct (preg_rpair_of r1); [|discriminate]; destruct r3; try discriminate; destruct (preg_rpair_of r2); try discriminate; destruct r4; inv EQ2; TailNoLabel.
    unfold switch_A_D_via_TMP. destruct (dreg_eq x0 D2); TailNoLabel.
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
  intros. unfold transf_function in H.
  destruct (wt_function f); inv H.
  monadInv H1.
  destruct (zlt Ptrofs.max_unsigned (list_length_z x.(fn_code))); inv EQ0.
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
- intros. unfold transf_function in H0.
  destruct (wt_function f0); inv H0.
  monadInv H2.
  destruct (zlt Ptrofs.max_unsigned (list_length_z x.(fn_code))); inv EQ0. monadInv EQ.
  rewrite transl_code'_transl_code in EQ0.
  exists x; exists true; split; auto. unfold fn_code.
  constructor.
  eapply tail_nolabel_trans. eapply (storeind_ptr_label A12 A10 (fn_link_ofs f0)).
  apply (storeind_ptr_label A11 A10 (fn_retaddr_ofs f0) x).
- exact transf_function_no_overflow.
Qed.

(** * Proof of semantic preservation *)

Ltac splitall := repeat (match goal with |- _ /\ _ => split end).

(* [sep_lia] wraps lia for range/alignment hypotheses of separation logic lemmas. *)
Ltac sep_lia :=
  unfold csa_size; simpl;
  match goal with
  | [ |- _ <= Ptrofs.modulus ] => change Ptrofs.modulus with 4294967296
  | _ => idtac
  end;
  lia || match goal with
        | [ |- (_ | 0) ] => apply Z.divide_0_r
        | [ |- (?x | ?x) ] => apply Z.divide_refl
        | [ |- (_ | 8) ] => change 8 with (4 + 4); apply Z.divide_add_r; sep_lia
        | [ |- (_ | 12) ] => change 12 with (4 + 8); apply Z.divide_add_r; sep_lia
        | [ |- (_ | 16) ] => change 16 with (4 + 12); apply Z.divide_add_r; sep_lia
        end.

(* Prevent simpl from unfolding memory asserions. *)
Local Arguments m_pred : simpl never.

Section CONTEXT_SAVE_AREA.

(** ** Separation logic assertions about the chain of context save areas (CSAs). *)

(** [contains_mregs j pcxi pos ctx ms] is a memory assertion that holds
  if block [pcxi], starting at offset [pos], contains the values of the
  context registers [ctx] as given by the register set [ms],
  up to the memory injection [j]. *)

Fixpoint contains_mregs (j: meminj) (pcxi: block) (pos: Z) (ctx: list mreg) (ms: Mach.regset) : massert :=
  match ctx with
  | nil => pure True
  | r :: ctx' => contains Many32 pcxi pos (fun v => Val.inject j (ms r) v)
                 ** contains_mregs j pcxi (pos + 4) ctx' ms
  end.

(** [prev_ctx_list j s pcxis pcxi] is a memory assertion that holds
   if block [pcxi] is a CSA, [pcxis] is a list of previous CSAs and
   they comprise the previous context list.

- At the top of the call stack, [pcxi] only points to some allocated memory.
- Down the callstack, [pcxi] points to a memory area that contains for each register
  in the upper context its value before the current function was called.
  As the PCXI is part of the upper context itself, the assertion is recursive, using the
  memory blocks from [pcxis]. *)
Fixpoint prev_ctx_list (j: meminj) (s: list Mach.stackframe) (pcxis : list block) (pcxi: block) {struct s} : massert :=
  match s, pcxis with
  | nil, nil =>
         range pcxi 0 8
      ** hasvalue Many32 pcxi 8 Vnullptr
      ** range pcxi 12 csa_size
  | Stackframe fb sp ra ms c :: s', pcxi' :: pcxis' =>
         hasvalue Many32 pcxi   0 (Vptr pcxi' Ptrofs.zero)
      ** contains Many32 pcxi   4 (fun v => True)
      ** contains Many32 pcxi   8 (fun v => Val.inject j sp v)
      ** contains Many32 pcxi  12 (fun v => True)
      ** contains_mregs j pcxi 16 upper_ctx_mr ms
      ** prev_ctx_list j s' pcxis' pcxi'
  | _, _ => pure False
  end.

Lemma contains_mregs_incr:
  forall j j' b pos rl rs,
  inject_incr j j' ->
  massert_imp (contains_mregs j b pos rl rs) (contains_mregs j' b pos rl rs).
Proof.
  intros. revert pos. induction rl.
    { red; split; red; simpl; intros. trivial. contradiction. }
    { red; split; simpl. intros.
      - eapply sep_imp. exact H0.
        + red; split; intros.
          eapply contains_imp. 2: exact H1. intros. simpl in H2.
          eapply val_inject_incr; eauto.
          red; simpl. red in H1. simpl in H1. assumption.
        + apply IHrl.
      - intros. destruct H0. now left. right.
        apply IHrl; auto.
    }
Qed.

Lemma pcl_incr_imp:
  forall j j' s pcxis pcxi,
  inject_incr j j' ->
  massert_imp (prev_ctx_list j s pcxis pcxi) (prev_ctx_list j' s pcxis pcxi).
Proof.
  intros j. induction s as [|[] s']; destruct pcxis as [|pcxi' pcxis']; intros; simpl.
  1-3: reflexivity.

  rewrite <- (IHs' pcxis' pcxi') by assumption.
  rewrite <- (contains_mregs_incr j j') by assumption.
  assert (forall v, Val.inject j sp v -> Val.inject j' sp v).
  { intros. inv H0; econstructor. apply H in H1. eassumption. reflexivity. }
  rewrite <- (contains_imp _ _ _ _ _ H0).
  reflexivity.
Qed.

Lemma pcl_inject_incr:
  forall j s ps pcxi m P j',
  m |= prev_ctx_list j s ps pcxi ** P ->
  inject_incr j j' ->
  m |= prev_ctx_list j' s ps pcxi ** P.
Proof.
  intros. rewrite <- (pcl_incr_imp j j'); auto.
Qed.

(** ** Lemmas about saving/restoring a context in a CSA. *)

Lemma store_mreg:
  forall j m b ofs ms rs r P,
  r <> Machregs.ErrorReg ->
  (forall r0, Val.has_type (ms r0) (mreg_type r0)) ->
  (forall r0, Val.inject j (ms r0) (rs (preg_of r0))) ->
  m |= contains Many32 b ofs (fun _ => True) ** P ->
  exists m',
     Mem.store Many32 m b ofs (rs (preg_of r)) = Some m'
  /\ m' |= contains Many32 b ofs (fun v => Val.inject j (ms r) v) ** P.
Proof.
  intros. set (spec := fun v => Val.inject j (ms r) v).
  assert (spec (Val.load_result Many32 (rs (preg_of r)))).
  { unfold spec. change Many32 with (chunk_of_type Tany32).
    eapply Val.load_result_inject'; auto.
    rewrite <- (mreg_type_no_err r); auto. }
  eapply store_rule; eauto.
Qed.

Lemma save_ctx_rec_mregs_correct:
  forall j rs m_asm pcxi pos ml ms P,
  ~ In Machregs.ErrorReg ml ->
  (forall r, Val.has_type (ms r) (mreg_type r)) ->
  (forall r, Val.inject j (ms r) (rs (preg_of r))) ->
  m_asm |= range pcxi pos (pos + (4 * Z.of_nat (length ml))) ** P ->
  (align_chunk Many32 | pos) ->
  exists m_asm',
     save_ctx_rec pcxi pos (List.map preg_of ml) rs m_asm = Some m_asm'
  /\ m_asm' |= contains_mregs j pcxi pos ml ms ** P.
Proof.
  intros until P. intros HErr TY LD SEP ALIGN. revert m_asm pos P SEP ALIGN. induction ml; intros.
  - exists m_asm. split.
    simpl. reflexivity. cbn [contains_mregs]. rewrite sep_pure.
    split; auto. apply sep_proj2 in SEP. exact SEP.
  - apply not_in_cons in HErr. destruct HErr as [? HErr].
    assert (a <> Machregs.ErrorReg) by congruence.
    replace (pos + 4 * Z.of_nat (length (a :: ml))) with (pos + 4 + 4 * Z.of_nat (length ml)) in SEP.
    2: change (Datatypes.length (a :: ml)) with (Datatypes.S (Datatypes.length ml)); lia. 
    eapply (range_split _ pos (pos + 4 + (4 * Z.of_nat (length ml))) _ (pos + 4)) in SEP; [|lia].

    (* store the current register *)
    apply (range_contains Many32) in SEP.
    exploit store_mreg. exact H0. exact TY. exact LD. exact SEP.
    clear SEP. intros (m_asm0 & Hstore0 & SEP).

    (* store the rest of the list *)
    rewrite sep_swap12 in SEP.
    (* assert ((align_chunk Mint32 | pos + 4)). *)
    exploit IHml. exact HErr. exact SEP. simpl. apply Z.divide_add_r. assumption. apply Z.divide_refl.
    clear SEP. intros (m_asm1 & Hstore1 & SEP). rewrite sep_swap12 in SEP.

    simpl. econstructor. rewrite Hstore0. split.
    + apply Hstore1.
    + rewrite sep_assoc. exact SEP.
    + assumption.
Qed.

Lemma save_ctx_rec_step_correct:
  forall rs r b pcxi m_asm pos P pl,
  rs#r = Vptr b Ptrofs.zero ->
  m_asm |= range pcxi pos (pos + 4) ** P ->
  (align_chunk Many32 | pos) ->
  exists m_asm',
     save_ctx_rec pcxi pos (r :: pl) rs m_asm = save_ctx_rec pcxi (pos + 4) pl rs m_asm'
  /\ m_asm' |= hasvalue Many32 pcxi pos (Vptr b Ptrofs.zero) ** P.
Proof.
  intros until pl. intros Hr SEP ALIGN.
  simpl.

  exploit store_rule'.
    apply (range_contains Many32) in SEP; [|assumption]. exact SEP.
  clear SEP. intros (m_asm' & -> & SEP).
  exists m_asm'. split.
  - reflexivity.
  - rewrite Hr in SEP. unfold Val.load_result in SEP.
    assumption.
Qed.

Lemma save_ctx_rec_step_correct':
  forall j rs r b ofs pcxi m_asm pos P pl,
  Val.inject j (Vptr b ofs) rs#r ->
  m_asm |= range pcxi pos (pos + 4) ** P ->
  (align_chunk Many32 | pos) ->
  exists m_asm',
     save_ctx_rec pcxi pos (r :: pl) rs m_asm = save_ctx_rec pcxi (pos + 4) pl rs m_asm'
  /\ m_asm' |= contains Many32 pcxi pos (fun v => Val.inject j (Vptr b ofs) v) ** P.
Proof.
  intros * INJ SEP ALIGN.
  simpl.

  apply (range_contains Many32) in SEP; [|assumption].
  specialize (store_rule Many32 _ _ _ (rs#r) _ (fun v => Val.inject j (Vptr b ofs) v) _ SEP).
  clear SEP. intros (m_asm' & -> & SEP).
  - inv INJ. unfold Val.load_result. simpl.
    econstructor. eassumption. reflexivity.
  - exists m_asm'. split. reflexivity. assumption.
Qed.

Lemma save_ctx_rec_skip_correct:
  forall rs b m_asm P pos p pl,
  m_asm |= range b pos (pos + 4) ** P ->
  (align_chunk Many32 | pos) ->
  exists m_asm',
     save_ctx_rec b pos (p :: pl) rs m_asm = save_ctx_rec b (pos + 4) pl rs m_asm'
  /\ m_asm' |= contains Many32 b pos (fun _ => True) ** P.
Proof.
  intros. apply (range_contains Many32) in H; auto.
  simpl. exploit store_rule'. exact H. intros (m_asm' & A & B).
  econstructor. rewrite A. split.
  - reflexivity.
  - unfold hasvalue in B.
    eapply sep_imp. exact B. apply contains_imp. trivial.
    trivial.
Qed.

Lemma save_ctx_upper_correct:
  forall j stk sofs ms s pcxis rs m_mach m_asm pcxi P,
  rs#PCXI = Vptr pcxi Ptrofs.zero ->
  Val.inject j (Vptr stk sofs) rs#SP ->
  (forall r, Val.has_type (ms r) (mreg_type r)) ->
  (forall r, Val.inject j (ms r) (rs (preg_of r))) ->
  m_asm |= prev_ctx_list j s pcxis pcxi ** minjection j m_mach ** P ->
  exists rs' m_asm' pcxi',
    save_ctx upper_ctx rs m_asm = Some (rs', m_asm')
    /\ (forall fb ra c, m_asm' |= prev_ctx_list j (Stackframe fb (Vptr stk sofs) ra ms c :: s) (pcxi :: pcxis) pcxi' ** minjection j m_mach ** P)
    /\ rs'#PCXI = (Vptr pcxi' Ptrofs.zero)
    /\ (forall (r: preg), r <> PCXI -> rs'#r = rs#r).
Proof.
  intros * CSA HSP TY INJ SEP.
  unfold save_ctx, upper_ctx.

  (* allocate fresh CSA *)
  destruct (Mem.alloc m_asm 0 csa_size) as [m_asm0 pcxi'] eqn:ALLOC.
  exploit alloc_rule.
    exact ALLOC. lia. apply csa_size_no_overflow.
    exact SEP.
  clear SEP. intros SEP.

  (* store PCXI *)
  apply (range_split _ _ _ _ 4) in SEP; [|sep_lia].
  exploit save_ctx_rec_step_correct.
    exact CSA. exact SEP. sep_lia.
  clear SEP. intros (m_asm1 & -> & SEP). rewrite sep_swap12 in SEP.
  change (0 + 4) with 4.

  (* store PSW *)
  apply (range_split _ _ _ _ 8) in SEP; [|sep_lia].
  exploit save_ctx_rec_skip_correct.
    exact SEP. sep_lia.
  clear SEP. intros (m_asm2 & -> & SEP). rewrite sep_swap12 in SEP.
  change (4 + 4) with 8.

  (* store SP *)
  apply (range_split _ _ _ _ 12) in SEP; [|sep_lia].
  exploit save_ctx_rec_step_correct'.
    exact HSP. exact SEP. sep_lia.
  clear SEP. intros (m_asm3 & -> & SEP).
  rewrite sep_swap12 in SEP.
  change (8 + 4) with 12.

  (* store RA *)
  apply (range_split _ _ _ _ 16) in SEP; [|sep_lia].
  exploit save_ctx_rec_skip_correct.
    exact SEP. sep_lia.
  clear SEP. intros (m_asm4 & -> & SEP). rewrite sep_swap12 in SEP.
  change (12 + 4) with 16.

  (* save the rest of the mregs *)
  exploit (save_ctx_rec_mregs_correct j rs m_asm4 pcxi' 16).
    apply upper_ctx_mr_not_err. exact TY. apply INJ.
    rewrite upper_ctx_mr_size. change (16 + 4 * Z.of_nat 12) with (csa_size).
    exact SEP.
    sep_lia.
  clear SEP. intros (m_asm5 & ? & SEP).
  rewrite H.

  assert (SEPFINAL: forall fb ra c, m_asm5 |= prev_ctx_list j (Stackframe fb (Vptr stk sofs) ra ms c :: s) (pcxi :: pcxis) pcxi'
                                           ** minjection j m_mach ** P).
  { intros. simpl. rewrite ! sep_assoc.
    rewrite <- sep_swap5 in SEP.
    rewrite sep_swap34, sep_swap23 in SEP.
    rewrite sep_swap34 in SEP.
    exact SEP. }

  eexists _, m_asm5, pcxi'. splitall.
  - reflexivity.
  - exact SEPFINAL.
  - Simpl.
  - intros. Simpl.
Qed.

Lemma restore_ctx_rec_skip_mregs_correct:
  forall P m_asm pcxi ml rs pos,
  m_asm |= range pcxi pos (pos + (4 * Z.of_nat (length ml))) ** P ->
  (align_chunk Many32 | pos) ->
  exists rs',
     restore_ctx_rec pcxi pos (List.map preg_of ml) rs m_asm = Some rs'
  /\ (forall p, ~In p (List.map preg_of ml) -> rs' p = rs p).
Proof.
  intros until ml. induction ml; intros * SEP ALIGN.
  - (* nil *)
    econstructor. split. reflexivity. intros. reflexivity.
  - (* cons *)
    simpl.
    replace (pos + 4 * Z.of_nat (length (a :: ml))) with (pos + 4 + 4 * Z.of_nat (length ml)) in SEP.
    2: change (Datatypes.length (a :: ml)) with (Datatypes.S (Datatypes.length ml)); lia.

    (* load current register *)
    apply (range_split _ _ _ _ (pos + 4)) in SEP.
    apply (range_contains Many32) in SEP; auto.
    exploit load_rule. eapply sep_proj1. exact SEP. intros (v&Hv&_).
    rewrite Hv.

    (* load rest of registers *)
    exploit (IHml (rs # (preg_of a) <- v) (pos + 4)).
    eapply sep_proj2. exact SEP. apply Z.divide_add_r. assumption. apply Z.divide_refl.
    intros (rs' & A & B).

    econstructor. rewrite A. split.
    + reflexivity.
    + intros. apply Decidable.not_or in H. destruct H.
      rewrite B; auto. Simpl.
    + lia.
Qed.

Lemma restore_ctx_rec_skip_correct:
  forall P rs b m_asm pos p pl,
  m_asm |= range b pos (pos + 4) ** P ->
  (align_chunk Many32 | pos) ->
  exists rs',
     restore_ctx_rec b pos (p :: pl) rs m_asm = restore_ctx_rec b (pos + 4) pl rs' m_asm
  /\ (forall p0, p0 <> p -> rs' p0 = rs p0).
Proof.
  intros. apply (range_contains Many32) in H; auto.
  simpl. exploit load_rule. eapply sep_proj1. exact H. intros (v & A & B).
  econstructor. rewrite A. split.
  - reflexivity.
  - intros. Simpl.
Qed.

Lemma restore_ctx_rec_mregs_correct:
  forall j P m_asm b ms ml rs pos,
  list_norepet ml ->
  m_asm |= contains_mregs j b pos ml ms ** P ->
  0 <= pos -> pos + (4 * Z.of_nat (Datatypes.length ml)) <= Ptrofs.modulus ->
  (align_chunk Many32 | pos) ->
  exists rs',
     restore_ctx_rec b pos (List.map preg_of ml) rs m_asm = Some rs'
  /\ (forall p, ~In p (List.map preg_of ml) -> rs' p = rs p)
  /\ (forall r, In r ml -> Val.inject j (ms r) (rs' (preg_of r)))
  /\ m_asm |= range b pos (pos + 4 * Z.of_nat (Datatypes.length ml)) ** P.
Proof.
  intros. revert rs pos P H0 H1 H2 H3. induction ml; intros * SEP ?? ALIGN.
  - (* nil *)
    econstructor. split; [|split; [|split]].
    reflexivity. intros. reflexivity. intros. simpl in H. contradiction.
    simpl. rewrite Z.add_0_r. apply range_empty_2. lia.
    apply SEP.
  - (* cons *)
    simpl in SEP. rewrite sep_assoc in SEP.
    replace (4 * Z.of_nat (length (a :: ml))) with (4 + 4 * Z.of_nat (length ml)) in *.
    2: change (Datatypes.length (a :: ml)) with (Datatypes.S (Datatypes.length ml)); lia.
    set (len := 4 + 4 * Z.of_nat (length ml)). simpl.
    inv H.

    (* load current register *)
    exploit load_rule. eapply sep_proj1. exact SEP. intros (v&Hload&Hv).
    rewrite Hload.

    (* load rest of registers *)
    exploit (IHml H5 (rs # (preg_of a) <- v) (pos + 4)).
    rewrite sep_swap12 in SEP. exact SEP. lia. lia. apply Z.divide_add_r. assumption. apply Z.divide_refl.
    intros (rs' & A & B & C & D). rewrite A.

    econstructor. split; [|split; [|split]].
    + reflexivity.
    + intros. apply Decidable.not_or in H. destruct H.
      rewrite B; auto. Simpl.
    + intros. destruct H; auto.
      subst a. rewrite B.
      Simpl.
      contradict H4. apply in_map_iff in H4. destruct H4 as (?&?&?).
      apply preg_of_injective in H. subst x. assumption.
    + unfold len. rewrite Z.add_assoc.
      rewrite sep_swap12 in D. apply contains_range in D. apply range_merge in D.
      assumption. lia. simpl. lia.
Qed.

Lemma restore_ctx_rec_step_correct:
  forall rs pcxi m_asm pos spec P r pl,
  m_asm |= contains Many32 pcxi pos spec ** P ->
  (align_chunk Many32 | pos) ->
  pos + size_chunk Many32 <= Ptrofs.modulus ->
  exists rs' v,
     restore_ctx_rec pcxi pos (r :: pl) rs m_asm = restore_ctx_rec pcxi (pos + 4) pl rs' m_asm
  /\ (forall r', r' <> r -> rs' r' = rs r')
  /\ rs' r = v
  /\ spec v
  /\ m_asm |= range pcxi pos (pos + 4) ** P.
Proof.
  intros until pl. intros SEP ALIGN SZ.
  exploit load_rule. eapply sep_proj1. exact SEP. intros (v & LD & Hspec).
  econstructor. exists v. splitall.
  - simpl. rewrite LD. reflexivity.
  - intros. Simpl.
  - Simpl.
  - assumption.
  - apply contains_range in SEP. exact SEP. assumption.
Qed.

Lemma restore_ctx_upper_correct:
  forall j s rs m_mach m_asm pcxis pcxi P,
  rs#PCXI = Vptr pcxi Ptrofs.zero ->
  m_asm |= prev_ctx_list j s pcxis pcxi ** minjection j m_mach ** P ->
  exists rs' m_asm',
       restore_ctx upper_ctx rs m_asm = Some (rs', m_asm')
    /\ (forall r, ~In r upper_ctx -> rs'#r = rs#r)
    /\ match s, pcxis with
       | nil, nil => rs'#SP = Vnullptr
       | (Stackframe _ sp' ra' ms _)::s', pcxi' :: pcxis' =>
             m_asm' |= prev_ctx_list j s' pcxis' pcxi' ** minjection j m_mach ** P
          /\ (forall r, is_auto_save r = true -> Val.inject j (ms#r) (rs'#(preg_of r)))
          /\ rs'#PCXI = (Vptr pcxi' Ptrofs.zero)
          /\ Val.inject j sp' rs'#SP
        | _, _ => False
       end.
Proof.
  intros * Hrpcxi SEP. unfold restore_ctx. rewrite Hrpcxi.

  destruct s as [|[fb sp' ra' c ms'] s']; destruct pcxis as [|pcxi0 pcxis'].
  2,3: now destruct SEP as [[]].
  - (* return from main. All loads except SP result in Vundef. *)
    unfold upper_ctx at 1.

    (* load PCXI *)
    simpl in SEP. rewrite ! sep_assoc in SEP.
    apply (range_split _ _ _ _ 4) in SEP; [|sep_lia].
    exploit restore_ctx_rec_skip_correct. exact SEP. sep_lia.
    intros (rs0 & -> & Hrs0).
    change (0 + 4) with 4.

    (* load PSW *)
    exploit restore_ctx_rec_skip_correct.
      rewrite sep_swap12 in SEP. exact SEP. sep_lia.
    intros (rs1 & -> & Hrs1).
    change (4 + 4) with 8.

    (* load SP as Vnullptr *)
    exploit restore_ctx_rec_step_correct.
      rewrite sep_swap3 in SEP. unfold hasvalue in SEP. apply SEP.
      sep_lia. sep_lia.
    clear SEP. intros (rs2 & sp' & -> & Hrs2 & Hrsp & -> & SEP).
    change (8 + 4) with 12 in SEP. rewrite sep_swap3 in SEP.

    (* load RA *)
    rewrite sep_swap4 in SEP. 
    apply (range_split _ _ _ _ 16) in SEP; [|sep_lia].
    exploit restore_ctx_rec_skip_correct. exact SEP. sep_lia.
    intros (rs3 & -> & Hrs3).
    change (12 + 4) with 16.

    (* load the rest of the mregs *)
    rewrite sep_swap12 in SEP.
    exploit restore_ctx_rec_skip_mregs_correct.
      rewrite upper_ctx_mr_size. change (16 + 4 * Z.of_nat 12) with (csa_size).
      exact SEP.
      sep_lia.
    intros (rs4 & -> & Hrs4).

    (* free CSA *)
    rewrite sep_swap5, sep_swap23, sep_swap34 in SEP.
    do 4 eapply range_merge in SEP; [|sep_lia..].
    exploit free_rule. exact SEP.
    clear SEP. intros (m_asm' & -> & SEP).

    econstructor. econstructor. splitall.
    + reflexivity.
    + intros. 
      apply not_in_cons in H as (?&H).
      apply not_in_cons in H as (?&H).
      apply not_in_cons in H as (?&H).
      apply not_in_cons in H as (?&H).
      rewrite Hrs4, Hrs3, Hrs2, Hrs1, Hrs0; auto.
    + rewrite Hrs4, Hrs3. assumption. congruence.
      rewrite upper_ctx_mr_regs. simpl. intuition discriminate.
  
  - (* return not from main. Loads restore register contents. *)
    unfold upper_ctx at 1.

    (* load PCXI *)
    simpl in SEP. rewrite ! sep_assoc in SEP.
    exploit restore_ctx_rec_step_correct.
      exact SEP. sep_lia. sep_lia.
    clear SEP. intros (rs0 & pcxi' & -> & Hrs0 & Hrpcxi' & -> & SEP). 
    change (0 + 4) with 4 in *.

    (* load PSW *)
    rewrite sep_swap12 in SEP. apply contains_range in SEP; [|sep_lia].
     exploit restore_ctx_rec_skip_correct.
      exact SEP. sep_lia.
     intros (rs1 & -> & Hrs1).
    rewrite sep_swap12 in SEP.
     change (4 + 4) with 8.

    (* load SP *)
    exploit restore_ctx_rec_step_correct.
      rewrite sep_swap3 in SEP. exact SEP.
      sep_lia. sep_lia.
    clear SEP. intros (rs2 & sp & -> & Hrs2 & Hrsp & Hsp & SEP). 
    change (8 + 4) with 12 in *.

    (* load RA *)
    rewrite sep_swap4 in SEP. apply contains_range in SEP; [|sep_lia].
    exploit restore_ctx_rec_skip_correct.
      exact SEP. sep_lia.
    intros (rs3 & -> & Hrs3). 
    change (12 + 4) with 16 in *.

    (* load the rest of the mregs *)
    exploit restore_ctx_rec_mregs_correct. 
      apply upper_ctx_mr_norepet.
      rewrite sep_swap5 in SEP. exact SEP.
      lia. rewrite upper_ctx_mr_size. sep_lia. sep_lia.
    clear SEP. intros (rs4 & -> & Hrs4 & Hinj & SEP).

    (* merge all ranges & free CSA *)
    rewrite upper_ctx_mr_size in SEP. change (16 + 4 * Z.of_nat 12) with (csa_size) in SEP.
    rewrite sep_swap5, sep_swap4, sep_swap3 in SEP.
    do 4 apply range_merge in SEP; [|sep_lia..].

    exploit free_rule.
      exact SEP.
    clear SEP. intros (m_asm' & -> & SEP).

    econstructor. econstructor.
    splitall.
    + reflexivity.
    + intros. 
      apply not_in_cons in H as (?&H).
      apply not_in_cons in H as (?&H).
      apply not_in_cons in H as (?&H).
      apply not_in_cons in H as (?&H).
      rewrite Hrs4, Hrs3, Hrs2, Hrs1, Hrs0; auto.
    + assumption.
    + intros. apply Hinj.
      apply auto_save_regs_in_upper_ctx in H. rewrite upper_ctx_regs_split in H.
      destruct H as [?|[?|[?|[?|]]]]. 
      * generalize preg_of_not_PCXI. congruence.
      * generalize preg_of_not_PSW. congruence.
      * generalize preg_of_not_SP. congruence.
      * generalize preg_of_not_RA. congruence.
      * apply in_map_iff in H. destruct H as (? & ? & ?).
        apply preg_of_injective in H. subst x.
        assumption.
    + rewrite Hrs4, Hrs3, Hrs2, Hrs1; eauto with asmgen.
      rewrite upper_ctx_mr_regs. simpl. intuition discriminate.
    + rewrite Hrs4, Hrs3; eauto with asmgen. 
      congruence.
      rewrite upper_ctx_mr_regs. simpl. intuition discriminate.
Qed.

End CONTEXT_SAVE_AREA.

(** Predicates to show that stack pointers are Vptr values and are mapped by the injection. *)

Inductive ptr_injects (j: meminj) : val -> Prop :=
  | ptr_injects_intro: forall b b' ofs,
      j b = Some (b', 0) ->
      ptr_injects j (Vptr b ofs).

Inductive stackframes_inject (j: meminj) : list stackframe -> Prop :=
  | stackframes_inject_nil:
      stackframes_inject j nil
  | stackframes_inject_cons: forall fb sp ra c rs s,
      ptr_injects j sp ->
      stackframes_inject j s ->
      stackframes_inject j (Stackframe fb sp ra rs c :: s).

Inductive stack_inject (j: meminj) : list stackframe -> val -> Prop :=
  | stack_inject_intro: forall s sp,
      ptr_injects j sp ->
      stackframes_inject j s ->
      stack_inject j s sp.

Lemma ptr_injects_incr:
  forall j j' p,
  inject_incr j j' ->
  ptr_injects j p -> ptr_injects j' p.
Proof.
  intros. inv H0. econstructor.
  apply H; eassumption.
Qed.

Lemma stackframes_inject_incr:
  forall j j' s,
  inject_incr j j' ->
  stackframes_inject j s -> stackframes_inject j' s.
Proof.
  intros. revert s H0. induction 1; intros.
  - constructor.
  - constructor.
    eapply ptr_injects_incr; eassumption.
    assumption.
Qed.

Lemma stack_inject_incr:
  forall j j' s sp,
  inject_incr j j' ->
  stack_inject j s sp -> stack_inject j' s sp.
Proof.
  intros. inv H0. econstructor.
  eapply ptr_injects_incr; eassumption.
  eapply stackframes_inject_incr; eassumption.
Qed.

Lemma exec_calli_correct:
  forall j fb sp ra ms c s rs rs0 pc m_mach m_asm pcxis pcxi P,
  rs#PCXI = Vptr pcxi Ptrofs.zero ->
  (forall r, Val.has_type (ms r) (mreg_type r)) ->
  agree_inj j ms sp rs ->
  stack_inject j s sp ->
  m_asm |= prev_ctx_list j s pcxis pcxi ** minjection j m_mach ** P ->
  rs0 = nextinstr (rs#TMPA <- pc) ->
  exists rs' m_asm' pcxi',
    exec_call ra pc rs0 m_asm = Next rs' m_asm'
    /\ m_asm' |= prev_ctx_list j (Stackframe fb sp ra ms c :: s) (pcxi :: pcxis) pcxi'
                 ** minjection j m_mach ** P
    /\ (forall (r: preg), r <> RA -> r <> PC -> r <> TMPA -> r <> PCXI -> rs'#r = rs#r)
    /\ rs'#PCXI = (Vptr pcxi' Ptrofs.zero) /\ rs'#PC = pc /\ rs'#RA = ra.
Proof.
  intros * Hrpcxi TY AG STKINJ SEP Hrs0. unfold exec_call.
  assert (rs0 PCXI = Vptr pcxi Ptrofs.zero).
  { rewrite Hrs0. replace (nextinstr rs # TMPA <- pc PCXI) with (rs PCXI) by Simpl. assumption. }
  assert (exists stk sofs, sp = Vptr stk sofs /\ Val.inject j sp rs0#SP).
  { rewrite Hrs0. Simpl.
    inv STKINJ. inv H0.
    eexists. eexists. split. reflexivity. apply AG. }
  destruct H0 as (stk & sofs & -> & HSP).
  assert (forall r, Val.inject j (ms r) (rs0 (preg_of r))).
  { intros. rewrite Hrs0. Simpl. apply AG. }
  exploit save_ctx_upper_correct. exact H. exact HSP. exact TY. exact H0. exact SEP.
  clear SEP. intros (rs' & m_asm' & pcxi' & A & SEP & D & E).
  eexists _, m_asm', pcxi'. splitall.
  - rewrite A. reflexivity.
  - apply SEP.
  - intros. Simpl. rewrite E, Hrs0. Simpl. assumption.
  - Simpl.
  - Simpl.
  - Simpl.
Qed.

Lemma exec_call_correct:
  forall j sp ra ms s rs pc m_mach m_asm pcxis pcxi P,
  rs#PCXI = Vptr pcxi Ptrofs.zero ->
  (forall r, Val.has_type (ms r) (mreg_type r)) ->
  agree_inj j ms sp rs ->
  stack_inject j s sp ->
  m_asm |= prev_ctx_list j s pcxis pcxi ** minjection j m_mach ** P ->
  exists rs' m_asm' pcxi',
    exec_call ra pc rs m_asm = Next rs' m_asm'
    /\ (forall fb c, 
        m_asm' |= prev_ctx_list j (Stackframe fb sp ra ms c :: s) (pcxi :: pcxis) pcxi'
                  ** minjection j m_mach ** P)
    /\ (forall (r: preg), r <> RA -> r <> PC -> r <> TMPA -> r <> PCXI -> rs'#r = rs#r)
    /\ rs'#PCXI = (Vptr pcxi' Ptrofs.zero) /\ rs'#PC = pc /\ rs'#RA = ra.
Proof.
  intros * Hrpcxi TY AG STKINJ SEP. unfold exec_call.
  assert (exists stk sofs, sp = Vptr stk sofs /\ Val.inject j sp rs#SP).
  { inv STKINJ. inv H.
    eexists. eexists. split. reflexivity. apply AG. }
  destruct H as (stk & sofs & -> & HSP).
  exploit save_ctx_upper_correct. exact Hrpcxi. apply HSP. exact TY. apply AG. exact SEP.
  clear SEP. intros (rs' & m_asm' & pcxi' & A & SEP & D & E).
  eexists _, m_asm', pcxi'. splitall.
  - rewrite A. reflexivity.
  - intros. apply SEP.
  - intros. Simpl. 
  - Simpl. 
  - Simpl. 
  - Simpl. 
Qed.

Lemma exec_ret_correct:
  forall j s rs m_mach m_asm pcxis pcxi P,
  rs#PCXI = Vptr pcxi Ptrofs.zero ->
  m_asm |= prev_ctx_list j s pcxis pcxi ** minjection j m_mach ** P ->
  exists rs' m_asm',
       exec_ret rs m_asm = Next rs' m_asm'
    /\ (forall r, r <> PC -> ~In r upper_ctx -> rs'#r = rs#r)
    /\ rs'#PC = rs#RA
    /\ match s, pcxis with
       | nil, nil => rs'#SP = Vnullptr
       | (Stackframe _ sp' ra' ms _)::s', pcxi' :: pcxis' =>
               m_asm' |= prev_ctx_list j s' pcxis' pcxi' ** minjection j m_mach ** P
            /\ (forall r, is_auto_save r = true -> Val.inject j (ms#r) (rs'#(preg_of r)))
            /\ rs'#PCXI = Vptr pcxi' Ptrofs.zero
            /\ Val.inject j sp' rs'#SP
        | _, _ => False
       end.
Proof.
  intros * Hrpcxi SEP. unfold exec_ret.
  exploit restore_ctx_upper_correct. exact Hrpcxi. exact SEP.
  intros (rs1 & m_asm1 & A & B & C).
  eexists _, m_asm1. splitall.
  - rewrite A. reflexivity.
  - intros. Simpl.
  - Simpl.
  - destruct s as [|[] s'], pcxis as [|pcxi' pcxis'].
    2,3: congruence.
    trivial.
    decompose [Logic.and] C.
    splitall; auto.
    intros. Simpl.
Qed.

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
      forall s fb sp c ep ms m m' rs f tf tc pcxis pcxi j
        (STACKS: match_stack ge s)
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
        (AT: transl_code_at_pc ge (rs PC) fb f c ep tf tc)
        (AG: agree_inj j ms sp rs)
        (SINJ: stack_inject j s sp)
        (DXP: ep = true -> Val.inject j (parent_sp s) rs#A12)
        (CSA: rs PCXI = Vptr pcxi Ptrofs.zero)
        (SEP: m' |= prev_ctx_list j s pcxis pcxi ** minjection j m ** globalenv_inject ge j),
      match_states (Mach.State s fb sp c ms m)
                   (Asm.State rs m')
  | match_states_call:
      forall s fb ms m m' rs pcxis pcxi j
        (STACKS: match_stack ge s)
        (AG: agree_inj j ms (parent_sp s) rs)
        (SFINJ: stackframes_inject j s)
        (ATPC: rs PC = Vptr fb Ptrofs.zero)
        (ATLR: rs RA = parent_ra s)
        (CSA: rs PCXI = Vptr pcxi  Ptrofs.zero)
        (SEP: m' |= prev_ctx_list j s pcxis pcxi ** minjection j m ** globalenv_inject ge j),
      match_states (Mach.Callstate s fb ms m)
                   (Asm.State rs m')
  | match_states_return:
      forall s ms m m' rs j pcxis
        (STACKS: match_stack ge s)
        (AG: agree_inj j ms (parent_sp s) rs)
        (SFINJ: stackframes_inject j s)
        (ATPC: rs PC = parent_ra s)
        (PCL: match s, pcxis with
              | nil, nil => True
              | (Stackframe fb sp ra ms c)::s', pcxi' :: pcxis' =>
                     rs PCXI = Vptr pcxi' Ptrofs.zero
                  /\ m' |= prev_ctx_list j s' pcxis' pcxi' ** minjection j m ** globalenv_inject ge j
              | _, _ => False
              end),
      match_states (Mach.Returnstate s ms m)
                   (Asm.State rs m').

Lemma exec_straight_steps:
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 pcxis pcxi j,
  match_stack ge s ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  stack_inject j s sp ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists rs2,
       exec_straight tge tf c rs1 m1' k rs2 m2'
    /\ agree_inj j ms2 sp rs2
    /\ (it1_is_parent ep i = true -> Val.inject j (parent_sp s) rs2#A12)
    /\ rs2#PCXI = Vptr pcxi Ptrofs.zero
    /\ m2' |= prev_ctx_list j s pcxis pcxi ** minjection j m2 ** globalenv_inject ge j) ->
  exists st',
  plus step tge (State rs1 m1') E0 st' /\
  match_states (Mach.State s fb sp c ms2 m2) st'.
Proof.
  intros. inversion H1. subst. monadInv H7.
  exploit H3; eauto. intros (rs2 & A & B & C & D & E).
  exists (State rs2 m2'); split.
  eapply exec_straight_exec; eauto.
  econstructor; eauto. eapply exec_straight_at; eauto.
Qed.

Lemma exec_straight_opt_steps_goto:
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 lbl c' pcxis pcxi j,
  match_stack ge s ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  it1_is_parent ep i = false ->
  stack_inject j s sp ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists jmp, exists k', exists rs2,
       exec_straight_opt tge tf c rs1 m1' (jmp :: k') rs2 m2'
    /\ agree_inj j ms2 sp rs2
    /\ exec_instr tge tf jmp rs2 m2' = goto_label tf lbl rs2 m2'
    /\ rs2#PCXI = Vptr pcxi Ptrofs.zero
    /\ m2' |= prev_ctx_list j s pcxis pcxi ** minjection j m2 ** globalenv_inject ge j) ->
  exists st',
  plus step tge (State rs1 m1') E0 st' /\
  match_states (Mach.State s fb sp c' ms2 m2) st'.
Proof.
  intros. inversion H2. subst. monadInv H9.
  exploit H5; eauto. intros (jmp & k' & rs2 & A & B & C & D & E).
  generalize (functions_transl _ _ _ H7 H8); intro FN.
  generalize (transf_function_no_overflow _ _ H8); intro NOOV.
  inv A.
- (* no steps before the jump *)
  exploit find_label_goto_label; eauto.
  intros [tc' [rs3 [GOTO [AT' OTH]]]].
  exists (State rs3 m2'); split.
  apply plus_one. econstructor; eauto.
  eapply find_instr_tail. eauto.
  rewrite C. eexact GOTO.
  econstructor; eauto.
  apply agree_inj_exten with rs2; auto with asmgen.
  congruence.
  rewrite OTH; eauto with asmgen.
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
  apply agree_inj_exten with rs2; auto with asmgen.
  congruence.
  rewrite OTH; eauto with asmgen.
Qed.

Section OP.

(** ** Small variations on lemmas from Op.v. *)

Variable F V: Type.
Variable genv: Genv.t F V.
Variable f: meminj.
Hypothesis globals: meminj_preserves_globals genv f.
Variable sp sp': val.
Hypothesis SPINJ: Val.inject f sp sp'.

Lemma eval_addressing_inject':
  forall addr vl1 vl2 v1,
  Val.inject_list f vl1 vl2 ->
  eval_addressing genv sp addr vl1 = Some v1 ->
  exists v2,
     eval_addressing genv sp' addr vl2 = Some v2
  /\ Val.inject f v1 v2.
Proof.
  intros.
  eapply eval_addressing_inj with (sp1 := sp); eauto.
  intros. apply symbol_address_inject. assumption.
Qed.

Lemma eval_operation_inject':
  forall op vl1 vl2 v1 m1 m2,
  Val.inject_list f vl1 vl2 ->
  Mem.inject f m1 m2 ->
  eval_operation genv sp op vl1 m1 = Some v1 ->
  exists v2,
     eval_operation genv sp' op vl2 m2 = Some v2
  /\ Val.inject f v1 v2.
Proof.
  intros.
  eapply eval_operation_inj with (sp1 := sp) (m1 := m1); eauto.
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
  intros. apply symbol_address_inject.
  assumption.
Qed.

End OP.

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

(** This is the simulation diagram.  We prove it by case analysis on the Mach transition. *)

Theorem step_simulation:
  forall S1 t S2, Mach.step return_address_offset ge S1 t S2 ->
  forall (WTS: wt_state ge S1) S1' (MS: match_states S1 S1'),
  (exists S2', plus step tge S1' t S2' /\ match_states S2 S2')
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 S1')%nat.
Proof.
  induction 1; intros; inv WTS; inv MS.

- (* Mlabel *)
  left; eapply exec_straight_steps; eauto; intros.
  monadInv TR. econstructor. splitall.
  + apply exec_straight_one; reflexivity.
  + apply agree_inj_nextinstr; eassumption.
  + simpl. congruence.
  + Simpl. exact CSA.
  + eassumption.

- (* Mgetstack *)
  unfold load_stack in H.
  exploit loadv_parallel_rule; eauto.
  + apply sep_proj2, sep_proj1 in SEP. exact SEP.
  + eapply Val.offset_ptr_inject. apply (agree_inj_sp _ _ _ _ AG).
  + intros [v' [A B]].
    left; eapply exec_straight_steps; eauto; intros. monadInv TR. ErrorSingle.
    exploit loadind_correct; eauto with asmgen. intros [rs' [P [Q R]]].
    exists rs'; splitall; try eassumption.
    * eapply agree_inj_set_mreg; eauto with asmgen. congruence.
    * simpl; congruence.
    * rewrite R; eauto with asmgen.

- (* Msetstack *)
  unfold store_stack in H.
  assert (Val.inject j (Mach.get_pair src rs) (get_pair (preg_rpair_of src) rs0)).
  { eapply preg_rpair_val2; eauto. }
  exploit storev_parallel_rule; try eassumption.
  + apply sep_swap in SEP. exact SEP.
  + eapply Val.offset_ptr_inject. apply (agree_inj_sp _ _ _ _ AG).
  + clear SEP. intros [m2' [A SEP]].
    left; eapply exec_straight_steps; eauto. intros. monadInv TR. ErrorSingle.
    exploit storeind_correct; eauto with asmgen. intros [rs' [P Q]].
    exists rs'; splitall. eassumption.
    * eapply agree_inj_undef_regs; eauto with asmgen.
    * simpl; intros. rewrite Q; auto with asmgen.
    * rewrite Q; eauto with asmgen.
    * apply sep_swap in SEP. exact SEP.

- (* Mrestorecallee *)
  inv AT. monadInv H3.

- (* Msavecallee *)
  inv AT. monadInv H4.

- (* Mgetparam *)
  assert (f0 = f) by congruence; subst f0.
  assert (f1 = f) by congruence; subst f1.
  unfold load_stack in *.
  exploit loadv_parallel_rule.
  + apply sep_proj2, sep_proj1 in SEP. exact SEP.
  + exact H0.
  + eapply Val.offset_ptr_inject. apply (agree_inj_sp _ _ _ _ AG).
  + intros [parent' [A B]].
    exploit loadv_parallel_rule.
  * apply sep_proj2, sep_proj1 in SEP. exact SEP.
  * exact H1.
  * eapply Val.offset_ptr_inject. exact B.
  * intros [v' [C D]].
Opaque loadind.
    left; eapply exec_straight_steps; eauto; intros. monadInv TR. ErrorSingle.
    destruct ep.
    { (* A12 contains parent *)
      assert (rs0 A12 = parent').
      { eapply Val.inject_injective.
        eapply parent_sp_def; eassumption.
        apply DXP; reflexivity. assumption. }
      subst parent'.
      assert (valid_index_reg A12 rs0 m' = true).
      { (* We know that we're not at the top of the callstack, so parent_sp has been saved in the CSA. *)
        simpl. rewrite CSA.
        destruct s as [|[] s'].
        - (* contradiction *)
          exfalso. simpl in H1. discriminate H1.
        - simpl in SEP. apply sep_proj1 in SEP.
          destruct pcxis as [|pcxi' pcxis']; [contradiction SEP|].
          exploit load_rule.
            apply sep_pick3 in SEP. apply SEP.
          intros (sp' & -> & Hsp').
          
          specialize (DXP eq_refl). simpl in DXP.
          assert (sp0 <> Vundef).
          { unfold not. intros ->. simpl in H1. discriminate H1. }
          rewrite (Val.inject_injective _ _ _ _ H2 DXP Hsp'). 
          rewrite proj_sumbool_is_true; reflexivity.
      }
      exploit loadind_correct; eauto.
      intros [rs1 [P [Q R]]].
      exists rs1; splitall; try eassumption.
      - eapply agree_inj_set_mreg. eapply agree_inj_set_mreg; eauto. congruence. auto with asmgen.
      - simpl; intros. rewrite R; auto with asmgen.
      - rewrite R; eauto with asmgen. 
    }
    { (* A12 does not contain parent *)
      exploit (loadind_ptr_correct tge tf SP (fn_link_ofs f) A12). apply valid_index_reg_A10. eexact A. 
      intros [rs1 [P [Q R]]].
      subst parent'.
      assert (valid_index_reg A12 rs1 m' = true).
      { (* We have just loaded parent_sp into A12, so same proof as above. *)
        simpl. rewrite R; [|congruence..]. rewrite CSA.
        destruct s as [|[] s'].
        - (* contradiction, not the top of stack *)
          exfalso. simpl in H1. discriminate H1.
        - simpl in SEP. apply sep_proj1 in SEP.
          destruct pcxis as [|pcxi' pcxis']; [contradiction SEP|].
          exploit load_rule.
            apply sep_pick3 in SEP. apply SEP.
          intros (sp' & -> & Hsp').
          
          assert (sp0 <> Vundef).
          { unfold not. intros ->. simpl in H1. discriminate H1. }
          rewrite (Val.inject_injective _ _ _ _ H2 B Hsp'). 
          rewrite proj_sumbool_is_true; reflexivity.
      }
      exploit loadind_correct; eauto.
      intros [rs2 [S [T U]]].
      exists rs2; splitall.
      - eapply exec_straight_trans; eassumption.
      - eapply agree_inj_set_mreg. eapply agree_inj_set_mreg.
        + eassumption.
        + constructor.
        + instantiate (1 := rs1#A12 <- (rs2#A12)). intros.
          rewrite Pregmap.gso; auto with asmgen.
        + congruence.
        + intros. unfold Pregmap.set. destruct (PregEq.eq r' A12). congruence. auto with asmgen.
      - simpl; intros. rewrite U; auto with asmgen.
      - rewrite U; auto with asmgen.
        rewrite R; auto with asmgen.
      - assumption. 
    }

- (* Mop *)
  exploit eval_operation_inject'.
    eapply globalenv_inject_preserves_globals. apply sep_proj2, sep_proj2 in SEP. exact SEP.
    apply AG.
    eapply preg_rpair_vals2; eauto. 
    eapply sep_proj2, sep_proj1 in SEP. exact SEP.
    exact H.
  intros [v' [A B]]. rewrite <- (eval_operation_preserved ge tge symbols_preserved) in A.
  left; eapply exec_straight_steps; eauto; intros.
  exploit transl_op_correct; eauto. intros (rs2 & P & Q & R & S).
  exists rs2; split. eauto. split.
  assert (Q': inject' j v (preg_rpair_of res) rs2) by (eapply inject_lessdef'_trans; eassumption).
  eapply agree_inj_set_undef_mreg_rpair; eauto with asmgen.
  split. 
  simpl; intros. destruct (andb_prop _ _ H0); clear H0.
  rewrite R; auto. destruct res; [| split; simpl in H2; rewrite andb_true_iff in H2; destruct H2]; simpl; apply preg_of_not_P12; auto.
  Local Transparent destroyed_by_op destroyed_by_cond.
  destruct op; simpl; auto; split; congruence.
  split. rewrite S. eassumption.
  eassumption.

- (* Mload *)
  exploit eval_addressing_inject'.
    eapply globalenv_inject_preserves_globals. apply sep_proj2, sep_proj2 in SEP. exact SEP.
    apply AG.
    eapply preg_vals2; eassumption.
    exact H.
  intros [a' [A B]]. rewrite <- (eval_addressing_preserved ge tge symbols_preserved) in A.
  exploit loadv_parallel_rule. 
    eapply sep_proj2, sep_proj1 in SEP. exact SEP. 
    exact H0. exact B.
  intros [v' [C D]].
  left; eapply exec_straight_steps; eauto; intros. monadInv TR. ErrorSingle.
  exploit transl_load_correct; eauto. intros [rs2 [P [Q R]]].
  exists rs2; split. eauto.
  split. eapply agree_inj_set_undef_mreg; eauto. congruence.
  intros; auto with asmgen.
  split. congruence.
  split. rewrite R; eauto with asmgen.
  eassumption.

- (* Mstore *)
  exploit eval_addressing_inject'.
    eapply globalenv_inject_preserves_globals. apply sep_proj2, sep_proj2 in SEP. exact SEP.
    apply AG.
    eapply preg_vals2; eassumption.
    exact H.
  intros [a' [A B]]. rewrite <- (eval_addressing_preserved ge tge symbols_preserved) in A.
  assert (Val.inject j (Mach.get_pair src rs) (get_pair (preg_rpair_of src) rs0)). eapply preg_rpair_val2; eauto.
  exploit storev_parallel_rule; eauto. 
    rewrite sep_comm, sep_assoc in SEP. exact SEP.
  clear SEP. intros [m2' [C SEP]].
    rewrite <- sep_assoc, sep_comm in SEP.
  left; eapply exec_straight_steps; eauto.
  intros. monadInv TR. ErrorSingle.
  exploit transl_store_correct; eauto. intros [rs2 [P Q]].
  exists rs2; split. eauto.
  split. eapply agree_inj_undef_regs; eauto with asmgen.
  split. congruence.
  split. rewrite Q; eauto with asmgen.
  eassumption.

- (* Mcall *)
  rename rs into ms, rs0 into rs, m into m_mach, m' into m_asm.
  assert (f0 = f) by congruence. subst f0.
  assert (f1 = f) by congruence; subst f1.
  inv AT.
  assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
  eapply transf_function_no_overflow; eauto.
  destruct ros as [rf|fid]; simpl in H; monadInv H6.
  + (* Indirect call *)
    assert (ms rf = Vptr fb' Ptrofs.zero).
    { destruct (ms rf); try discriminate.
      revert H; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence. }
    (* fb' is a global allocation, so unaffected by injections. *)
    assert (rs x0 = Vptr fb' Ptrofs.zero).
    { assert (Val.inject j (Vptr fb' Ptrofs.zero) (rs x0)).
      { rewrite <- H6. eapply areg_val; eassumption. }
      inv H8.
      apply sep_proj2, sep_proj2 in SEP. destruct SEP as (bound&?&[]).
      apply FUNCTIONS in H0. apply DOMAIN in H0.
      rewrite H0 in H12. inv H12.
      rewrite Ptrofs.add_zero. reflexivity. }
    generalize (code_tail_next_int _ _ _ _ NOOV H7). intro CT1.
    assert (TCA: transl_code_at_pc ge (Vptr fb (Ptrofs.add ofs Ptrofs.one)) fb f c false tf x).
    { econstructor; eauto. }
    exploit return_address_offset_correct; eauto. intros; subst ra.
    exploit exec_call_correct; eauto.
    clear SEP. intros (rs1 & m_asm1 & pcxi' & A & SEP & C & D & E & F).

    left; econstructor; split.
    eapply plus_one. eapply exec_step_internal. Simpl. rewrite <- H3; simpl; eauto.
    eapply functions_transl; eauto. eapply find_instr_tail; eauto.
    simpl. rewrite <- H3. simpl. exact A. traceEq.

    econstructor.
    * econstructor; eauto.
      eapply agree_inj_sp_def; eauto.
    * simpl. eapply agree_inj_exten; eauto. intros.
      rewrite C; eauto with asmgen.
    * inv SINJ. constructor; assumption.
    * rewrite E. assumption.
    * rewrite F. simpl. reflexivity.
    * eassumption.
    * apply SEP.
  + (* Direct call *)
    generalize (code_tail_next_int _ _ _ _ NOOV H7). intro CT1.
    assert (TCA: transl_code_at_pc ge (Vptr fb (Ptrofs.add ofs Ptrofs.one)) fb f c false tf x).
    econstructor; eauto.
    exploit return_address_offset_correct; eauto. intros; subst ra.
    exploit exec_call_correct; eauto.
    clear SEP. intros (rs1 & m_asm1 & pcxi' &  A & SEP & C & D & E & F).

    left; econstructor; split.
    apply plus_one. eapply exec_step_internal. eauto.
    eapply functions_transl; eauto. eapply find_instr_tail; eauto.
    simpl. unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H.
    rewrite <- H3. simpl. exact A.

    econstructor.
    * econstructor; eauto.
      eapply agree_inj_sp_def; eauto.
    * eapply agree_inj_exten; eauto. intros.
      rewrite C; eauto with asmgen.
    * inv SINJ. constructor; assumption.
    * rewrite E. reflexivity.
    * rewrite F. simpl. reflexivity.
    * eassumption.
    * apply SEP.

- (* Mtailcall *)
  rename rs into ms, rs0 into rs, m into m_mach, m' into m_mach1, m'0 into m_asm.
  assert (f0 = f) by congruence.  subst f0.
  assert (f1 = f) by congruence; subst f1.
  inversion AT; subst.
  assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
  { eapply transf_function_no_overflow; eauto. }
  inv SINJ. 
  assert (exists stk', Val.inject j (Vptr stk soff) (Vptr stk' soff)).
  { inv H10. rename b' into stk'. exists stk'.
    econstructor. eassumption. rewrite Ptrofs.add_zero. reflexivity. }
  destruct H12 as [stk' ?].
  exploit loadv_parallel_rule.
    apply sep_proj2, sep_proj1 in SEP. exact SEP.
    exact H3.
    eapply Val.offset_ptr_inject. eassumption.
  intros (parent' & A & B).
  destruct ros as [rf|fid]; simpl in H0; monadInv H8.
  + (* Indirect call *)
    assert (ms rf = Vptr fb' Ptrofs.zero).
    { destruct (ms rf); try discriminate.
      revert H0; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence. }
    (* fb' is a global allocation, so unaffected by injections. *)
    assert (rs x0 = Vptr fb' Ptrofs.zero).
    { assert (Val.inject j (Vptr fb' Ptrofs.zero) (rs x0)).
      { rewrite <- H8. eapply areg_val; eassumption. }
      inv H13.
      apply sep_proj2, sep_proj2 in SEP. destruct SEP as (bound&?&[]).
      apply FUNCTIONS in H1. apply DOMAIN in H1.
      rewrite H1 in H17. inv H17.
      rewrite Ptrofs.add_zero. reflexivity. }
    exploit make_epilogue_correct; eauto with asmgen.
      inv H10. exists b'; assumption.
      rewrite sep_comm, sep_assoc in SEP. exact SEP.
    clear SEP. intros (rs1 & m_asm1 & U & V & W & X & SEP).
      rewrite <- sep_assoc, sep_comm in SEP.
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
    * apply agree_inj_set_other; auto with asmgen.
    * Simpl. rewrite X; eauto with asmgen.
    * Simpl. rewrite X; eauto with asmgen.
  + (* Direct call *)
    exploit make_epilogue_correct; eauto.
      inv H10. exists b'; assumption.
      rewrite sep_comm, sep_assoc in SEP. exact SEP.
    clear SEP. intros (rs1 & m_asm1 & U & V & W & X & SEP).
      rewrite <- sep_assoc, sep_comm in SEP.
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
    * apply agree_inj_set_other; auto with asmgen.
    * Simpl. unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H0. reflexivity.
    * Simpl. rewrite X; eauto with asmgen.

- (* Mbuiltin *)
  inv AT. monadInv H4.
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H3); intro NOOV.
  exploit builtin_args_match2; eauto.
    apply sep_proj2, sep_proj1 in SEP. exact SEP.
    eapply globalenv_inject_preserves_globals. apply sep_proj2, sep_proj2 in SEP. exact SEP.
  intros [vargs' [P Q]].
  exploit external_call_parallel_rule; eauto.
    rewrite sep_comm, sep_assoc in SEP. exact SEP.
  clear SEP. intros (j' & vres' & m2' & A & B & SEP & C & D).
    rewrite <- sep_assoc, sep_comm in SEP.
  left. econstructor; split. apply plus_one.
  eapply exec_step_builtin. eauto. eauto.
  eapply find_instr_tail; eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  eapply restrict_builtin_args_single; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  eauto.
  econstructor.
  + assumption.
  + eassumption.
  + instantiate (2 := tf); instantiate (1 := x).
    unfold nextinstr. rewrite Pregmap.gss.
    rewrite set_res_other. rewrite undef_regs_other_2.
    rewrite <- H1. simpl. econstructor; eauto.
    eapply code_tail_next_int; eauto.
    rewrite preg_notin_charact. intros. auto with asmgen.
    auto with asmgen.
  + instantiate (1 := j').
    apply agree_inj_nextinstr. erewrite restrict_builtin_res_single; eauto. eapply agree_inj_set_res; auto.
    eapply agree_inj_undef_regs. eapply agree_inj_inject_incr; eassumption.
    intros. rewrite undef_regs_other_2; auto.
  + eapply stack_inject_incr; eassumption.
  + congruence.
  + Simpl. rewrite set_res_other; eauto. rewrite undef_regs_other_2.
    * eassumption.
    * apply preg_notin_charact. intros. eauto with asmgen.
  + eapply pcl_inject_incr; eassumption.

- (* Mgoto *)
  assert (f0 = f) by congruence. subst f0.
  assert (f1 = f) by congruence; subst f1.
  inv AT. monadInv H4.
  exploit find_label_goto_label; eauto. intros [tc' [rs' [GOTO [AT2 INV]]]].
  left; exists (State rs' m'); split.
  apply plus_one. econstructor; eauto.
  eapply functions_transl; eauto.
  eapply find_instr_tail; eauto.
  simpl; eauto.
  econstructor; eauto.
  eapply agree_inj_exten; eauto with asmgen.
  congruence.
  rewrite INV; auto with asmgen.

- (* Mcond true *)
  assert (f0 = f) by congruence. subst f0.
  assert (f1 = f) by congruence; subst f1.
  assert (Mem.inject j m m').
  { apply sep_proj2, sep_proj1 in SEP. exact SEP. }
  exploit eval_condition_inject.
    eapply preg_rpair_vals2; eauto.
    eassumption. eassumption.
  intros EC.
  left; eapply exec_straight_opt_steps_goto; eauto.
  intros. monadInv TR. ErrorSingle.
  exploit transl_cbranch_correct_true; eauto. intros (rs' & jmp & A & B & C).
  exists jmp; exists k; exists rs'.
  split. eexact A.
  split. apply agree_inj_exten with rs0; auto with asmgen.
  split. exact B.
  split. rewrite C; eauto with asmgen.
  eassumption.

- (* Mcond false *)
  assert (Mem.inject j m m').
  { apply sep_proj2, sep_proj1 in SEP. exact SEP. }
  exploit eval_condition_inject.
    eapply preg_rpair_vals2; eauto.
    eassumption. eassumption.
  intros EC.
  left; eapply exec_straight_steps; eauto.
  intros. monadInv TR. ErrorSingle.
  exploit transl_cbranch_correct_false; eauto. intros (rs' & A & B).
  exists rs'.
  split. eexact A.
  split. apply agree_inj_exten with rs0; auto with asmgen.
  split. simpl. congruence.
  split. rewrite B; eauto with asmgen.
  eassumption.

- (* Mjumptable *)
  assert (f0 = f) by congruence. subst f0.
  assert (f1 = f) by congruence; subst f1.
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
  eapply agree_inj_undef_regs; eauto.
  simpl. intros. rewrite C; auto with asmgen. Simpl.
  congruence.
  rewrite C; eauto with asmgen.

- (* Mreturn *)
  assert (f0 = f) by congruence. subst f0.
  assert (f1 = f) by congruence; subst f1.
  inversion AT; subst. simpl in H6; monadInv H6.
  assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  (* compute j stk *)
  inv SINJ.
  exploit make_epilogue_correct; eauto.
    inv H6. exists b'; assumption.
    rewrite sep_comm, sep_assoc in SEP. exact SEP.
  clear SEP. intros (rs1' & m1' & U & V & W & X & SEP).
  rewrite <- sep_assoc, sep_comm in SEP.
  exploit exec_straight_steps_2; eauto using functions_transl.
  intros (ofs' & P & Q).
  exploit (exec_ret_correct j s rs1'). 
    rewrite X; eauto with asmgen. eassumption.
  intros (rs2' & m2' & A & B & C & D).
  left; econstructor; split.
  (* execution *)
  eapply plus_right'. eapply exec_straight_exec; eauto.
  econstructor. eexact P. eapply functions_transl; eauto. eapply find_instr_tail. eexact Q.
  simpl. eassumption. traceEq.
  (* match states *)
  destruct s as [|[] s'], pcxis as [|pcxi' pcxis']; try now contradiction D.
  + (* return from main. PCL & Stack empty *)
    econstructor; eauto.
    simpl. constructor.
    * rewrite D. constructor.
    * unfold Vnullptr. simpl; congruence.
    * intros. unfold Mach.restore_auto_save_regs. destruct (is_auto_save r) eqn:Er.
      constructor. rewrite B; eauto with asmgen. apply V. apply not_auto_save_regs_not_in_upper_ctx; auto.
    * rewrite C. assumption.
    * instantiate (1 := nil). exact I.

  + clear SEP. destruct D as (SEP & D & E & F). econstructor; eauto. simpl.
    constructor.
    * assumption.
    * apply V.
    * intros. unfold Mach.restore_auto_save_regs. destruct (is_auto_save r) eqn:Er.
      auto.
      rewrite B. apply V. auto with asmgen. apply not_auto_save_regs_not_in_upper_ctx; auto.
    * rewrite C. assumption.
    * instantiate (1 := pcxi' :: pcxis'). simpl. split.
      assumption.
      assumption.

- (* internal function *)
  rename m into m_mach, m' into m_asm.
  assert (fd = Internal f) by congruence; subst fd.
  exploit functions_translated; eauto. intros [tf [A B]]. monadInv B.
  generalize EQ; intros EQ'.
  unfold transf_function in EQ'. 
  destruct (wt_function f); inv EQ'. monadInv H4.
  destruct (zlt Ptrofs.max_unsigned (list_length_z x0.(fn_code))); inversion EQ1. clear EQ1. subst x0.
  unfold store_stack in *.
  exploit alloc_parallel_rule_0.
    rewrite sep_comm, sep_assoc in SEP. exact SEP.
    exact H0.
  clear SEP. intros (j' & m1' & stk' & SEP & ALLOC' & ? & JSTK).
  set (sp' := Vptr stk' Ptrofs.zero).
  (* case analysis on s.
     - at the top of the callstack, the parent_* functions result in Vnullptr.
     - down the callstack, the parent_* functions result in pointers.

     Since they use difference constructors we cannot handle them in the same goal. *)
  assert (exists (m2' m3' : mem),
               Mem.storev (chunk_of_type Tptr) m1' (Val.offset_ptr sp' (fn_link_ofs f)) (rs0#SP) = Some m2'
            /\ Mem.storev (chunk_of_type Tptr) m2' (Val.offset_ptr sp' (fn_retaddr_ofs f)) (parent_ra s) = Some m3'
            /\ Val.inject j' (parent_sp s) (rs0#SP)
            /\ m3' |= prev_ctx_list j' s pcxis pcxi ** minjection j' m3 ** globalenv_inject ge j').
  { destruct s as [|[] s'] eqn:Es.
    - (* top of the callstack *)
      exploit storev_parallel_rule; eauto.
      { eapply Val.offset_ptr_inject. unfold sp. econstructor. eassumption. rewrite Ptrofs.add_zero. reflexivity. }
      { simpl. instantiate (1:=Vnullptr). unfold Vnullptr. simpl; constructor. }
      clear SEP. intros (m2' & ST1 & SEP).
      exploit storev_parallel_rule; eauto.
      { eapply Val.offset_ptr_inject. unfold sp. econstructor. eassumption. rewrite Ptrofs.add_zero. reflexivity. }
      { simpl. instantiate (1:=Vnullptr). unfold Vnullptr. simpl; constructor. }
      clear SEP. intros (m3' & ST2 & SEP).
      rewrite <- sep_assoc, sep_comm in SEP. eapply pcl_inject_incr in SEP. 2: eassumption.
      assert (Vnullptr = rs0#SP).
      { destruct AG. simpl in agree_inj_sp.
        unfold Vnullptr. unfold Vnullptr in agree_inj_sp.
        simpl. inv agree_inj_sp; reflexivity. }
      rewrite H4 in ST1.
      exists m2', m3'. splitall; try eassumption.
      simpl. rewrite <- H4. unfold Vnullptr. simpl; constructor.
    - (* down the callstack *)
      eapply stackframes_inject_incr in SFINJ. 2: eassumption.
      revert Es.
      inv SFINJ. inv H6. intros.
      exploit storev_parallel_rule; eauto.
      { eapply Val.offset_ptr_inject. unfold sp. econstructor. eassumption. rewrite Ptrofs.add_zero. reflexivity. }
      { simpl. econstructor. eassumption. rewrite Ptrofs.add_zero. reflexivity. }
      clear SEP. intros (m2' & ST1 & SEP).
      exploit storev_parallel_rule; eauto.
      { eapply Val.offset_ptr_inject. unfold sp. econstructor. eassumption. rewrite Ptrofs.add_zero. reflexivity. }
      { (* ra' is a pointer to a global declaration, so it's unaffected by injections. *)
        simpl. instantiate (1:=retaddr). inv STACKS. inv H13. apply sep_proj2, sep_proj1 in SEP.
        destruct SEP as (bound&?&?). destruct H12.
        apply FUNCTIONS in H5. apply DOMAIN in H5.
        econstructor. eassumption. rewrite Ptrofs.add_zero. reflexivity. }
      clear SEP. intros (m3' & ST2 & SEP).
      rewrite <- sep_assoc, sep_comm in SEP. eapply pcl_inject_incr in SEP. 2: eassumption.
      assert (Vptr b' ofs = rs0#SP).
      { simpl in AG. destruct AG. inv agree_inj_sp.
        apply H3 in H8. rewrite H4 in H8. inv H8.
        rewrite Ptrofs.add_zero. reflexivity. }
      rewrite H5 in ST1.
      exists m2', m3'. splitall; try eassumption.
      simpl. rewrite <- H5. econstructor. eassumption. rewrite Ptrofs.add_zero. reflexivity. }

  clear SEP. destruct H4 as (m2' & m3' & ST1 & ST2 & ? & SEP).

  (* Execution of function prologue *)
  monadInv EQ0. rewrite transl_code'_transl_code in EQ1.
  set (tfbody := Pallocframe (fn_stacksize f) ::
                  storeind_ptr A12 SP (fn_link_ofs f)
                  (storeind_ptr RA SP (fn_retaddr_ofs f) x0)) in *.
  set (tf := {| fn_sig := Mach.fn_sig f; fn_code := tfbody |}) in *.
  (* Prologue moves previous SP to A12 and allocates new sp.
     Due to the injection we use a new value sp'. *)
  set (rs2 := nextinstr (rs0#A12 <- (rs0#SP) #SP <- sp')).
  exploit (storeind_ptr_correct tge tf SP (fn_link_ofs f) A12); eauto with asmgen.
    rewrite chunk_of_Tptr in ST1. instantiate (2 := rs2).
    change (rs2 A12) with (rs0 A10). eexact ST1.
  intros (rs3 & U & V).
  exploit (storeind_ptr_correct tge tf SP (fn_retaddr_ofs f) RA); eauto.
    rewrite chunk_of_Tptr in ST2. instantiate (2 := rs3).
    rewrite (V A11) by congruence.
    change (rs2 A11) with (rs0 A11). rewrite ATLR.
    rewrite (V A10) by congruence.
    change (rs2 A10) with sp'. eexact ST2.
    congruence.
  intros (rs4 & U' & V').
  assert (EXEC_PROLOGUE:
            exec_straight tge tf
              tf.(fn_code) rs0 m_asm
              x0 rs4 m3').
  { change (fn_code tf) with tfbody; unfold tfbody.
    apply exec_straight_step with rs2 m1'.
    unfold exec_instr. rewrite ALLOC'. fold sp'. 
    reflexivity. reflexivity.
    eapply exec_straight_trans. eexact U. eexact U'.
  }
  exploit exec_straight_steps_2; eauto using functions_transl. lia. constructor.
  intros (ofs' & X & Y).
  left; exists (State rs4 m3'); split.
  eapply exec_straight_steps_1; eauto. lia. constructor.
  econstructor; eauto.
  rewrite X; econstructor; eauto.
  apply agree_inj_exten with rs2; eauto with asmgen.
  unfold rs2.
  apply agree_inj_nextinstr.
  apply agree_inj_change_sp with (parent_sp s).
  apply agree_inj_undef_regs with rs0.
  eapply agree_inj_inject_incr. eassumption. auto.
Local Transparent destroyed_at_function_entry.
  simpl; intros; Simpl.
  unfold sp; congruence.
  econstructor. eassumption. rewrite Ptrofs.add_zero. reflexivity.
  intros. rewrite V', V; auto with asmgen.
  econstructor. econstructor. eassumption. eapply stackframes_inject_incr; eassumption.
  intros. rewrite V', V; auto with asmgen.
  rewrite V', V; auto with asmgen.

- (* external function *)
  rename m into m_mach, m' into m_mach1, m'0 into m_asm.
  exploit functions_translated. exact H.
  intros [tf [A B]]. simpl in B. inv B.
  assert (Mem.inject j m_mach m_asm).
  { apply sep_proj2, sep_proj1 in SEP. apply SEP. }
  exploit extcall_arguments_match2; eauto.
  intros [args' [C D]].
  exploit external_call_parallel_rule; eauto.
  1: { apply sep_comm, sep_assoc in SEP. exact SEP. }
  clear SEP. intros (j' & res' & m1' & P & Q & SEP & R & S).
  rewrite <- sep_assoc, sep_comm in SEP.
  eapply pcl_inject_incr in SEP; eauto.
  set (rs1' := undef_callee_may_modify_regs rs0).
  assert (CSA1: rs1' PCXI = Vptr pcxi Ptrofs.zero).
  { unfold rs1'.
    unfold undef_callee_may_modify_regs.
    rewrite pred_dec_false; [|congruence].
    rewrite pred_dec_false. assumption.
    unfold callee_may_modify_regs. unfold not.
    intros. apply in_map_iff in H3. destruct H3 as (?&?&?).
    generalize (preg_of_not_PCXI x). congruence. }

  exploit restore_ctx_upper_correct.
    apply CSA1. apply SEP.
  intros (rs2' & m3' & T & U & Hs).
  left; econstructor; split.
  + apply plus_one. eapply exec_step_external; eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  + (* Case analysis on whether we are at the top of the callstack.
     - At the top, we free the current CSA and are left without any prev_ctx_list assertion.
       This case should only happen when we tailcall an external function from main.
     - Otherwise we free the current CSA and continue with the nested prev_ctx_list assertion. *)
    destruct s as [|[fb' sp' ra' c' rs'] s'] eqn:Es, pcxis as [|pcxi' pcxis'].
    2,3: now destruct SEP as [[]].
    { (* Top of the call stack. *)
      apply (stackframes_inject_incr _ _ _ R) in SFINJ.
      econstructor; eauto.
      unfold loc_external_result. apply agree_inj_set_other; auto. apply agree_inj_set_pair; auto.
      eapply agree_inj_inject_incr. eassumption.
      simpl. constructor.
      - rewrite Hs. unfold Vnullptr. simpl; constructor.
      - unfold Vnullptr. simpl; congruence.
      - intros. unfold external_call_regs, restore_auto_save_regs, Mach.undef_callee_may_modify_regs.
        unfold is_auto_save, is_modifiable_by_callee. destruct (reg_cc r) eqn:Er; [|constructor..].
        contradiction (regcc_not_callee r).
      - instantiate (1 := nil). exact I. }
    { (* Down the call stack. *)
      clear SEP. destruct Hs as (SEP & V & W & X).
      apply (stackframes_inject_incr _ _ _ R) in SFINJ.
      econstructor; eauto.
      unfold loc_external_result. apply agree_inj_set_other; auto. apply agree_inj_set_pair; auto.
      simpl. constructor.
      - assumption.
      - apply AG.
      - intros. unfold external_call_regs, restore_auto_save_regs, Mach.undef_callee_may_modify_regs.
        unfold is_auto_save, is_modifiable_by_callee. destruct (reg_cc r) eqn:Er.
        + contradiction (regcc_not_callee r).
        + apply V. unfold is_auto_save. now rewrite Er.
        + constructor. 
      - instantiate (1 := pcxi' :: pcxis'). split; [|assumption].
        Simpl. unfold loc_external_result. destruct (loc_result (ef_sig ef)); simpl.
        rewrite Pregmap.gso; eauto with asmgen.
        rewrite 2 Pregmap.gso; eauto with asmgen. }

- (* return *)
  inv STACKS. simpl in *.
  right. split. lia. split. auto.
  rewrite <- ATPC in H6.
  destruct pcxis as [|pcxi' pcxis']; try contradiction.
  destruct PCL as (CSA & SEP).
  econstructor; eauto.
  + inv SFINJ. econstructor; assumption.
  + congruence.
Qed.

Lemma transf_initial_states:
  forall st1, Mach.initial_state prog st1 ->
  exists st2, Asm.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H. unfold ge0 in *.
  (* Store Vnullptr into the initial CSA.
     We know that the access is valid, so the store succeeds. *)
  destruct (Mem.alloc m0 0 csa_size) as [m1 pcxi] eqn:ALLOC.
  assert (ACCESS_SP: Mem.valid_access m1 Many32 pcxi 8 Writable).
  { apply Mem.valid_access_freeable_any.
    unfold Mem.valid_access. split. 2: sep_lia.
    unfold Mem.range_perm.
    intros. eapply Mem.perm_alloc_2. eassumption. 
    simpl in H4. sep_lia. }
  destruct (Mem.valid_access_store _ _ _ _ Vnullptr ACCESS_SP) as (m2 & STORE_SP).

  econstructor; split.
  econstructor.
  eapply (Genv.init_mem_transf_partial TRANSF); eauto.
  eassumption. eassumption.
  replace (Genv.symbol_address (Genv.globalenv tprog) (prog_main tprog) Ptrofs.zero)
     with (Vptr fb Ptrofs.zero).
  pose proof (Genv.initmem_inject _ H0).
  set (j := Mem.flat_inj (Mem.nextblock m0)) in *.
  assert (~ Coqlib.Plt pcxi (Mem.nextblock m0)).
  { erewrite <- Mem.alloc_result. 2: exact ALLOC.
    apply Pos.lt_irrefl. }
  eapply match_states_call with (j := j) (pcxis := nil); Simpl.
  - econstructor; eauto.
  - split.
    + Simpl. simpl. unfold Vnullptr. simpl; constructor.
    + simpl. unfold Vnullptr. simpl; congruence.
    + intros. rewrite Regmap.gi. auto.
  - constructor.
  - assert (SEP: m0 |= minjection j m0 ** globalenv_inject ge j).
    { split; [|split].
      unfold m_pred. simpl.
      + eapply Genv.initmem_inject; eauto.
      + red; simpl. exists (Mem.nextblock m0); split. apply Ple_refl.
        unfold j, Mem.flat_inj; constructor; intros.
          apply pred_dec_true; auto.
          destruct (plt b1 (Mem.nextblock m0)); congruence.
          change (Mem.valid_block m0 b). eapply Genv.find_symbol_not_fresh; eauto.
          change (Mem.valid_block m0 b). eapply Genv.find_funct_ptr_not_fresh; eauto.
          change (Mem.valid_block m0 b). eapply Genv.find_var_info_not_fresh; eauto.
      + red; simpl; tauto. }
    exploit alloc_rule; eauto.
      lia.
      apply csa_size_no_overflow.
    clear SEP. intros SEP.

    (* massage SEP to prepare for saving Vnullptr in SP position. *)
    apply (range_split _ _ _ _ 8) in SEP; [|sep_lia].
    rewrite sep_swap in SEP.
    apply (range_split _ _ _ _ 12) in SEP; [|sep_lia].
    change (range pcxi 8 12) with (range pcxi 8 (8 + size_chunk Many32)) in SEP.
    apply range_contains in SEP; [|sep_lia].
    apply (store_rule _ _ _ _ Vnullptr _ (fun v' => v' = Vnullptr)) in SEP.
    destruct SEP as (m2' & STORE_SP' & SEP).
    rewrite STORE_SP' in STORE_SP. inv STORE_SP.
    rewrite sep_swap23, sep_swap12 in SEP.

    simpl. rewrite ! sep_assoc. exact SEP. 
    reflexivity.
  - unfold Genv.symbol_address.
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
  generalize (preg_val2 _ _ _ _ R2 AG). rewrite H2. intros LD; inv LD. auto.
Qed.

Lemma wt_prog:
  forall i fd, In (i, Gfun fd) prog.(prog_defs) -> wt_fundef fd.
Proof.
  intros.
  exploit list_forall2_in_left. eexact (proj1 TRANSF). eauto.
  intros ([i' g] & P & Q & R). simpl in *. inv R. destruct fd; simpl in *.
- monadInv H2. unfold transf_function in EQ.
  destruct (wt_function f). auto. discriminate.
- auto.
Qed.

Theorem transf_program_correct:
  forward_simulation (Mach.semantics return_address_offset prog) (Asm.semantics tprog).
Proof.
  set (ms := fun s s' => wt_state ge s /\ match_states s s').
  eapply forward_simulation_star with (measure := measure) (match_states := ms).
  - apply senv_preserved.
  - intros. exploit transf_initial_states; eauto. intros [st2 [A B]].
    exists st2; split; [|split].
    assumption. 
    apply wt_initial_state; eauto using wt_prog.
    assumption.
  - intros. destruct H. eapply transf_final_states; eauto.
  - intros. destruct H0. 
    exploit step_simulation; eauto.
    intros [(s2' & A & B)|(?&?&?)].
    + left. exists s2'. split; auto. split; auto. 
      eapply step_type_preservation; eauto. apply wt_prog. apply H.
    + right. split; auto. split; auto. split; auto. 
      eapply step_type_preservation; eauto. apply wt_prog. apply H.
Qed.

End PRESERVATION.
