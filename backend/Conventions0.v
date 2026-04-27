Require Import Machregs.

(** * Classification of machine registers

  For most architectures, registers are classified as either callee-save or caller-save.
  The TriCore architecture additionally designates the registers of the upper context
  as being automatically saved on `call` instructions, and restored on `return` instructions.
  We name these auto-save. *)

(*- E_COMPCERT_FTR_Function_Conventions0_RegCC_0_001 *)
(*- #Justify_Derived "Internal type" *)
Inductive RegCC :=
  | RCCallee
  | RCAuto
  | RCCaller.
(*- #End *)

(* Each architecture needs to define a reg_cc function, assigning the calling-conventions of its registers.
   We use a Coq functor to reduce code duplication. The functor is instiantiated in each <arch>/Conventions1.v file. *)
Module Type REGCC.
  (*- E_COMPCERT_FTR_Function_Conventions_reg_cc_001 *)
  (*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_005 *)
  Parameter reg_cc: mreg -> RegCC.
  (*- #End *)
End REGCC.

Module Make(CC: REGCC).

Include CC.

(** * Predicates on the classification.

 Often easier to read than a match expression, but they require some rewriting machinery for proofs.
 This is implemented by the is_X_Y lemmas and the [reg_cc_all] tactic below. *)

(*- E_COMPCERT_FTR_Function_Conventions_is_caller_save_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_005 *)
Definition is_caller_save (r: mreg): bool :=
  match reg_cc r with RCCaller => true | _ => false end.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Conventions_is_callee_save_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_005 *)
Definition is_callee_save (r: mreg): bool :=
  match reg_cc r with RCCallee => true | _ => false end.
(*- #End *)

Definition is_auto_save (r: mreg): bool :=
  match reg_cc r with RCAuto => true | _ => false end.

(* Register is preserved across call.
   - Callee-save registers are restored by callee.
   - Auto-save registers are restored by ret instruction. *)
Definition is_preserved_across_call (r: mreg): bool :=
  match reg_cc r with RCCallee | RCAuto => true | _ => false end.

(* Register is modifiable by callee without saving its previous value.
   - Caller-save registers are restored by caller if needed.
   - Auto-save registers are restored by ret instruction. *)
Definition is_modifiable_by_callee (r: mreg): bool :=
  match reg_cc r with RCCaller | RCAuto => true | _ => false end.

Lemma is_preserved_callee_auto:
  forall r, is_preserved_across_call r = true -> is_callee_save r = true \/ is_auto_save r = true.
Proof. intros r; cbv; destruct (reg_cc r); intuition congruence. Qed.

Lemma is_callee_preserved:
  forall r, is_callee_save r = true -> is_preserved_across_call r = true.
Proof. intros r; cbv; destruct (reg_cc r); intuition congruence. Qed.

Lemma is_auto_preserved:
  forall r, is_auto_save r = true -> is_preserved_across_call r = true.
Proof. intros r; cbv; destruct (reg_cc r); intuition congruence. Qed.

Lemma is_not_preserved_caller:
  forall r, is_preserved_across_call r = false -> is_caller_save r = true.
Proof. intros r; cbv; destruct (reg_cc r); intuition congruence. Qed.

Lemma is_caller_not_preserved:
  forall r, is_caller_save r = true -> is_preserved_across_call r = false.
Proof. intros r; cbv; destruct (reg_cc r); intuition congruence. Qed.

Lemma is_modifiable_caller_auto:
  forall r, is_modifiable_by_callee r = true -> is_caller_save r = true \/ is_auto_save r = true.
Proof. intros r; cbv; destruct (reg_cc r); intuition congruence. Qed.

Lemma is_caller_modifiable:
  forall r, is_caller_save r = true -> is_modifiable_by_callee r = true.
Proof. intros r; cbv; destruct (reg_cc r); intuition congruence. Qed.

Lemma is_auto_modifiable:
  forall r, is_auto_save r = true -> is_modifiable_by_callee r = true.
Proof. intros r; cbv; destruct (reg_cc r); intuition congruence. Qed.

Lemma is_not_modifiable_callee:
  forall r, is_modifiable_by_callee r = false -> is_callee_save r = true.
Proof. intros r; cbv; destruct (reg_cc r); intuition congruence. Qed.

Lemma is_callee_not_modifiable:
  forall r, is_callee_save r = true -> is_modifiable_by_callee r = false.
Proof. intros r; cbv; destruct (reg_cc r); intuition congruence. Qed.

Lemma reg_cc_complete:
  forall r,
     (is_caller_save r = true  /\ is_callee_save r = false /\ is_auto_save r = false /\ is_preserved_across_call r = false /\ is_modifiable_by_callee r = true)
  \/ (is_caller_save r = false /\ is_callee_save r = true  /\ is_auto_save r = false /\ is_preserved_across_call r = true  /\ is_modifiable_by_callee r = false)
  \/ (is_caller_save r = false /\ is_callee_save r = false /\ is_auto_save r = true  /\ is_preserved_across_call r = true /\ is_modifiable_by_callee r = true).
Proof. intros r; cbv; destruct (reg_cc r); tauto. Qed.

Ltac reg_cc_congruence :=
  match goal with
  | [ H : is_preserved_across_call ?r = true |- _ ] => apply (is_preserved_callee_auto r) in H; destruct H as [?|?]
  | [ H : is_preserved_across_call ?r = false |- _ ] => apply (is_not_preserved_caller r H)
  | [ H : is_modifiable_by_callee ?r = true |- _ ] => apply (is_modifiable_caller_auto r) in H; destruct H as [?|?]
  | [ H : is_modifiable_by_callee ?r = false |- _ ] => apply (is_not_modifiable_callee r)
  | _ => idtac
  end; congruence.

(** Split the current goal into subgoals, adding hypotheses about the value of [reg_cc r].
    Contradictory subgoals are cleaned up. *)
Ltac reg_cc_all r :=
  let HrCaller := fresh "HrCaller" in
  let HrCallee := fresh "HrCallee" in
  let HrAuto := fresh "HrAuto" in
  let HrPreserve := fresh "HrPreserve" in
  let HrModify := fresh "HrModify" in
  destruct (reg_cc_complete r) as [   (HrCaller&HrCallee&HrAuto&HrPreserve&HrModify)
                                  | [ (HrCaller&HrCallee&HrAuto&HrPreserve&HrModify)
                                    | (HrCaller&HrCallee&HrAuto&HrPreserve&HrModify) ] ];
  try reg_cc_congruence.

End Make.
