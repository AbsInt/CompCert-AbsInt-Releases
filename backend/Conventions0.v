Require Import Machregs.

(** * Classification of machine registers

  For most architectures, registers are classified as either callee-save or caller-save. 
  The TriCore architecture additionally designates the registers of the upper context 
  as being automatically saved on `call` instructions, and restored on `return` instructions. 
  We name these auto-save. *)

(*- E_COMPCERT_FTR_Function_Conventions0_RegCC_0_001 *)
(*- #Justify_Derived "Internal type" *)
Inductive RegCC :=
  | Callee
  | Auto
  | Caller.
(*- #End *)

(* Each architecture needs to define a reg_cc function, assigning the calling-convention of that register. 
   We use a Coq functor to reduce some code. The functor is instiantiated in each <arch>/Conventions1.v file. *)
Module Type REGCC.
  (*- E_COMPCERT_FTR_Function_Conventions_reg_cc_001 *)
  (*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_005 *)
  Parameter reg_cc: mreg -> RegCC.
  (*- #End *)
End REGCC.

Module Make(CC: REGCC).

Include CC.

(*- E_COMPCERT_FTR_Function_Conventions_is_caller_save_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_005 *)
Definition is_caller_save (r: mreg): bool :=
  match reg_cc r with Caller => true | _ => false end.
(*- #End *)

Definition is_callee_save (r: mreg): bool :=
  match reg_cc r with Callee => true | _ => false end.

Definition is_auto_save (r: mreg): bool :=
  match reg_cc r with Auto => true | _ => false end.

Ltac solve_reg :=
  intros r; unfold is_caller_save, is_callee_save, is_auto_save;
  destruct (reg_cc r); congruence.

Lemma reg_caller_not_callee:
  forall r, is_caller_save r = true -> is_callee_save r = false.
Proof. solve_reg. Qed.

Lemma reg_caller_not_auto:
  forall r, is_caller_save r = true -> is_auto_save r = false.
Proof. solve_reg. Qed.

Lemma reg_callee_not_caller:
  forall r, is_callee_save r = true -> is_caller_save r = false.
Proof. solve_reg. Qed.

Lemma reg_cc_complete:
  forall r, is_caller_save r = true \/ is_callee_save r = true \/ is_auto_save r = true.
Proof. 
  intros. unfold is_caller_save, is_callee_save, is_auto_save.
  destruct (reg_cc r); simpl; intuition.
Qed.

End Make.
