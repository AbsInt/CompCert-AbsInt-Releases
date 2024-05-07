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

Require Import String.
Require Import Coqlib.
Require Import Decidableplus.
Require Import Maps.
Require Import AST.
Require Import Op.

(** ** Machine registers *)

(** The following type defines the machine registers that can be referenced
  as locations.  These include:
- Integer registers that can be allocated to RTL pseudo-registers ([Rxx]).

  The type [mreg] does not include special-purpose or reserved
  machine registers such as the stack pointer (GPR1), the small data area
  pointers (GPR2, GPR13), and the condition codes. *)

(*- E_COMPCERT_FTR_Function_Machregs_mreg_0_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_EABI_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Inductive mreg: Type :=
  (** Allocatable integer regs *)
  | R3: mreg  | R4: mreg  | R5: mreg  | R6: mreg
  | R7: mreg  | R8: mreg  | R9: mreg  | R10: mreg
  | R11: mreg | R12: mreg
  | R14: mreg | R15: mreg | R16: mreg
  | R17: mreg | R18: mreg | R19: mreg | R20: mreg
  | R21: mreg | R22: mreg | R23: mreg | R24: mreg
  | R25: mreg | R26: mreg | R27: mreg | R28: mreg
  | R29: mreg | R30: mreg | R31: mreg
  (** Dummy floating point register for double *)
  | ErrorReg: mreg.
(*- #End *)

Lemma mreg_eq: forall (r1 r2: mreg), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.
Global Opaque mreg_eq.

(*- E_COMPCERT_FTR_Function_Machregs_all_mregs_001 *)
(*- #Justify_Derived "Internal list of all registers" *)
Definition all_mregs :=
     R3  :: R4  :: R5  :: R6  :: R7  :: R8  :: R9  :: R10
  :: R11 :: R12 :: R14 :: R15 :: R16 :: R17 :: R18 :: R19 :: R20
  :: R21 :: R22 :: R23 :: R24 :: R25 :: R26 :: R27 :: R28
  :: R29 :: R30 :: R31
  :: ErrorReg :: nil.
(*- #End *)

Lemma all_mregs_complete:
  forall (r: mreg), In r all_mregs.
Proof.
  assert (forall r, proj_sumbool (In_dec mreg_eq r all_mregs) = true) by (destruct r; reflexivity).
  intros. specialize (H r). InvBooleans. auto.
Qed.

Global Instance Decidable_eq_mreg : forall (x y: mreg), Decidable (eq x y) := Decidable_eq mreg_eq.

Global Instance Finite_mreg : Finite mreg := {
  Finite_elements := all_mregs;
  Finite_elements_spec := all_mregs_complete
}.

Definition mreg_type (r: mreg): typ :=
  match r with
  | R3  | R4  | R5  | R6  | R7  | R8  | R9  | R10  | R11 | R12
  | R14 | R15 | R16 | R17 | R18 | R19 | R20 | R21 | R22 | R23 | R24
  | R25 | R26 | R27 | R28 | R29 | R30 | R31 =>  Tany32
  | ErrorReg => Tany64
  end.

Open Scope positive_scope.

Module IndexedMreg <: INDEXED_TYPE.
  Definition t := mreg.
  Definition eq := mreg_eq.
  Definition index (r: mreg): positive :=
    match r with
    | R3 => 1  | R4 => 2  | R5 => 3  | R6 => 4
    | R7 => 5  | R8 => 6  | R9 => 7  | R10 => 8
    | R11 => 9 | R12 => 10
    | R14 => 11 | R15 => 12 | R16 => 13
    | R17 => 14 | R18 => 15 | R19 => 16 | R20 => 17
    | R21 => 18 | R22 => 19 | R23 => 20 | R24 => 21
    | R25 => 22 | R26 => 23 | R27 => 24 | R28 => 25
    | R29 => 26 | R30 => 27 | R31 => 28
    | ErrorReg => 29
    end.
  Lemma index_inj:
    forall r1 r2, index r1 = index r2 -> r1 = r2.
  Proof.
    decide_goal.
  Qed.
End IndexedMreg.

Definition is_stack_reg (r: mreg) : bool := false.

(** ** Names of registers *)

Local Open Scope string_scope.

(*- E_COMPCERT_FTR_Function_Machregs_register_names_001 *)
(*- #Justify_Derived "Internal list of all registers with their names" *)
Definition register_names :=
  ("R3", R3) ::  ("R4", R4) ::  ("R5", R5) ::  ("R6", R6) ::
  ("R7", R7) ::  ("R8", R8) ::  ("R9", R9) ::  ("R10", R10) ::
  ("R11", R11) :: ("R12", R12) ::
  ("R14", R14) :: ("R15", R15) :: ("R16", R16) ::
  ("R17", R17) :: ("R18", R18) :: ("R19", R19) :: ("R20", R20) ::
  ("R21", R21) :: ("R22", R22) :: ("R23", R23) :: ("R24", R24) ::
  ("R25", R25) :: ("R26", R26) :: ("R27", R27) :: ("R28", R28) ::
  ("R29", R29) :: ("R30", R30) :: ("R31", R31) :: nil.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Machregs_register_by_name_001 *)
(*- #Justify_Derived "Auxiliary function" *)
Definition register_by_name (s: string) : option mreg :=
  let fix assoc (l: list (string * mreg)) : option mreg :=
    match l with
    | nil => None
    | (s1, r1) :: l' => if string_dec s s1 then Some r1 else assoc l'
    end
  in assoc register_names.
(*- #End *)

(** ** Destroyed registers, preferred registers *)

(*- E_COMPCERT_FTR_Function_Machregs_destroyed_by_cond_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Definition destroyed_by_cond (cond: condition): list mreg := nil.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Machregs_destroyed_by_op_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Definition destroyed_by_op (op: operation): list mreg :=
  match op with
  | Ocmp c => destroyed_by_cond c
  | _ => nil
  end.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Machregs_destroyed_by_load_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Definition destroyed_by_load (chunk: memory_chunk) (addr: addressing): list mreg :=
  R12 :: nil.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Machregs_destroyed_by_store_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Definition destroyed_by_store (chunk: memory_chunk) (addr: addressing): list mreg :=
  R11 :: R12 :: nil.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Machregs_destroyed_by_jumptable_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Definition destroyed_by_jumptable: list mreg :=
  R12 :: nil.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Machregs_destroyed_by_clobber_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_EXTENDED_ASM_003 *)
Fixpoint destroyed_by_clobber (cl: list string): list mreg :=
  match cl with
  | nil => nil
  | c1 :: cl =>
      match register_by_name c1 with
      | Some r => r :: destroyed_by_clobber cl
      | None   => destroyed_by_clobber cl
      end
  end.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Machregs_destroyed_by_builtin_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_BUILTIN_011 *)
(*- #Link_to E_COMPCERT_TOR_Function_BUILTIN_POWERPC_032 *)
(*- #Link_to E_COMPCERT_TOR_Function_BUILTIN_POWERPC_033 *)
(*- #Link_to E_COMPCERT_TOR_Function_BUILTIN_POWERPC_035 *)
Definition destroyed_by_builtin (ef: external_function): list mreg :=
  match ef with
  | EF_builtin id sg => nil
  | EF_vload _ => R11 :: nil
  | EF_vstore Mint64 => R10 :: R11 :: R12 :: nil
  | EF_vstore _ => R11 :: R12 :: nil
  | EF_memcpy _ _ => R11 :: R12 :: nil
  | EF_inline_asm txt sg clob => destroyed_by_clobber clob
  | _ => nil
  end.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Machregs_destroyed_by_setstack_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Definition destroyed_by_setstack (ty: typ): list mreg :=
  nil.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Machregs_destroyed_at_function_entry_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Definition destroyed_at_function_entry: list mreg :=
  nil.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Machregs_destroyed_at_indirect_call_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Definition destroyed_at_indirect_call: list mreg :=
  nil.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Machregs_temp_for_parent_frame_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Definition temp_for_parent_frame: mreg :=
  R11.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Machregs_mregs_for_operation_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Definition mregs_for_operation (op: operation): list (option mreg) * option mreg :=
  (nil, None).
(*- #End *)


(*- E_COMPCERT_FTR_Function_Machregs_mregs_for_builtin_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_BUILTIN_POWERPC_032 *)
(*- #Link_to E_COMPCERT_TOR_Function_BUILTIN_POWERPC_033 *)
(*- #Link_to E_COMPCERT_TOR_Function_BUILTIN_POWERPC_035 *)
Definition mregs_for_builtin (ef: external_function): list (option mreg) * list (option mreg) :=
  (nil, nil).
(*- #End *)

Global Opaque
    destroyed_by_op destroyed_by_load destroyed_by_store
    destroyed_by_cond destroyed_by_jumptable destroyed_by_builtin
    destroyed_at_indirect_call
    destroyed_by_setstack destroyed_at_function_entry temp_for_parent_frame
    mregs_for_operation mregs_for_builtin.

(** Two-address operations.  Return [true] if the first argument and
  the result must be in the same location *and* are unconstrained
  by [mregs_for_operation]. *)

(*- E_COMPCERT_FTR_Function_Machregs_two_address_op_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Definition two_address_op (op: operation) : bool :=
  match op with
  | Oroli _ _ => true
  | Olowlong => true
  | Ofloatofsingle => true
  | _ => false
  end.
(*- #End *)

(* Constraints on constant propagation for builtins *)

Definition builtin_constraints (ef: external_function) :
                                       list builtin_arg_constraint :=
  match ef with
  | EF_builtin id sg =>
      if string_dec id "__builtin_get_spr" then OK_const :: nil
      else if string_dec id "__builtin_set_spr" then OK_const :: OK_default :: nil
      else if string_dec id "__builtin_prefetch" then OK_default :: OK_const :: OK_const :: nil
      else if string_dec id "__builtin_dcbtls" then OK_default :: OK_const :: nil
      else if string_dec id "__builtin_icbtls" then OK_default :: OK_const :: nil
      else if string_dec id "__builtin_mr" then OK_const :: OK_const :: nil
      else nil
  | EF_vload _ => OK_addressing :: nil
  | EF_vstore _ => OK_addressing :: OK_default :: nil
  | EF_memcpy _ _ => OK_addrstack :: OK_addrstack :: nil
  | EF_annot kind txt targs => map (fun _ => OK_all) targs
  | EF_debug kind txt targs => map (fun _ => OK_all) targs
  | _ => nil
  end.
