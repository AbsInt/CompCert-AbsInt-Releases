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

From Coq Require Import String.
Require Import Coqlib.
Require Import Decidableplus.
Require Import Maps.
Require Import AST.
Require Import Op.
Require Import Values.

(** ** Machine registers *)

(** The following type defines the machine registers that can be referenced
  as locations.  These include:
- Integer registers that can be allocated to RTL pseudo-registers ([Rxx]).
- Floating-point registers that can be allocated to RTL pseudo-registers
  ([Fxx]).

  The type [mreg] does not include reserved machine registers
  such as the stack pointer, the link register, and the condition codes. *)

(*- E_COMPCERT_FTR_Function_Machregs_mreg_0_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_EABI_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Inductive mreg: Type :=
  (** Allocatable integer regs *)
  | R0: mreg  | R1: mreg  | R2: mreg  | R3: mreg
  | R4: mreg  | R5: mreg  | R6: mreg  | R7: mreg
  | R8: mreg  | R9: mreg  | R10: mreg | R11: mreg
  | R12: mreg
  (** Allocatable single-precision float regs *)
  | F0: mreg  | F1: mreg  | F2: mreg  | F3: mreg
  | F4: mreg  | F5: mreg  | F6: mreg  | F7: mreg
  | F8: mreg  | F9: mreg  | F10: mreg | F11: mreg
  | F12: mreg | F13: mreg | F14: mreg | F15: mreg
  | F16: mreg | F17: mreg | F18: mreg | F19: mreg
  | F20: mreg | F21: mreg | F22: mreg | F23: mreg
  | F24: mreg | F25: mreg | F26: mreg | F27: mreg
  | F28: mreg | F29: mreg | F30: mreg | F31: mreg
  (** Allocatable double-precision float regs
      - Note that we do not model any aliasing,
        they can not be translated into pregs and are only used
        in XTL during Register Allocation *)
  | D0: mreg  | D1: mreg  | D2: mreg  | D3: mreg
  | D4: mreg  | D5: mreg  | D6: mreg  | D7: mreg
  | D8: mreg  | D9: mreg  | D10: mreg | D11: mreg
  | D12: mreg | D13: mreg | D14: mreg | D15: mreg
  (** Error Register for handling calling convention for pairs *)
  | ErrorReg.
(*- #End *)

Lemma mreg_eq: forall (r1 r2: mreg), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.
Global Opaque mreg_eq.

Definition all_mregs :=
     R0  :: R1  :: R2  :: R3 :: R4  :: R5  :: R6  :: R7
  :: R8  :: R9  :: R10 :: R11 :: R12
  :: F0  :: F1  :: F2  :: F3  :: F4  :: F5  :: F6  :: F7
  :: F8  :: F9  :: F10 :: F11 :: F12 :: F13 :: F14 :: F15
  :: F16 :: F17 :: F18 :: F19 :: F20 :: F21 :: F22 :: F23
  :: F24 :: F25 :: F26 :: F27 :: F28 :: F29 :: F30 :: F31
  :: D0  :: D1  :: D2  :: D3  :: D4  :: D5  :: D6  :: D7
  :: D8  :: D9  :: D10 :: D11 :: D12 :: D13 :: D14 :: D15
  :: ErrorReg :: nil.

(*- E_COMPCERT_FTR_Function_Machregs_all_mregs_001 *)
(*- #Justify_Derived "Internal list of all registers" *)
Lemma all_mregs_complete:
  forall (r: mreg), In r all_mregs.
Proof.
  assert (forall r, proj_sumbool (In_dec mreg_eq r all_mregs) = true) by (destruct r; reflexivity).
  intros. specialize (H r). InvBooleans. auto.
Qed.
(*- #End *)

Global Instance Decidable_eq_mreg : forall (x y: mreg), Decidable (eq x y) := Decidable_eq mreg_eq.

Global Instance Finite_mreg : Finite mreg := {
  Finite_elements := all_mregs;
  Finite_elements_spec := all_mregs_complete
}.

Definition mreg_type (r: mreg): typ :=
  match r with
  | D0 | D1 | D2 | D3 | D4 | D5 | D6 | D7 | D8
  | D9 | D10 | D11 | D12 | D13 | D14 | D15 => Tany64
  | ErrorReg => Tany64
  | _ => Tany32
  end.

Definition mreg_pair_type (p: rpair mreg): typ :=
  match p with
  | One r => mreg_type r
  | _ => Tany64
  end.

Lemma pair_words_type:
  forall rlo rhi v,
    Val.has_type v (mreg_pair_type (Two rhi rlo)) ->
    Val.has_type (Val.hiword v) (mreg_type rhi)
    /\ Val.has_type (Val.loword v) (mreg_type rlo).
Proof.
  intros. split.
  destruct v; auto; destruct rhi; easy.
  destruct v; auto; destruct rlo; easy.
Qed.

Lemma words_pair_type:
  forall rlo rhi v1 v2,
    Val.has_type v1 (mreg_type rhi) ->
    Val.has_type v2 (mreg_type rlo) ->
    Val.has_type (Val.combine v1 v2) (mreg_pair_type (Two rhi rlo)).
Proof.
  intros. assert (mreg_pair_type (Two rhi rlo) = Tany64) by (destruct rhi, rlo; auto).
  rewrite H1. destruct (Val.combine v1 v2); exact I.
Qed.

Open Scope positive_scope.

Module IndexedMreg <: INDEXED_TYPE.
  Definition t := mreg.
  Definition eq := mreg_eq.
  Definition index (r: mreg): positive :=
    match r with
    | R0 => 1  | R1 => 2  | R2 => 3  | R3 => 4
    | R4 => 5  | R5 => 6  | R6 => 7  | R7 => 8
    | R8 => 9  | R9 => 10 | R10 => 11 | R11 => 12
    | R12 => 13
    | F0 => 14  | F1 => 15  | F2 => 16  | F3 => 17
    | F4 => 18  | F5 => 19  | F6 => 20  | F7 => 21
    | F8 => 22  | F9 => 23  | F10 => 24 | F11 => 25
    | F12 => 26 | F13 => 27 | F14 => 28 | F15 => 29
    | F16 => 30 | F17 => 31 | F18 => 32 | F19 => 33
    | F20 => 34 | F21 => 35 | F22 => 36 | F23 => 37
    | F24 => 38 | F25 => 39 | F26 => 40 | F27 => 41
    | F28 => 42 | F29 => 43 | F30 => 44 | F31 => 45
    | D0 => 46  | D1 => 47  | D2 => 48  | D3 => 49
    | D4 => 50  | D5 => 51  | D6 => 52  | D7 => 53
    | D8 => 54  | D9 => 55  | D10 => 56 | D11 => 57
    | D12 => 58 | D13 => 59 | D14 => 60 | D15 => 61
    | ErrorReg => 62
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
  ("R0", R0)   :: ("R1", R1)   :: ("R2", R2)   :: ("R3", R3)   ::
  ("R4", R4)   :: ("R5", R5)   :: ("R6", R6)   :: ("R7", R7)   ::
  ("R8", R8)   :: ("R9", R9)   :: ("R10", R10) :: ("R11", R11) ::
  ("R12", R12) ::
  ("S0", F0)   :: ("S1", F1)   :: ("S2", F2)   :: ("S3", F3)   ::
  ("S4", F4)   :: ("S5", F5)   :: ("S6", F6)   :: ("S7", F7)   ::
  ("S8", F8)   :: ("S9", F9)   :: ("S10", F10) :: ("S11", F11) ::
  ("S12", F12) :: ("S13", F13) :: ("S14", F14) :: ("S15", F15) ::
  ("S16", F16) :: ("S17", F17) :: ("S18", F18) :: ("S19", F19) ::
  ("S20", F20) :: ("S21", F21) :: ("S22", F22) :: ("S23", F23) ::
  ("S24", F24) :: ("S25", F25) :: ("S26", F26) :: ("S27", F27) ::
  ("S28", F28) :: ("S29", F29) :: ("S30", F30) :: ("S31", F31) ::
  ("D0", D0)   :: ("D1", D1)   :: ("D2", D2)   :: ("D3", D3)   ::
  ("D4", D4)   :: ("D5", D5)   :: ("D6", D6)   :: ("D7", D7)   ::
  ("D8", D8)   :: ("D9", D9)   :: ("D10", D10) :: ("D11", D11) ::
  ("D12", D12) :: ("D13", D13) :: ("D14", D14) :: ("D15", D15) :: nil.
(*- #End *)


(*- E_COMPCERT_FTR_Function_Machregs_expand_register_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_EXTENDED_ASM_003 *)
Definition expand_register (mr: mreg): rpair mreg :=
  match mr with
  | D0 => Two F1 F0
  | D1 => Two F3 F2
  | D2 => Two F5 F4
  | D3 => Two F7 F6
  | D4 => Two F9 F8
  | D5 => Two F11 F10
  | D6 => Two F13 F12
  | D7 => Two F15 F14
  | D8 => Two F17 F16
  | D9 => Two F19 F18
  | D10 => Two F21 F20
  | D11 => Two F23 F22
  | D12 => Two F25 F24
  | D13 => Two F27 F26
  | D14 => Two F29 F28
  | D15 => Two F31 F30
  | mr => One mr
  end.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Machregs_register_by_name_001 *)
(*- #Justify_Derived "Auxiliary function" *)
Definition register_by_name (s: string) : option (rpair mreg) :=
  let fix assoc (l: list (string * mreg)) : option (rpair mreg) :=
    match l with
    | nil => None
    | (s1, r1) :: l' => if string_dec s s1 then Some (expand_register r1) else assoc l'
    end
  in assoc register_names.
(*- #End *)

(** ** Destroyed registers, preferred registers *)

(*- E_COMPCERT_FTR_Function_Machregs_destroyed_by_op_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Definition destroyed_by_op (op: operation): list mreg :=
  match op with
  | Odiv | Odivu =>
             if Archi.hardware_idiv tt then
              nil
             else
              R0 :: R1 :: R2 :: R3 :: R12 :: F0  :: F1  :: F2  :: F3  :: F4  :: F5
                 :: F6 :: F7 :: F8 :: F9  :: F10 :: F11 :: F12 :: F13 :: F14 :: F15 :: nil
  | Ointoffloat | Ointuoffloat | Ointofsingle | Ointuofsingle => F12 :: nil
  | _ => nil
  end.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Machregs_destroyed_by_load_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Definition destroyed_by_load (chunk: memory_chunk) (addr: addressing): list mreg :=
  nil.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Machregs_destroyed_by_store_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Definition destroyed_by_store (chunk: memory_chunk) (addr: addressing): list mreg := nil.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Machregs_destroyed_by_cond_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Definition destroyed_by_cond (cond: condition): list mreg :=
  nil.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Machregs_destroyed_by_jumptable_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Definition destroyed_by_jumptable: list mreg :=
  nil.
(*- #End *)


(*- E_COMPCERT_FTR_Function_Machregs_destroyed_by_clobber_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_EXTENDED_ASM_003 *)
Fixpoint destroyed_by_clobber (cl: list string): list mreg :=
  match cl with
  | nil => nil
  | c1 :: cl =>
      match register_by_name c1 with
      | Some r =>
          match r with
          | One r => r :: destroyed_by_clobber cl
          | Two r1 r2 => r1 :: r2 :: destroyed_by_clobber cl
          end
      | None   => destroyed_by_clobber cl
      end
  end.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Machregs_destroyed_by_builtin_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_MULTIPLICATIVE_OPERATORS_005 *)
Definition destroyed_by_builtin (ef: external_function): list mreg :=
  match ef with
  | EF_memcpy sz al => R2 :: R3 :: R12 :: F14 :: F15 :: nil
  | EF_inline_asm txt sg clob => destroyed_by_clobber clob
  | EF_builtin id sg =>
      if string_dec id "__builtin_udivl" then
        R0 :: R1 :: R2 :: R3 :: R4 :: R5 :: R6 :: R7 :: R8  :: nil
      else
        nil
  | _ => nil
  end.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Machregs_destroyed_by_setstack_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Definition destroyed_by_setstack (ty: typ): list mreg := nil.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Machregs_destroyed_at_function_entry_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Definition destroyed_at_function_entry: list mreg :=
  R12 :: nil.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Machregs_destroyed_at_indirect_call_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Definition destroyed_at_indirect_call: list mreg :=
  R0 :: R1 :: R2 :: R3 :: nil.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Machregs_temp_for_parent_frame_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Definition temp_for_parent_frame: mreg :=
  R12.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Machregs_mregs_for_operation_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Definition mregs_for_operation (op: operation): list (option (rpair mreg)) * option (rpair mreg) :=
  match op with
  | Odiv | Odivu => if Archi.hardware_idiv tt then (nil, None) else (Some (One R0) :: Some (One R1) :: nil, Some (One R0))
  | _ => (nil, None)
  end.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Machregs_mregs_for_builtin_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_MULTIPLICATIVE_OPERATORS_005 *)
Definition mregs_for_builtin (ef: external_function): list (option mreg) * list(option mreg) :=
  match ef with
  | EF_builtin id sg =>
      if string_dec id "__builtin_udivl" then
         (Some R0 :: Some R1 :: Some R2 :: Some R3 :: nil, Some R4 :: Some R5 :: nil)
      else
        (nil, nil)
  | _ => (nil, nil)
  end.
(*- #End *)

Global Opaque
    destroyed_by_op destroyed_by_load destroyed_by_store
    destroyed_by_cond destroyed_by_jumptable destroyed_by_builtin
    destroyed_by_setstack destroyed_at_function_entry temp_for_parent_frame
    destroyed_at_indirect_call
    mregs_for_operation mregs_for_builtin.

(** Two-address operations.  Return [true] if the first argument and
  the result must be in the same location *and* are unconstrained
  by [mregs_for_operation].  There are none for ARM. *)

(*- E_COMPCERT_FTR_Function_Machregs_two_address_op_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Definition two_address_op (op: operation) : bool :=
  false.
(*- #End *)

Global Opaque two_address_op.

(* Constraints on constant propagation for builtins *)

Definition builtin_constraints (ef: external_function) :
                                       list builtin_arg_constraint :=
  match ef with
  | EF_vload _ => OK_addressing :: nil
  | EF_vstore _ => OK_addressing :: OK_default :: nil
  | EF_memcpy _ _ => OK_addrstack :: OK_addrstack :: nil
  | EF_annot kind txt targs => map (fun _ => OK_all) targs
  | EF_debug kind txt targs => map (fun _ => OK_all) targs
  | _ => nil
  end.
