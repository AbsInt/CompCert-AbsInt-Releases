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


From Coq Require Import String.
Require Import Coqlib.
Require Import Decidableplus.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Op.
Require Import Values.

(** ** Machine registers *)

(** Not allocatable registers:
    - P0, P1, P8, P9 are global address registers defiend by the ABI and should not be used in programs.
    - P3 is designated as TMPA.
    - R0 is designated as TMP. *)

Inductive mreg: Type :=
  (** Allocatable address registers *)
  | P2: mreg  | P4: mreg  | P5:mreg   | P6:  mreg
  | P7: mreg  | P12: mreg | P13: mreg | P14: mreg
  | P15: mreg
  (** Allocatable integer regs *)
  | R1: mreg  | R2: mreg  | R3: mreg  | R4:mreg
  | R5: mreg  | R6: mreg  | R7: mreg  | R8:mreg
  | R9: mreg  | R10: mreg | R11: mreg | R12:mreg
  | R13: mreg | R14: mreg | R15: mreg | ErrorReg: mreg.

Lemma mreg_eq: forall (r1 r2: mreg), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.
Global Opaque mreg_eq.

Definition all_mregs :=
     P2  :: P4  :: P5  :: P6  :: P7  :: P12 :: P13 :: P14 :: P15
  :: R1  :: R2  :: R3  :: R4  :: R5  :: R6  :: R7  :: R8  :: R9  :: R10
  :: R11 :: R12 :: R13 :: R14 :: R15 :: ErrorReg :: nil.

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
  | P2  | P4  | P5  | P6  | P7  | P12 | P13 | P14 | P15
  | R1  | R2  | R3  | R4  | R5  | R6  | R7  | R8  | R9
  | R10 | R11 | R12 | R13 | R14 | R15 => Tany32
  | ErrorReg => Tany64
  end.

Definition mreg_pair_type (p: rpair mreg): typ :=
  match p with
  | One r => mreg_type r
  | _ => Tany64 (* Should not be used *)
  end.

Lemma pair_words_type:
  forall rlo rhi v,
    Val.has_type v (mreg_pair_type (Two rhi rlo)) ->
    Val.has_type (Val.hiword v) (mreg_type rhi)
    /\ Val.has_type (Val.loword v) (mreg_type rlo).
Proof.
  simpl. intros. split.
  destruct v; auto; destruct rhi; simpl; destruct Archi.ptr64; easy.
  destruct v; auto; destruct rlo; simpl; destruct Archi.ptr64; easy.
Qed.

Lemma words_pair_type:
  forall rlo rhi v1 v2,
    Val.has_type v1 (mreg_type rhi) ->
    Val.has_type v2 (mreg_type rlo) ->
    Val.has_type (Val.combine v1 v2) (mreg_pair_type (Two rhi rlo)).
Proof.
  intros. destruct rhi, rlo; simpl; destruct (Val.combine v1 v2); exact I.
Qed.

Remark mreg_type_no_err:
  forall r, r <> ErrorReg -> mreg_type r = Tany32.
Proof.
  intros. destruct r; simpl; congruence.
Qed.

Open Scope positive_scope.

Module IndexedMreg <: INDEXED_TYPE.
  Definition t := mreg.
  Definition eq := mreg_eq.
  Definition index (r: mreg): positive :=
    match r with
    | P2 => 1   | P4 => 2   | P5 => 3   | P6 => 4
    | P7 => 5   | P12 => 6  | P13 => 7  | P14 => 8
    | P15 => 9  | R1 => 10  | R2 => 11  | R3 => 12
    | R4 => 13  | R5 => 14  | R6 => 15  | R7 => 16
    | R8 => 17  | R9 => 18  | R10 => 19 | R11 => 20
    | R12 => 21 | R13 => 22 | R14 => 23 | R15 => 24
    | ErrorReg => 25
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

Definition register_names :=
  ("A2", P2)   :: ("A4", P4)   :: ("A5", P5)   :: ("A6", P6)   :: ("A7", P7)   :: 
  ("A12", P12) :: ("A13", P13) :: ("A14", P14) :: ("A15",P15)  ::
  ("D1", R1)   :: ("D2", R2)   :: ("D3", R3)   :: ("D4", R4)   :: ("D5", R5)   ::
  ("D6", R6)   :: ("D7", R7)   :: ("D8", R8)   :: ("D9", R9)   :: ("D10", R10) ::
  ("D11", R11) :: ("D12", R12) :: ("D13", R13) :: ("D14", R14) :: ("D15", R15) :: nil.

Definition register_by_name (s: string) : option (rpair mreg) :=
  let fix assoc (l: list (string * mreg)) : option (rpair mreg) :=
    match l with
    | nil => None
    | (s1, r1) :: l' => if string_dec s s1 then Some (One r1) else assoc l'
    end
  in assoc register_names.

(** ** Destroyed registers, preferred registers *)

Definition destroyed_by_cond (cond: condition): list mreg := nil.

Definition destroyed_by_op (op: operation): list mreg :=
  match op with
  | Ocmp c => destroyed_by_cond c
  | Odiv => R4 :: R5 :: nil
  | Odivu => R4 :: R5 :: nil
  | Omod => R4 :: R5 :: nil
  | Omodu => R4 :: R5 :: nil
  | Omulhs => R4 :: R5 :: nil
  | Omulhu => R4 :: R5 :: nil
  | _ => nil
  end.

Definition destroyed_by_load (chunk: memory_chunk) (addr: addressing): list mreg := nil.

Definition destroyed_by_store (chunk: memory_chunk) (addr: addressing): list mreg := nil.

Definition destroyed_by_jumptable: list mreg := nil.

Fixpoint destroyed_by_clobber (cl: list string): list mreg :=
  match cl with
  | nil => nil
  | c1 :: cl =>
      match register_by_name c1 with
      | Some (One r) => r :: destroyed_by_clobber cl
      | Some (Two r1 r2) => r1 :: r2 :: destroyed_by_clobber cl
      | None   => destroyed_by_clobber cl
      end
  end.

Definition destroyed_by_builtin (ef: external_function): list mreg :=
  match ef with
  | EF_inline_asm txt sg clob => destroyed_by_clobber clob
  | EF_memcpy _ _ => P12 :: P13 :: nil
  | EF_builtin id sg =>
      if string_dec id "__builtin_va_start" then P13 :: nil
      else nil
  | _ => nil
  end.

Definition destroyed_by_setstack (ty: typ): list mreg := nil.

Definition destroyed_at_function_entry: list mreg := P12 :: nil.

Definition destroyed_at_indirect_call: list mreg := nil.

Definition temp_for_parent_frame: mreg := P12.

Definition mregs_for_operation (op: operation): list (option (rpair mreg)) * option (rpair mreg) :=
  match op with
  | Odiv => (None :: None :: nil, Some (One R4))
  | Odivu => (None :: None :: nil, Some (One R4))
  | Omod => (None :: None :: nil, Some (One R5))
  | Omodu => (None :: None :: nil, Some (One R5))
  | Omulhs => (None :: None :: nil, Some (One R5))
  | Omulhu => (None :: None :: nil, Some (One R5))
  | Omulu => (None :: None :: nil, Some (Two R5 R4))
  | _ => (nil, None)
  end.

Definition mregs_for_builtin (ef: external_function): list (option mreg) * list (option mreg) :=
  match ef with
  | _ => (nil, nil)
  end.

Global Opaque
    destroyed_by_op destroyed_by_load destroyed_by_store
    destroyed_by_cond destroyed_by_jumptable destroyed_by_builtin
    destroyed_by_setstack destroyed_at_function_entry temp_for_parent_frame
    destroyed_at_indirect_call
    mregs_for_operation mregs_for_builtin.

(** Two-address operations.  Return [true] if the first argument and
  the result must be in the same location *and* are unconstrained
  by [mregs_for_operation].  There is one for AArch64: [Olowlong],
  which is actually a no-operation in the generated asm code. *)

Definition two_address_op (op: operation) : bool := false.

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
