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


Require Import String.
Require Import Coqlib.
Require Import Decidableplus.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Op.

(** ** Machine registers *)

(** The following type defines the machine registers that can be referenced
  as locations.  These include:
- General purpose registers that can be allocated to RTL pseudo-registers ([Rxx]).

  The type [mreg] does not include reserved machine registers such as
  the stack pointer (reg0). Finally, register (reg1) is reserved for
  use as a temporary by the assembly-code generator [Asmgen].

  [ErrorR1] is dummy register for double values, currently we don't
  have any 64bit register and double is not supported at all so they should
  never be used at all.
*)

Inductive mreg: Type :=
  (** Allocatable general purpose registers *)
  | R2:  mreg | R3:  mreg | R4:  mreg | R5:  mreg
  | R6:  mreg | R7:  mreg | R8:  mreg | R9:  mreg
  | R10: mreg | R11: mreg | R12: mreg | R13: mreg
  | R14: mreg | R15: mreg | R16: mreg | R17: mreg
  | R18: mreg | R19: mreg | R20: mreg | R21: mreg
  | R22: mreg | R23: mreg | R24: mreg | R25: mreg
  | R26: mreg | R27: mreg | R28: mreg | R29: mreg
  | R30: mreg | R31: mreg
  (** Dummy dobule regsiter *)
  | ErrorReg: mreg.

Lemma mreg_eq: forall (r1 r2: mreg), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.
Global Opaque mreg_eq.

Definition all_mregs :=
    R2  :: R3  :: R4  :: R5  :: R6  :: R7  :: R8  :: R9
  :: R10 :: R11 :: R12 :: R13 :: R14 :: R15 :: R16 :: R17
  :: R18 :: R19 :: R20 :: R21 :: R22 :: R23 :: R24 :: R25
  :: R26 :: R27 :: R28 :: R29 :: R30 :: R31
  :: ErrorReg  :: nil.

Lemma all_mregs_complete:
  forall (r: mreg), In r all_mregs.
Proof.
  assert (forall r, proj_sumbool (In_dec mreg_eq r all_mregs) = true) by (destruct r; reflexivity).
  intros. specialize (H r). InvBooleans. auto.
Qed.

Instance Decidable_eq_mreg : forall (x y: mreg), Decidable (eq x y) := Decidable_eq mreg_eq.

Instance Finite_mreg : Finite mreg := {
  Finite_elements := all_mregs;
  Finite_elements_spec := all_mregs_complete
}.

Definition mreg_type (r: mreg): typ :=
  match r with
  | ErrorReg => Tany64
  | _ => Tany32
  end.

Open Scope positive_scope.

Module IndexedMreg <: INDEXED_TYPE.
  Definition t := mreg.
  Definition eq := mreg_eq.
  Definition index (r: mreg): positive :=
    match r with
    | R2  => 1   | R3  => 2   | R4  => 3
    | R5  => 4   | R6  => 5   | R7  => 6
    | R8  => 7   | R9  => 8   | R10 => 9
    | R11 => 10  | R12 => 11  | R13 => 12
    | R14 => 13  | R15 => 14  | R16 => 15
    | R17 => 16  | R18 => 17  | R19 => 18
    | R20 => 19  | R21 => 20  | R22 => 21
    | R23 => 22  | R24 => 23  | R25 => 24
    | R26 => 25  | R27 => 26  | R28 => 27
    | R29 => 28  | R30 => 29  | R31 => 30
    | ErrorReg => 31
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
                                    ("reg2", R2)   :: ("reg3",  R3)  ::
  ("reg4",  R4)  :: ("reg5",  R5)  :: ("reg6",  R6)  :: ("reg7",  R7)  ::
  ("reg8",  R8)  :: ("reg9",  R9)  :: ("reg10", R10) :: ("reg11", R11) ::
  ("reg12", R12) :: ("reg13", R13) :: ("reg14", R14) :: ("reg15", R15) ::
  ("reg16", R16) :: ("reg17", R17) :: ("reg18", R18) :: ("reg19", R19) ::
  ("reg20", R20) :: ("reg21", R21) :: ("reg22", R22) :: ("reg23", R23)  ::
  ("reg24", R24) :: ("reg25", R25) :: ("reg26", R26) :: ("reg27", R27) ::
  ("reg28", R28) :: ("reg29", R29) :: ("reg30", R30) :: ("reg31", R31) ::
  nil.

Definition register_by_name (s: string) : option mreg :=
  let fix assoc (l: list (string * mreg)) : option mreg :=
    match l with
    | nil => None
    | (s1, r1) :: l' => if string_dec s s1 then Some r1 else assoc l'
    end
  in assoc register_names.

(** ** Destroyed registers, preferred registers *)

Definition destroyed_by_cond (cond: condition): list mreg := R3 :: R4 :: R5 :: R6 :: nil.

Definition destroyed_by_op (op: operation): list mreg :=
  match op with
  | Omul => R3 :: R4 :: nil
  | Omulimm _ => R3 :: R4 :: nil
  | Omulhs => R3 :: R4 :: nil
  | Omulhu => R3 :: R4 :: nil
  | Odiv => R3 :: R4 :: nil
  | Odivu => R3 :: R4 :: nil
  | Omod => R3 :: R4 :: nil
  | Omodu => R3 :: R4 :: nil
  | Omadd => R3 :: R4 :: nil
  | Omsub => R3 :: R4 :: nil
  | Ocmp c => destroyed_by_cond c
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
      | Some r => r :: destroyed_by_clobber cl
      | None   => destroyed_by_clobber cl
      end
  end.

Definition destroyed_by_builtin (ef: external_function): list mreg :=
  match ef with
  | EF_inline_asm txt sg clob => destroyed_by_clobber clob
  | EF_memcpy sz al => R2 :: R3 :: R4 :: nil
  | EF_builtin name sg =>
     if string_dec name "__builtin_clz"
     || string_dec name "__builtin_clzl"
     || string_dec name "__builtin_ctz"
     || string_dec name "__builtin_ctzl" then
       R3 :: nil
     else if string_dec name "__builtin_clzll"
     || string_dec name "__builtin_ctzll" then
       R3 :: R4 :: nil
     else if string_dec name "__builtin_addl"
      || string_dec name "__builtin_negl"
      || string_dec name "__builtin_subl" then
       R7 :: nil
     else
       nil
  | _ => nil
  end.

Definition destroyed_by_setstack (ty: typ): list mreg := nil.

Definition destroyed_at_function_entry: list mreg := R2 :: nil.

Definition temp_for_parent_frame: mreg := R2.

Definition destroyed_at_indirect_call: list mreg := nil.

Definition mregs_for_operation (op: operation): list (option mreg) * option mreg :=
  match op with
  | Omul => (Some R3 :: None :: nil, Some R3)
  | Omulimm _ => (None :: None :: nil, Some R3)
  | Omulhs => (Some R3 :: None :: nil, Some R3)
  | Omulhu => (Some R3 :: None :: nil, Some R3)
  | Odiv => (Some R3 :: None :: nil, Some R3)
  | Odivu => (Some R3 :: None :: nil, Some R3)
  | Omod => (Some R3 :: None :: nil, Some R3)
  | Omodu => (Some R3 :: None :: nil, Some R3)
  | Omadd => (Some R3 :: None :: None :: nil, Some R3)
  | Omsub => (Some R3 :: None :: None :: nil, Some R3)
  | _ => (nil, None)
  end.

Definition mregs_for_builtin (ef: external_function): list (option mreg) * list(option mreg) :=
  match ef with
  | EF_builtin name sg =>
    if string_dec name "__builtin_negl" then
      (Some R5 :: Some R6 :: nil, Some R3 :: Some R4 :: nil)
    else if string_dec name "__builtin_addl" then
      (Some R3 :: Some R4 :: Some R5 :: Some R6 :: nil, Some R3 :: Some R4 :: nil)
    else if string_dec name "__builtin_subl" then
      (Some R3 :: Some R4 :: Some R5 :: Some R6 :: nil, Some R3 :: Some R4 :: nil)
    else if string_dec name "__builtin_mull" then
           (Some R3 :: Some R4 :: nil, Some R4 :: Some R3 :: nil)
    else if string_dec name "__builtin_clz"
         || string_dec name "__builtin_clzl"
         || string_dec name "__builtin_ctz"
         || string_dec name "__builtin_ctzl" then
           (Some R3 :: nil, Some R4 :: nil)
    else if string_dec name "__builtin_clzll"
         || string_dec name "__builtin_ctzll" then
           (Some R3 :: Some R4 :: nil, Some R5 :: nil)
    else
      (nil, nil)
  | _ =>  (nil, nil)
  end.

Global Opaque
    destroyed_by_op destroyed_by_load destroyed_by_store
    destroyed_by_cond destroyed_by_jumptable destroyed_by_builtin
    destroyed_by_setstack destroyed_at_function_entry temp_for_parent_frame
    mregs_for_operation mregs_for_builtin.

(** Two-address operations.  Return [true] if the first argument and
  the result must be in the same location *and* are unconstrained
  by [mregs_for_operation]. *)

Definition two_address_op (op: operation) : bool :=
  match op with
  | Omove => false
  | Ointconst _ => false
  | Ofloatconst _ => false
  | Osingleconst _ => false
  | Osingleofint => false
  | Osingleofintu => false
  | Ointofsingle => false
  | Ointuofsingle => false
  | Oaddrsymbol _ _ => false
  | Oaddrstack _ => false
  | Ocast8signed => false
  | Ocast16signed => false
  | Ocmp c => false
  | _ => true
  end.

(** Constraints on constant propagation for builtins *)

Definition builtin_constraints (ef: external_function) :
                                       list builtin_arg_constraint :=
  match ef with
  | EF_builtin id sg => nil
  | EF_vload _ => OK_addressing :: nil
  | EF_vstore _ => OK_addressing :: OK_default :: nil
  | EF_memcpy _ _ => OK_addrstack :: OK_addrstack :: nil
  | EF_annot kind txt targs => map (fun _ => OK_all) targs
  | EF_debug kind txt targs => map (fun _ => OK_all) targs
  | _ => nil
  end.
