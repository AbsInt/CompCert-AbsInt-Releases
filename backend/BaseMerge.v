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

(** Simplfied constant propagation just to perform strength reduction for
    extracted base address *)

Require Import Coqlib Maps Integers Floats Lattice Kildall.
Require Import AST Linking Builtins.
Require Compopts Machregs.
Require Import Op Registers RTL.
Require Import Liveness ValueDomain ValueAOp ValueAnalysis.
Require Import ConstpropOp BaseExtraction.

Definition usage_map := PTree.t Nat.t.

Definition usage_count (mp : usage_map) (r: reg) : Nat.t :=
  match PTree.get r mp with
  | Some cnt => cnt
  | None => 0%nat
  end.

Definition used (mp: usage_map) (r: reg) :=
  PTree.set r (Nat.succ (usage_count mp r)) mp.

Definition count_usage (mp: usage_map) (nid: ident) (instr: instruction) :=
  match instr with
  | Iload chunk (Aindexed n as addr) (r :: nil as args) dst s => used mp r
  | Istore chunk (Aindexed n as addr) (r :: nil as args) src s => used mp r
  | _ => mp
  end.

(** We additionally count any other usages of the Address registers,
    if they are used in a call, operation or built-in we must compute
    them anyway, so we should increase the usage counter in such a way
    that we avoid the simplification *)
Definition increase (mp: usage_map) (r: reg) :=
  match PTree.get r mp with
  | None => mp
  | Some rc => PTree.set r (Nat.add rc minimal_usage) mp
  end.

Definition builtin_arg_usage (mp: usage_map) (a: builtin_arg reg) :=
  match a with
  | BA r => increase mp r
  | _ => mp
  end.

Definition count_other_usage (mp: usage_map) (nid: ident) (instr: instruction) :=
  match instr with
  | Iop op args dst s =>
      List.fold_left increase args mp
  | Icall sig f args dst s =>
      List.fold_left increase args mp
  | Itailcall sig f args =>
      List.fold_left increase args mp
  | Ibuiltin ef args res s =>
      match ef with
      | EF_debug _ _ _ => mp
       | _ =>
           List.fold_left builtin_arg_usage args mp
      end
  | _ => mp
  end.


Definition usage_analysis (f: function) : usage_map :=
  let load_vars := PTree.fold count_usage f.(fn_code) (PTree.empty Nat.t) in
  PTree.fold count_other_usage f.(fn_code) load_vars.

Definition should_reduce (mp: usage_map) addr args :=
  match addr, args with
  | Aindexed n, r :: nil =>
      Nat.leb (usage_count mp r) minimal_usage
  | _, _ => true
  end.

Definition transf_instr (f: function) (an: PMap.t VA.t) (mp: usage_map) (rm: romem)
                        (pc: node) (instr: instruction) :=
  match an!!pc with
  | VA.Bot =>
      instr
  | VA.State ae am =>
      match instr with
      | Iload chunk addr args dst s =>
          if should_reduce mp addr args then
            let aargs := aregs ae args in
            let a := ValueDomain.loadv chunk rm am (eval_static_addressing addr aargs) in
            match const_for_result a with
            | Some cop =>
                Iop cop nil dst s
            | None =>
                let (addr', args') := addr_strength_reduction addr args aargs in
                Iload chunk addr' args' dst s
            end
          else
        instr
      | Istore chunk addr args src s =>
          if should_reduce mp addr args then
            let aargs := aregs ae args in
            let (addr', args') := addr_strength_reduction addr args aargs in
            Istore chunk addr' args' src s
          else
        instr
      | _ =>
          instr
      end
  end.

Definition transf_function (rm: romem) (f: function) : function :=
  let an := ValueAnalysis.analyze rm f in
  let mp := usage_analysis f in
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    (PTree.map (transf_instr f an mp rm) f.(fn_code))
    f.(fn_entrypoint).

Definition transf_fundef (rm: romem) (fd: fundef) : fundef :=
  AST.transf_fundef (transf_function rm) fd.

Definition transf_program (p: program) : program :=
  let rm := romem_for p in
  transform_program (transf_fundef rm) p.
