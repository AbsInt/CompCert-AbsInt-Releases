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

(** Extracting common base symbols from load/store operatios *)

Require Import Coqlib Wfsimpl Maps Errors Integers.
Require Import AST Linking.
Require Import Op Registers RTL.

(** We don't want to extract small data access, since they are already just one
    instruction *)

Parameter is_small_data_symbol: ident -> ptrofs -> bool.

(** Simple analysis for base extraction, we count how often a symbol is used in
    load/store operations *)

Definition symbol_map  :=  PTree.t Nat.t.

Definition symbol_count (s: symbol_map) (id: ident) :=
  match PTree.get id s with
  | Some cnt => cnt
  | None => 0%nat
  end.

Definition used (s: symbol_map) (addr: option (ident * ptrofs)) :=
  match addr with
  | Some (id, _) => PTree.set id (Nat.succ (symbol_count s id)) s
  | None  => s
  end.

Definition count_inst (s: symbol_map) (nid: ident) (instr: instruction) :=
  match instr with
  | Iload _ addr _ _ _ => used s (symbol_addressing addr)
  | Istore _ addr _ _ _ => used s (symbol_addressing addr)
  | _ => s
  end.

Definition extract_analysis (f: function) : symbol_map :=
  PTree.fold count_inst f.(fn_code) (PTree.empty Nat.t).

(* The minimal number of usages of an address before we want to extract it.
   Currently we should only extract if the address is used more than 3 times,
   since then we produce less instructions per access. For 2 it would be the
   same number of instructions but one additional register used. *)
Definition minimal_usage := 3%nat.

Inductive extract_decision (addr: addressing) (args: list reg) :=
  | Cannot_extract
  | Can_extract (id: ident) (ofs: ptrofs) (P: Some (id, ofs) = symbol_addressing addr) (Q: args = nil).

Definition should_extract s id ofs :=
  andb (negb (is_small_data_symbol id ofs))
  (Nat.leb minimal_usage (symbol_count s id)).

Arguments Cannot_extract {addr args}.
Arguments Can_extract {addr args}.

Program Definition can_extract
  (io: symbol_map) (addr: addressing) (args: list reg) : extract_decision addr args :=
  match symbol_addressing addr, args with
  | Some (symb, ofs), nil =>
    if should_extract io symb ofs then
      Can_extract  symb ofs _ _
    else
      Cannot_extract
  | _, _ => Cannot_extract
  end.

(** State monad *)

(** To construct incrementally the CFG of a function after inlining,
  we use a state monad similar to that used in module [RTLgen].
  It records the current state of the CFG, plus counters to generate
  fresh pseudo-registers and fresh CFG nodes.  It also records the
  stack size needed for the inlined function. *)

Record state : Type := mkstate {
  st_nextreg: positive;                 (**r next fresh pseudo-register *)
  st_nextnode: positive;                (**r next fresh CFG node *)
  st_code: code;                        (**r current CFG  *)
}.

(** Monotone evolution of the state. *)

Inductive sincr (s1 s2: state) : Prop :=
  Sincr (NEXTREG: Ple s1.(st_nextreg) s2.(st_nextreg))
        (NEXTNODE: Ple s1.(st_nextnode) s2.(st_nextnode)).

Remark sincr_refl: forall s, sincr s s.
Proof.
  intros; constructor; extlia.
Qed.

Lemma sincr_trans: forall s1 s2 s3, sincr s1 s2 -> sincr s2 s3 -> sincr s1 s3.
Proof.
  intros. inv H; inv H0. constructor; extlia.
Qed.

(** Dependently-typed state monad, ensuring that the final state is
  greater or equal (in the sense of predicate [sincr] above) than
  the initial state. *)

Inductive res {A: Type} {s: state}: Type := R (x: A) (s': state) (I: sincr s s').

Definition mon (A: Type) : Type := forall (s: state), @res A s.

(** Operations on this monad. *)

Definition ret {A: Type} (x: A): mon A :=
  fun s => R x s (sincr_refl s).

Definition bind {A B: Type} (x: mon A) (f: A -> mon B): mon B :=
  fun s1 => match x s1 with R vx s2 I1 =>
              match f vx s2 with R vy s3 I2 =>
                R vy s3 (sincr_trans s1 s2 s3 I1 I2)
              end
            end.

Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X name, A at level 100, B at level 200).

Definition initstate :=
  mkstate 1%positive 1%positive (PTree.empty instruction).

Program Definition set_instr (pc: node) (i: instruction): mon unit :=
  fun s =>
    R tt
      (mkstate s.(st_nextreg) s.(st_nextnode) (PTree.set pc i s.(st_code)))
      _.
Next Obligation.
  intros; constructor; simpl; extlia.
Qed.

Program Definition add_instr (i: instruction): mon node :=
  fun s =>
    let pc := s.(st_nextnode) in
    R pc
      (mkstate s.(st_nextreg) (Pos.succ pc) (PTree.set pc i s.(st_code)))
      _.
Next Obligation.
  intros; constructor; simpl; extlia.
Qed.

Program Definition reserve_nodes (numnodes: positive): mon unit :=
  fun s =>
    R tt
      (mkstate s.(st_nextreg) (Pos.add s.(st_nextnode) numnodes) s.(st_code))
      _.
Next Obligation.
  intros; constructor; simpl; extlia.
Qed.

Program Definition reserve_regs (numregs: positive): mon unit :=
  fun s =>
    R tt
      (mkstate (Pos.add s.(st_nextreg) numregs) s.(st_nextnode) s.(st_code))
      _.
Next Obligation.
  intros; constructor; simpl; extlia.
Qed.

Program Definition new_reg : mon reg :=
  fun s =>
    R s.(st_nextreg)
      (mkstate (Pos.succ s.(st_nextreg)) s.(st_nextnode) s.(st_code))
      _.
Next Obligation.
  intros; constructor; simpl; extlia.
Qed.

Program Definition ptree_mfold {A: Type} (f: positive -> A -> mon unit) (t: PTree.t A): mon unit :=
  fun s =>
    R tt
      (PTree.fold (fun s1 k v => match f k v s1 return _ with R _ s2 _ => s2 end) t s)
      _.
Next Obligation.
  apply PTree_Properties.fold_rec.
  auto.
  apply sincr_refl.
  intros. destruct (f k v a). eapply sincr_trans; eauto.
Qed.

(** Expansion and copying of an instruction. *)

Definition expand_instr (io: symbol_map) (pc: node) (i: instruction): mon unit :=
  match i with
  | Iload chunk addr args dst s =>
    match can_extract io addr args with
    | Cannot_extract => set_instr pc i
    | Can_extract id ofs P Q =>
      do r <- new_reg;
      do n1 <- add_instr (Iload chunk (aindexed_addr ofs) (r :: nil) dst s);
      set_instr pc (Iop (symbol_op id) nil r n1)
    end
  | Istore chunk addr args src s =>
    match can_extract io addr args with
    | Cannot_extract => set_instr pc i
    | Can_extract id ofs P Q =>
      do r <- new_reg;
      do n1 <- add_instr (Istore chunk (aindexed_addr ofs) (r :: nil) src s);
      set_instr pc (Iop (symbol_op id) nil r n1)
    end
  | _ => set_instr pc i
  end.


(** Start of the recursion: copy and inline function [f] in the
  initial context. *)

Definition expand_function (f: function): mon unit :=
  let npc := max_pc_function f in
  let nreg := max_reg_function f in
  do x <- reserve_nodes npc;
  do x <- reserve_regs nreg;
  let io := extract_analysis f in
  ptree_mfold (expand_instr io) f.(fn_code).


Definition transf_function  (f: function) : function :=
  let '(R _ s _) := expand_function f initstate in
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    s.(st_code)
    f.(fn_entrypoint).

Definition transf_fundef (f: fundef) : fundef :=
  AST.transf_fundef transf_function f.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.
