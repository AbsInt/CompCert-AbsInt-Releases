(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*             AbsInt Angewandte Informatik GmbH                       *)
(*                                                                     *)
(*  AbsInt Angewandte Informatik GmbH. All rights reserved. This file  *)
(*  is distributed under the terms of the INRIA Non-Commercial         *)
(*  License Agreement.                                                 *)
(*                                                                     *)
(* *********************************************************************)

(** Add explicit pointer cast operations whenever a register is used as an address register.
 This prevents problems during type inference as results of pointer computations might otherwise be treated as ints.*)

Require Import Coqlib Maps Errors Integers.
Require Import AST.
Require Import Op Registers RTL.

(** State monad *)

(** To construct the revised program including pointer casts,
  we use a state monad similar to that used in module [RTLgen].
  It records the current state of the CFG, plus counters to generate
  fresh pseudo-registers and fresh CFG nodes. *)

Record state : Type := mkstate {
  st_nextreg: positive;                 (**r last used pseudo-register *)
  st_nextnode: positive;                (**r last used CFG node *)
  st_code: code;                        (**r current CFG  *)
                         }.

(** Monotone evolution of the state. *)

(* Unlike in RTLgen we do not require that future states do not change
   existing instructions because we specifically want to change
   existing instructions *)
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

Definition initstate :=
  mkstate 1%positive 1%positive (PTree.empty instruction).

(** Replaces memory instructions with pcasts + memory instruction using the new register *)
Definition add_pcast (pc: node) (i: instruction) : mon unit :=
  match i with
  | Iload chunk (Aindexed i) args dst s =>
      do r <- new_reg;
      do n1 <- add_instr (Iload chunk (Aindexed i) (r :: nil) dst s);
      set_instr pc (Iop Opcast args r n1)
  | Istore chunk (Aindexed i) args src s =>
      do r <- new_reg;
      do n1 <- add_instr (Istore chunk (Aindexed i) (r :: nil) src s);
      set_instr pc (Iop Opcast args r n1)
  | Icall sig ros args dst s =>
      (* Function calls do not rely on their arguments having the correct type.
         This means we would have to show that a function call with arguments
         of the wrong type still gets translated correctly. Because the
         pointer casts return Undefined if the arguments have a wrong type,
         we cannot do this if we insert pointer casts for function arguments
         before the call. Hence we do not add casts before function calls.
         When typing this requires us to type function calls as typ and
         not as argtype. As before, in the called function arguments are
         treated as if they had the argument type. Hence from the
         perspective of a called function nothing changes. In effect
         a function call acts like a pointer cast for arguments of pointer
         type in itself. *)
      match ros with
      | inl r =>
          do r' <- new_reg;
          let ros' := inl r' in
          do n <- add_instr (Icall sig ros' args dst s);
          set_instr pc (Iop Opcast (r::nil) r' n)
      | inr name =>
          let ros' := inr name in
          do n <- add_instr (Icall sig ros' args dst s);
          set_instr pc (Inop n)
      end
  | Itailcall sig ros args =>
      (* Same applies as for normal calls *)
      match ros with
      | inl r =>
          do r' <- new_reg;
          let ros' := inl r' in
          do n <- add_instr (Itailcall sig ros' args);
          set_instr pc (Iop Opcast (r::nil) r' n)
      | inr name =>
          let ros' := inr name in
          do n <- add_instr (Itailcall sig ros' args);
          set_instr pc (Inop n)
      end
  | _ => set_instr pc i
  end.

Definition function_state (f:function) : state :=
  mkstate (Pos.succ (max_reg_function f)) (Pos.succ (max_pc_function f)) (fn_code f).
  
Definition add_pcasts (f: function) : mon unit :=
  ptree_mfold add_pcast (f.(fn_code)).


Definition transf_function  (f: function) : function :=
  let '(R _ s _) := add_pcasts f (function_state f) in
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
