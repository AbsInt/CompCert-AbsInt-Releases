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

(** Typing rules and a type inference algorithm for RTL. *)

Require Import Coqlib.
Require Import Errors.
Require Import Subtyping.
Require Import Maps.
Require Import AST.
Require Import Op.
Require Import Registers.
Require Import Globalenvs.
Require Import Values.
Require Import Integers.
Require Import Memory.
Require Import Events.
Require Import Smallstep.
Require Import RTL.
Require Import Conventions.
Require Import Linking.


(** * The type system *)

(* a.d. TODO update description for ptype. *)
(** Like Cminor and all intermediate languages, RTL can be equipped with
  a simple type system that statically guarantees that operations
  and addressing modes are applied to the right number of arguments
  and that the arguments are of the correct types.   The type algebra
  is very simple, consisting of the four types [Tint] (for integers
  and pointers), [Tfloat] (for double-precision floats), [Tlong]
  (for 64-bit integers) and [Tsingle] (for single-precision floats).

  Additionally, we impose that each pseudo-register has the same type
  throughout the function.  This requirement helps with register allocation,
  enabling each pseudo-register to be mapped to a single hardware register
  or stack location of the correct type.

  Finally, we also check that the successors of instructions
  are valid, i.e. refer to non-empty nodes in the CFG.

  The typing judgement for instructions is of the form [wt_instr f env
  instr], where [f] is the current function (used to type-check
  [Ireturn] instructions) and [env] is a typing environment
  associating types to pseudo-registers.  Since pseudo-registers have
  unique types throughout the function, the typing environment does
  not change during type-checking of individual instructions.  One
  point to note is that we have one polymorphic operator, [Omove],
  which can work over both integers and floats.
*)

Definition regenv := reg -> ptype.

Section WT_INSTR.

Variable funct: function.
Variable env: regenv.

Definition valid_successor (s: node) : Prop :=
  exists i, funct.(fn_code)!s = Some i.

Definition type_of_builtin_arg (a: builtin_arg reg) : ptype :=
  match a with
  | BA r => env r
  | BA_int _ => Ptyp Tint
  | BA_long _ => Ptyp Tlong
  | BA_float _ => Ptyp Tfloat
  | BA_single _ => Ptyp Tsingle
  | BA_loadstack chunk ofs => inj_typ_ptype (type_of_chunk chunk)
  | BA_addrstack ofs => Pptr 
  | BA_loadglobal chunk id ofs => inj_typ_ptype (type_of_chunk chunk)
  | BA_addrglobal id ofs => Pptr
  | BA_splitlong hi lo => Ptyp Tlong
  | BA_addptr a1 a2 => Pptr
  end.

Definition type_of_builtin_res (r: builtin_res reg) : ptype :=
  match r with
  | BR r => env r
  | _    => Ptyp Tint
  end.

Definition bounds_of_chunk (chunk: memory_chunk): S.bounds :=
  let default m := S.brefl (inj_typ_ptype (type_of_chunk m)) in
  match chunk with
  | Mint32 => if Archi.ptr64 then default chunk else S.bhigh (inj_typ_ptype (type_of_chunk chunk)) 
  | Mint64 => if Archi.ptr64 then S.bhigh (inj_typ_ptype (type_of_chunk chunk)) else default chunk
  | _ => default chunk
  end.

Inductive wt_instr : instruction -> Prop :=
  | wt_Inop:
      forall s,
      valid_successor s ->
      wt_instr (Inop s)
  | wt_Iopmove:
    forall r1 r s,
      subptype (env r1) (env r) -> 
      valid_successor s ->
      wt_instr (Iop Omove (r1 :: nil) r s)
  | wt_Iop:
      forall op args res s targs tres eti,
      op <> Omove ->
      type_of_operation op args res = OK (targs, tres, eti) ->
      list_forall2 S.match_bounds (map env args) targs ->
      S.match_bounds (env res) tres ->
      Forall (fun '(r1, r2) => subptype (env r1) (env r2)) eti ->
      valid_successor s ->
      wt_instr (Iop op args res s)
  | wt_Iload:
      forall chunk addr args dst s,
      list_forall2 S.match_bounds (map env args) (type_of_addressing addr) ->
      S.match_bounds (env dst) (bounds_of_chunk chunk) ->
      valid_successor s ->
      wt_instr (Iload chunk addr args dst s)
  | wt_Istore:
      forall chunk addr args src s,
      list_forall2 S.match_bounds (map env args) (type_of_addressing addr) ->
      S.match_bounds (env src) (bounds_of_chunk chunk) ->
      valid_successor s ->
      wt_instr (Istore chunk addr args src s)
  | wt_Icall:
      forall sig ros args res s,
      match ros with inl r => S.match_bounds (env r) S.bptr | inr s => True end ->
      list_forall2 S.match_bounds (map env args) (map S.blow (proj_sig_args_ptype sig)) -> 
      S.match_bounds (env res) (S.blow (proj_sig_res_ptype sig)) ->
      valid_successor s ->
      wt_instr (Icall sig ros args res s)
  | wt_Itailcall:
      forall sig ros args,
      match ros with inl r => S.match_bounds (env r) S.bptr | inr s => True end ->
      list_forall2 S.match_bounds (map env args) (map S.blow (proj_sig_args_ptype sig)) -> 
      sig.(sig_res) = funct.(fn_sig).(sig_res) ->
      tailcall_possible sig ->
      wt_instr (Itailcall sig ros args)
  | wt_Ibuiltin:
      forall ef args res s,
      match ef with
      | EF_annot _ _ _ | EF_debug _ _ _ => True
      | _ => list_forall2 S.match_bounds (map type_of_builtin_arg args) (map S.blow (proj_sig_args_ptype (ef_sig ef))) 
      end ->
      S.match_bounds (type_of_builtin_res res) (S.blow (proj_sig_res_ptype (ef_sig ef))) ->
      valid_successor s ->
      wt_instr (Ibuiltin ef args res s)
  | wt_Icond:
      forall cond args s1 s2,
      list_forall2 S.match_bounds (map env args) (type_of_condition cond) ->
      valid_successor s1 ->
      valid_successor s2 ->
      wt_instr (Icond cond args s1 s2)
  | wt_Ijumptable:
      forall arg tbl,
      env arg = Ptyp Tint ->
      (forall s, In s tbl -> valid_successor s) ->
      list_length_z tbl * 4 <= Int.max_unsigned ->
      wt_instr (Ijumptable arg tbl)
  | wt_Ireturn_none:
      funct.(fn_sig).(sig_res) = Xvoid ->
      wt_instr (Ireturn None)
  | wt_Ireturn_some:
      forall arg,
      funct.(fn_sig).(sig_res) <> Xvoid ->
      S.match_bounds (env arg) (S.blow (proj_sig_res_ptype funct.(fn_sig))) ->
      wt_instr (Ireturn (Some arg)).

End WT_INSTR.

(** A function [f] is well-typed w.r.t. a typing environment [env],
   written [wt_function env f], if all instructions are well-typed,
   parameters agree in types with the function signature, and
   parameters are pairwise distinct. *)

Record wt_function (f: function) (env: regenv): Prop :=
  mk_wt_function {
    wt_params:
      list_forall2 S.match_bounds (map env f.(fn_params)) (map S.blow (proj_sig_args_ptype f.(fn_sig)));
    wt_norepet:
      list_norepet f.(fn_params);
    wt_instrs:
      forall pc instr,
      f.(fn_code)!pc = Some instr -> wt_instr f env instr;
    wt_entrypoint:
      valid_successor f f.(fn_entrypoint)
}.

Inductive wt_fundef: fundef -> Prop :=
  | wt_fundef_external: forall ef,
      wt_fundef (External ef)
  | wt_function_internal: forall f env,
      wt_function f env ->
      wt_fundef (Internal f).

Definition wt_program (p: program): Prop :=
  forall i f, In (i, Gfun f) (prog_defs p) -> wt_fundef f. 

(** * Type inference *)

(** Type inference reuses the generic solver for unification constraints
  defined in module [Subtyping]. *)

Section INFERENCE.

Local Open Scope error_monad_scope.

Variable f: function.

(** Checking the validity of successor nodes. *)

Definition check_successor (s: node): res unit :=
  match f.(fn_code)!s with
  | None => Error (MSG "bad successor " :: POS s :: nil)
  | Some i => OK tt
  end.

Fixpoint check_successors (sl: list node): res unit :=
  match sl with
  | nil => OK tt
  | s1 :: sl' => do x <- check_successor s1; check_successors sl'
  end.

(** Check structural constraints and process / record all type constraints. *)

Definition type_ros (e: S.typenv) (ros: reg + ident) : res S.typenv :=
  match ros with
  | inl r => S.add_bound e r S.bptr
  | inr s => OK e
  end.

Definition is_move (op: operation) : bool :=
  match op with Omove => true | _ => false end.

Definition type_builtin_arg (e: S.typenv) (a: builtin_arg reg) (b: S.bounds) : res S.typenv :=
  match a with
  | BA r => S.add_bound e r b
  | BA_int _ => S.type_expect e (Ptyp Tint) b
  | BA_long _ => S.type_expect e (Ptyp Tlong) b
  | BA_float _ => S.type_expect e (Ptyp Tfloat) b
  | BA_single _ => S.type_expect e (Ptyp Tsingle) b
  | BA_loadstack chunk ofs => S.type_expect e (inj_typ_ptype (type_of_chunk chunk)) b
  | BA_addrstack ofs => S.type_expect e Pptr b
  | BA_loadglobal chunk id ofs => S.type_expect e (inj_typ_ptype (type_of_chunk chunk)) b
  | BA_addrglobal id ofs => S.type_expect e Pptr b
  | BA_splitlong hi lo => S.type_expect e (Ptyp Tlong) b
  | BA_addptr a1 a2 => S.type_expect e Pptr b
  end.

Fixpoint type_builtin_args (e: S.typenv) (al: list (builtin_arg reg)) (bl: list S.bounds) : res S.typenv :=
  match al, bl with
  | nil, nil => OK e
  | a1 :: al, b1 :: bl =>
      do e1 <- type_builtin_arg e a1 b1; type_builtin_args e1 al bl
  | _, _ =>
      Error (msg "builtin arity mismatch")
  end.

Definition type_builtin_res (e: S.typenv) (a: builtin_res reg) (b: S.bounds) : res S.typenv :=
  match a with
  | BR r => S.add_bound e r b
  | _    => S.type_expect e (Ptyp Tint) b
  end.

Definition type_instr (e: S.typenv) (i: instruction) : res S.typenv :=
  match i with
  | Inop s =>
      do x <- check_successor s; OK e
  | Iop op args res s =>
      do x <- check_successor s;
      if is_move op then
        match args with
        | arg :: nil => do (changed, e') <- S.type_move e arg res; OK e'
        | _ => Error (msg "ill-formed move")
        end
      else 
        (do t <- type_of_operation op args res;
         let '((targs, tres), eti) := t in
         do e1 <- S.add_bounds e args targs; 
         do e2 <- S.add_bound e1 res tres;
         S.type_subs_rr e2 eti)
  | Iload chunk addr args dst s =>
      do x <- check_successor s;
      do e1 <- S.add_bounds e args (type_of_addressing addr);
      S.add_bound e1 dst (bounds_of_chunk chunk)
  | Istore chunk addr args src s =>
      do x <- check_successor s;
      do e1 <- S.add_bounds e args ((type_of_addressing addr));
      S.add_bound e1 src (bounds_of_chunk chunk)
  | Icall sig ros args res s =>
      do x <- check_successor s;
      do e1 <- type_ros e ros;
      do e2 <- S.add_bounds e1 args (map S.blow (proj_sig_args_ptype sig));
      S.add_bound e2 res (S.blow (proj_sig_res_ptype sig))
  | Itailcall sig ros args =>
      do e1 <- type_ros e ros;
      do e2 <- S.add_bounds e1 args (map S.blow (proj_sig_args_ptype sig));
      if xtype_eq sig.(sig_res) f.(fn_sig).(sig_res) then
        if tailcall_is_possible sig
        then OK e2
        else Error(msg "tailcall not possible")
      else Error(msg "bad return type in tailcall")
  | Ibuiltin ef args res s =>
      let sig := ef_sig ef in
      do x <- check_successor s;
      do e1 <-
        match ef with
        | EF_annot _ _ _ | EF_debug _ _ _ => OK e
        | _ => type_builtin_args e args (map S.blow (proj_sig_args_ptype sig))
        end;
      type_builtin_res e1 res (S.blow (proj_sig_res_ptype sig))
 | Icond cond args s1 s2 =>
      do x1 <- check_successor s1;
      do x2 <- check_successor s2;
      S.add_bounds e args (type_of_condition cond)
 | Ijumptable arg tbl =>
      do x <- check_successors tbl;
      do e1 <- S.add_bound e arg (S.brefl (Ptyp Tint));
      if zle (list_length_z tbl * 4) Int.max_unsigned
      then OK e1
      else Error(msg "jumptable too big")
  | Ireturn optres =>
      match optres, xtype_eq f.(fn_sig).(sig_res) Xvoid with
      | None, left _ => OK e
      | Some r, right _ => S.add_bound e r (S.blow (proj_sig_res_ptype f.(fn_sig)))
      | _, _ => Error(msg "bad return")
      end
  end.

Definition type_code (e: S.typenv): res S.typenv :=
  PTree.fold (fun re pc i =>
    match re with
    | Error _ => re
    | OK e =>
        match type_instr e i with
        | Error msg => Error(MSG "At PC " :: POS pc :: MSG ": " :: msg)
        | OK e' => OK e'
        end
    end)
  f.(fn_code) (OK e).

(** Solve remaining constraints *)

Definition check_params_norepet (params: list reg): res unit :=
  if list_norepet_dec Reg.eq params
  then OK tt
  else Error(msg "duplicate parameters").

Definition type_function : res S.typassign :=
  do e1 <- type_code S.initial;
  do e2 <- S.add_bounds e1 f.(fn_params) (map S.blow (proj_sig_args_ptype f.(fn_sig)));
  do te <- S.solve e2;
  do x1 <- check_params_norepet f.(fn_params);
  do x2 <- check_successor f.(fn_entrypoint);
  OK te.

(** ** Soundness proof *)

Remark type_ros_incr:
  forall e ros e' te, type_ros e ros = OK e' -> S.satisf te e' -> S.satisf te e.
Proof.
  unfold type_ros; intros. destruct ros. eauto with ty. inv H; auto with ty.
Qed.

Hint Resolve type_ros_incr: ty.

Lemma type_ros_sound:
  forall e ros e' te, type_ros e ros = OK e' -> S.satisf te e' ->
  match ros with inl r => S.match_bounds (te r) S.bptr | inr s => True end.
Proof.
  unfold type_ros; intros. destruct ros; try tauto.
  eauto with ty.
Qed.

Lemma check_successor_sound:
  forall s x, check_successor s = OK x -> valid_successor f s.
Proof.
  unfold check_successor, valid_successor; intros.
  destruct (fn_code f)!s; inv H. exists i; auto.
Qed.

Hint Resolve check_successor_sound: ty.

Lemma check_successors_sound:
  forall sl x, check_successors sl = OK x -> forall s, In s sl -> valid_successor f s.
Proof.
  induction sl; simpl; intros.
  contradiction.
  monadInv H. destruct H0. subst a; eauto with ty. eauto.
Qed.

Lemma type_builtin_arg_incr:
  forall e a ty e' te, type_builtin_arg e a ty = OK e' -> S.satisf te e' -> S.satisf te e.
Proof.
  unfold type_builtin_arg; intros; destruct a; eauto with ty.
Qed.

Lemma type_builtin_args_incr:
  forall a ty e e' te, type_builtin_args e a ty = OK e' -> S.satisf te e' -> S.satisf te e.
Proof.
  induction a; destruct ty; simpl; intros; try discriminate.
  inv H; auto.
  monadInv H. eapply type_builtin_arg_incr; eauto.
Qed.

Lemma type_builtin_res_incr:
  forall e a ty e' te, type_builtin_res e a ty = OK e' -> S.satisf te e' -> S.satisf te e.
Proof.
  unfold type_builtin_res; intros; destruct a; inv H; eauto with ty.
Qed.

Hint Resolve type_builtin_args_incr type_builtin_res_incr: ty.

Lemma type_builtin_arg_sound:
  forall e a b e' te,
  type_builtin_arg e a b = OK e' -> S.satisf te e' -> S.match_bounds (type_of_builtin_arg te a) b.
Proof.
  intros. destruct a; simpl in *; try (eapply S.type_expect_sound; eassumption).
  eauto with ty.
Qed.

Lemma type_builtin_args_sound:
  forall al tyl e e' te,
  type_builtin_args e al tyl = OK e' -> S.satisf te e' -> list_forall2 S.match_bounds (List.map (type_of_builtin_arg te) al) tyl.
Proof.
  induction al as [|a al]; destruct tyl as [|ty tyl]; simpl; intros; try discriminate.
- constructor.
- monadInv H. constructor.
  + eapply type_builtin_arg_sound; eauto with ty.
  + eauto.
Qed.

Lemma type_builtin_res_sound:
  forall e a b e' te,
  type_builtin_res e a b = OK e' -> S.satisf te e' -> S.match_bounds (type_of_builtin_res te a) b.
Proof.
  intros. destruct a; simpl in *.
  - eauto with ty.
  - eapply S.type_expect_sound; eauto.
  - eapply S.type_expect_sound; eauto.
Qed.

Lemma type_instr_incr:
  forall e i e' te,
  type_instr e i = OK e' -> S.satisf te e' -> S.satisf te e.
Proof.
  intros; destruct i eqn:Ei; try (monadInv H); eauto with ty.
- (* op *)
  destruct (is_move o) eqn:ISMOVE.
  destruct l; try discriminate. destruct l; monadInv EQ0. eauto with ty.
  destruct (type_of_operation o l r) as [[[targs tres] eti]|] eqn:TYOP; 
    cbn in EQ0; [|monadInv EQ0].
  monadInv EQ0.
  now eauto with ty.
- (* tailcall *)
  destruct (xtype_eq (sig_res s) (sig_res (fn_sig f))); try discriminate.
  destruct (tailcall_is_possible s) eqn:TCIP; inv EQ2.
  now eauto with ty.
- (* builtin *)
  destruct e0; try monadInv EQ1; eauto with ty.
- (* jumptable *)
  destruct (zle (list_length_z l * 4) Int.max_unsigned); inv EQ2.
  eauto with ty.
- (* return *)
  simpl in H.
  destruct o as [r|] eqn: RET; destruct (xtype_eq (sig_res (fn_sig f)) Xvoid); try discriminate.
  eauto with ty.
  inv H; auto with ty.
Qed.

Lemma type_instr_sound:
  forall e i e' te,
  type_instr e i = OK e' -> S.satisf te e' -> wt_instr f te i.
Proof.
  intros;destruct i; try (monadInv H); simpl.
- (* nop *)
  constructor; eauto with ty.
- (* op *)
  destruct (is_move o) eqn:ISMOVE.
  (* move *)
  + unfold is_move in ISMOVE; destruct o; try congruence.
    destruct l; try discriminate. destruct l; monadInv EQ0.
    constructor. eapply S.type_move_sound; eauto. eauto with ty.
  + destruct (type_of_operation o l r) as [[[targs tres] eti]|] eqn:TYOP; cbn in EQ0.
    monadInv EQ0.
    eapply wt_Iop; eauto with ty.
    unfold is_move in ISMOVE; destruct o; (congruence || trivial).
    monadInv EQ0.
- (* load *)
  constructor; eauto with ty.
- (* store *)
  constructor; eauto with ty.
- (* call *)
  constructor; eauto with ty.
  eapply type_ros_sound; eauto with ty.
- (* tailcall *)
  destruct (xtype_eq (sig_res s) (sig_res (fn_sig f))); try discriminate.
  destruct (tailcall_is_possible s) eqn:TCIP; inv EQ2.
  constructor; eauto with ty.
  eapply type_ros_sound; eauto with ty.
  apply tailcall_is_possible_correct; auto.
- (* builtin *)
  constructor; eauto with ty.
  + destruct e0; auto; eapply type_builtin_args_sound; eauto with ty.
  + eapply type_builtin_res_sound; eauto.
- (* cond *)
  constructor; eauto with ty.
- (* jumptable *)
  destruct (zle (list_length_z l * 4) Int.max_unsigned); inv EQ2.
  constructor; eauto.
  specialize (S.add_bound_sound _ _ _ _ _ EQ1 H0) as H.
  apply subptype_antisymmetric; apply H.
  eapply check_successors_sound; eauto.
- (* return *)
  simpl in H.
  destruct o as [r|] eqn: RET; destruct (xtype_eq (sig_res (fn_sig f)) Xvoid); try discriminate.
  econstructor; eauto with ty.
  constructor; eauto with ty.
Qed.

Lemma type_code_sound:
  forall pc i e e' te,
  type_code e = OK e' ->
  f.(fn_code)!pc = Some i -> S.satisf te e' -> wt_instr f te i.
Proof.
  intros pc i e0 e1 te TCODE.
  set (P := fun c opte =>
         match opte with
         | Error _ => True
         | OK e' => c!pc = Some i -> S.satisf te e' -> wt_instr f te i
         end).
  change (P f.(fn_code) (OK e1)).
  rewrite <- TCODE. unfold type_code. apply PTree_Properties.fold_rec; unfold P; intros.
  - (* extensionality *)
    destruct a; auto; intros. rewrite <- H in H1. eapply H0; eauto.
  - (* base case *)
    rewrite PTree.gempty in H; discriminate.
  - (* inductive case *)
    destruct a as [e|?]; auto.
    destruct (type_instr e v) as [e'|?] eqn:TYINSTR; auto.
    intros. rewrite PTree.gsspec in H2. destruct (peq pc k).
    inv H2. eapply type_instr_sound; eauto.
    eapply H1; eauto. eapply type_instr_incr; eauto.
Qed.

Theorem type_function_correct:
  forall env, type_function = OK env -> wt_function f env.
Proof.
  unfold type_function; intros. monadInv H.
  assert (SAT0: S.satisf env x0) by (eapply S.solve_sound; eauto).
  assert (SAT1: S.satisf env x) by (eauto with ty).
  constructor.
- (* type of parameters *)
  eauto with ty.
- (* parameters are unique *)
  unfold check_params_norepet in EQ2.
  destruct (list_norepet_dec Reg.eq (fn_params f)); inv EQ2; auto.
- (* instructions are well typed *)
  intros. eapply type_code_sound; eauto.
- (* entry point is valid *)
  eauto with ty.
Qed.

End INFERENCE.
(** * Type preservation during evaluation *)

(** The type system for RTL is not sound in that it does not guarantee
  progress: well-typed instructions such as [Icall] can fail because
  of run-time type tests (such as the equality between callee and caller's
  signatures).  However, the type system guarantees a type preservation
  property: if the execution does not fail because of a failed run-time
  test, the result values and register states match the static
  typing assumptions.  This preservation property will be useful
  later for the proof of semantic equivalence between [Linear] and [Mach].
  Even though we do not need it for [RTL], we show preservation for [RTL]
  here, as a warm-up exercise and because some of the lemmas will be
  useful later. *)

Definition wt_regset (env: regenv) (rs: regset) : Prop :=
  forall r, Val.has_ptype (rs#r) (env r).

Lemma wt_regset_assign:
  forall env rs v r,
  wt_regset env rs ->
  Val.has_ptype v (env r) ->
  wt_regset env (rs#r <- v).
Proof.
  intros; red; intros.
  rewrite Regmap.gsspec.
  case (peq r0 r); intro.
  subst r0. assumption.
  apply H.
Qed.

Lemma wt_regset_list:
  forall env rs,
  wt_regset env rs ->
  forall rl, Val.has_ptype_list (rs##rl) (List.map env rl).
Proof.
  induction rl; cbn; constructor. 
  - apply H.
  - apply IHrl.
Qed.

Lemma wt_regset_list3:
  forall env rs,
  wt_regset env rs ->
  forall rl al,
  list_forall2 subptype (List.map env rl) (map high_bound al) ->
  Val.has_ptype_list (rs##rl) al.
Proof.
  intros * H.
  induction rl; destruct al; intros; inv H0.
  - constructor.
  - constructor.
    + eapply Val.has_ptype_sub'; eauto with ty.
    + apply IHrl; assumption.
Qed.

Lemma wt_init_regs:
  forall env rl args,
  Val.has_ptype_list args (List.map env rl) ->
  wt_regset env (init_regs args rl).
Proof.
  induction rl; destruct args; simpl; try (intros H; inv H).
  - red; intros. rewrite Regmap.gi. exact I.
  - apply wt_regset_assign; auto.
Qed.

Lemma wt_exec_Iop:
  forall (ge: genv) env f sp op args res s rs m v,
  wt_instr f env (Iop op args res s) ->
  eval_operation ge sp op rs##args m = Some v ->
  wt_regset env rs ->
  wt_regset env (rs#res <- v).
Proof.
  intros. inv H.
  (* move *)
  simpl in H0. inv H0. apply wt_regset_assign; auto.
  eapply Val.has_ptype_sub; eauto with ty.
  (* other op *)
  eapply wt_regset_assign; auto with ty.
  destruct H9.
  eapply Val.has_ptype_sub; eauto with ty.
  eapply type_of_operation_sound; eauto.
Qed.

Lemma mem_load_bounds:
  forall (m : mem) (chunk : memory_chunk) (b : block)
         (ofs : Z) (v : val),
  Mem.load chunk m b ofs = Some v ->
  Val.has_ptype v (S.proj_lo (bounds_of_chunk chunk)).
Proof.
  intros.
  unfold Val.has_ptype.
  destruct chunk eqn:Ech.
  6: {
    (* Mint32 *)
    cbn.
    destruct Archi.ptr64 eqn:SF; cbn; try rewrite SF; cbn; unfold Tptr; try rewrite SF.
    change Tint with (type_of_chunk Mint32). 
    eapply Mem.load_type; eassumption.
    change Tint with (type_of_chunk Mint32). 
    eapply Mem.load_type; eassumption.
  }
  6: {
    (* Mint64 *)
    cbn.
    destruct Archi.ptr64 eqn:SF; cbn; try rewrite SF; cbn; unfold Tptr; try rewrite SF.
    change Tlong with (type_of_chunk Mint64). 
    eapply Mem.load_type; eassumption.
    change Tlong with (type_of_chunk Mint64). 
    eapply Mem.load_type; eassumption.
  }
  all: eapply Mem.load_type; eassumption.
Qed.

Lemma wt_exec_Iload:
  forall env f chunk addr args dst s m a v rs,
  wt_instr f env (Iload chunk addr args dst s) ->
  Mem.loadv chunk m a = Some v ->
  wt_regset env rs ->
  wt_regset env (rs#dst <- v).
Proof.
  intros. destruct a; simpl in H0; try discriminate. inv H.
  eapply wt_regset_assign; eauto.
  apply (Val.has_ptype_sub (S.proj_lo (bounds_of_chunk chunk))); auto with ty.
  eapply mem_load_bounds; eauto.
  destruct (zle (Ptrofs.unsigned i + size_chunk chunk) Ptrofs.modulus); try discriminate; eauto.
Qed.

Lemma wt_exec_Ibuiltin:
  forall env f ef (ge: genv) args res s vargs m t vres m' rs,
  wt_instr f env (Ibuiltin ef args res s) ->
  external_call ef ge vargs m t vres m' ->
  wt_regset env rs ->
  wt_regset env (regmap_setres res vres rs).
Proof.
  intros. inv H.
  destruct res; simpl in *; auto. apply wt_regset_assign; auto.
  eapply Val.has_ptype_sub; eauto with ty.
  unfold proj_sig_res_ptype, Val.has_ptype.
  rewrite <- proj_xtype_ptype_typ.
  eapply external_call_well_typed; eauto.
Qed.

Lemma wt_instr_at:
  forall f env pc i,
  wt_function f env -> f.(fn_code)!pc = Some i -> wt_instr f env i.
Proof.
  intros. inv H. eauto.
Qed.

Inductive wt_stackframes: list stackframe -> signature -> Prop :=
  | wt_stackframes_nil: forall sg,
      sg.(sig_res) = Xint ->
      wt_stackframes nil sg
  | wt_stackframes_cons:
      forall s res f sp pc rs env sg,
      wt_function f env ->
      wt_regset env rs ->
      subptype (proj_sig_res_ptype sg) (env res) ->
      wt_stackframes s (fn_sig f) ->
      wt_stackframes (Stackframe res f sp pc rs :: s) sg.

Inductive wt_state: state -> Prop :=
  | wt_state_intro:
      forall s f sp pc rs m env
        (WT_STK: wt_stackframes s (fn_sig f))
        (WT_FN: wt_function f env)
        (WT_RS: wt_regset env rs),
      wt_state (State s f sp pc rs m)
  | wt_state_call:
      forall s f args m,
      wt_stackframes s (funsig f) ->
      wt_fundef f ->
      Val.has_ptype_list args (proj_sig_args_ptype (funsig f)) ->
      wt_state (Callstate s f args m)
  | wt_state_return:
      forall s v m sg,
      wt_stackframes s sg ->
      Val.has_ptype v (proj_sig_res_ptype sg) ->
      wt_state (Returnstate s v m).


Remark wt_stackframes_change_sig:
  forall s sg1 sg2,
  sg1.(sig_res) = sg2.(sig_res) -> wt_stackframes s sg1 -> wt_stackframes s sg2.
Proof.
  intros. inv H0.
  - constructor; congruence.
  - econstructor; eauto.
    unfold proj_sig_res_ptype in *. rewrite <- H. assumption.
Qed.

Section SUBJECT_REDUCTION.

Variable p: program.

Hypothesis wt_p: wt_program p.

Let ge := Genv.globalenv p.

Lemma subject_reduction:
  forall st1 t st2, step ge st1 t st2 ->
  forall (WT: wt_state st1), wt_state st2.
Proof.
  induction 1; intros; inv WT;
    try (generalize (wt_instrs _ _ WT_FN pc _ H); intros WTI).
  (* Inop *)
  - econstructor; eauto.
  (* Iop *)
  - econstructor; eauto. eapply wt_exec_Iop; eauto.
  (* Iload *)
  - econstructor; eauto. eapply wt_exec_Iload; eauto.
  (* Istore *)
  - econstructor; eauto.
  (* Icall *)
  - assert (wt_fundef fd).
    { destruct ros; simpl in H0.
      apply (Genv.find_funct_prop _ p (rs#r)); eauto.
      fold fundef in *.
      caseEq (Genv.find_symbol ge i); intros; rewrite H1 in H0.
      pattern fd. apply Genv.find_funct_ptr_prop with fundef unit p b; eauto.
      discriminate. }
    econstructor; eauto.
    + econstructor; eauto. inv WTI; auto with ty.
    + inv WTI.
      apply (wt_regset_list3 env); auto with ty.
  (* Itailcall *)
  -  assert (wt_fundef fd).
     { destruct ros; simpl in H0.
       pattern fd. apply Genv.find_funct_prop with fundef unit p (rs#r); eauto.
       fold fundef in *.
       caseEq (Genv.find_symbol ge i); intros; rewrite H1 in H0.
       pattern fd. apply Genv.find_funct_ptr_prop with fundef unit p b; eauto.
       discriminate. }
     econstructor; eauto.
     inv WTI. apply wt_stackframes_change_sig with (fn_sig f); auto.
     inv WTI. apply (wt_regset_list3 env); auto with ty.
  (* Ibuiltin *)
  - econstructor; eauto. eapply wt_exec_Ibuiltin; eauto.    
  (* Icond *)
  - econstructor; eauto.    
  (* Ijumptable *)
  - econstructor; eauto.    
  (* Ireturn *)
  - econstructor; eauto.    
    inv WTI; simpl. auto.
    unfold wt_regset in *.
    eapply Val.has_ptype_sub'; eauto with ty.
  (* internal function *)
  - simpl in *. inv H6.
    econstructor; eauto.
    inv H2. apply wt_init_regs.
    eapply Val.has_ptype_sub_list; eauto with ty.
  (* external function *)
  - econstructor; eauto.    
    unfold proj_sig_res_ptype, Val.has_ptype.
    rewrite <- proj_xtype_ptype_typ.
    eapply external_call_well_typed; eauto.
  (* return *)
  - inv H1. econstructor; eauto.    
    apply wt_regset_assign; auto. 
    eapply Val.has_ptype_sub; eauto with ty.
Qed.

Lemma wt_initial_state:
  forall S, initial_state p S -> wt_state S.
Proof.
  intros. inv H. constructor. constructor. rewrite H3; auto.
  pattern f. apply Genv.find_funct_ptr_prop with fundef unit p b.
  exact wt_p. exact H2.
  rewrite H3. constructor.
Qed.

Lemma wt_instr_inv:
  forall s f sp pc rs m i,
  wt_state (State s f sp pc rs m) ->
  f.(fn_code)!pc = Some i ->
  exists env, wt_instr f env i /\ wt_regset env rs.
Proof.
  intros. inv H. exists env; split; auto.
  inv WT_FN. eauto.
Qed.

End SUBJECT_REDUCTION.

Section TypedRTL.

Inductive typed_fun: Type :=
  TF f env : wt_function f env -> typed_fun.

Definition typed_fundef := AST.fundef typed_fun.
Definition program := AST.program typed_fundef unit.

Coercion untype g := match g with TF f _ _ => f end.
Definition get_env g := match g with TF _ env _ => env end.

Definition get_wt g: wt_function (untype g) (get_env g) := match g with TF f env wt => wt end.

Definition untype_fundef := transf_fundef untype.

Definition get_typed_function (f: function): res typed_fun.
  destruct (type_function f) eqn:E.
  - refine (OK (TF f t (type_function_correct f t E))).
  - exact (Error e).
Defined.

Definition type_fundef : fundef -> res typed_fundef := transf_partial_fundef get_typed_function.

Lemma untype_program_preserves_find_symbol:
  forall {V} {L: Linking.Linker V} (prog: AST.program typed_fundef V) s,
    Genv.find_symbol (Genv.globalenv prog) s = Genv.find_symbol (Genv.globalenv (transform_program untype_fundef prog)) s.
Proof.
  intros. revert s. symmetry.  eapply Genv.find_symbol_transf.
  eapply Linking.match_transform_program.
Qed.

Definition type_program (p: RTL.program): res program :=
  transform_partial_program (type_fundef) p.

Definition untype_globdef {V} (g: globdef typed_fundef V) :=
  match g with
  | Gfun f => Gfun (untype_fundef f)
  | Gvar v => Gvar v
  end.

Definition untype_genv (genv: Genv.t typed_fundef unit): Genv.t fundef unit.
refine (@Genv.mkgenv _ _
          (Genv.genv_public genv)
          (Genv.genv_symb genv)
          (PTree.map1 untype_globdef (Genv.genv_defs genv))
          (Genv.genv_next genv) (Genv.genv_symb_range genv) _ _).
- destruct genv. cbn; intros.
  rewrite PTree.gmap1 in H. unfold option_map in H.
  destruct (genv_defs ! b) eqn:E; try discriminate.
  eapply (genv_defs_range b g0). assumption.
- intros. destruct genv. cbn in *. eapply genv_vars_inj; eassumption.
Defined.  

Definition step (g: Genv.t typed_fundef unit) := RTL.step (untype_genv g).

Definition initial_state p := (RTL.initial_state (transform_program untype_fundef p)).

Definition semantics (p: program) := Semantics step (initial_state p) RTL.final_state (Genv.globalenv p).

End TypedRTL.

Definition match_prog (p: RTL.program) (tp: program) :=
  match_program (fun _ f tf => transf_partial_fundef get_typed_function f = OK tf) eq p tp.

Definition match_prog2 (p:program) (tp: RTL.program) :=
  match_program (fun _ f tf => tf = untype_fundef f) eq p tp.

Lemma type_program_match:
  forall p tp, type_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.

Lemma untype_program_match:
  forall p tp, (transform_program untype_fundef p) = tp -> match_prog2 p tp.
Proof.
  intros. rewrite <- H. eapply match_transform_program.
Qed.

Lemma untype_function_eq:
  forall f f' env w,
    get_typed_function f = OK (TF f' env w) ->
    f' = f.
Proof.
  intros until w. unfold get_typed_function.
  generalize (eq_refl (type_function f)).
  generalize (type_function f) at 2 3.
  intros. destruct r; try discriminate. inv H. reflexivity.
Qed.
  
Lemma untype_type_fundef_eq:
  forall f tf,
    type_fundef f = OK tf -> untype_fundef tf = f.
Proof.
  intros until tf. unfold type_fundef.
  destruct f.
  - cbn. intros H. apply bind_inversion in H as (x & eq1 & eq2). inv eq2.
    cbn. destruct x. f_equal. now apply untype_function_eq in eq1.
  - intros eq. inv eq. cbn. reflexivity.
Qed.

Lemma find_function_preserved':
  forall F V V' (g: Genv.t (AST.fundef F) V) (g': Genv.t (AST.fundef F) V') ros rs,
    (forall i, Genv.find_symbol g i = Genv.find_symbol g' i) ->
    (forall b, Genv.find_funct_ptr g b = Genv.find_funct_ptr g' b) ->
    find_function g ros rs = find_function g' ros rs.
Proof.
  intros. unfold find_function.  destruct ros.
  - unfold Genv.find_funct. destruct (rs # r); try reflexivity.
    destruct (Ptrofs.eq_dec i Ptrofs.zero); auto.
  - rewrite (H i). destruct (Genv.find_symbol g' i); auto.
Qed.

Lemma find_some_function_preserved':
  forall F V V' (g: Genv.t (AST.fundef F) V) (g': Genv.t (AST.fundef F) V') ros rs rd,
    (forall i, Genv.find_symbol g i = Genv.find_symbol g' i) ->
    (forall b f, Genv.find_funct_ptr g b = Some f -> Genv.find_funct_ptr g' b = Some f) ->
    find_function g ros rs = Some rd -> find_function g' ros rs = Some rd.
Proof.
  intros until rd. intros E1 E2. unfold find_function.  destruct ros.
  - unfold Genv.find_funct. destruct (rs # r); try auto.
    destruct (Ptrofs.eq_dec i Ptrofs.zero); auto.
  - rewrite (E1 i). destruct (Genv.find_symbol g' i); auto.
Qed.

Lemma find_function_preserved:
  forall F V (g: Genv.t (AST.fundef F) V) (g': Genv.t (AST.fundef F) V) ros rs,
    (forall i, Genv.find_symbol g i = Genv.find_symbol g' i) ->
    (forall b, Genv.find_def g b = Genv.find_def g' b) ->
    find_function g ros rs = find_function g' ros rs.
Proof.
  intros. apply find_function_preserved'; try assumption.
  unfold Genv.find_funct_ptr. intros b. rewrite (H0 b).
  reflexivity.
Qed.

Lemma symbols_preserved':
  forall tge (s: ident),
    Genv.find_symbol (untype_genv tge) s = Genv.find_symbol tge s.
Proof.
  intros. unfold Genv.find_symbol. destruct tge; cbn. reflexivity.
Qed.

Lemma find_untyped_funct_ptr:
  forall ge b fd,
    Genv.find_funct_ptr (untype_genv ge) b = Some fd ->
    exists fd', Genv.find_funct_ptr ge b = Some fd' /\ untype_fundef fd' = fd.
Proof.
  intros. rewrite Genv.find_funct_ptr_iff in H.
  destruct ge; unfold untype_genv in H; cbn in *. unfold Genv.find_def in H; cbn in H.  
  rewrite PTree.gmap1 in H. unfold Genv.find_funct_ptr.  
  unfold Genv.find_def. cbn. destruct (genv_defs ! b); cbn in *; inv H.  
  destruct g; cbn in *; try discriminate. exists f.
  split; congruence.
Qed.

Lemma find_funct_ptr_in_untyped:
  forall ge b fd,
    Genv.find_funct_ptr ge b = Some fd ->
    Genv.find_funct_ptr (untype_genv ge) b = Some (untype_fundef fd).
Proof.
  intros. rewrite Genv.find_funct_ptr_iff in H.
  destruct ge; unfold untype_genv; cbn in *. unfold Genv.find_def in H; cbn in H.  
  unfold Genv.find_funct_ptr.  
  unfold Genv.find_def. cbn. rewrite PTree.gmap1. destruct (genv_defs ! b); cbn in *; inv H.  
  destruct fd; cbn in *; try reflexivity.
Qed.

Lemma untype_fundef_internal:
  forall fd f,
    untype_fundef fd = Internal f ->
    exists env p, fd = Internal (TF f env p).
Proof.
  intros. destruct fd; try discriminate. destruct t; cbn in *.
  exists env. inv H. exists w. reflexivity.
Qed.

Lemma untype_fundef_external:
  forall fd f,
    untype_fundef fd = External f ->
    fd = External f.
Proof.
  intros. destruct fd; cbn in *.
  - destruct t; discriminate.
  - congruence.
Qed.

Lemma funct_ptr_preserved_from_untype:
  forall (prog: program) f b,
    Genv.find_funct_ptr (Genv.globalenv (transform_program untype_fundef prog)) b = Some f ->
    exists f', Genv.find_funct_ptr (Genv.globalenv prog) b = Some f'
          /\  untype_fundef f' = f.
Proof.
  intros.
  pose proof (Genv.find_funct_ptr_inversion _ _ H) as (id & H').
  rewrite Genv.find_funct_ptr_iff in H.
  apply Genv.find_def_transform_Gfun in H as (gd' & eq1 & eq2).
  destruct gd'.
  - exists (Internal t). rewrite Genv.find_funct_ptr_iff. split; auto.
  - eexists. rewrite Genv.find_funct_ptr_iff. split; eauto.
Qed.

Lemma init_mem_preserved_from_untype:
  forall (prog: program) m,
    Genv.init_mem (transform_program untype_fundef prog) = Some m ->
    Genv.init_mem prog = Some m.
Proof.
  intros.
  eapply (@Genv.init_mem_transf' fundef typed_fundef); try eassumption.
  apply match_transform_program'.
Qed.

Lemma init_mem_preserved_in_untyped:
  forall (prog: program) m,
  Genv.init_mem prog = Some m ->
  Genv.init_mem (transform_program untype_fundef prog) = Some m.
Proof.
  intros.
  eapply (@Genv.init_mem_transf typed_fundef fundef); try eassumption.
  apply untype_program_match. reflexivity.
Qed.

Lemma typed_program_wt:
  forall (prog: program), wt_program (transform_program untype_fundef prog).
Proof.
  unfold wt_program. intros.
  destruct prog; cbn in H.
  apply list_in_map_inv in H as (y & eq & H). destruct y; cbn in eq. destruct g; inv eq.
  destruct f0.
  - cbn. destruct t; cbn in *. econstructor. eassumption.
  - cbn in *. constructor.
Qed.

Section PRESERVATION.

Variable prog: RTL.program.
Variable tprog: program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intros s. pose proof (Genv.find_symbol_match TRANSF s).
  fold tge in H.  fold ge in H. exact H.
Qed.

Lemma symbols_preserved'':
  forall (s: ident), Genv.find_symbol (untype_genv tge) s = Genv.find_symbol ge s.
Proof.
  intros s. rewrite <- symbols_preserved. apply symbols_preserved'.
Qed.

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof.
  pose proof (Genv.senv_match TRANSF). fold tge in H.
  fold ge in H. assumption.
Qed.

Lemma var_info_preserved:
  forall b, Genv.find_var_info (untype_genv tge) b = Genv.find_var_info tge b.
Proof.
  intros. unfold Genv.find_var_info. unfold Genv.find_def.  unfold untype_genv; cbn.
  rewrite PTree.gmap1. destruct tge; cbn. destruct (genv_defs ! b); cbn.
  - destruct g; cbn. all: reflexivity.
  - reflexivity.
Qed.

Lemma senv_preserved': Senv.equiv tge (untype_genv tge).
Proof.
  repeat split. intros.
  unfold Senv.block_is_volatile; cbn.
  apply Genv.block_is_volatile_preserved.
  apply var_info_preserved.
Qed.

Lemma senv_preserved'': Senv.equiv ge (untype_genv tge).
Proof.
  eapply Senv.equiv_trans.
  - apply senv_preserved.
  - apply senv_preserved'.
Qed.      
  
Lemma find_some_untype_function_preserved:
  forall ros rs fd,
    find_function ge ros rs = Some fd ->
    find_function (untype_genv tge) ros rs = Some fd.
Proof.
  intros untol fd. unfold match_prog in TRANSF.  fold type_fundef in TRANSF.
  intros. eapply find_some_function_preserved'; try eassumption.
  - intros. symmetry. apply symbols_preserved''.
  - intros. eapply Genv.find_funct_ptr_transf_partial in H0 as (fd' & eq1 & eq2); [| eassumption].
    unfold tge. revert eq1. unfold Genv.globalenv. fold typed_fundef.
    eapply Genv.add_globals_preserves; intros.
    + rewrite Genv.find_funct_ptr_iff in *.
      unfold Genv.find_def in *.
      apply Genv.add_global_genv_defs_some in eq1 as [ [eq eq1] | [eq eq1]].
      * specialize (H0 eq1). destruct ge0; cbn in *. rewrite PTree.gmap1.
           rewrite PTree.gso; try assumption.
           rewrite eq1. cbn. f_equal.  f_equal.
           apply untype_type_fundef_eq. assumption.
      * cbn. destruct ge0; cbn in *.  rewrite eq. rewrite PTree.gmap1. rewrite PTree.gss.
        rewrite <- eq1. cbn. repeat f_equal. apply untype_type_fundef_eq. assumption
    + rewrite Genv.no_pointer_in_empty_genv in eq1.
    + discriminate eq1.
Qed.

Lemma step_preserved:
  forall s1 t s2,
    RTL.step ge s1 t s2 ->
    step tge s1 t s2.
Proof.
  unfold step. intros. inv H; try now constructor.
  - econstructor; eauto. erewrite eval_operation_preserved; try eassumption. apply symbols_preserved''.
  - eapply exec_Iload.  exact H0.
    rewrite <- H1. eapply eval_addressing_preserved.
    apply symbols_preserved''.
    auto.
  - eapply exec_Istore. exact H0.
    rewrite <- H1. eapply eval_addressing_preserved.
     apply symbols_preserved''.
     auto.
  - econstructor; eauto.
    apply find_some_untype_function_preserved; auto.
  - econstructor; eauto.
    apply find_some_untype_function_preserved; auto.
  - econstructor; eauto.
    + eapply eval_builtin_args_preserved.
      * eapply symbols_preserved''.
      * eassumption.        
    + eapply external_call_symbols_preserved.
      * apply senv_preserved''.    
      * assumption.
  - eapply exec_Icond; eauto.
  - eapply exec_Ijumptable; eauto. 
  - econstructor; eauto. eapply external_call_symbols_preserved; eauto.
    apply senv_preserved''.
Qed.

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (semantics tprog).
Proof. 
  eapply forward_simulation_plus.
  - apply senv_preserved.
  - intros. inv H. exists (Callstate nil f nil m0). split.
    + replace ge0 with ge in * by reflexivity.
      econstructor; try eassumption.
      * eapply (@Genv.init_mem_transf typed_fundef fundef unit).
        eapply match_transform_program.
        eapply (@Genv.init_mem_transf_partial fundef typed_fundef); eassumption.
      * assert ((prog_main (transform_program untype_fundef tprog)) = prog_main prog).
        {
          cbn.  eapply match_program_main. eassumption.
        }
        fold fundef in *.
        rewrite H.
        erewrite (@Genv.find_symbol_transf typed_fundef fundef unit); [| eapply match_transform_program].
        fold tge. rewrite symbols_preserved. exact H1.
      * eapply Genv.find_funct_ptr_transf_partial in H2 as (tf & eq1 & eq2); [| exact TRANSF].
        eapply Genv.find_funct_ptr_transf in eq1; [| eapply match_transform_program].
        eapply eq_rect.
        exact eq1.
        f_equal. apply untype_type_fundef_eq; auto.
    + reflexivity.
  - intros. inv H0.  constructor.
  - intros. subst. exists s1'. split; try reflexivity. eapply plus_one. cbn in *.
    apply step_preserved. assumption.
Qed.    
End PRESERVATION. 

Lemma find_some_untype_function_preserve':
  forall (ge: Genv.t typed_fundef unit)  ros rs fd,
    find_function (untype_genv ge) ros rs = Some fd ->
    exists fd', find_function ge ros rs = Some fd' /\ untype_fundef fd' = fd.
Proof.
  intros. unfold find_function. destruct ros.
  - cbn in H. pose proof (Genv.find_funct_inv _ _ H) as (b & eq).
    rewrite eq in *. rewrite Genv.find_funct_find_funct_ptr in *.
    now apply find_untyped_funct_ptr.
  - cbn in H. rewrite symbols_preserved' in H. destruct (Genv.find_symbol ge i) eqn:E; try discriminate.
    apply find_untyped_funct_ptr in H as (fd' & eq & eq').
    exists fd'. rewrite E at 1. tauto.  
Qed.

Lemma find_some_function_in_untype:
  forall (ge: Genv.t typed_fundef unit)  ros rs fd,
    find_function ge ros rs = Some fd ->
    find_function (untype_genv ge) ros rs = Some (untype_fundef fd).
Proof.
  intros. unfold find_function. destruct ros.
  - cbn in H. pose proof (Genv.find_funct_inv _ _ H) as (b & eq).
    rewrite eq in *. rewrite Genv.find_funct_find_funct_ptr in *.
    now apply find_funct_ptr_in_untyped.
  - cbn in H. rewrite symbols_preserved'. destruct (Genv.find_symbol ge i) eqn:E.
    + rewrite E in H at 1. now apply find_funct_ptr_in_untyped. 
    + rewrite E in H at 1. discriminate.
Qed.

Section Preservation2.

  Variable prog: program.
  Variable tprog: RTL.program.
  Hypothesis TRANSF: match_prog2 prog tprog.
  Let ge := Genv.globalenv prog.  
  Let tge := Genv.globalenv tprog.

  Lemma symbols_preserved3:
    forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof.
    intros s. generalize (Genv.find_symbol_match TRANSF s). auto.
  Qed.

  Lemma symbols_preserved4:
    forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol (untype_genv ge) s.
  Proof.
    intros s. rewrite symbols_preserved3. apply symbols_preserved'.
  Qed.

Lemma find_funct_ptr_preserved:
  forall b f,
    Genv.find_funct_ptr ge b = Some f ->
    Genv.find_funct_ptr tge b = Some (untype_fundef f).
Proof.
  intros. eapply Genv.find_funct_ptr_transf; eauto.
Qed.

Lemma find_funct_ptr_preserved':
  forall b f, Genv.find_funct_ptr (untype_genv ge) b = Some f ->
         Genv.find_funct_ptr tge b = Some f.
Proof.
  intros. apply find_untyped_funct_ptr in H as (f' & eq1 & eq2).
  subst f. now apply find_funct_ptr_preserved.
Qed.

Lemma senv_preserved3:
  Senv.equiv ge tge.
Proof.
  generalize (Genv.senv_match TRANSF). auto.
Qed.

Lemma senv_preserved4:
  Senv.equiv (untype_genv ge) tge.
Proof.
  eapply Senv.equiv_trans.
  - apply Senv.equiv_symmetric. apply senv_preserved'.
  - apply senv_preserved3.
Qed.

Lemma init_mem_preserved_some:
  forall m,
    Genv.init_mem prog = Some m ->
    Genv.init_mem tprog = Some m.
Proof.
   apply (Genv.init_mem_match TRANSF).
Qed.

Lemma step_preserved2:
  forall s1 t s2,
    step ge s1 t s2 ->
    RTL.step tge s1 t s2.
 Proof.
 unfold step. intros. inv H; try now constructor.
 - econstructor; eauto. erewrite eval_operation_preserved; try eassumption.
   apply symbols_preserved4.
  - eapply exec_Iload. exact H0.
    rewrite <- H1. eapply eval_addressing_preserved.
    apply symbols_preserved4.
    auto.
  - eapply exec_Istore. exact H0.
    rewrite <- H1. eapply eval_addressing_preserved.
    apply symbols_preserved4.
    auto.
  - econstructor; eauto. eapply find_some_function_preserved'; try eassumption.
    + symmetry. apply symbols_preserved4.
    + intros. now apply find_funct_ptr_preserved'.
  -  econstructor; eauto.
     eapply find_some_function_preserved' in H1; try eassumption.
     + symmetry. apply symbols_preserved4.
     + apply find_funct_ptr_preserved'.
  - econstructor; eauto.
    + eapply eval_builtin_args_preserved.
      * eapply symbols_preserved4.
      * eassumption.        
    + eapply external_call_symbols_preserved; try eassumption.
      apply senv_preserved4.
  - eapply exec_Icond; eauto.
  - eapply exec_Ijumptable; eauto. 
  - econstructor; eauto. eapply external_call_symbols_preserved; try eassumption.
    apply senv_preserved4.
Qed.

End Preservation2.

Lemma step_untype_preserved:
  forall prog s1 t s2,
    step (Genv.globalenv prog) s1 t s2 ->
    RTL.step (Genv.globalenv (transform_program untype_fundef prog)) s1 t s2.
Proof.
  intros. eapply step_preserved2; eauto. apply untype_program_match; auto.
Qed.  

Lemma some_init_mem_preserved_to_untype:
  forall (prog: program) m,
    Genv.init_mem prog = Some m ->
    Genv.init_mem (transform_program untype_fundef prog) = Some m.
Proof.
  intros. eapply init_mem_preserved_some; eauto. apply untype_program_match. reflexivity.
Qed.

Lemma find_some_funct_ptr_preserved_to_untype:
  forall (prog: program) f b,
    Genv.find_funct_ptr (Genv.globalenv prog) b = Some f ->
    Genv.find_funct_ptr (Genv.globalenv (transform_program untype_fundef prog)) b = Some (untype_fundef f).
Proof.
  intros. eapply find_funct_ptr_preserved; eauto. apply untype_program_match. reflexivity.
Qed.   
