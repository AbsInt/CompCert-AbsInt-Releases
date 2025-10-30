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

(** Correctness of instruction selection for integer division *)

From Coq Require Import String.
Require Import Coqlib Maps.
Require Import AST Errors Integers Floats.
Require Import Values Memory Globalenvs Builtins Events Cminor Op CminorSel.
Require Import SelectOp SelectOpproof SplitLong.

Local Open Scope cminorsel_scope.
Local Open Scope string_scope.

(** * Properties of the helper functions *)

Definition helper_declared {F V: Type} (p: AST.program (AST.fundef F) V) (id: ident) (name: string) (sg: signature) : Prop :=
  (prog_defmap p)!id = Some (Gfun (External (EF_runtime name sg))).

Definition helper_functions_declared {F V: Type} (p: AST.program (AST.fundef F) V) (hf: helper_functions) : Prop :=
     helper_declared p i64_ftos "__compcert_i64_ftos" sig_s_l
  /\ helper_declared p i64_ftou "__compcert_i64_ftou" sig_s_l
  /\ helper_declared p i64_dtos "__compcert_i64_dtos" sig_f_l
  /\ helper_declared p i64_dtou "__compcert_i64_dtou" sig_f_l
  /\ helper_declared p i64_stod "__compcert_i64_stod" sig_l_f
  /\ helper_declared p i64_utod "__compcert_i64_utod" sig_l_f
  /\ helper_declared p i64_stof "__compcert_i64_stof" sig_l_s
  /\ helper_declared p i64_utof "__compcert_i64_utof" sig_l_s
  /\ helper_declared p i64_sdiv "__compcert_i64_sdiv" sig_ll_l
  /\ helper_declared p i64_udiv "__compcert_i64_udiv" sig_ll_l
  /\ helper_declared p i64_smod "__compcert_i64_smod" sig_ll_l
  /\ helper_declared p i64_umod "__compcert_i64_umod" sig_ll_l
  /\ helper_declared p i64_shl "__compcert_i64_shl" sig_li_l
  /\ helper_declared p i64_shr "__compcert_i64_shr" sig_li_l
  /\ helper_declared p i64_sar "__compcert_i64_sar" sig_li_l
  /\ helper_declared p i64_umulh "__compcert_i64_umulh" sig_ll_l
  /\ helper_declared p i64_smulh "__compcert_i64_smulh" sig_ll_l.

(** * Correctness of the instruction selection functions for 64-bit operators *)

Section CMCONSTR.

Variable prog: program.
Variable hf: helper_functions.
Hypothesis HELPERS: helper_functions_declared prog hf.
Let ge := Genv.globalenv prog.
Variable sp: val.
Variable e: env.
Variable m: mem.

Ltac DeclHelper := red in HELPERS; decompose [Logic.and] HELPERS; eauto.

Lemma eval_helper:
  forall bf le id name sg args vargs vres,
  eval_exprlist ge sp e m le args vargs ->
  helper_declared prog id name sg  ->
  lookup_builtin_function name sg = Some bf ->
  builtin_function_sem bf vargs = Some vres ->
  eval_expr ge sp e m le (Eexternal id sg args) vres.
Proof.
  intros.
  red in H0. apply Genv.find_def_symbol in H0. destruct H0 as (b & P & Q).
  rewrite <- Genv.find_funct_ptr_iff in Q.
  econstructor; eauto. 
  simpl. red. rewrite H1. constructor; auto.
Qed.

Corollary eval_helper_1:
  forall bf le id name sg arg1 varg1 vres,
  eval_expr ge sp e m le arg1 varg1 ->
  helper_declared prog id name sg  ->
  lookup_builtin_function name sg = Some bf ->
  builtin_function_sem bf (varg1 :: nil) = Some vres ->
  eval_expr ge sp e m le (Eexternal id sg (arg1 ::: Enil)) vres.
Proof.
  intros. eapply eval_helper; eauto. constructor; auto. constructor.
Qed.

Corollary eval_helper_2:
  forall bf le id name sg arg1 arg2 varg1 varg2 vres,
  eval_expr ge sp e m le arg1 varg1 ->
  eval_expr ge sp e m le arg2 varg2 ->
  helper_declared prog id name sg  ->
  lookup_builtin_function name sg = Some bf ->
  builtin_function_sem bf (varg1 :: varg2 :: nil) = Some vres ->
  eval_expr ge sp e m le (Eexternal id sg (arg1 ::: arg2 ::: Enil)) vres.
Proof.
  intros. eapply eval_helper; eauto. constructor; auto. constructor; auto. constructor.
Qed.

Remark eval_builtin_1:
  forall bf le id sg arg1 varg1 vres,
  eval_expr ge sp e m le arg1 varg1 ->
  lookup_builtin_function id sg = Some bf ->
  builtin_function_sem bf (varg1 :: nil) = Some vres ->
  eval_expr ge sp e m le (Ebuiltin (EF_builtin id sg) (arg1 ::: Enil)) vres.
Proof.
  intros. econstructor. econstructor. eauto. constructor.
  simpl. red. rewrite H0. constructor. auto.
Qed.

Remark eval_builtin_2:
  forall bf le id sg arg1 arg2 varg1 varg2 vres,
  eval_expr ge sp e m le arg1 varg1 ->
  eval_expr ge sp e m le arg2 varg2 ->
  lookup_builtin_function id sg = Some bf ->
  builtin_function_sem bf (varg1 :: varg2 :: nil) = Some vres ->
  eval_expr ge sp e m le (Ebuiltin (EF_builtin id sg) (arg1 ::: arg2 ::: Enil)) vres.
Proof.
  intros. econstructor. constructor; eauto. constructor; eauto. constructor.
  simpl. red. rewrite H1. constructor. auto.
Qed.

Definition unary_constructor_sound (cstr: expr -> expr) (sem: val -> val) : Prop :=
  forall le a x,
  eval_expr ge sp e m le a x ->
  exists v, eval_expr ge sp e m le (cstr a) v /\ Val.lessdef (sem x) v.

Definition binary_constructor_sound (cstr: expr -> expr -> expr) (sem: val -> val -> val) : Prop :=
  forall le a x b y,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  exists v, eval_expr ge sp e m le (cstr a b) v /\ Val.lessdef (sem x y) v.

Ltac EvalOp :=
  eauto;
  match goal with
  | [ |- eval_exprlist _ _ _ _ _ Enil _ ] => constructor
  | [ |- eval_exprlist _ _ _ _ _ (_:::_) _ ] => econstructor; EvalOp
  | [ |- eval_expr _ _ _ _ _ (Eletvar _) _ ] => constructor; simpl; eauto
  | [ |- eval_expr _ _ _ _ _ (Elet _ _) _ ] => econstructor; EvalOp
  | [ |- eval_expr _ _ _ _ _ (lift _) _ ] => apply eval_lift; EvalOp
  | [ |- eval_expr _ _ _ _ _ _ _ ] => eapply eval_Eop; [EvalOp | simpl; eauto]
  | _ => idtac
  end.

Lemma eval_splitlong:
  forall le a f v sem,
  (forall le a b x y,
   eval_expr ge sp e m le a x ->
   eval_expr ge sp e m le b y ->
   exists v, eval_expr ge sp e m le (f a b) v /\
             (forall p q, x = Vint p -> y = Vint q -> v = sem (Vlong (Int64.ofwords p q)))) ->
  match v with Vlong _ => True | _ => sem v = Vundef end ->
  eval_expr ge sp e m le a v ->
  exists v', eval_expr ge sp e m le (splitlong a f) v' /\ Val.lessdef (sem v) v'.
Proof.
  intros until sem; intros EXEC UNDEF.
  unfold splitlong. case (splitlong_match a); intros.
- InvEval; subst.
  exploit EXEC. eexact H2. eexact H3. intros [v' [A B]].
  exists v'; split. auto.
  destruct v1; simpl in *; try (rewrite UNDEF; auto).
  destruct v0; simpl in *; try (rewrite UNDEF; auto).
  erewrite B; eauto.
- exploit (EXEC (v :: le) (Eop Ohighlong (Eletvar 0 ::: Enil)) (Eop Olowlong (Eletvar 0 ::: Enil))).
  EvalOp. EvalOp.
  intros [v' [A B]].
  exists v'; split. econstructor; eauto.
  destruct v; try (rewrite UNDEF; auto). erewrite B; simpl; eauto. rewrite Int64.ofwords_recompose. auto.
Qed.

Lemma eval_splitlong_strict:
  forall le a f va v,
  eval_expr ge sp e m le a (Vlong va) ->
  (forall le a1 a2,
     eval_expr ge sp e m le a1 (Vint (Int64.hiword va)) ->
     eval_expr ge sp e m le a2 (Vint (Int64.loword va)) ->
     eval_expr ge sp e m le (f a1 a2) v) ->
  eval_expr ge sp e m le (splitlong a f) v.
Proof.
  intros until v.
  unfold splitlong. case (splitlong_match a); intros.
- InvEval. destruct v1; simpl in H; try discriminate. destruct v0; inv H.
  apply H0. rewrite Int64.hi_ofwords; auto. rewrite Int64.lo_ofwords; auto.
- EvalOp. apply H0; EvalOp.
Qed.

Lemma eval_splitlong2:
  forall le a b f va vb sem,
  (forall le a1 a2 b1 b2 x1 x2 y1 y2,
   eval_expr ge sp e m le a1 x1 ->
   eval_expr ge sp e m le a2 x2 ->
   eval_expr ge sp e m le b1 y1 ->
   eval_expr ge sp e m le b2 y2 ->
   exists v,
     eval_expr ge sp e m le (f a1 a2 b1 b2) v /\
     (forall p1 p2 q1 q2,
       x1 = Vint p1 -> x2 = Vint p2 -> y1 = Vint q1 -> y2 = Vint q2 ->
       v = sem (Vlong (Int64.ofwords p1 p2)) (Vlong (Int64.ofwords q1 q2)))) ->
  match va, vb with Vlong _, Vlong _ => True | _, _ => sem va vb = Vundef end ->
  eval_expr ge sp e m le a va ->
  eval_expr ge sp e m le b vb ->
  exists v, eval_expr ge sp e m le (splitlong2 a b f) v /\ Val.lessdef (sem va vb) v.
Proof.
  intros until sem; intros EXEC UNDEF.
  unfold splitlong2. case (splitlong2_match a b); intros.
- InvEval; subst.
  exploit (EXEC le h1 l1 h2 l2); eauto. intros [v [A B]].
  exists v; split; auto.
  destruct v1; simpl in *; try (rewrite UNDEF; auto).
  destruct v0; try (rewrite UNDEF; auto).
  destruct v2; simpl in *; try (rewrite UNDEF; auto).
  destruct v3; try (rewrite UNDEF; auto).
  erewrite B; eauto.
- InvEval; subst.
  exploit (EXEC (vb :: le) (lift h1) (lift l1)
                (Eop Ohighlong (Eletvar 0 ::: Enil)) (Eop Olowlong (Eletvar 0 ::: Enil))).
  EvalOp. EvalOp. EvalOp. EvalOp.
  intros [v [A B]].
  exists v; split.
  econstructor; eauto.
  destruct v1; simpl in *; try (rewrite UNDEF; auto).
  destruct v0; try (rewrite UNDEF; auto).
  destruct vb; try (rewrite UNDEF; auto).
  erewrite B; simpl; eauto. rewrite Int64.ofwords_recompose. auto.
- InvEval; subst.
  exploit (EXEC (va :: le)
                (Eop Ohighlong (Eletvar 0 ::: Enil)) (Eop Olowlong (Eletvar 0 ::: Enil))
                (lift h2) (lift l2)).
  EvalOp. EvalOp. EvalOp. EvalOp.
  intros [v [A B]].
  exists v; split.
  econstructor; eauto.
  destruct va; try (rewrite UNDEF; auto).
  destruct v1; simpl in *; try (rewrite UNDEF; auto).
  destruct v0; try (rewrite UNDEF; auto).
  erewrite B; simpl; eauto. rewrite Int64.ofwords_recompose. auto.
- exploit (EXEC (vb :: va :: le)
                (Eop Ohighlong (Eletvar 1 ::: Enil)) (Eop Olowlong (Eletvar 1 ::: Enil))
                (Eop Ohighlong (Eletvar 0 ::: Enil)) (Eop Olowlong (Eletvar 0 ::: Enil))).
  EvalOp. EvalOp. EvalOp. EvalOp.
  intros [v [A B]].
  exists v; split. EvalOp.
  destruct va; try (rewrite UNDEF; auto); destruct vb; try (rewrite UNDEF; auto).
  erewrite B; simpl; eauto. rewrite ! Int64.ofwords_recompose; auto.
Qed.

Lemma eval_splitlong2_strict:
  forall le a b f va vb v,
  eval_expr ge sp e m le a (Vlong va) ->
  eval_expr ge sp e m le b (Vlong vb) ->
  (forall le a1 a2 b1 b2,
     eval_expr ge sp e m le a1 (Vint (Int64.hiword va)) ->
     eval_expr ge sp e m le a2 (Vint (Int64.loword va)) ->
     eval_expr ge sp e m le b1 (Vint (Int64.hiword vb)) ->
     eval_expr ge sp e m le b2 (Vint (Int64.loword vb)) ->
     eval_expr ge sp e m le (f a1 a2 b1 b2) v) ->
  eval_expr ge sp e m le (splitlong2 a b f) v.
Proof.
  assert (INV: forall v1 v2 n,
    Val.longofwords v1 v2 = Vlong n -> v1 = Vint(Int64.hiword n) /\ v2 = Vint(Int64.loword n)).
  {
    intros. destruct v1; simpl in H; try discriminate. destruct v2; inv H.
    rewrite Int64.hi_ofwords; rewrite Int64.lo_ofwords; auto.
  }
  intros until v.
  unfold splitlong2. case (splitlong2_match a b); intros.
- InvEval. exploit INV. eexact H. intros [EQ1 EQ2]. exploit INV. eexact H0. intros [EQ3 EQ4].
  subst. auto.
- InvEval. exploit INV; eauto. intros [EQ1 EQ2]. subst.
  econstructor. eauto. apply H1; EvalOp.
- InvEval. exploit INV; eauto. intros [EQ1 EQ2]. subst.
  econstructor. eauto. apply H1; EvalOp.
- EvalOp. apply H1; EvalOp.
Qed.

Lemma is_longconst_sound:
  forall le a x n,
  is_longconst a = Some n ->
  eval_expr ge sp e m le a x ->
  x = Vlong n.
Proof.
  unfold is_longconst; intros until n; intros LC.
  destruct (is_longconst_match a); intros.
  inv LC. InvEval. simpl in H5. inv H5. auto.
  discriminate.
Qed.

Lemma is_longconst_zero_sound:
  forall le a x,
  is_longconst_zero a = true ->
  eval_expr ge sp e m le a x ->
  x = Vlong Int64.zero.
Proof.
  unfold is_longconst_zero; intros.
  destruct (is_longconst a) as [n|] eqn:E; try discriminate.
  revert H. predSpec Int64.eq Int64.eq_spec n Int64.zero.
  intros. subst. eapply is_longconst_sound; eauto.
  congruence.
Qed.

Lemma eval_lowlong: unary_constructor_sound lowlong Val.lowordoflong.
Proof.
  unfold lowlong; red. intros until x. destruct (lowlong_match a); intros.
  InvEval; subst. exists v0; split; auto.
  destruct v1; simpl; auto. destruct v0; simpl; auto.
  rewrite Int64.lo_ofwords. auto.
  exists (Val.lowordoflong x); split; auto. EvalOp.
Qed.

Lemma eval_highlong: unary_constructor_sound highlong Val.hiwordoflong.
Proof.
  unfold highlong; red. intros until x. destruct (highlong_match a); intros.
  InvEval; subst. exists v1; split; auto.
  destruct v1; simpl; auto. destruct v0; simpl; auto.
  rewrite Int64.hi_ofwords. auto.
  exists (Val.hiwordoflong x); split; auto. EvalOp.
Qed.

Lemma eval_longconst:
  forall le n, eval_expr ge sp e m le (longconst n) (Vlong n).
Proof.
  intros. EvalOp. rewrite Int64.ofwords_recompose; auto.
Qed.

Theorem eval_intoflong: unary_constructor_sound intoflong Val.lowordoflong.
Proof eval_lowlong.

Theorem eval_longofintu: unary_constructor_sound longofintu Val.longofintu.
Proof.
  red; intros. unfold longofintu. econstructor; split. EvalOp.
  unfold Val.longofintu. destruct x; auto.
  replace (Int64.repr (Int.unsigned i)) with (Int64.ofwords Int.zero i); auto.
  apply Int64.same_bits_eq; intros.
  rewrite Int64.testbit_repr by auto.
  rewrite Int64.bits_ofwords by auto.
  fold (Int.testbit i i0).
  destruct (zlt i0 Int.zwordsize).
  auto.
  rewrite Int.bits_zero. rewrite Int.bits_above by lia. auto.
Qed.

Theorem eval_longofint: unary_constructor_sound longofint Val.longofint.
Proof.
  red; intros. unfold longofint. destruct (longofint_match a).
- InvEval. econstructor; split. apply eval_longconst. auto.
- exploit (eval_shrimm ge sp e m (Int.repr 31) (x :: le) (Eletvar 0)). EvalOp.
  intros [v1 [A B]].
  econstructor; split. EvalOp.
  destruct x; simpl; auto.
  simpl in B. inv B. simpl.
  replace (Int64.repr (Int.signed i))
     with (Int64.ofwords (Int.shr i (Int.repr 31)) i); auto.
  apply Int64.same_bits_eq; intros.
  rewrite Int64.testbit_repr by auto.
  rewrite Int64.bits_ofwords by auto.
  rewrite Int.bits_signed by lia.
  destruct (zlt i0 Int.zwordsize).
  auto.
  assert (Int64.zwordsize = 2 * Int.zwordsize) by reflexivity.
  rewrite Int.bits_shr by lia.
  change (Int.unsigned (Int.repr 31)) with (Int.zwordsize - 1).
  f_equal. destruct (zlt (i0 - Int.zwordsize + (Int.zwordsize - 1)) Int.zwordsize); lia.
Qed.

Theorem eval_negl: unary_constructor_sound negl Val.negl.
Proof.
  unfold negl; red; intros. destruct (is_longconst a) eqn:E.
- econstructor; split. apply eval_longconst.
  exploit is_longconst_sound; eauto. intros EQ; subst x. simpl. auto.
- destruct (platform_standard_builtin BI_negl (a ::: Enil)) eqn:SEL.
  eapply eval_platform_standard_builtin; eauto. econstructor; eauto.
  econstructor; eauto. reflexivity.
  exists (Val.negl x); split; auto.
  eapply (eval_builtin_1 (BI_standard BI_negl)); eauto.
Qed.

Theorem eval_notl: unary_constructor_sound notl Val.notl.
Proof.
  red; intros. unfold notl. apply eval_splitlong; auto.
  intros.
  exploit eval_notint. eexact H0. intros [va [A B]].
  exploit eval_notint. eexact H1. intros [vb [C D]].
  exists (Val.longofwords va vb); split. EvalOp.
  intros; subst. simpl in *. inv B; inv D.
  simpl. unfold Int.not. rewrite <- Int64.decompose_xor. auto.
  destruct x; auto.
Qed.

Theorem eval_andl: binary_constructor_sound andl Val.andl.
Proof.
  red; intros. unfold andl. apply eval_splitlong2; auto.
  intros.
  exploit eval_and. eexact H1. eexact H3. intros [va [A B]].
  exploit eval_and. eexact H2. eexact H4. intros [vb [C D]].
  exists (Val.longofwords va vb); split. EvalOp.
  intros; subst. simpl in B; inv B. simpl in D; inv D.
  simpl. f_equal. rewrite Int64.decompose_and. auto.
  destruct x; auto. destruct y; auto.
Qed.

Theorem eval_orl: binary_constructor_sound orl Val.orl.
Proof.
  red; intros. unfold orl. apply eval_splitlong2; auto.
  intros.
  exploit eval_or. eexact H1. eexact H3. intros [va [A B]].
  exploit eval_or. eexact H2. eexact H4. intros [vb [C D]].
  exists (Val.longofwords va vb); split. EvalOp.
  intros; subst. simpl in B; inv B. simpl in D; inv D.
  simpl. f_equal. rewrite Int64.decompose_or. auto.
  destruct x; auto. destruct y; auto.
Qed.

Theorem eval_xorl: binary_constructor_sound xorl Val.xorl.
Proof.
  red; intros. unfold xorl. apply eval_splitlong2; auto.
  intros.
  exploit eval_xor. eexact H1. eexact H3. intros [va [A B]].
  exploit eval_xor. eexact H2. eexact H4. intros [vb [C D]].
  exists (Val.longofwords va vb); split. EvalOp.
  intros; subst. simpl in B; inv B. simpl in D; inv D.
  simpl. f_equal. rewrite Int64.decompose_xor. auto.
  destruct x; auto. destruct y; auto.
Qed.

Lemma is_intconst_sound:
  forall le a x n,
  is_intconst a = Some n ->
  eval_expr ge sp e m le a x ->
  x = Vint n.
Proof.
  unfold is_intconst; intros until n; intros LC.
  destruct a; try discriminate. destruct o; try discriminate. destruct e0; try discriminate.
  inv LC. intros. InvEval. auto.
Qed.

Remark eval_shift_imm:
  forall (P: expr -> Prop) n a0 a1 a2 a3,
  (n = Int.zero -> P a0) ->
  (0 <= Int.unsigned n < Int.zwordsize ->
   Int.ltu n Int.iwordsize = true ->
   Int.ltu (Int.sub Int.iwordsize n) Int.iwordsize = true ->
   Int.ltu n Int64.iwordsize' = true ->
   P a1) ->
  (Int.zwordsize <= Int.unsigned n < Int64.zwordsize ->
   Int.ltu (Int.sub n Int.iwordsize) Int.iwordsize = true ->
   P a2) ->
  P a3 ->
  P (if Int.eq n Int.zero then a0
     else if Int.ltu n Int.iwordsize then a1
     else if Int.ltu n Int64.iwordsize' then a2
     else a3).
Proof.
  intros until a3; intros A0 A1 A2 A3.
  predSpec Int.eq Int.eq_spec n Int.zero.
  apply A0; auto.
  assert (NZ: Int.unsigned n <> 0).
  { red; intros. elim H. rewrite <- (Int.repr_unsigned n). rewrite H0. auto. }
  destruct (Int.ltu n Int.iwordsize) eqn:LT.
  exploit Int.ltu_iwordsize_inv; eauto. intros RANGE.
  assert (0 <= Int.zwordsize - Int.unsigned n < Int.zwordsize) by lia.
  apply A1. auto. auto.
  unfold Int.ltu, Int.sub. rewrite Int.unsigned_repr_wordsize.
  rewrite Int.unsigned_repr. rewrite zlt_true; auto. lia.
  generalize Int.wordsize_max_unsigned; lia.
  unfold Int.ltu. rewrite zlt_true; auto.
  change (Int.unsigned Int64.iwordsize') with 64.
  change Int.zwordsize with 32 in RANGE. lia.
  destruct (Int.ltu n Int64.iwordsize') eqn:LT'.
  exploit Int.ltu_inv; eauto.
  change (Int.unsigned Int64.iwordsize') with (Int.zwordsize * 2).
  intros RANGE.
  assert (Int.zwordsize <= Int.unsigned n).
    unfold Int.ltu in LT. rewrite Int.unsigned_repr_wordsize in LT.
    destruct (zlt (Int.unsigned n) Int.zwordsize). discriminate. lia.
  apply A2. tauto. unfold Int.ltu, Int.sub. rewrite Int.unsigned_repr_wordsize.
  rewrite Int.unsigned_repr. rewrite zlt_true; auto. lia.
  generalize Int.wordsize_max_unsigned; lia.
  auto.
Qed.

Remark select_int_supported: select_supported Tint = true.
Proof. reflexivity. Qed.

Remark select_long_unsupported: select_supported Tlong = false -> Archi.ptr64 = false.
Proof.
  unfold select_supported; intros; auto; congruence.
Qed.

Theorem eval_select_long:
  forall le cond al vl a1 v1 a2 v2,
  eval_exprlist ge sp e m le al vl ->
  eval_expr ge sp e m le a1 v1 ->
  eval_expr ge sp e m le a2 v2 ->
  exists v,
     eval_expr ge sp e m le (select_long cond al a1 a2) v
  /\ Val.lessdef (Val.select (eval_condition cond vl m) v1 v2 Tlong) v.
Proof.
  unfold select_long; intros. destruct (select_supported Tlong) eqn:SUP.
- eapply eval_select; eauto.
- assert (NOT64: Archi.ptr64 = false) by auto using select_long_unsupported.
  assert (AUX: forall v vhi vlo,
      Val.lessdef (Val.normalize (Val.hiwordoflong v) Tint) vhi ->
      Val.lessdef (Val.normalize (Val.lowordoflong v) Tint) vlo ->
      Val.lessdef (Val.normalize v Tlong) (Val.longofwords vhi vlo)).
  { intros. unfold Val.normalize. rewrite NOT64. destruct v; auto.
    simpl in *. inv H2; inv H3. simpl. rewrite Int64.ofwords_recompose. auto. }
  eapply eval_bind_exprs_gen with (P := Val.lessdef (Val.select (eval_condition cond vl m) v1 v2 Tlong)); eauto using eval_exprlist.
  intros args EV. set (le' := app (rev (v1 :: v2 :: vl)) le) in *.
  inv EV. inv H7. rename a0 into b1. rename a3 into b2. rename al1 into bl.
  exploit eval_select.
    apply select_int_supported.
    eexact H9.
    eapply eval_Eop with (op := Ohighlong) (al := b1 ::: Enil); eauto using eval_exprlist. simpl; eauto.
    eapply eval_Eop with (op := Ohighlong) (al := b2 ::: Enil); eauto using eval_exprlist. simpl; eauto.
  intros (vhi & EHI & LHI).
  exploit eval_select.
    apply select_int_supported.
    eexact H9.
    eapply eval_Eop with (op := Olowlong) (al := b1 ::: Enil); eauto using eval_exprlist. simpl; eauto.
    eapply eval_Eop with (op := Olowlong) (al := b2 ::: Enil); eauto using eval_exprlist. simpl; eauto.
  intros (vlo & ELO & LLO).
  exists (Val.longofwords vhi vlo); split.
  eapply eval_Eop; eauto using eval_exprlist.
  destruct (eval_condition cond vl m) as [b|]; simpl in *; auto.
  destruct b; apply AUX; auto.
Qed.

Lemma eval_select_shift:
  forall le a b f_low f_high va vb base sem,
  (forall le a1 a2 b x1 x2 y,
   eval_expr ge sp e m le a1 x1 ->
   eval_expr ge sp e m le a2 x2 ->
   eval_expr ge sp e m le b y ->
   exists v,
     eval_expr ge sp e m le (f_low a1 a2 b) v /\
     (forall p1 p2 q,
       0 <= Int.unsigned q < Int.zwordsize ->
       Int.ltu q Int.iwordsize = true ->
       Int.ltu (Int.sub Int.iwordsize q) Int.iwordsize = true ->
       Int.ltu q Int64.iwordsize' = true ->
       x1 = Vint p1 -> x2 = Vint p2 -> y = Vint q ->
       v = sem (Vlong (Int64.ofwords p1 p2)) (Vint q))) ->
  (forall le a1 a2 b x1 x2 y,
   eval_expr ge sp e m le a1 x1 ->
   eval_expr ge sp e m le a2 x2 ->
   eval_expr ge sp e m le b y ->
   exists v,
     eval_expr ge sp e m le (f_high a1 a2 b) v /\
     (forall p1 p2 q,
       Int.zwordsize <= Int.unsigned q < Int64.zwordsize ->
       Int.ltu (Int.sub q Int.iwordsize) Int.iwordsize = true ->
       x1 = Vint p1 -> x2 = Vint p2 -> y = Vint q ->
       v = sem (Vlong (Int64.ofwords p1 p2)) (Vint q))) ->
  (exists v, eval_expr ge sp e m le base v /\ Val.lessdef (sem va vb) v) ->
  match va, vb with Vlong _, Vint i => if Int.ltu i Int64.iwordsize' then exists v, sem va vb = Vlong v else sem va vb = Vundef | _, _ => sem va vb = Vundef end ->
  (forall l, sem (Vlong l) Vzero = Vlong l) ->
  eval_expr ge sp e m le a va ->
  eval_expr ge sp e m le b vb ->
  exists v, eval_expr ge sp e m le (select_shift a b base f_low f_high) v /\ Val.lessdef (sem va vb) v.
Proof.
  unfold select_shift. intros.
  destruct Compopts.inlined_runtime; [|eexact H1].
  assert (Val.normalize (sem va vb) Tlong = sem va vb).
  { destruct va, vb; try rewrite H2; auto. destruct (Int.ltu i0 Int64.iwordsize').
    destruct H2; rewrite H2; auto. rewrite H2. auto.
  }
  exploit eval_lowlong. eexact H4. intros [v1 [A1 B1]].
  exploit eval_highlong. eexact H4. intros [v2 [A2 B2]].
  exploit H. eexact A2. eexact A1. eexact H5. intros [v3 [A3 B3]].
  exploit H0. eexact A2. eexact A1. eexact H5. intros [v4 [A4 B4]].
  exploit eval_select_long. instantiate (2 := (b ::: Eop (Ointconst Int.iwordsize) Enil ::: Enil)). EvalOp.
  eexact A3. eexact A4. instantiate (1 := (Ccompu Clt)). intros [v5 [A5 B5]].
  exploit eval_select_long. instantiate (2 := (b ::: Eop (Ointconst Int.zero) Enil ::: Enil)). EvalOp. eexact H4. eexact A5. intros [v6 [A6 B6]].
  exists v6; split. EvalOp.
  destruct va; try rewrite H2; auto. simpl in *. inv B1. inv B2. destruct vb; try rewrite H2; auto. simpl in *.
  predSpec Int.eq Int.eq_spec i0 Int.zero. rewrite H7 in B6.
  inv B6; auto. rewrite H3. auto.
  rewrite Int.eq_false in B6 by auto.
  assert (NZ: Int.unsigned i0 <> 0).
  { red; intros. elim H7. rewrite <- (Int.repr_unsigned i0). rewrite H8. auto. }
  destruct (Int.ltu i0 Int.iwordsize) eqn:?. generalize (Int.ltu_inv i0 Int.iwordsize Heqb0).
  rewrite Int.unsigned_repr_wordsize. intros.
  rewrite (B3 (Int64.hiword i) (Int64.loword i) i0) in B5; auto.
  rewrite Int64.ofwords_recompose in B5.
  rewrite H6 in B5.
  inv B5; auto. rewrite H6 in B6. auto.
  unfold Int.ltu. apply zlt_true; auto. unfold Int.sub. rewrite Int.unsigned_repr_wordsize.
  rewrite Int.unsigned_repr; auto.  generalize Int.wordsize_pos. lia.
  generalize Int.wordsize_max_unsigned. lia.
  unfold Int.ltu. change (Int.unsigned Int64.iwordsize') with (2 * Int.zwordsize).
  apply zlt_true. generalize Int.wordsize_pos. lia.
  destruct (Int.ltu i0 Int64.iwordsize') eqn:?; try rewrite H2; auto.
  assert (Int.zwordsize <= Int.unsigned i0).
  { unfold Int.ltu in Heqb0. rewrite Int.unsigned_repr_wordsize in Heqb0.
    destruct (zlt (Int.unsigned i0) Int.zwordsize). discriminate. lia. }
  exploit Int.ltu_inv. eexact Heqb1. intros.
  rewrite (B4 (Int64.hiword i) (Int64.loword i) i0) in B5; auto; try lia.
  rewrite Int64.ofwords_recompose in B5. rewrite H6 in B5. inv B5; auto.
  rewrite H6 in B6. auto.
  change (Int.unsigned Int64.iwordsize') with Int64.zwordsize in H9.
  lia.
  unfold Int.ltu, Int.sub. rewrite Int.unsigned_repr_wordsize.
  change (Int.unsigned Int64.iwordsize') with (2 * Int.zwordsize) in H9.
  rewrite Int.unsigned_repr. rewrite zlt_true; auto. lia.
  generalize Int.wordsize_max_unsigned; lia.
Qed.

Theorem eval_shll_base_small:
  forall le a1 a2 b x1 x2 y,
    eval_expr ge sp e m le a1 x1 ->
    eval_expr ge sp e m le a2 x2 ->
    eval_expr ge sp e m le b y ->
   exists v,
     eval_expr ge sp e m le (shll_base_small a1 a2 b) v /\
     (forall p1 p2 q,
       0 <= Int.unsigned q < Int.zwordsize ->
       Int.ltu q Int.iwordsize = true ->
       Int.ltu (Int.sub Int.iwordsize q) Int.iwordsize = true ->
       Int.ltu q Int64.iwordsize' = true ->
       x1 = Vint p1 -> x2 = Vint p2 -> y = Vint q ->
       v = Val.shll (Vlong (Int64.ofwords p1 p2)) (Vint q)).
Proof.
  unfold shll_base_small. intros. simpl.
    exploit eval_shl. eexact H0. eexact H1. intros [v1 [A1 B1]].
    exploit (eval_sub ge sp e m le (Eop (Ointconst Int.iwordsize) Enil)). EvalOp. eexact H1.
    intros [v2 [A2 B2]].
    exploit eval_shru. eexact H0. eexact A2. intros [v3 [A3 B3]].
    exploit eval_shl. eexact H. eexact H1. intros [v4 [A4 B4]].
    exploit eval_or. eexact A4. eexact A3. intros [v5 [A5 B5]].
    econstructor; split; EvalOp. intros.
    subst x1. subst x2. subst y. simpl in *.
    rewrite H3 in *.  rewrite H5.
    inv B1. inv B2. rewrite H4 in B3. inv B3. inv B4. simpl in *.
    inv B5.  simpl. rewrite Int64.decompose_shl_1 by lia.
    reflexivity.
Qed.

Theorem eval_shll_base: binary_constructor_sound shll_base Val.shll.
Proof.
  unfold shll_base; red; intros.
  eapply eval_select_shift; eauto.
  - eapply eval_shll_base_small.
  - intros. simpl.
    exploit eval_addimm. eexact H3. instantiate (1 := Int.neg Int.iwordsize).
    intros [v1 [A1 B1]].
    exploit eval_shl. eexact H2. eexact A1.
    intros [v2 [A2 B2]].
    econstructor; split; EvalOp. intros.
    subst x1. subst x2. subst y0. simpl in *. rewrite <- Int.sub_add_opp in B1.
    inv B1. simpl in B2. rewrite H5 in B2.  inv B2. unfold Int.ltu.
    change (Int.unsigned Int64.iwordsize') with Int64.zwordsize.
    rewrite zlt_true by lia. simpl. rewrite Int64.decompose_shl_2 by lia.
    reflexivity.
  - econstructor; split.
    eapply eval_helper_2; eauto. EvalOp. DeclHelper. reflexivity. reflexivity.
    auto.
  - destruct x; auto. destruct y; auto. unfold Val.shll. destruct (Int.ltu i0 Int64.iwordsize'); eauto.
  - intros. unfold Val.shll. simpl. unfold Int.ltu. rewrite zlt_true. rewrite Int64.shl'_zero.
    reflexivity. rewrite Int.unsigned_zero. change (Int.unsigned Int64.iwordsize') with 64. lia.
Qed.

Lemma eval_shllimm:
  forall n,
  unary_constructor_sound (fun e => shllimm e n) (fun v => Val.shll v (Vint n)).
Proof.
  unfold shllimm; red; intros.
  apply eval_shift_imm; intros.
  + (* n = 0 *)
    subst n. exists x; split; auto. destruct x; simpl; auto.
    change (Int64.shl' i Int.zero) with (Int64.shl i Int64.zero).
    rewrite Int64.shl_zero. auto.
  + (* 0 < n < 32 *)
    apply eval_splitlong with (sem := fun x => Val.shll x (Vint n)); auto.
    intros.
    exploit eval_shlimm. eexact H4. instantiate (1 := n). intros [v1 [A1 B1]].
    exploit eval_shlimm. eexact H5. instantiate (1 := n). intros [v2 [A2 B2]].
    exploit eval_shruimm. eexact H5. instantiate (1 := Int.sub Int.iwordsize n). intros [v3 [A3 B3]].
    exploit eval_or. eexact A1. eexact A3. intros [v4 [A4 B4]].
    econstructor; split. EvalOp.
    intros. subst. simpl in *. rewrite H1 in *. rewrite H2 in *. rewrite H3.
    inv B1; inv B2; inv B3. simpl in B4. inv B4.
    simpl. rewrite Int64.decompose_shl_1; auto.
    destruct x; auto.
  + (* 32 <= n < 64 *)
    exploit eval_lowlong. eexact H. intros [v1 [A1 B1]].
    exploit eval_shlimm. eexact A1. instantiate (1 := Int.sub n Int.iwordsize). intros [v2 [A2 B2]].
    econstructor; split. EvalOp.
    destruct x; simpl; auto.
    destruct (Int.ltu n Int64.iwordsize'); auto.
    simpl in B1; inv B1. simpl in B2. rewrite H1 in B2. inv B2.
    simpl. erewrite <- Int64.decompose_shl_2. instantiate (1 := Int64.hiword i).
    rewrite Int64.ofwords_recompose. auto. auto.
  + (* n >= 64 *)
    eapply eval_shll_base; eauto. EvalOp.
Qed.

Theorem eval_shll: binary_constructor_sound shll Val.shll.
Proof.
  unfold shll; red; intros.
  destruct (is_intconst b) as [n|] eqn:IC.
- (* Immediate *)
  exploit is_intconst_sound; eauto. intros EQ; subst y; clear H0.
  eapply eval_shllimm; eauto.
- (* General case *)
  eapply eval_shll_base; eauto.
Qed.

Theorem eval_shrlu_base: binary_constructor_sound shrlu_base Val.shrlu.
Proof.
  unfold shrlu_base; red; intros.
  eapply eval_select_shift; eauto.
  - intros. simpl.
    exploit eval_shru. eexact H1. eexact H3. intros [v1 [A1 B1]].
    exploit (eval_sub ge sp e m le0 (Eop (Ointconst Int.iwordsize) Enil)). EvalOp. eexact H3.
    intros [v2 [A2 B2]].
    exploit eval_shl. eexact H1. eexact A2. intros [v3 [A3 B3]].
    exploit eval_shru. eexact H2. eexact H3. intros [v4 [A4 B4]].
    exploit eval_or. eexact A4. eexact A3. intros [v5 [A5 B5]].
    econstructor; split; EvalOp. intros.
    subst x1. subst x2. subst y0. simpl in *.
    rewrite H5 in *. inv B1. inv B2. rewrite H7. rewrite H6 in *. inv B3. inv B4.
    inv B5.  simpl. rewrite Int64.decompose_shru_1 by lia.
    reflexivity.
  - intros. simpl.
    exploit eval_addimm. eexact H3. instantiate (1 := Int.neg Int.iwordsize).
    intros [v1 [A1 B1]].
    exploit eval_shru. eexact H1. eexact A1.
    intros [v2 [A2 B2]].
    econstructor; split; EvalOp. intros.
    subst x1. subst x2. subst y0. simpl in *. rewrite <- Int.sub_add_opp in B1.
    inv B1. rewrite H5 in B2. inv B2. unfold Int.ltu.
    change (Int.unsigned Int64.iwordsize') with Int64.zwordsize.
    rewrite zlt_true by lia. simpl. rewrite Int64.decompose_shru_2 by lia.
    reflexivity.
  - econstructor; split.
    eapply eval_helper_2; eauto. EvalOp. DeclHelper. reflexivity. reflexivity.
    auto.
  - destruct x; auto. destruct y; auto. unfold Val.shrlu. destruct (Int.ltu i0 Int64.iwordsize'); eauto.
  - intros. unfold Val.shrlu. simpl. unfold Int.ltu. rewrite zlt_true. f_equal.  apply Int64.shru'_zero.
    rewrite Int.unsigned_zero. change (Int.unsigned Int64.iwordsize') with 64. lia.
Qed.

Lemma eval_shrluimm:
  forall n,
  unary_constructor_sound (fun e => shrluimm e n) (fun v => Val.shrlu v (Vint n)).
Proof.
  unfold shrluimm; red; intros. apply eval_shift_imm; intros.
  + (* n = 0 *)
    subst n. exists x; split; auto. destruct x; simpl; auto.
    change (Int64.shru' i Int.zero) with (Int64.shru i Int64.zero).
    rewrite Int64.shru_zero. auto.
  + (* 0 < n < 32 *)
    apply eval_splitlong with (sem := fun x => Val.shrlu x (Vint n)); auto.
    intros.
    exploit eval_shruimm. eexact H5. instantiate (1 := n). intros [v1 [A1 B1]].
    exploit eval_shruimm. eexact H4. instantiate (1 := n). intros [v2 [A2 B2]].
    exploit eval_shlimm. eexact H4. instantiate (1 := Int.sub Int.iwordsize n). intros [v3 [A3 B3]].
    exploit eval_or. eexact A1. eexact A3. intros [v4 [A4 B4]].
    econstructor; split. EvalOp.
    intros. subst. simpl in *. rewrite H1 in *. rewrite H2 in *. rewrite H3.
    inv B1; inv B2; inv B3. simpl in B4. inv B4.
    simpl. rewrite Int64.decompose_shru_1; auto.
    destruct x; auto.
  + (* 32 <= n < 64 *)
    exploit eval_highlong. eexact H. intros [v1 [A1 B1]].
    exploit eval_shruimm. eexact A1. instantiate (1 := Int.sub n Int.iwordsize). intros [v2 [A2 B2]].
    econstructor; split. EvalOp.
    destruct x; simpl; auto.
    destruct (Int.ltu n Int64.iwordsize'); auto.
    simpl in B1; inv B1. simpl in B2. rewrite H1 in B2. inv B2.
    simpl. erewrite <- Int64.decompose_shru_2. instantiate (1 := Int64.loword i).
    rewrite Int64.ofwords_recompose. auto. auto.
  + (* n >= 64 *)
    eapply eval_shrlu_base; EvalOp.
Qed.

Theorem eval_shrlu: binary_constructor_sound shrlu Val.shrlu.
Proof.
  unfold shrlu; red; intros.
  destruct (is_intconst b) as [n|] eqn:IC.
- (* Immediate *)
  exploit is_intconst_sound; eauto. intros EQ; subst y; clear H0.
  eapply eval_shrluimm; eauto.
- (* General case *)
  eapply eval_shrlu_base; eauto.
Qed.

Theorem eval_shrl_base: binary_constructor_sound shrl_base Val.shrl.
Proof.
  unfold shrl_base; red; intros.
  eapply eval_select_shift; eauto.
  - intros. simpl.
    exploit eval_shr. eexact H1. eexact H3. intros [v1 [A1 B1]].
    exploit (eval_sub ge sp e m le0 (Eop (Ointconst Int.iwordsize) Enil)). EvalOp. eexact H3.
    intros [v2 [A2 B2]].
    exploit eval_shl. eexact H1. eexact A2. intros [v3 [A3 B3]].
    exploit eval_shru. eexact H2. eexact H3. intros [v4 [A4 B4]].
    exploit eval_or. eexact A4. eexact A3. intros [v5 [A5 B5]].
    econstructor; split; EvalOp. intros.
    subst x1. subst x2. subst y0. simpl in *.
    rewrite H5 in *. inv B1. inv B2. rewrite H7. rewrite H6 in *. inv B3. inv B4.
    inv B5.  simpl. rewrite Int64.decompose_shr_1 by lia.
    reflexivity.
  - intros. simpl.
    exploit eval_addimm. eexact H3. instantiate (1 := Int.neg Int.iwordsize).
    intros [v1 [A1 B1]].
    exploit eval_shr. eexact H1. eexact A1.
    intros [v2 [A2 B2]].
    exploit eval_shrimm. eexact H1. instantiate (1 := Int.repr 31).
    intros [v3 [A3 B3]].
    econstructor; split; EvalOp. intros.
    subst x1. subst x2. subst y0. simpl in *. rewrite <- Int.sub_add_opp in B1.
    inv B1. rewrite H5 in B2. inv B2. unfold Int.ltu.
    change (Int.unsigned Int64.iwordsize') with Int64.zwordsize.
    unfold Int.ltu in B3. change (Int.unsigned (Int.repr 31)) with 31 in B3.
    change (Int.unsigned Int.iwordsize) with 32 in B3. simpl in B3. inv B3.
    rewrite zlt_true by lia. simpl. f_equal. rewrite Int64.decompose_shr_2 by lia.
    reflexivity.
  - econstructor; split.
    eapply eval_helper_2; eauto. EvalOp. DeclHelper. reflexivity. reflexivity.
    auto.
  - destruct x; auto. destruct y; auto. unfold Val.shrl. destruct (Int.ltu i0 Int64.iwordsize'); eauto.
  - intros. unfold Val.shrl. simpl. unfold Int.ltu. rewrite zlt_true. f_equal. apply Int64.shr'_zero.
    rewrite Int.unsigned_zero. change (Int.unsigned Int64.iwordsize') with 64. lia.
Qed.

Lemma eval_shrlimm:
  forall n,
  unary_constructor_sound (fun e => shrlimm e n) (fun v => Val.shrl v (Vint n)).
Proof.
  unfold shrlimm; red; intros. apply eval_shift_imm; intros.
  + (* n = 0 *)
    subst n. exists x; split; auto. destruct x; simpl; auto.
    change (Int64.shr' i Int.zero) with (Int64.shr i Int64.zero).
    rewrite Int64.shr_zero. auto.
  + (* 0 < n < 32 *)
    apply eval_splitlong with (sem := fun x => Val.shrl x (Vint n)); auto.
    intros.
    exploit eval_shruimm. eexact H5. instantiate (1 := n). intros [v1 [A1 B1]].
    exploit eval_shrimm. eexact H4. instantiate (1 := n). intros [v2 [A2 B2]].
    exploit eval_shlimm. eexact H4. instantiate (1 := Int.sub Int.iwordsize n). intros [v3 [A3 B3]].
    exploit eval_or. eexact A1. eexact A3. intros [v4 [A4 B4]].
    econstructor; split. EvalOp.
    intros. subst. simpl in *. rewrite H1 in *. rewrite H2 in *. rewrite H3.
    inv B1; inv B2; inv B3. simpl in B4. inv B4.
    simpl. rewrite Int64.decompose_shr_1; auto.
    destruct x; auto.
  + (* 32 <= n < 64 *)
    exploit eval_highlong. eexact H. intros [v1 [A1 B1]].
    assert (eval_expr ge sp e m (v1 :: le) (Eletvar 0) v1) by EvalOp.
    exploit eval_shrimm. eexact H2. instantiate (1 := Int.sub n Int.iwordsize). intros [v2 [A2 B2]].
    exploit eval_shrimm. eexact H2. instantiate (1 := Int.repr 31). intros [v3 [A3 B3]].
    econstructor; split. EvalOp.
    destruct x; simpl; auto.
    destruct (Int.ltu n Int64.iwordsize'); auto.
    simpl in B1; inv B1. simpl in B2. rewrite H1 in B2. inv B2.
    simpl in B3. inv B3.
    change (Int.ltu (Int.repr 31) Int.iwordsize) with true. simpl.
    erewrite <- Int64.decompose_shr_2. instantiate (1 := Int64.loword i).
    rewrite Int64.ofwords_recompose. auto. auto.
  + (* n >= 64 *)
    eapply eval_shrl_base; eauto. EvalOp.
Qed.

Theorem eval_shrl: binary_constructor_sound shrl Val.shrl.
Proof.
  unfold shrl; red; intros.
  destruct (is_intconst b) as [n|] eqn:IC.
- (* Immediate *)
  exploit is_intconst_sound; eauto. intros EQ; subst y; clear H0.
  eapply eval_shrlimm; eauto.
- (* General case *)
  eapply eval_shrl_base; eauto.
Qed.

Theorem eval_addl: Archi.ptr64 = false -> binary_constructor_sound addl Val.addl.
Proof.
  unfold addl; red; intros.
  set (default :=
         match platform_standard_builtin BI_addl (a ::: b ::: Enil) with
         | Some e0 => e0
         | None => Ebuiltin (EF_builtin "__builtin_addl" sig_ll_l) (a ::: b ::: Enil)
         end).
  assert (DEFAULT:
    exists v, eval_expr ge sp e m le default v /\ Val.lessdef (Val.addl x y) v).
  {
    destruct (platform_standard_builtin BI_addl (a ::: b ::: Enil)) eqn:?.
    eapply eval_platform_standard_builtin; eauto.
    do 3 (econstructor; eauto). reflexivity.
    econstructor; split.
    eapply eval_builtin_2; eauto. reflexivity. reflexivity. auto.
  }
  destruct (is_longconst a) as [p|] eqn:LC1;
  destruct (is_longconst b) as [q|] eqn:LC2.
- exploit (is_longconst_sound le a); eauto. intros EQ; subst x.
  exploit (is_longconst_sound le b); eauto. intros EQ; subst y.
  econstructor; split. apply eval_longconst. simpl; auto.
- predSpec Int64.eq Int64.eq_spec p Int64.zero; auto.
  subst p. exploit (is_longconst_sound le a); eauto. intros EQ; subst x.
  exists y; split; auto. unfold Val.addl; rewrite H; destruct y; auto. rewrite Int64.add_zero_l; auto.
- predSpec Int64.eq Int64.eq_spec q Int64.zero; auto.
  subst q. exploit (is_longconst_sound le b); eauto. intros EQ; subst y.
  exists x; split; auto. unfold Val.addl; rewrite H; destruct x; simpl; auto. rewrite Int64.add_zero; auto.
- auto.
Qed.

Theorem eval_subl: Archi.ptr64 = false -> binary_constructor_sound subl Val.subl.
Proof.
  unfold subl; red; intros.
  set (default :=
         match platform_standard_builtin BI_subl (a ::: b ::: Enil) with
         | Some e0 => e0
         | None => Ebuiltin (EF_builtin "__builtin_subl" sig_ll_l) (a ::: b ::: Enil)
         end).
  assert (DEFAULT:
           exists v, eval_expr ge sp e m le default v /\ Val.lessdef (Val.subl x y) v).
  {
    destruct (platform_standard_builtin BI_subl (a ::: b ::: Enil)) eqn:?.
    eapply eval_platform_standard_builtin; eauto.
    do 3 (econstructor; eauto). reflexivity.
    econstructor; split.
    eapply eval_builtin_2; eauto. reflexivity. reflexivity. auto.
  }
  destruct (is_longconst a) as [p|] eqn:LC1;
  destruct (is_longconst b) as [q|] eqn:LC2.
- exploit (is_longconst_sound le a); eauto. intros EQ; subst x.
  exploit (is_longconst_sound le b); eauto. intros EQ; subst y.
  econstructor; split. apply eval_longconst. simpl; auto.
- predSpec Int64.eq Int64.eq_spec p Int64.zero; auto.
  replace (Val.subl x y) with (Val.negl y). eapply eval_negl; eauto.
  subst p. exploit (is_longconst_sound le a); eauto. intros EQ; subst x.
  destruct y; simpl; auto.
- predSpec Int64.eq Int64.eq_spec q Int64.zero; auto.
  subst q. exploit (is_longconst_sound le b); eauto. intros EQ; subst y.
  exists x; split; auto. unfold Val.subl; rewrite H; destruct x; simpl; auto. rewrite Int64.sub_zero_l; auto.
- auto.
Qed.

Lemma eval_mull_base: binary_constructor_sound mull_base Val.mull.
Proof.
  unfold mull_base; red; intros. apply eval_splitlong2; auto.
- intros.
  destruct (platform_standard_builtin) eqn:?.
  + exploit (eval_platform_standard_builtin); eauto.
    EvalOp. reflexivity. intros [v5 [E5 L5]].
    exploit eval_highlong. eexact E5. intros [v6 [E6 L6]].
    exploit eval_lowlong. eexact E5. intros [v7 [E7 L7]].
    exploit eval_mul. eexact H2. eexact H3. intros [v8 [E8 L8]].
    exploit eval_add. eexact E6. eexact E8. intros [v9 [E9 L9]].
    exploit eval_mul. eexact H1. eexact H4. intros [v10 [E10 L10]].
    exploit eval_add. eexact E9. eexact E10. intros [v11 [E11 L11]].
    exists (Val.longofwords v11 v7). split.
    EvalOp. intros. subst; simpl in *.
    inv L5. inv L6. inv L7. inv L8. simpl in L9. inv L9. simpl in L10. inv L10.
    simpl in L11. inv L11. simpl. f_equal. symmetry. apply Int64.decompose_mul.
  + set (p := Val.mull' x2 y2). set (le1 := p :: le0).
    assert (E1: eval_expr ge sp e m le1 (Eop Olowlong (Eletvar O ::: Enil)) (Val.lowordoflong p)) by EvalOp.
    assert (E2: eval_expr ge sp e m le1 (Eop Ohighlong (Eletvar O ::: Enil)) (Val.hiwordoflong p)) by EvalOp.
    exploit eval_mul. apply eval_lift. eexact H2. apply eval_lift. eexact H3.
    instantiate (1 := p). fold le1. intros [v3 [E3 L3]].
    exploit eval_mul. apply eval_lift. eexact H1. apply eval_lift. eexact H4.
    instantiate (1 := p). fold le1. intros [v4 [E4 L4]].
    exploit eval_add. eexact E2. eexact E3. intros [v5 [E5 L5]].
    exploit eval_add. eexact E5. eexact E4. intros [v6 [E6 L6]].
    exists (Val.longofwords v6 (Val.lowordoflong p)); split.
    EvalOp. eapply eval_builtin_2; eauto. reflexivity. reflexivity.
    intros. unfold le1, p in *; subst; simpl in *.
    inv L3. inv L4. inv L5. simpl in L6. inv L6.
    simpl. f_equal. symmetry. apply Int64.decompose_mul.
- destruct x; auto; destruct y; auto.
Qed.

Lemma eval_mullimm:
  forall n, unary_constructor_sound (mullimm n) (fun v => Val.mull v (Vlong n)).
Proof.
  unfold mullimm; red; intros.
  predSpec Int64.eq Int64.eq_spec n Int64.zero.
  subst n. econstructor; split. apply eval_longconst.
  destruct x; simpl; auto. rewrite Int64.mul_zero. auto.
  predSpec Int64.eq Int64.eq_spec n Int64.one.
  subst n. exists x; split; auto.
  destruct x; simpl; auto. rewrite Int64.mul_one. auto.
  destruct (Int64.is_power2' n) as [l|] eqn:P2.
  exploit eval_shllimm. eauto. instantiate (1 := l). intros [v [A B]].
  exists v; split; auto.
  destruct x; simpl; auto.
  erewrite Int64.mul_pow2' by eauto.
  simpl in B. erewrite Int64.is_power2'_range in B by eauto.
  exact B.
  apply eval_mull_base; auto. apply eval_longconst.
Qed.

Theorem eval_mull: binary_constructor_sound mull Val.mull.
Proof.
  unfold mull; red; intros.
  destruct (is_longconst a) as [p|] eqn:LC1;
  destruct (is_longconst b) as [q|] eqn:LC2.
- exploit (is_longconst_sound le a); eauto. intros EQ; subst x.
  exploit (is_longconst_sound le b); eauto. intros EQ; subst y.
  econstructor; split. apply eval_longconst. simpl; auto.
- exploit (is_longconst_sound le a); eauto. intros EQ; subst x.
  replace (Val.mull (Vlong p) y) with (Val.mull y (Vlong p)) in *.
  eapply eval_mullimm; eauto.
  destruct y; simpl; auto. rewrite Int64.mul_commut; auto.
- exploit (is_longconst_sound le b); eauto. intros EQ; subst y.
  eapply eval_mullimm; eauto.
- apply eval_mull_base; auto.
Qed.

Theorem eval_shrxlimm:
  forall le a n x z,
  Archi.ptr64 = false ->
  eval_expr ge sp e m le a x ->
  Val.shrxl x (Vint n) = Some z ->
  exists v, eval_expr ge sp e m le (shrxlimm a n) v /\ Val.lessdef z v.
Proof.
  intros.
  apply Val.shrxl_shrl_2 in H1. unfold shrxlimm.
  destruct (Int.eq n Int.zero).
- subst z; exists x; auto.
- set (le' := x :: le).
  edestruct (eval_shrlimm (Int.repr 63) le' (Eletvar O)) as (v1 & A1 & B1).
  constructor. reflexivity.
  edestruct (eval_shrluimm (Int.sub (Int.repr 64) n) le') as (v2 & A2 & B2).
  eexact A1.
  edestruct (eval_addl H le' (Eletvar 0)) as (v3 & A3 & B3).
  constructor. reflexivity. eexact A2.
  edestruct (eval_shrlimm n le') as (v4 & A4 & B4). eexact A3.
  exists v4; split.
  econstructor; eauto.
  assert (X: forall v1 v2 n, Val.lessdef v1 v2 -> Val.lessdef (Val.shrl v1 (Vint n)) (Val.shrl v2 (Vint n))).
  { intros. inv H2; auto. }
  assert (Y: forall v1 v2 n, Val.lessdef v1 v2 -> Val.lessdef (Val.shrlu v1 (Vint n)) (Val.shrlu v2 (Vint n))).
  { intros. inv H2; auto. }
  subst z. eapply Val.lessdef_trans; [|eexact B4]. apply X.
  eapply Val.lessdef_trans; [|eexact B3]. apply Val.addl_lessdef; auto.
  eapply Val.lessdef_trans; [|eexact B2]. apply Y.
  auto.
Qed.

Theorem eval_divlu_base:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.divlu x y = Some z ->
  exists v, eval_expr ge sp e m le (divlu_base a b) v /\ Val.lessdef z v.
Proof.
  intros; unfold divlu_base.
  destruct (platform_standard_builtin) eqn:?.
  - exploit eval_platform_standard_builtin; eauto. EvalOp. apply H1.
  - econstructor; split. eapply eval_helper_2; eauto. DeclHelper. reflexivity. eassumption. auto.
Qed.

Theorem eval_modlu_base:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.modlu x y = Some z ->
  exists v, eval_expr ge sp e m le (modlu_base a b) v /\ Val.lessdef z v.
Proof.
  intros; unfold modlu_base.
  destruct (Compopts.inlined_runtime tt && negb Archi.ptr64) eqn:?.
  - rewrite andb_true_iff in Heqb0. destruct Heqb0. rewrite negb_true_iff in H3.
    exploit Val.modlu_divlu; eauto. intros [v [A B]].
    set (le1 := y :: x :: le).
    exploit (eval_divlu_base le1 (Eletvar 1) (Eletvar 0) x y).
    econstructor; eauto. econstructor; eauto. eexact A.
    intros [v1 [A1 B1]].
    set (d := divlu_base (Eletvar 1) (Eletvar 0)) in *.
    exploit (eval_mull le1 d v1 (Eletvar 0)). eexact A1. econstructor; eauto. reflexivity.
    intros [v2 [A2 B2]].
    exploit (eval_subl H3 le1 (Eletvar 1)). econstructor; eauto. reflexivity.
    eexact A2.
    intros [v3 [A3 B3]].
    exists v3; split. EvalOp. inv B.
    destruct x, y; inv A. destruct (Int64.eq i0 Int64.zero); inv H5.
    simpl. inv B1. inv B2. inv B3. auto.
  - econstructor; split. eapply eval_helper_2; eauto. DeclHelper. reflexivity. eassumption. auto.
Qed.

Lemma eval_exponentofbits:
  forall le a f,
  eval_expr ge sp e m le a (Vint (Int64.hiword (Float.to_bits f))) ->
  eval_expr ge sp e m le (exponentofbits a) (Vint (Int.sub (Int.shru (Int.shl (Int64.hiword (Float.to_bits f)) (Int.repr 1)) (Int.repr 21)) (Int.repr 1075))).
Proof.
  unfold exponentofbits. intros.
  exploit eval_shl; auto. eexact H. instantiate (2:=Eop (Ointconst Int.one) Enil). EvalOp. intros [v1 [A1 B1]].
  exploit eval_shru; auto. eexact A1. instantiate (2:=Eop (Ointconst (Int.repr 21)) Enil). EvalOp. intros [v2 [A2 B2]].
  exploit eval_sub; auto. eexact A2. instantiate (2:=Eop (Ointconst (Int.repr 1075)) Enil). EvalOp. intros [v3 [A3 B3]].
  inv B1. inv B2. inv B3. eauto.
Qed.

Lemma eval_exponentofbits_finite:
  forall le a s ex mx bnd,
  eval_expr ge sp e m le a (Vint (Int64.hiword (Float.to_bits (Binary.B754_finite 53 1024 s mx ex bnd)))) ->
  exists r, eval_expr ge sp e m le (exponentofbits a) (Vint (Int.repr r))
       /\ (Z.pos mx >= 2 ^ 52 /\ r = ex
          \/ Z.pos mx < 2 ^ 52 /\ r = ex - 1 /\ ex = -1074).
Proof.
  intros.
  exploit eval_exponentofbits; eauto.
  set (bits := Float.to_bits (Binary.B754_finite 53 1024 s mx ex bnd)) in *.
  replace (Int.shru (Int.shl (Int64.hiword bits) (Int.repr 1)) (Int.repr 21)) with (Int64.loword (Int64.shru (Int64.shl bits (Int64.one)) (Int64.repr 53))).
  unfold bits. rewrite Float.exponent_to_bits. intros.
  destruct ((0 <=? (Z.pos mx - 2 ^ 52))%Z) eqn:Esubn.
  - exists ex. split; auto.
    destruct (IEEE754_extra.binary_float_bounds _ _ _ _ bnd) as (?&?&?&?).
    assert (Int.sub (Int64.loword (Int64.repr (ex + 1075))) (Int.repr 1075) = Int.repr (ex)).
    unfold Int.sub, Int64.loword. rewrite (Int.unsigned_repr 1075) by Float.smart_omega.
    rewrite Int64.unsigned_repr by Float.smart_omega. rewrite Int.unsigned_repr by Float.smart_omega.
    f_equal. lia. rewrite <- H5; eauto. lia.
  - exists (ex - 1).
    destruct (IEEE754_extra.binary_float_bounds _ _ _ _ bnd) as (?&?&?&?).
    split. replace (Int.sub (Int64.loword (Int64.repr 0)) (Int.repr 1075)) with (Int.repr (- 1075)) in *.
    rewrite H4 by lia. eauto. change (Int64.loword (Int64.repr 0)) with Int.zero. rewrite Int.sub_zero_r.
    rewrite Int.neg_repr. reflexivity. lia.
  - apply Int.same_bits_eq; intros.
    rewrite Int64.bits_loword by lia.
    assert (Int64.zwordsize = 2 * Int.zwordsize) by (fold Int64.zwordsize; simpl; auto).
    assert (Int.zwordsize = 32) by auto.
    rewrite Int64.bits_shru by lia.
    rewrite Int64.unsigned_repr by Float.smart_omega.
    destruct (zlt (i + 53) Int64.zwordsize).
    rewrite Int64.bits_shl by lia. rewrite Int64.unsigned_one. rewrite zlt_false by lia.
    rewrite Int.bits_shru by lia. rewrite Int.unsigned_repr by Float.smart_omega.
    rewrite zlt_true by lia.
    rewrite Int.bits_shl by lia. rewrite (Int.unsigned_repr 1) by Float.smart_omega. rewrite zlt_false by lia.
    rewrite Int64.bits_hiword by lia. rewrite H2. f_equal. lia.
    rewrite Int.bits_shru by lia. rewrite Int.unsigned_repr by Float.smart_omega.
    symmetry. apply zlt_false; lia.
Qed.

Lemma eval_signofbits_finite:
  forall le a s ex mx bnd,
  eval_expr ge sp e m le a (Vint (Int64.hiword (Float.to_bits (Binary.B754_finite 53 1024 s mx ex bnd)))) ->
   eval_expr ge sp e m le (signofbits a) (Vint (Int.repr (if s then 1 else 0))).
Proof.
  intros.
  unfold signofbits.
  exploit eval_shru. eexact H. instantiate (2:=Eop (Ointconst (Int.repr 31)) Enil). EvalOp. intros [v1 [A1 B1]].
  inv B1. simpl in A1.
  rewrite Int64.lo_hi_shru in A1 by (unfold Int.zwordsize; simpl; lia).
  rewrite Float.signbit_to_bits in A1.
  destruct s; auto.
Qed.

Lemma eval_mantissaofbits_normal: 
  forall le a s mx ex bnd,
  eval_expr ge sp e m le a (Vlong (Float.to_bits (Binary.B754_finite 53 1024 s mx ex bnd))) ->
  0 <= Z.pos mx - 2 ^ 52 ->
  exists v, eval_expr ge sp e m le (mantissaofbits a) v
            /\ Val.lessdef (Vlong (Int64.repr (Z.pos mx))) v.
Proof.
  intros.
  unfold mantissaofbits.
  set (le1:=Vlong (Float.to_bits (Binary.B754_finite 53 1024 s mx ex bnd)) :: le).
  assert (Hv0: eval_expr ge sp e m le1 (Eletvar 0) (Vlong (Float.to_bits (Binary.B754_finite 53 1024 s mx ex bnd)))) by EvalOp.
  exploit eval_lowlong; auto. eexact Hv0. intros [v1 [A1 B1]].
  exploit eval_highlong; auto. eexact Hv0. intros [v2 [A2 B2]].
  exploit eval_and; auto. eexact A2. instantiate (2:=Eop (Ointconst (Int.repr (two_p 20 - 1))) Enil). EvalOp. intros [v3 [A3 B3]].
  exploit eval_or; auto. eexact A3. instantiate (2:=Eop (Ointconst (Int.repr (two_p 20))) Enil). EvalOp. intros [v4 [A4 B4]].
  econstructor; split. EvalOp.
  inv B1. inv B2. inv B3. inv B4. simpl.
  apply Val.lessdef_same. f_equal.
  rewrite <- (Float.mantissa_to_bits s mx ex bnd); auto.
  set (bits := Float.to_bits (Binary.B754_finite 53 1024 s mx ex bnd)).
  rewrite <- (Int64.ofwords_recompose bits) at 1.
  assert (Int64.repr (two_p 52 - 1) = Int64.ofwords (Int.repr (two_p 20 -1)) Int.mone).
  { rewrite Int64.ofwords_add.  change (two_p 20) with (2 ^ 20).
    rewrite Int.unsigned_repr by Float.smart_omega. rewrite Int.unsigned_mone. reflexivity.
  }
  rewrite H1. rewrite Int64.decompose_and. rewrite Int.and_mone.
  assert (Int64.repr (two_p 52) = Int64.ofwords (Int.repr (two_p 20)) Int.zero).
  { rewrite Int64.ofwords_add. rewrite Int.unsigned_zero.
    change (two_p 20) with (2 ^ 20). rewrite Int.unsigned_repr by Float.smart_omega.
    reflexivity.
  }
  rewrite H2. rewrite Int64.decompose_or. rewrite Int.or_zero. reflexivity.
Qed.

Lemma eval_shift_mantissa:
  forall le a mx b ex,
    eval_expr ge sp e m le a (Vlong (Int64.repr (Z.pos mx))) ->
    eval_expr ge sp e m le b (Vint (Int.repr ex)) ->
    -52 <= ex < 11 ->
    eval_expr ge sp e m le (shift_mantissa a b) (Vlong (Float.to_long_finite ex mx)).
Proof.
  unfold shift_mantissa. intros.
  destruct (zlt ex 1).
  - exploit eval_negint. eexact H0. intros [vn [AN BN]]. simpl in BN.
    try rewrite Int.sub_zero_r in BN.
    exploit eval_shrlu. eexact H. eexact AN. intros [v [A B]].
    inv BN. simpl in B. rewrite Int.neg_repr in B.
    unfold Int.ltu in B. change (Int.unsigned Int64.iwordsize') with 64 in *.
    rewrite Int.unsigned_repr in B by Float.smart_omega. rewrite zlt_true in B by lia.
    eapply eval_Econdition with (va := Int.cmp Clt (Int.zero) (Int.repr ex)).
    econstructor. EvalOp. simpl. reflexivity.
    simpl. unfold Int.lt. rewrite !Int.signed_repr by Float.smart_omega. rewrite Int.signed_zero.
    unfold Float.to_long_finite.
    rewrite zlt_false by lia.  rewrite zlt_false by lia. inv B.  eexact A.
  - exploit eval_highlong. eexact H. intros [vh [AH BH]].
    exploit eval_lowlong. eexact H. intros [vl [AL BL]].
    exploit eval_shll_base_small. eexact AH. eexact AL. eexact H0. intros [v [A B]].
    simpl in BL. unfold Int.ltu in BL. change (Int.unsigned Int64.iwordsize') with 64 in *.
    eapply eval_Econdition with (va := Int.cmp Clt (Int.zero) (Int.repr ex)).
    econstructor. EvalOp. simpl. reflexivity.
    simpl. unfold Int.lt. rewrite !Int.signed_repr by Float.smart_omega. rewrite Int.signed_zero.
    unfold Float.to_long_finite.
    rewrite ! zlt_true by lia.
    assert (Int.unsigned (Int.repr ex) = ex) by (rewrite Int.unsigned_repr; Float.smart_omega).
    assert (0 <= Int.unsigned (Int.repr ex) < Int.zwordsize).
    {  rewrite H2. change Int.zwordsize with 32. lia. }
    assert (Int.ltu (Int.repr ex) Int.iwordsize = true).
    {  unfold Int.ltu. rewrite H2. change (Int.unsigned Int.iwordsize) with 32.
       apply zlt_true. lia. }
    inv BL. inv BH.
    rewrite (B (Int64.hiword (Int64.repr (Z.pos mx))) (Int64.loword (Int64.repr (Z.pos mx))) (Int.repr ex)) in A; auto; try reflexivity.
    rewrite Int64.ofwords_recompose in A. simpl in A.
    unfold Int.ltu in A. rewrite zlt_true in A. eexact A. rewrite H2.
    change (Int.unsigned Int64.iwordsize') with 64 in *. lia.
    unfold Int.sub. rewrite H2. unfold Int.ltu.
    change (Int.unsigned Int.iwordsize) with 32. rewrite Int.unsigned_repr by Float.smart_omega.
    apply zlt_true; lia.
    unfold Int.ltu. rewrite H2.
    change (Int.unsigned Int64.iwordsize') with 64 in *.
    apply zlt_true; lia.
Qed.

Theorem eval_dtob:
  forall le a f,
  eval_expr ge sp e m le a (Vfloat f) ->
  Binary.is_nan _ _ f = false ->
  eval_expr ge sp e m le (dtob a) (Val.bitsoffloat (Vfloat f)).
Proof.
  unfold dtob; intros.
  destruct (platform_standard_builtin BI_dtob (a ::: Enil)) eqn:?.
  - exploit (eval_platform_standard_builtin); eauto. EvalOp.
    simpl. rewrite H0. reflexivity. intros [v [A B]].
    inv B; simpl; eauto.
  - eapply (eval_builtin_1 (BI_standard BI_dtob)); eauto.
    simpl. rewrite H0. reflexivity.
Qed.

Theorem eval_longoffloat:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.longoffloat x = Some y ->
  exists v, eval_expr ge sp e m le (longoffloat a) v /\ Val.lessdef y v.
Proof.
  intros; unfold longoffloat.
  assert (exists v, eval_expr ge sp e m le (Eexternal i64_dtos sig_f_l (a ::: Enil)) v /\ Val.lessdef y v).
  { econstructor; split.
    eapply (eval_helper_1 (BI_standard BI_i64_dtos)); eauto. DeclHelper. auto. auto.
  }
  destruct (Compopts.inlined_runtime tt && negb Archi.ptr64) eqn:?; eauto. clear H1.
  destruct x; simpl in H0; try discriminate.
  destruct f; try discriminate.
  - (* case: f = B754_zero *)
    inv H0.
    exists (Vlong Int64.zero); split; auto.
    set (le1 := Vint (Int64.hiword (Float.to_bits (Binary.B754_zero 53 1024 s)))
                  :: Vlong (Float.to_bits (Binary.B754_zero 53 1024 s)) :: le).
    econstructor. eapply eval_dtob; eauto.
    econstructor. EvalOp. econstructor. eapply eval_exponentofbits. econstructor. reflexivity.
    eapply eval_Econdition with (va:=Int.cmp Clt (Int.repr (-1075)) (Int.repr (-52))).
    econstructor. EvalOp. simpl. rewrite Float.exponent_to_bits_zero.
    simpl. unfold Int.lt. rewrite ! Int.signed_repr by Float.smart_omega. rewrite zlt_true by lia. reflexivity.
    EvalOp.
  - destruct (Float.to_long (Binary.B754_finite 53 1024 s m0 e0 e1)) eqn:?; inv H0.
    exploit Float.to_long_bounds; eauto. intros.
    exists (Vlong i); split; auto.
    econstructor; eauto.
    eapply eval_dtob; eauto.
    econstructor; eauto. EvalOp.
    set (le1 := Vint (Int64.hiword (Float.to_bits (Binary.B754_finite 53 1024 s m0 e0 e1)))
                  :: Vlong (Float.to_bits (Binary.B754_finite 53 1024 s m0 e0 e1)) :: le).
    exploit (eval_exponentofbits_finite le1 (Eletvar 0) s).
    EvalOp. intros [r [E]].
    destruct H0;[|destruct H0;[|destruct H0]].
    + (* exponent small *)
      econstructor; eauto.
      eapply eval_Econdition with (va:=Int.cmp Clt (Int.repr r) (Int.repr (-52))).
      econstructor. EvalOp. simpl. reflexivity.
      unfold Int.cmp, Int.lt. rewrite ! Int.signed_repr by Float.smart_omega.
      destruct H0. rewrite zlt_true by lia. rewrite H2. EvalOp.
    + (* positive with large enough exponent *)
      destruct H0; destruct H2. subst s. rewrite <- H0.
      destruct H1; try lia. destruct H1. subst r.
      econstructor; eauto.
      eapply eval_Econdition with (va:=Int.cmp Clt (Int.repr e0) (Int.repr (-52))).
      econstructor. EvalOp. simpl. reflexivity.
      unfold Int.cmp, Int.lt. rewrite ! Int.signed_repr by Float.smart_omega.
      rewrite zlt_false by lia.
      econstructor. eapply (eval_signofbits_finite (Vint (Int.repr e0) :: le1) (Eletvar 1)). EvalOp. simpl.
      eapply eval_Econdition with (va := Int.cmp Cge (Int.repr e0) (Int.repr 11)).
      econstructor. EvalOp. simpl. reflexivity.
      unfold Int.cmp, Int.lt. rewrite ! Int.signed_repr by Float.smart_omega.
      rewrite zlt_true by lia.  simpl.
      set (le2 := (Vint (Int.repr 0) :: Vint (Int.repr e0) :: le1)).
      exploit (eval_mantissaofbits_normal le2 (Eletvar 3)). EvalOp. lia. intros [v1 [A1 B1]].
      econstructor. eexact A1. inv B1.
      set (le3 := (Vlong (Int64.repr (Z.pos m0))::le2)).
      econstructor.
      eapply eval_shift_mantissa; eauto. EvalOp. EvalOp.
      eapply eval_Econdition with (va := Int.cmp Ceq (Int.repr 0) (Int.repr 1)).
      econstructor; EvalOp. reflexivity. simpl. econstructor. reflexivity.
    + (* negative with large enought exponent *)
      destruct H0; destruct H2. subst s. rewrite <- H0.
      destruct H1; try lia. destruct H1. subst r.
      econstructor; eauto.
      eapply eval_Econdition with (va:=Int.cmp Clt (Int.repr e0) (Int.repr (-52))).
      econstructor. EvalOp. simpl. reflexivity.
      unfold Int.cmp, Int.lt. rewrite ! Int.signed_repr by Float.smart_omega.
      rewrite zlt_false by lia.
      econstructor. eapply (eval_signofbits_finite (Vint (Int.repr e0) :: le1) (Eletvar 1)). EvalOp. simpl.
      eapply eval_Econdition with (va := Int.cmp Cge (Int.repr e0) (Int.repr 11)).
      econstructor. EvalOp; simpl. reflexivity.
      unfold Int.cmp, Int.lt. rewrite ! Int.signed_repr by Float.smart_omega. rewrite zlt_true by lia.
      simpl.
      set (le2 := (Vint (Int.repr 1) :: Vint (Int.repr e0) :: le1)).
      exploit (eval_mantissaofbits_normal le2 (Eletvar 3)). EvalOp. lia. intros [v1 [A1 B1]].
      econstructor. eexact A1. inv B1.
      set (le3 := (Vlong (Int64.repr (Z.pos m0))::le2)).
      econstructor.
      eapply eval_shift_mantissa; eauto; EvalOp.
      eapply eval_Econdition with (va := Int.cmp Ceq (Int.repr 1) (Int.repr 1)).
      econstructor; EvalOp; simpl; reflexivity.
      set (le4 := (Vlong (Float.to_long_finite e0 m0) :: le3)).
      assert (H4let0: eval_expr ge sp e m le4 (Eletvar 0) (Vlong (Float.to_long_finite e0 m0))) by EvalOp.
      exploit eval_negl. eexact H4let0. intros [v [A B]]. inv B. eexact A.
    + (* min_signed *)
      destruct H0; destruct H2. subst s. rewrite H2.
      destruct H1; try lia. destruct H1. subst r.
      econstructor. EvalOp.
      eapply eval_Econdition with (va:=Int.cmp Clt (Int.repr e0) (Int.repr (-52))).
      econstructor. EvalOp. simpl. reflexivity.
      unfold Int.cmp, Int.lt. rewrite ! Int.signed_repr by Float.smart_omega.
      rewrite zlt_false by lia.
      econstructor. eapply (eval_signofbits_finite (Vint (Int.repr e0) :: le1) (Eletvar 1)). EvalOp. simpl.
      eapply eval_Econdition with (va := Int.cmp Cge (Int.repr e0) (Int.repr 11)).
      econstructor. EvalOp. simpl. reflexivity.
      unfold Int.cmp, Int.lt. rewrite ! Int.signed_repr by Float.smart_omega.
      rewrite zlt_false by lia. simpl.
      eapply eval_Econdition with (va := Int.cmp Cge (Int.repr 1) (Int.repr 1)).
      econstructor. EvalOp. reflexivity.
      unfold Int.cmp, Int.lt. rewrite ! Int.signed_repr by Float.smart_omega.
      rewrite zlt_false by lia. simpl. EvalOp.
      rewrite Int64.ofwords_recompose. reflexivity.
Qed.

Theorem eval_longuoffloat:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.longuoffloat x = Some y ->
  exists v, eval_expr ge sp e m le (longuoffloat a) v /\ Val.lessdef y v.
Proof.
  intros; unfold longuoffloat. destruct (Compopts.inlined_runtime tt && negb Archi.ptr64) eqn:?.
  - destruct x; simpl in H0; try discriminate.
    destruct (Float.to_longu f) as [n|] eqn:?; simpl in H0; inv H0.
    exists (Vlong n); split; auto.
    set (im := Float.ox8000_0000_0000_0000).
    set (fm := Float.of_longu im).
    assert (eval_expr ge sp e m (Vfloat fm :: Vfloat f :: le) (Eletvar (S O)) (Vfloat f)).
    constructor. auto.
    assert (eval_expr ge sp e m (Vfloat fm :: Vfloat f :: le) (Eletvar O) (Vfloat fm)).
    constructor. auto.
    econstructor. eauto.
    econstructor. instantiate (1 := Vfloat fm). EvalOp.
    eapply eval_Econdition with (va := Float.cmp Clt f fm).
    eauto with evalexpr.
    destruct (Float.cmp Clt f fm) eqn:?.
    exploit Float.to_longu_to_long_1; eauto. intro EQ.
    exploit eval_longoffloat. eexact H0. simpl. rewrite  EQ.  reflexivity.
    intros [v [A B]]. inv B. eexact A.
    exploit Float.to_longu_to_long_2; eauto.
    change Float.ox8000_0000_0000_0000 with im. fold fm. intro EQ.
    set (t2 := subf (Eletvar (S O)) (Eletvar O)).
    set (t3 := longoffloat t2).
    exploit (eval_subf ge sp e m (Vfloat fm :: Vfloat f :: le) (Eletvar (S O)) (Vfloat f) (Eletvar O)); eauto.
    fold t2. intros [v2 [A2 B2]]. simpl in B2. inv B2.
    exploit eval_longconst. instantiate (1 := im). instantiate (1 := (Vfloat fm :: Vfloat f :: le)). intros.
    exploit eval_longoffloat. eexact A2. simpl. rewrite EQ. reflexivity.
    intros [v [A B]]. inv B.
    exploit eval_addl. rewrite andb_true_iff in Heqb. destruct Heqb.  rewrite negb_true_iff in H4. auto.
    eexact H2.  eexact A. fold t3. intros [v1 [A1 B1]]. inv B1.
    simpl in A1. rewrite Int64.sub_add_opp in A1.
    rewrite <- (Int64.add_commut (Int64.neg im)) in A1.
    rewrite <- Int64.add_assoc in A1.
    rewrite Int64.add_neg_zero in A1.
    rewrite  Int64.add_zero_l in A1. auto.
  - econstructor; split.
    eapply (eval_helper_1 (BI_standard BI_i64_dtou)); eauto. DeclHelper. auto. auto.
Qed.

Theorem eval_floatoflong:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.floatoflong x = Some y ->
  exists v, eval_expr ge sp e m le (floatoflong a) v /\ Val.lessdef y v.
Proof.
  intros; unfold floatoflong.
  destruct (Compopts.inlined_runtime).
  - destruct x; inv H0.
    exploit eval_lowlong. eexact H. intros [v1 [A1 B1]].
    exploit eval_floatofintu. eexact A1. inv B1. reflexivity. intros [v2 [A2 B2]].
    exploit eval_highlong. eexact H. intros [v3 [A3 B3]].
    exploit eval_floatofint. eexact A3. inv B3. reflexivity. intros [v4 [A4 B4]].
    set (two_pf := IEEE754_extra.BofZ 53 1024 eq_refl eq_refl (2 ^ 32)) in *.
    assert (TWO_P: eval_expr ge sp e m le (Eop (Ofloatconst two_pf) Enil) (Vfloat two_pf)) by EvalOp.
    exploit eval_mulf. eexact A4. eexact TWO_P. intros [v5 [A5 B5]].
    exploit eval_addf. eexact A5. eexact A2. intros [v6 [A6 B6]].
    exists v6; split. EvalOp. inv B1. inv B2. inv B3. inv B4. inv B5. inv B6.
    simpl. rewrite Float.of_long_decomp; auto.
  - exists y; split; auto.
    eapply (eval_helper_1 (BI_standard BI_i64_stod)); eauto. DeclHelper. auto.
    simpl. destruct x; simpl in H0; inv H0; auto.
Qed.

Theorem eval_floatoflongu:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.floatoflongu x = Some y ->
  exists v, eval_expr ge sp e m le (floatoflongu a) v /\ Val.lessdef y v.
Proof.
  intros; unfold floatoflongu.
  destruct (Compopts.inlined_runtime).
  - destruct x; inv H0.
    exploit eval_lowlong. eexact H. intros [v1 [A1 B1]].
    exploit eval_floatofintu. eexact A1. inv B1. reflexivity. intros [v2 [A2 B2]].
    exploit eval_highlong. eexact H. intros [v3 [A3 B3]].
    exploit eval_floatofintu. eexact A3. inv B3. reflexivity. intros [v4 [A4 B4]].
    set (two_pf := IEEE754_extra.BofZ 53 1024 eq_refl eq_refl (2 ^ 32)) in *.
    assert (TWO_P: eval_expr ge sp e m le (Eop (Ofloatconst two_pf) Enil) (Vfloat two_pf)) by EvalOp.
    exploit eval_mulf. eexact A4. eexact TWO_P. intros [v5 [A5 B5]].
    exploit eval_addf. eexact A5. eexact A2. intros [v6 [A6 B6]].
    exists v6; split. EvalOp. inv B1. inv B2. inv B3. inv B4. inv B5. inv B6.
    simpl. rewrite Float.of_longu_decomp; auto.
  - exists y; split; auto.
    eapply (eval_helper_1 (BI_standard BI_i64_utod)); eauto. DeclHelper. auto.
    simpl. destruct x; simpl in H0; inv H0; auto.
Qed.

Theorem eval_longofsingle:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.longofsingle x = Some y ->
  exists v, eval_expr ge sp e m le (longofsingle a) v /\ Val.lessdef y v.
Proof.
  intros; unfold longofsingle.
  destruct Compopts.supports_double.
  - simpl. destruct x; simpl in H0; inv H0; auto.
    destruct (Float32.to_long f) as [n|] eqn:EQ; simpl in H2; inv H2.
    exploit eval_floatofsingle; eauto. intros (v & A & B). simpl in B. inv B.
    apply Float32.to_long_double in EQ.
    eapply eval_longoffloat; eauto. simpl.
    change (Float.of_single f) with (Float32.to_double f); rewrite EQ; auto.
  - exists y; split; auto.
    eapply (eval_helper_1 (BI_standard BI_i64_ftos)); eauto. DeclHelper. auto.
Qed.

Theorem eval_longuofsingle:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.longuofsingle x = Some y ->
  exists v, eval_expr ge sp e m le (longuofsingle a) v /\ Val.lessdef y v.
Proof.
  intros; unfold longuofsingle.
  destruct Compopts.supports_double.
  - destruct x; simpl in H0; inv H0. destruct (Float32.to_longu f) as [n|] eqn:EQ; simpl in H2; inv H2.
    exploit eval_floatofsingle; eauto. intros (v & A & B). simpl in B. inv B.
    apply Float32.to_longu_double in EQ.
    eapply eval_longuoffloat; eauto. simpl.
    change (Float.of_single f) with (Float32.to_double f); rewrite EQ; auto.
  - exists y; split; auto.
    eapply (eval_helper_1 (BI_standard BI_i64_ftou)); eauto. DeclHelper. auto.
Qed.

Remark decompose_cmpl_eq_zero:
  forall h l,
  Int64.eq (Int64.ofwords h l) Int64.zero = Int.eq (Int.or h l) Int.zero.
Proof.
  intros.
  assert (Int64.zwordsize = Int.zwordsize * 2) by reflexivity.
  predSpec Int64.eq Int64.eq_spec (Int64.ofwords h l) Int64.zero.
  replace (Int.or h l) with Int.zero. rewrite Int.eq_true. auto.
  apply Int.same_bits_eq; intros.
  rewrite Int.bits_zero. rewrite Int.bits_or by auto.
  symmetry. apply orb_false_intro.
  transitivity (Int64.testbit (Int64.ofwords h l) (i + Int.zwordsize)).
  rewrite Int64.bits_ofwords by lia. rewrite zlt_false by lia. f_equal; lia.
  rewrite H0. apply Int64.bits_zero.
  transitivity (Int64.testbit (Int64.ofwords h l) i).
  rewrite Int64.bits_ofwords by lia. rewrite zlt_true by lia. auto.
  rewrite H0. apply Int64.bits_zero.
  symmetry. apply Int.eq_false. red; intros; elim H0.
  apply Int64.same_bits_eq; intros.
  rewrite Int64.bits_zero. rewrite Int64.bits_ofwords by auto.
  destruct (zlt i Int.zwordsize).
  assert (Int.testbit (Int.or h l) i = false) by (rewrite H1; apply Int.bits_zero).
  rewrite Int.bits_or in H3 by lia. exploit orb_false_elim; eauto. tauto.
  assert (Int.testbit (Int.or h l) (i - Int.zwordsize) = false) by (rewrite H1; apply Int.bits_zero).
  rewrite Int.bits_or in H3 by lia. exploit orb_false_elim; eauto. tauto.
Qed.

Lemma eval_cmpl_eq_zero:
  forall le a x,
  eval_expr ge sp e m le a (Vlong x) ->
  eval_expr ge sp e m le (cmpl_eq_zero a) (Val.of_bool (Int64.eq x Int64.zero)).
Proof.
  intros. unfold cmpl_eq_zero.
  eapply eval_splitlong_strict; eauto. intros.
  exploit eval_or. eexact H0. eexact H1. intros [v1 [A1 B1]]. simpl in B1; inv B1.
  exploit eval_comp. eexact A1. instantiate (2 := Eop (Ointconst Int.zero) Enil). EvalOp.
  instantiate (1 := Ceq). intros [v2 [A2 B2]].
  unfold Val.cmp in B2; simpl in B2.
  rewrite <- decompose_cmpl_eq_zero in B2.
  rewrite Int64.ofwords_recompose in B2.
  destruct (Int64.eq x Int64.zero); inv B2; auto.
Qed.

Lemma eval_cmpl_ne_zero:
  forall le a x,
  eval_expr ge sp e m le a (Vlong x) ->
  eval_expr ge sp e m le (cmpl_ne_zero a) (Val.of_bool (negb (Int64.eq x Int64.zero))).
Proof.
  intros. unfold cmpl_ne_zero.
  eapply eval_splitlong_strict; eauto. intros.
  exploit eval_or. eexact H0. eexact H1. intros [v1 [A1 B1]]. simpl in B1; inv B1.
  exploit eval_comp. eexact A1. instantiate (2 := Eop (Ointconst Int.zero) Enil). EvalOp.
  instantiate (1 := Cne). intros [v2 [A2 B2]].
  unfold Val.cmp in B2; simpl in B2.
  rewrite <- decompose_cmpl_eq_zero in B2.
  rewrite Int64.ofwords_recompose in B2.
  destruct (negb (Int64.eq x Int64.zero)); inv B2; auto.
Qed.

Lemma eval_cmplu_gen:
  forall ch cl a b le x y,
  eval_expr ge sp e m le a (Vlong x) ->
  eval_expr ge sp e m le b (Vlong y) ->
  eval_expr ge sp e m le (cmplu_gen ch cl a b)
    (Val.of_bool (if Int.eq (Int64.hiword x) (Int64.hiword y)
                  then Int.cmpu cl (Int64.loword x) (Int64.loword y)
                  else Int.cmpu ch (Int64.hiword x) (Int64.hiword y))).
Proof.
  intros. unfold cmplu_gen. eapply eval_splitlong2_strict; eauto. intros.
  econstructor. econstructor. EvalOp. simpl. eauto.
  destruct (Int.eq (Int64.hiword x) (Int64.hiword y)); EvalOp.
Qed.

Remark int64_eq_xor:
  forall p q, Int64.eq p q = Int64.eq (Int64.xor p q) Int64.zero.
Proof.
  intros.
  predSpec Int64.eq Int64.eq_spec p q.
  subst q. rewrite Int64.xor_idem. rewrite Int64.eq_true. auto.
  predSpec Int64.eq Int64.eq_spec (Int64.xor p q) Int64.zero.
  elim H. apply Int64.xor_zero_equal; auto.
  auto.
Qed.

Theorem eval_cmplu:
  forall c le a x b y v,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.cmplu (Mem.valid_pointer m) c x y = Some v ->
  Archi.ptr64 = false ->
  eval_expr ge sp e m le (cmplu c a b) v.
Proof.
  intros. unfold Val.cmplu, Val.cmplu_bool in H1. rewrite H2 in H1. simpl in H1.
  destruct x; simpl in H1; try discriminate H1; destruct y; inv H1.
  rename i into x. rename i0 into y.
  destruct c; simpl.
- (* Ceq *)
  exploit eval_xorl. eexact H. eexact H0. intros [v1 [A B]]. simpl in B. inv B.
  rewrite int64_eq_xor. apply eval_cmpl_eq_zero; auto.
- (* Cne *)
  exploit eval_xorl. eexact H. eexact H0. intros [v1 [A B]]. simpl in B. inv B.
  rewrite int64_eq_xor. apply eval_cmpl_ne_zero; auto.
- (* Clt *)
  exploit (eval_cmplu_gen Clt Clt). eexact H. eexact H0. simpl.
  rewrite <- Int64.decompose_ltu. rewrite ! Int64.ofwords_recompose. auto.
- (* Cle *)
  exploit (eval_cmplu_gen Clt Cle). eexact H. eexact H0. intros.
  rewrite <- (Int64.ofwords_recompose x). rewrite <- (Int64.ofwords_recompose y).
  rewrite Int64.decompose_leu. auto.
- (* Cgt *)
  exploit (eval_cmplu_gen Cgt Cgt). eexact H. eexact H0. simpl.
  rewrite Int.eq_sym. rewrite <- Int64.decompose_ltu. rewrite ! Int64.ofwords_recompose. auto.
- (* Cge *)
  exploit (eval_cmplu_gen Cgt Cge). eexact H. eexact H0. intros.
  rewrite <- (Int64.ofwords_recompose x). rewrite <- (Int64.ofwords_recompose y).
  rewrite Int64.decompose_leu. rewrite Int.eq_sym. auto.
Qed.

Lemma eval_cmpl_gen:
  forall ch cl a b le x y,
  eval_expr ge sp e m le a (Vlong x) ->
  eval_expr ge sp e m le b (Vlong y) ->
  eval_expr ge sp e m le (cmpl_gen ch cl a b)
    (Val.of_bool (if Int.eq (Int64.hiword x) (Int64.hiword y)
                  then Int.cmpu cl (Int64.loword x) (Int64.loword y)
                  else Int.cmp ch (Int64.hiword x) (Int64.hiword y))).
Proof.
  intros. unfold cmpl_gen. eapply eval_splitlong2_strict; eauto. intros.
  econstructor. econstructor. EvalOp. simpl. eauto.
  destruct (Int.eq (Int64.hiword x) (Int64.hiword y)); EvalOp.
Qed.

Remark decompose_cmpl_lt_zero:
  forall h l,
  Int64.lt (Int64.ofwords h l) Int64.zero = Int.lt h Int.zero.
Proof.
  intros.
  generalize (Int64.shru_lt_zero (Int64.ofwords h l)).
  change (Int64.shru (Int64.ofwords h l) (Int64.repr (Int64.zwordsize - 1)))
    with (Int64.shru' (Int64.ofwords h l) (Int.repr 63)).
  rewrite Int64.decompose_shru_2.
  change (Int.sub (Int.repr 63) Int.iwordsize)
    with (Int.repr (Int.zwordsize - 1)).
  rewrite Int.shru_lt_zero.
  destruct (Int64.lt (Int64.ofwords h l) Int64.zero); destruct (Int.lt h Int.zero); auto; intros.
  elim Int64.one_not_zero. auto.
  elim Int64.one_not_zero. auto.
  vm_compute. intuition congruence.
Qed.

Theorem eval_cmpl:
  forall c le a x b y v,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.cmpl c x y = Some v ->
  eval_expr ge sp e m le (cmpl c a b) v.
Proof.
  intros. unfold Val.cmpl in H1.
  destruct x; simpl in H1; try discriminate. destruct y; inv H1.
  rename i into x. rename i0 into y.
  destruct c; simpl.
- (* Ceq *)
  exploit eval_xorl. eexact H. eexact H0. intros [v1 [A B]]. simpl in B; inv B.
  rewrite int64_eq_xor. apply eval_cmpl_eq_zero; auto.
- (* Cne *)
  exploit eval_xorl. eexact H. eexact H0. intros [v1 [A B]]. simpl in B; inv B.
  rewrite int64_eq_xor. apply eval_cmpl_ne_zero; auto.
- (* Clt *)
  destruct (is_longconst_zero b) eqn:LC.
+ exploit is_longconst_zero_sound; eauto. intros EQ; inv EQ; clear H0.
  exploit eval_highlong. eexact H. intros [v1 [A1 B1]]. simpl in B1. inv B1.
  exploit eval_comp. eexact A1.
  instantiate (2 := Eop (Ointconst Int.zero) Enil). EvalOp.
  instantiate (1 := Clt). intros [v2 [A2 B2]].
  unfold Val.cmp in B2. simpl in B2.
  rewrite <- (Int64.ofwords_recompose x). rewrite decompose_cmpl_lt_zero.
  destruct (Int.lt (Int64.hiword x) Int.zero); inv B2; auto.
+ exploit (eval_cmpl_gen Clt Clt). eexact H. eexact H0. simpl.
  rewrite <- Int64.decompose_lt. rewrite ! Int64.ofwords_recompose. auto.
- (* Cle *)
  exploit (eval_cmpl_gen Clt Cle). eexact H. eexact H0. intros.
  rewrite <- (Int64.ofwords_recompose x). rewrite <- (Int64.ofwords_recompose y).
  rewrite Int64.decompose_le. auto.
- (* Cgt *)
  exploit (eval_cmpl_gen Cgt Cgt). eexact H. eexact H0. simpl.
  rewrite Int.eq_sym. rewrite <- Int64.decompose_lt. rewrite ! Int64.ofwords_recompose. auto.
- (* Cge *)
  destruct (is_longconst_zero b) eqn:LC.
+ exploit is_longconst_zero_sound; eauto. intros EQ; inv EQ; clear H0.
  exploit eval_highlong. eexact H. intros [v1 [A1 B1]]. simpl in B1; inv B1.
  exploit eval_comp. eexact A1.
  instantiate (2 := Eop (Ointconst Int.zero) Enil). EvalOp.
  instantiate (1 := Cge). intros [v2 [A2 B2]].
  unfold Val.cmp in B2; simpl in B2.
  rewrite <- (Int64.ofwords_recompose x). rewrite decompose_cmpl_lt_zero.
  destruct (negb (Int.lt (Int64.hiword x) Int.zero)); inv B2; auto.
+ exploit (eval_cmpl_gen Cgt Cge). eexact H. eexact H0. intros.
  rewrite <- (Int64.ofwords_recompose x). rewrite <- (Int64.ofwords_recompose y).
  rewrite Int64.decompose_le. rewrite Int.eq_sym. auto.
Qed.

Theorem eval_long_round_odd:
  forall le a i,
  Archi.ptr64 = false ->
  eval_expr ge sp e m le a (Vlong i) ->
  eval_expr ge sp e m le (long_round_odd a)
    (Vlong (Int64.and (Int64.or i (Int64.add (Int64.and i (Int64.repr 2047)) (Int64.repr 2047))) (Int64.repr (-2048)))).
Proof.
  unfold long_round_odd; intros.
  exploit eval_longconst. instantiate (1 := Int64.repr 2047). instantiate (1:= le). intros A1.
  exploit eval_andl. eexact H0. eexact A1. intros [v2 [A2 B2]]. inv B2.
  exploit eval_addl; auto. eexact A2. eexact A1. intros [v3 [A3 B3]]. inv B3.
  exploit eval_orl. eexact H0. eexact A3. intros [v4 [A4 B4]]. inv B4.
  exploit eval_longconst. instantiate (1 := Int64.repr (-2048)). instantiate (1:= le). intros A5.
  exploit eval_andl. eexact A4. eexact A5. intros [v6 [A6 B6]]. inv B6.
  eauto.
Qed.

Lemma eval_condition_bool:
  forall le c cb a y b z,
    eval_expr ge sp e m le c (Val.of_bool cb) ->
    eval_expr ge sp e m le a y ->
    eval_expr ge sp e m le b z ->
    eval_expr ge sp e m le (Econdition (CEcond (Ccomp Ceq) (c ::: (Eop (Ointconst Int.zero) Enil) ::: Enil)) a b) (if negb cb then y else z).
Proof.
  intros. econstructor. econstructor; EvalOp. simpl.
  instantiate (1:= negb cb).
  unfold Val.of_bool. destruct cb; auto.
  destruct cb; auto.
Qed.

Theorem eval_singleoflongu:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.singleoflongu x = Some y ->
  exists v, eval_expr ge sp e m le (singleoflongu a) v /\ Val.lessdef y v.
Proof.
  intros; unfold singleoflongu.
  destruct (negb Archi.ptr64 && Compopts.inlined_runtime tt && Compopts.supports_double) eqn:?.
  - InvBooleans. rewrite negb_true_iff in H3. clear H2. clear H4.
    destruct x; inv H0.
    set (twop53 := 9007199254740992) in *.
    exploit eval_long_round_odd; auto. eexact H. intros A1.
    exploit eval_cmplu; auto. eexact H. eapply (eval_longconst le (Int64.repr twop53)). instantiate (2:= Cle). reflexivity. intros A2.
    exploit eval_condition_bool. eexact A2. eexact A1. eexact H. intros A3.
    simpl in A3. rewrite negb_involutive in A3.
    destruct (Int64.ltu (Int64.repr twop53) i) eqn:?.
    * exploit eval_floatoflongu. eexact A3. simpl. reflexivity. intros [v4 [A4 B4]]. inv B4.
      exploit eval_singleoffloat. eexact A4. intros [v5 [A5 B5]]. inv B5.
      rewrite Float32.of_longu_double_2. eauto.
      unfold Int64.ltu in Heqb.
      change (2^36) with 68719476736. subst twop53.
      rewrite Int64.unsigned_repr in Heqb by (unfold Int64.max_unsigned; simpl; lia).
      destruct (zlt _ (Int64.unsigned i)); inv Heqb.
      lia.
    * exploit eval_floatoflongu. eexact A3. simpl. reflexivity. intros [v4 [A4 B4]]. inv B4.
      exploit eval_singleoffloat. eexact A4. intros [v5 [A5 B5]]. inv B5.
      rewrite Float32.of_longu_double_1; eauto.
      unfold Int64.ltu in Heqb.
      change (2 ^ 53) with twop53. subst twop53.
      rewrite Int64.unsigned_repr in Heqb by (unfold Int64.max_unsigned; simpl; lia).
      simpl. destruct (zlt _ (Int64.unsigned i)); inv Heqb.
      lia.
  - exists y; split; auto.
    eapply (eval_helper_1 (BI_standard BI_i64_utof)); eauto. DeclHelper. auto.
    simpl. destruct x; simpl in H0; inv H0; auto.
Qed.

Theorem eval_singleoflong:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.singleoflong x = Some y ->
  exists v, eval_expr ge sp e m le (singleoflong a) v /\ Val.lessdef y v.
Proof.
  intros; unfold singleoflong.
  destruct (negb Archi.ptr64 && Compopts.inlined_runtime tt && Compopts.supports_double) eqn:?.
  - InvBooleans. rewrite negb_true_iff in H3. clear H2. clear H4.
    set (twop53 :=  9007199254740992) in *.
    set (mtwop53 := -9007199254740992) in *.
    destruct x; inv H0.
    exploit eval_long_round_odd; auto. eexact H. intros A1.
    exploit eval_cmpl; auto. eexact H. eapply (eval_longconst le (Int64.repr mtwop53)). instantiate (2 := Clt). reflexivity. intros A2.
    exploit eval_cmpl; auto. eexact H. eapply (eval_longconst le (Int64.repr twop53)). instantiate (2:= Cge). reflexivity. intros A3.
    exploit eval_or. eexact A2. eexact A3. intros [v4 [A4 B4]]. simpl in B4.
    replace v4 with (Val.of_bool (Int64.lt i (Int64.repr mtwop53) || negb (Int64.lt i (Int64.repr twop53)))) in A4 by
      (destruct (Int64.lt i (Int64.repr mtwop53)) eqn:? ; destruct (negb (Int64.lt i (Int64.repr twop53))) eqn:?; inv B4; auto).
    exploit eval_condition_bool.
    eexact A4. eexact H. eexact A1. intros A5.
    destruct ( Int64.lt i (Int64.repr mtwop53) || negb (Int64.lt i (Int64.repr twop53))) eqn:?; simpl in A5.
    * exploit eval_floatoflong. eexact A5. simpl. reflexivity. intros [v6 [A6 B6]]. inv B6.
      exploit eval_singleoffloat. eexact A6. intros [v7 [A7 B7]]. inv B7.
      rewrite Float32.of_long_double_2; eauto.
      rewrite orb_true_iff in Heqb. destruct Heqb; unfold Int64.lt in *.
      rewrite Int64.signed_repr in H0 by (unfold mtwop53; unfold Int64.min_signed, Int64.max_signed; simpl; lia). subst mtwop53.
      destruct (zlt (Int64.signed i) (-9007199254740992)); inv H0. rewrite Z.abs_neq. lia. lia.
      rewrite negb_true_iff in H0.
      rewrite Int64.signed_repr in H0 by (unfold twop53; unfold Int64.min_signed, Int64.max_signed; simpl; lia).
      subst twop53.
      destruct (zlt (Int64.signed i) 9007199254740992); inv H0. rewrite Z.abs_eq;  lia.
    * exploit eval_floatoflong. eexact A5. simpl. reflexivity. intros [v6 [A6 B6]]. inv B6.
      exploit eval_singleoffloat. eexact A6. intros [v7 [A7 B7]]. inv B7.
      rewrite Float32.of_long_double_1; eauto.
      rewrite orb_false_iff in Heqb. destruct Heqb; unfold Int64.lt in *.
      rewrite negb_false_iff in H1.
      rewrite Int64.signed_repr in H0 by (unfold mtwop53, Int64.min_signed, Int64.max_signed; simpl; lia).
      rewrite Int64.signed_repr in H1 by (unfold twop53, Int64.min_signed, Int64.max_signed; simpl; lia).
      subst mtwop53. subst twop53.
      destruct (zlt (Int64.signed i) (-9007199254740992)); inv H0.
      destruct (zlt (Int64.signed i) 9007199254740992); inv H1.
      change (2 ^ 53) with 9007199254740992.
      assert (Int64.signed i <= 0 \/ Int64.signed i > 0) by lia.
      destruct H0; [rewrite Z.abs_neq| rewrite Z.abs_eq]; lia.
  - exists y; split; auto.
    eapply (eval_helper_1 (BI_standard BI_i64_stof)); eauto. DeclHelper. auto.
    simpl. destruct x; simpl in H0; inv H0; auto.
Qed.


Lemma eval_mask_zero:
  forall le a x,
  eval_expr ge sp e m le a (Vlong x) ->
  eval_expr ge sp e m le (makelong (shrimm (highlong a) (Int.repr 31)) (shrimm (highlong a) (Int.repr 31)))
          (Vlong (if Int64.lt x Int64.zero then Int64.mone else Int64.zero)).
Proof.
  intros.
  exploit eval_highlong. eexact H. intros [v1 [A1 B1]].  inv B1.
  exploit eval_shrimm. eexact A1. instantiate (1 := Int.repr 31). intros [v2 [A2 B2]]. inv B2.
  EvalOp.
  rewrite Int.shr_lt_zero. rewrite <- (decompose_cmpl_lt_zero _ (Int64.loword x)). rewrite Int64.ofwords_recompose.
  unfold Int.ltu. change (Int.unsigned (Int.repr 31)) with 31. change (Int.unsigned Int.iwordsize) with 32.
  simpl. destruct (Int64.lt x Int64.zero); [rewrite Int64.ofwords_mone | rewrite Int64.ofwords_zero]; reflexivity.
Qed.

Theorem eval_neg_cond:
  forall le a x b y,
  Archi.ptr64 = false ->
  eval_expr ge sp e m le a (Vlong x) ->
  eval_expr ge sp e m le b (Vlong y) ->
  eval_expr ge sp e m le (neg_cond a b) (Vlong (if Int64.lt x Int64.zero then Int64.neg y else y)).
Proof.
  unfold neg_cond; intros.
  exploit eval_mask_zero. eexact H0. intros.
  exploit eval_xorl. eexact H1. eexact H2. intros [v4 [A4 B4]]. inv B4.
  exploit eval_subl; auto. eexact A4. eexact H2. intros [v5 [A5 B5]].
  simpl in B5. inv B5.
  destruct (Int64.lt x Int64.zero).
  replace (Int64.xor y Int64.mone) with (Int64.not y) in A5.
  rewrite Int64.sub_add_opp in A5.
  unfold Int64.mone in A5. rewrite Int64.neg_repr in A5. simpl in *.
  rewrite Int64.neg_not. eexact A5.
  rewrite <- (Int64.xor_zero (Int64.not y)). rewrite <- Int64.not_mone.
  apply Int64.xor_not_xor.
  rewrite Int64.xor_zero in A5. rewrite Int64.sub_zero_l in A5. auto.
Qed.

Theorem eval_modls_base:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.modls x y = Some z ->
  exists v, eval_expr ge sp e m le (modls_base a b) v /\ Val.lessdef z v.
Proof.
  intros; unfold modls_base. destruct (Compopts.inlined_runtime tt && negb Archi.ptr64) eqn:?.
  - rewrite andb_true_iff in Heqb0. destruct Heqb0. rewrite negb_true_iff in H3.
    unfold Val.modls in H1. destruct x, y; inv H1.
    destruct (Int64.eq i0 Int64.zero || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone) eqn:?; inv H5. InvBooleans.
    exploit eval_neg_cond; auto. eexact H. eexact H. intros A1.
    exploit eval_neg_cond; auto. eexact H0. eexact H0. intros A2.
    set (modlu_v :=Vlong (Int64.modu (if Int64.lt i Int64.zero then Int64.neg i else i) (if Int64.lt i0 Int64.zero then Int64.neg i0 else i0))).
    exploit eval_modlu_base.  eexact A1. eexact A2. instantiate (1:= modlu_v).
    unfold Val.modlu. destruct (Int64.lt i0 Int64.zero); [rewrite <- Int64.neg_eq_zero|]; rewrite H1; reflexivity.
    intros [v1 [A3 B3]]. inv B3.
    exploit eval_neg_cond; auto. eexact H. eexact A3. intros. rewrite <- Int64.mods_modu in H5 by auto.
    econstructor; split; EvalOp.
  - econstructor; split. eapply eval_helper_2; eauto. DeclHelper. reflexivity. eassumption. auto.
Qed.

Theorem eval_divls_base:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.divls x y = Some z ->
  exists v, eval_expr ge sp e m le (divls_base a b) v /\ Val.lessdef z v.
Proof.
  intros; unfold divls_base. destruct (Compopts.inlined_runtime tt && negb Archi.ptr64) eqn:?.
  - rewrite andb_true_iff in Heqb0. destruct Heqb0. rewrite negb_true_iff in H3. unfold Val.divls in H1. destruct x, y; inv H1.
    destruct (Int64.eq i0 Int64.zero || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone) eqn:?; inv H5.
    InvBooleans.
    exploit eval_neg_cond; auto. eexact H. eexact H. intros A1.
    exploit eval_neg_cond; auto. eexact H0. eexact H0. intros A2.
    set (divlu_v :=Vlong (Int64.divu (if Int64.lt i Int64.zero then Int64.neg i else i) (if Int64.lt i0 Int64.zero then Int64.neg i0 else i0))).
    exploit eval_divlu_base.  eexact A1. eexact A2. instantiate (1:= divlu_v).
    unfold Val.divlu. destruct (Int64.lt i0 Int64.zero); [rewrite <- Int64.neg_eq_zero |]; rewrite H1; reflexivity.
    intros [v1 [A3 B3]]. inv B3.
    exploit eval_xorl. eexact H. eexact H0. intros [v4 [A4 B4]]. inv B4.
    exploit eval_neg_cond; auto. eexact A4. eexact A3. intros.
    rewrite Int64.xor_lt_zero in H5 by (change Int64.zwordsize with 64; lia).
    rewrite <- Int64.divs_divu in H5 by auto.
    econstructor; split; eauto.
  - econstructor; split. eapply eval_helper_2; eauto. DeclHelper. reflexivity. eassumption. auto.
Qed.

Theorem eval_mul':
  binary_constructor_sound mul' Val.mull'.
Proof.
  unfold mul'; intros; red; intros.
  destruct (platform_standard_builtin) eqn:?.
  + exploit (eval_platform_standard_builtin); eauto. EvalOp.
    reflexivity.
  + exploit eval_mulhu. eexact H. eexact H0. intros [v1 [A1 B1]].
    exploit eval_mul. eexact H. eexact H0. intros [v2 [A2 B2]].
    econstructor; split. EvalOp. destruct x, y; auto.
    simpl in *. inv B1. inv B2. simpl. rewrite Int64.mul'_mulhu.
    auto.
Qed.

Theorem eval_mullhu:
  forall n, unary_constructor_sound (fun a => mullhu a n) (fun v => Val.mullhu v (Vlong n)).
Proof.
  unfold mullhu; intros; red; intros.
  destruct (Compopts.inlined_runtime tt && negb Archi.ptr64) eqn:?.
  - InvBooleans. apply negb_true_iff in H1.
    assert (eval_makelong_lo: forall a v,
               eval_expr ge sp e m le a v ->
               exists v',
                 eval_expr ge sp e m le (makelong (Eop (Ointconst Int.zero) Enil) a) v'
                 /\ Val.lessdef (Val.longofwords Vzero v) v').
    { intros. econstructor; split; EvalOp. }
    exploit eval_highlong. eexact H. intros [v1 [A1 B1]].
    exploit eval_lowlong. eexact H. intros [v2 [A2 B2]].
    assert (A3: eval_expr ge sp e m le (Eop (Ointconst (Int64.loword n)) Enil) (Vint (Int64.loword n))) by EvalOp.
    assert (A4: eval_expr ge sp e m le (Eop (Ointconst (Int64.hiword n)) Enil) (Vint (Int64.hiword n))) by EvalOp.
    set (xhyh := mul' (highlong a) (Eop (Ointconst (Int64.hiword n)) Enil)).
    exploit eval_mul'. eexact A1. eexact A4. fold xhyh. intros [v5 [A5 B5]].
    set (xhyl_h := makelong (Eop (Ointconst Int.zero) Enil) (mulhu (highlong a) (Eop (Ointconst (Int64.loword n)) Enil))).
    exploit eval_mulhu. eexact A1. eexact A3. intros [v6 [A6 B6]].
    exploit eval_makelong_lo. eexact A6. fold xhyl_h. intros [v7 [A7 B7]].
    set (xlyh_h := makelong (Eop (Ointconst Int.zero) Enil) (mulhu (lowlong a) (Eop (Ointconst (Int64.hiword n)) Enil))).
    exploit eval_mulhu. eexact A2. eexact A4. intros [v8 [A8 B8]].
    exploit eval_makelong_lo. eexact A8. fold xlyh_h. intros [v9 [A9 B9]].
    exploit eval_addl; auto. eexact A7. eexact A9. intros [v10 [A10 B10]].
    set (xlyl := makelong (Eop (Ointconst Int.zero) Enil) (mulhu (lowlong a) (Eop (Ointconst (Int64.loword n)) Enil))).
    exploit eval_mulhu. eexact A2. eexact A3. intros [v11 [A11 B11]].
    exploit eval_makelong_lo. eexact A11. fold xlyl. intros [v12 [A12 B12]].
    set (xhyl_l := makelong (Eop (Ointconst Int.zero) Enil) (mulimm (Int64.loword n) (highlong a))).
    exploit eval_mulimm. eexact A1. instantiate (1 := Int64.loword n). intros [v13 [A13 B13]].
    exploit eval_makelong_lo. eexact A13. fold xhyl_l. intros [v14 [A14 B14]].
    set (xlyh_l := makelong (Eop (Ointconst Int.zero) Enil) (mulimm (Int64.hiword n) (lowlong a))).
    exploit eval_mulimm. eexact A2. instantiate (1 := Int64.hiword n). intros [v15 [A15 B15]].
    exploit eval_makelong_lo. eexact A15. fold xlyh_l. intros [v16 [A16 B16]].
    set (k1 := addl xhyl_l xlyh_l).
    exploit eval_addl; auto. eexact A14. eexact A16. fold k1. intros [v17 [A17 B17]].
    set (k2 := addl k1 xlyl).
    exploit eval_addl; auto. eexact A17. eexact A12. fold k2. intros [v18 [A18 B18]].
    set (k3:= addl xhyl_h xlyh_h) in *.
    exploit eval_shrluimm. eexact A18. instantiate (1:= Int.repr (32)). intros [v19 [A19 B19]].
    set (k4 := addl k3 (shrluimm k2 (Int.repr 32))).
    exploit eval_addl; auto. eexact A10. eexact A19. fold k4. intros [v20 [A20 B20]].
    exploit eval_addl; auto. eexact A5. eexact A20. intros [v21 [A21 B21]].
    exists v21; split; EvalOp.
    destruct x; auto. inv B1. inv B2. inv B5. inv B6. inv B7. inv B8. inv B9. inv B10. inv B11. inv B12.
    inv B13. inv B14. inv B15. inv B16. inv B17. inv B18. inv B19. inv B20. inv B21. simpl.
    rewrite ! H1. change (Int.ltu (Int.repr 32) Int64.iwordsize') with true. simpl.
    rewrite <- (Int64.ofwords_recompose i). rewrite <- (Int64.ofwords_recompose n).
    rewrite Int64.decompose_mulhu. rewrite ! Int64.hi_ofwords. rewrite ! Int64.lo_ofwords. auto.
  - econstructor; split; eauto.
    eapply eval_helper_2; eauto. apply eval_longconst. DeclHelper. reflexivity. reflexivity.
Qed.


Theorem eval_mullhs:
  forall n, unary_constructor_sound (fun a => mullhs a n) (fun v => Val.mullhs v (Vlong n)).
Proof.
  unfold mullhs; intros; red; intros.
  destruct (Compopts.inlined_runtime tt && negb Archi.ptr64) eqn:?; eauto.
  - rewrite andb_true_iff in Heqb. destruct Heqb. rewrite negb_true_iff in H1.
    set (mask := makelong (shrimm (highlong a) (Int.repr 31)) (shrimm (highlong a) (Int.repr 31))).
    exploit eval_mullhu. eexact H. instantiate (1 := n).
    intros [v1 [A1 B1]].
    generalize (eval_longconst le n). intros A2.
    exploit eval_highlong. eexact H.
    intros [v3 [A3 B3]].
    exploit eval_shrimm. eexact A3. instantiate (1 := (Int.repr 31)).
    intros [v4 [A4 B4]].
    exploit eval_andl. instantiate (2 := mask). EvalOp. eexact A2.
    intros [v5 [A5 B5]].
    exploit eval_subl; auto. eexact A1. eexact A5.
    intros [v6 [A6 B6]].
    exploit eval_subl; auto. eexact A6. eexact H.
    intros [v7 [A7 B7]].
    set (e0 := subl (mullhu a n) (andl mask (longconst n))) in *.
    set (e' := if Int64.lt n Int64.zero then subl e0 a else e0).
    set (v8 := if Int64.lt n Int64.zero then v7 else v6).
    assert (eval_expr ge sp e m le e' v8) by (destruct (Int64.lt n Int64.zero); eauto).
    exists v8; split; EvalOp.
    destruct x; auto. simpl. inv B1. inv B3. simpl in *.
    change (Int.ltu (Int.repr 31) Int.iwordsize) with true in B4. simpl in B4.
    inv B4. simpl in *.
    rewrite Int.shr_lt_zero in B5. rewrite <- (decompose_cmpl_lt_zero _ (Int64.loword i)) in B5. rewrite Int64.ofwords_recompose in B5.
    inv B5. inv B6. inv B7. subst v8.
    rewrite Int64.mulhs_mulhu.
    destruct (Int64.lt i Int64.zero).
    replace (Int64.and (Int64.ofwords Int.mone Int.mone) n) with n. destruct Int64.lt; auto.
    replace (Int64.ofwords Int.mone Int.mone) with Int64.mone. symmetry. apply Int64.and_mone_l.
    apply Int64.same_bits_eq. intros. rewrite Int64.bits_ofwords by lia.
    rewrite Int64.bits_mone; try lia.
    change Int64.zwordsize with (2 * Int.zwordsize) in *.
    destruct (zlt i0 Int.zwordsize); rewrite Int.bits_mone; auto; lia.
    replace (Int64.ofwords Int.zero Int.zero) with Int64.zero by (rewrite Int64.ofwords_add; reflexivity). rewrite Int64.and_zero_l.
    rewrite Int64.sub_zero_l. simpl. destruct Int64.lt; auto.
  - econstructor; split; eauto.
    eapply eval_helper_2; eauto. apply eval_longconst. DeclHelper. reflexivity. reflexivity .
Qed.

End CMCONSTR.
