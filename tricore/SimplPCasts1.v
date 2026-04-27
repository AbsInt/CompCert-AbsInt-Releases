(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Jan Menz, AbsInt Angewandte Informatik GmbH                *)
(*                                                                     *)
(*  AbsInt Angewandte Informatik GmbH. All rights reserved. This file  *)
(*  is distributed under the terms of the INRIA Non-Commercial         *)
(*  License Agreement.                                                 *)
(*                                                                     *)
(* *********************************************************************)

Require Import  Coqlib Op AST RTL RTLtyping.

Definition simplify  (env: regenv) instr: instruction :=
  match instr with
  | Iop Opcast (r1 :: nil) res n =>
      match env r1 with
      | Pptr => Iop Omove (r1 :: nil) res n
      | _ => instr
      end
  | _ => instr
  end.

Definition simplify_function env (f:function): function :=
  mkfunction
    (fn_sig f)
    (fn_params f)
    (fn_stacksize f)
    (Maps.PTree.map1 (simplify env) (fn_code f))
    (fn_entrypoint f).

Lemma simplify_function_preserves_valid_successor:
  forall env f s,
    valid_successor f s -> valid_successor (simplify_function env f) s.
Proof.
  intros. inv H.  econstructor.  simpl.
  rewrite Maps.PTree.gmap1. rewrite H0. reflexivity.
Qed.

Lemma simplify_preserves_typing:
  forall f instr env,
    wt_instr f env instr -> wt_instr (simplify_function env f) env (simplify env instr).
Proof.
  intros. inv H; cbn; try econstructor; eauto using simplify_function_preserves_valid_successor.
  destruct op; try congruence; try now (econstructor; eauto using simplify_function_preserves_valid_successor).
  destruct args.
  - econstructor; eauto using simplify_function_preserves_valid_successor.
  - destruct args; try econstructor; eauto using simplify_function_preserves_valid_successor.
    destruct (env r) eqn:E; econstructor; eauto using simplify_function_preserves_valid_successor.
    simpl in *. rewrite E in *. inv H1.
    destruct H3; auto.
Qed.        

Lemma get_simplified_instr:
  forall pc env f i,
    Maps.PTree.get pc (fn_code (simplify_function env f)) = Some i ->
    exists inst, Maps.PTree.get pc (fn_code f) = Some inst /\ i = simplify env inst.
Proof.
  intros. cbn in H. rewrite Maps.PTree.gmap1 in H.
  destruct (Maps.PTree.get pc (fn_code f)) eqn:E; inv H. eauto.
Qed.

Lemma simplify_preserves_function_typing:
  forall f env,
    wt_function f env -> wt_function (simplify_function env f) env.
Proof.
  intros. inv H. constructor; try assumption.
  - intros. apply get_simplified_instr in H as (inst & A & B). rewrite B.
    apply simplify_preserves_typing. eapply wt_instrs; eauto.
  - apply simplify_function_preserves_valid_successor; auto.
Qed.

Definition simplify_typed_fun f: typed_fun :=
  match f with
  | TF f env wt => TF (simplify_function env f) env (simplify_preserves_function_typing f env wt)
  end.
    
Definition simplify_fundef (f: typed_fundef) : typed_fundef :=
  transf_fundef simplify_typed_fun f.

Definition transf_program p: AST.program typed_fundef unit :=
  transform_program (simplify_fundef) p.
