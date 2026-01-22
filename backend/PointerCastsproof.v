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


Require Import RTL PointerCasts Smallstep.
Require PointerCastsproof1.

Definition match_prog := PointerCastsproof1.match_prog.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  exact PointerCastsproof1.transf_program_match.
Qed.

Section PRESERVATION.

Variable prog: program.
Variable tprog : program.
Hypothesis TRANSF: match_prog prog tprog.

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  exact (PointerCastsproof1.transf_program_correct prog tprog TRANSF).
Qed.

End PRESERVATION.


