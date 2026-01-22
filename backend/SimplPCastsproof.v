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

Require SimplPCastsproof1.
Require Import RTLtyping SimplPCasts1 Smallstep.

Definition match_prog := SimplPCastsproof1.match_prog.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  exact SimplPCastsproof1.transf_program_match. 
Qed.

Section PRESERVATION.
  
Variable prog: program.
Variable tprog : program.
Hypothesis TRANSF: match_prog prog tprog.

Theorem transf_program_correct:
  forward_simulation (RTLtyping.semantics prog) (RTLtyping.semantics tprog).
Proof.
  exact (SimplPCastsproof1.transf_program_correct prog tprog TRANSF).
Qed.

End PRESERVATION.
