(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(*- E_COMPCERT_FTR_Clightdefs_001 *)
(*- #Justify_Derived "Module Clightdefs.v is part of the clightgen tool and not part of CompCert." *)

(** Definitions used by .v files generated by clightgen *)

From Coq Require Import List.
From compcert Require Import Maps Errors AST Ctypes Clight.
From compcert Require Export Ctypesdefs.

(** ** Constructor for programs and compilation units *)

Definition wf_composites (types: list composite_definition) : Prop :=
  match build_composite_env types with OK _ => True | Error _ => False end.

Definition build_composite_env' (types: list composite_definition)
                                (WF: wf_composites types)
                             : { ce | build_composite_env types  = OK ce }.
Proof.
  revert WF. unfold wf_composites. case (build_composite_env types); intros.
- exists c; reflexivity.
- contradiction.
Defined.

Definition mkprogram (types: list composite_definition)
                     (defs: list (ident * globdef fundef type))
                     (public: list ident)
                     (main: ident)
                     (WF: wf_composites types) : Clight.program :=
  let (ce, EQ) := build_composite_env' types WF in
  {| prog_defs := defs;
     prog_public := public;
     prog_main := main;
     prog_types := types;
     prog_comp_env := ce;
     prog_comp_env_eq := EQ |}.

(** ** Notations *)

Module ClightNotations.

(** A convenient notation [$ "ident"] to force evaluation of
    [ident_of_string "ident"] *)

Ltac ident_of_string s :=
  let x := constr:(ident_of_string s) in
  let y := eval compute in x in
  exact y.

Notation "$ s" := (ltac:(ident_of_string s))
                  (at level 1, only parsing) : clight_scope.

End ClightNotations.
(*- #End *)
