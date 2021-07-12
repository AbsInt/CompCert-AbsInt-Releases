(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, Collège de France and Inria Paris            *)
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

(** Platform-specific built-in functions *)

Require Import String Coqlib.
Require Import AST Integers Floats Values.
Require Import Builtins0.

Inductive platform_builtin : Type :=
  | BI_isnanf
  | BI_isnan
  | BI_isinff
  | BI_isinf
  | BI_isfinitef
  | BI_isfinite.

Local Open Scope string_scope.

Definition platform_builtin_table : list (string * platform_builtin) :=
    ("__builtin_isnanf", BI_isnanf)
  :: ("__builtin_isnan", BI_isnan)
  :: ("__builtin_isinff", BI_isinff)
  :: ("__builtin_isinf", BI_isinf)
  :: ("__builtin_isfinitef", BI_isfinitef)
  :: ("__builtin_isfinite", BI_isfinite)
  :: nil.

Definition platform_builtin_sig (b: platform_builtin) : signature :=
  match b with
  | BI_isnanf | BI_isinff | BI_isfinitef =>
     mksignature (Tsingle :: nil) Tint cc_default
  | BI_isnan | BI_isinf | BI_isfinite =>
    mksignature (Tfloat :: nil) Tint cc_default
  end.

Definition platform_builtin_sem (b: platform_builtin) : builtin_sem (sig_res (platform_builtin_sig b)) :=
  match b with
  | BI_isnanf =>
      mkbuiltin_n1t Tsingle Tint (fun f => if Binary.is_nan _ _ f then Int.one else Int.zero)
  | BI_isnan =>
      mkbuiltin_n1t Tfloat Tint (fun f => if Binary.is_nan _ _ f then Int.one else Int.zero)
  | BI_isinff =>
      mkbuiltin_n1t Tsingle Tint (fun f => if negb (Binary.is_finite _ _ f || Binary.is_nan _ _ f) then Int.one else Int.zero)
  | BI_isinf =>
      mkbuiltin_n1t Tfloat Tint (fun f => if negb (Binary.is_finite _ _ f || Binary.is_nan _ _ f) then Int.one else Int.zero)
  | BI_isfinitef =>
      mkbuiltin_n1t Tsingle Tint (fun f => if Binary.is_finite _ _ f then Int.one else Int.zero)
  | BI_isfinite =>
      mkbuiltin_n1t Tfloat Tint (fun f => if Binary.is_finite _ _ f then Int.one else Int.zero)
  end.
