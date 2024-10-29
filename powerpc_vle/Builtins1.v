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
Local Open Scope asttyp_scope.

(*- E_COMPCERT_FTR_Function_Builtins1_platform_builtin_0_001 *)
(*- #Justify_Derived "Internal type" *)
Inductive platform_builtin : Type :=
  | BI_isel
  | BI_uisel
  | BI_bsel
  | BI_mulhw
  | BI_mulhwu.
(*- #End *)

Local Open Scope string_scope.

(*- E_COMPCERT_FTR_Function_Builtins1_platform_builtin_table_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_EXTERNAL_FUNCTIONS_001 *)
Definition platform_builtin_table : list (string * platform_builtin) :=
    ("__builtin_isel", BI_isel)
  :: ("__builtin_uisel", BI_uisel)
  :: ("__builtin_bsel", BI_bsel)
  :: ("__builtin_mulhw", BI_mulhw)
  :: ("__builtin_mulhwu", BI_mulhwu)
  :: nil.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Builtins1_platform_builtin_sig_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_EXTERNAL_FUNCTIONS_001 *)
Definition platform_builtin_sig (b: platform_builtin) : signature :=
  match b with
  | BI_isel | BI_uisel =>
     [Xbool; Xint; Xint ---> Xint]
  | BI_bsel =>
     [Xbool; Xbool; Xbool ---> Xbool]
  | BI_mulhw | BI_mulhwu =>
     [Xint; Xint ---> Xint]
  end.
(*- #End *)

Definition isel {A: Type} (c: int) (n1 n2: A) : A :=
  if Int.eq c Int.zero then n2 else n1.

Program Definition bsel (c n1 n2: int) : { n : int | n = Int.zero \/ n = Int.one } :=
  if Int.eq (isel c n1 n2) Int.zero then Int.zero else Int.one.

(*- E_COMPCERT_FTR_Function_Builtins1_platform_builtin_sem_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_EXTERNAL_FUNCTIONS_001 *)
Definition platform_builtin_sem (b: platform_builtin) : builtin_sem (sig_res (platform_builtin_sig b)) :=
  match b with
  | BI_isel | BI_uisel =>
    mkbuiltin_n3t Tint Tint Tint Xint isel
  | BI_bsel =>
    mkbuiltin_n3t Tint Tint Tint Xbool bsel
  | BI_mulhw =>
    mkbuiltin_n2t Tint Tint Xint Int.mulhs
  | BI_mulhwu =>
    mkbuiltin_n2t Tint Tint Xint Int.mulhu
  end.
(*- #End *)
