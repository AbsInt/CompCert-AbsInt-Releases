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

(** All imports and definitions used by .v Clight files generated by clightgen *)

From Coq Require Import Ascii String List ZArith.
From compcert Require Import Integers Floats Maps Errors AST Ctypes Cop Clight.

(** ** Short names for types *)

Definition tvoid := Tvoid.
Definition tschar := Tint I8 Signed noattr.
Definition tuchar := Tint I8 Unsigned noattr.
Definition tshort := Tint I16 Signed noattr.
Definition tushort := Tint I16 Unsigned noattr.
Definition tint := Tint I32 Signed noattr.
Definition tuint := Tint I32 Unsigned noattr.
Definition tbool := Tint IBool Unsigned noattr.
Definition tlong := Tlong Signed noattr.
Definition tulong := Tlong Unsigned noattr.
Definition tfloat := Tfloat F32 noattr.
Definition tdouble := Tfloat F64 noattr.
Definition tptr (t: type) := Tpointer t noattr.
Definition tarray (t: type) (sz: Z) := Tarray t sz noattr.

Definition volatile_attr := {| attr_volatile := true; attr_alignas := None |}.

Definition tattr (a: attr) (ty: type) :=
  match ty with
  | Tvoid => Tvoid
  | Tint sz si _ => Tint sz si a
  | Tlong si _ => Tlong si a
  | Tfloat sz _ => Tfloat sz a
  | Tpointer elt _ => Tpointer elt a
  | Tarray elt sz _ => Tarray elt sz a
  | Tfunction args res cc => Tfunction args res cc
  | Tstruct id _ => Tstruct id a
  | Tunion id  _ => Tunion id a
  end.

Definition tvolatile (ty: type) := tattr volatile_attr ty.

Definition talignas (n: N) (ty: type) :=
  tattr {| attr_volatile := false; attr_alignas := Some n |} ty.

Definition tvolatile_alignas (n: N) (ty: type) :=
  tattr {| attr_volatile := true; attr_alignas := Some n |} ty.

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

(** ** Encoding character strings as positive numbers *)

(** The following encoding of character strings as positive numbers
    must be kept consistent with the OCaml function [Camlcoq.pos_of_string]. *)

Definition append_bit_pos (b: bool) (p: positive) : positive :=
  if b then xI p else xO p.

Definition append_char_pos_default (c: ascii) (p: positive) : positive :=
  let '(Ascii b7 b6 b5 b4 b3 b2 b1 b0) := c in
  xI (xI (xI (xI (xI (xI
    (append_bit_pos b0 (append_bit_pos b1
    (append_bit_pos b2 (append_bit_pos b3
    (append_bit_pos b4 (append_bit_pos b5
    (append_bit_pos b6 (append_bit_pos b7 p))))))))))))).

Definition append_char_pos (c: ascii) (p: positive) : positive :=
  match c with
  | "0"%char => xO (xO (xO (xO (xO (xO p)))))
  | "1"%char => xI (xO (xO (xO (xO (xO p)))))
  | "2"%char => xO (xI (xO (xO (xO (xO p)))))
  | "3"%char => xI (xI (xO (xO (xO (xO p)))))
  | "4"%char => xO (xO (xI (xO (xO (xO p)))))
  | "5"%char => xI (xO (xI (xO (xO (xO p)))))
  | "6"%char => xO (xI (xI (xO (xO (xO p)))))
  | "7"%char => xI (xI (xI (xO (xO (xO p)))))
  | "8"%char => xO (xO (xO (xI (xO (xO p)))))
  | "9"%char => xI (xO (xO (xI (xO (xO p)))))
  | "a"%char => xO (xI (xO (xI (xO (xO p)))))
  | "b"%char => xI (xI (xO (xI (xO (xO p)))))
  | "c"%char => xO (xO (xI (xI (xO (xO p)))))
  | "d"%char => xI (xO (xI (xI (xO (xO p)))))
  | "e"%char => xO (xI (xI (xI (xO (xO p)))))
  | "f"%char => xI (xI (xI (xI (xO (xO p)))))
  | "g"%char => xO (xO (xO (xO (xI (xO p)))))
  | "h"%char => xI (xO (xO (xO (xI (xO p)))))
  | "i"%char => xO (xI (xO (xO (xI (xO p)))))
  | "j"%char => xI (xI (xO (xO (xI (xO p)))))
  | "k"%char => xO (xO (xI (xO (xI (xO p)))))
  | "l"%char => xI (xO (xI (xO (xI (xO p)))))
  | "m"%char => xO (xI (xI (xO (xI (xO p)))))
  | "n"%char => xI (xI (xI (xO (xI (xO p)))))
  | "o"%char => xO (xO (xO (xI (xI (xO p)))))
  | "p"%char => xI (xO (xO (xI (xI (xO p)))))
  | "q"%char => xO (xI (xO (xI (xI (xO p)))))
  | "r"%char => xI (xI (xO (xI (xI (xO p)))))
  | "s"%char => xO (xO (xI (xI (xI (xO p)))))
  | "t"%char => xI (xO (xI (xI (xI (xO p)))))
  | "u"%char => xO (xI (xI (xI (xI (xO p)))))
  | "v"%char => xI (xI (xI (xI (xI (xO p)))))
  | "w"%char => xO (xO (xO (xO (xO (xI p)))))
  | "x"%char => xI (xO (xO (xO (xO (xI p)))))
  | "y"%char => xO (xI (xO (xO (xO (xI p)))))
  | "z"%char => xI (xI (xO (xO (xO (xI p)))))
  | "A"%char => xO (xO (xI (xO (xO (xI p)))))
  | "B"%char => xI (xO (xI (xO (xO (xI p)))))
  | "C"%char => xO (xI (xI (xO (xO (xI p)))))
  | "D"%char => xI (xI (xI (xO (xO (xI p)))))
  | "E"%char => xO (xO (xO (xI (xO (xI p)))))
  | "F"%char => xI (xO (xO (xI (xO (xI p)))))
  | "G"%char => xO (xI (xO (xI (xO (xI p)))))
  | "H"%char => xI (xI (xO (xI (xO (xI p)))))
  | "I"%char => xO (xO (xI (xI (xO (xI p)))))
  | "J"%char => xI (xO (xI (xI (xO (xI p)))))
  | "K"%char => xO (xI (xI (xI (xO (xI p)))))
  | "L"%char => xI (xI (xI (xI (xO (xI p)))))
  | "M"%char => xO (xO (xO (xO (xI (xI p)))))
  | "N"%char => xI (xO (xO (xO (xI (xI p)))))
  | "O"%char => xO (xI (xO (xO (xI (xI p)))))
  | "P"%char => xI (xI (xO (xO (xI (xI p)))))
  | "Q"%char => xO (xO (xI (xO (xI (xI p)))))
  | "R"%char => xI (xO (xI (xO (xI (xI p)))))
  | "S"%char => xO (xI (xI (xO (xI (xI p)))))
  | "T"%char => xI (xI (xI (xO (xI (xI p)))))
  | "U"%char => xO (xO (xO (xI (xI (xI p)))))
  | "V"%char => xI (xO (xO (xI (xI (xI p)))))
  | "W"%char => xO (xI (xO (xI (xI (xI p)))))
  | "X"%char => xI (xI (xO (xI (xI (xI p)))))
  | "Y"%char => xO (xO (xI (xI (xI (xI p)))))
  | "Z"%char => xI (xO (xI (xI (xI (xI p)))))
  | "_"%char => xO (xI (xI (xI (xI (xI p)))))
  | _ => append_char_pos_default c p
  end.

Fixpoint ident_of_string (s: string) : ident :=
  match s with
  | EmptyString => xH
  | String c s => append_char_pos c (ident_of_string s)
  end.

(** The inverse conversion, from encoded strings to strings *)

Section DECODE_BITS.

Variable rec: positive -> string.

Fixpoint decode_n_bits (n: nat) (l: list bool) (p: positive) : string :=
  match n with
  | O => 
      match l with 
      | b7 :: b6 :: b5 :: b4 :: b3 :: b2 :: b1 :: b0 :: _ =>
          String (Ascii b7 b6 b5 b4 b3 b2 b1 b0) (rec p)
      | _ => EmptyString
      end
  | S n =>
      match p with
      | xO q => decode_n_bits n (false :: l) q
      | xI q => decode_n_bits n (true :: l) q
      | xH => EmptyString
      end
  end.

Definition decode_8_bits := Eval compute in (decode_n_bits 8%nat nil).

End DECODE_BITS.

Fixpoint string_of_ident (p: positive) : string :=
  match p with
  | xO (xO (xO (xO (xO (xO p))))) => String "0"%char (string_of_ident p)
  | xI (xO (xO (xO (xO (xO p))))) => String "1"%char (string_of_ident p)
  | xO (xI (xO (xO (xO (xO p))))) => String "2"%char (string_of_ident p)
  | xI (xI (xO (xO (xO (xO p))))) => String "3"%char (string_of_ident p)
  | xO (xO (xI (xO (xO (xO p))))) => String "4"%char (string_of_ident p)
  | xI (xO (xI (xO (xO (xO p))))) => String "5"%char (string_of_ident p)
  | xO (xI (xI (xO (xO (xO p))))) => String "6"%char (string_of_ident p)
  | xI (xI (xI (xO (xO (xO p))))) => String "7"%char (string_of_ident p)
  | xO (xO (xO (xI (xO (xO p))))) => String "8"%char (string_of_ident p)
  | xI (xO (xO (xI (xO (xO p))))) => String "9"%char (string_of_ident p)
  | xO (xI (xO (xI (xO (xO p))))) => String "a"%char (string_of_ident p)
  | xI (xI (xO (xI (xO (xO p))))) => String "b"%char (string_of_ident p)
  | xO (xO (xI (xI (xO (xO p))))) => String "c"%char (string_of_ident p)
  | xI (xO (xI (xI (xO (xO p))))) => String "d"%char (string_of_ident p)
  | xO (xI (xI (xI (xO (xO p))))) => String "e"%char (string_of_ident p)
  | xI (xI (xI (xI (xO (xO p))))) => String "f"%char (string_of_ident p)
  | xO (xO (xO (xO (xI (xO p))))) => String "g"%char (string_of_ident p)
  | xI (xO (xO (xO (xI (xO p))))) => String "h"%char (string_of_ident p)
  | xO (xI (xO (xO (xI (xO p))))) => String "i"%char (string_of_ident p)
  | xI (xI (xO (xO (xI (xO p))))) => String "j"%char (string_of_ident p)
  | xO (xO (xI (xO (xI (xO p))))) => String "k"%char (string_of_ident p)
  | xI (xO (xI (xO (xI (xO p))))) => String "l"%char (string_of_ident p)
  | xO (xI (xI (xO (xI (xO p))))) => String "m"%char (string_of_ident p)
  | xI (xI (xI (xO (xI (xO p))))) => String "n"%char (string_of_ident p)
  | xO (xO (xO (xI (xI (xO p))))) => String "o"%char (string_of_ident p)
  | xI (xO (xO (xI (xI (xO p))))) => String "p"%char (string_of_ident p)
  | xO (xI (xO (xI (xI (xO p))))) => String "q"%char (string_of_ident p)
  | xI (xI (xO (xI (xI (xO p))))) => String "r"%char (string_of_ident p)
  | xO (xO (xI (xI (xI (xO p))))) => String "s"%char (string_of_ident p)
  | xI (xO (xI (xI (xI (xO p))))) => String "t"%char (string_of_ident p)
  | xO (xI (xI (xI (xI (xO p))))) => String "u"%char (string_of_ident p)
  | xI (xI (xI (xI (xI (xO p))))) => String "v"%char (string_of_ident p)
  | xO (xO (xO (xO (xO (xI p))))) => String "w"%char (string_of_ident p)
  | xI (xO (xO (xO (xO (xI p))))) => String "x"%char (string_of_ident p)
  | xO (xI (xO (xO (xO (xI p))))) => String "y"%char (string_of_ident p)
  | xI (xI (xO (xO (xO (xI p))))) => String "z"%char (string_of_ident p)
  | xO (xO (xI (xO (xO (xI p))))) => String "A"%char (string_of_ident p)
  | xI (xO (xI (xO (xO (xI p))))) => String "B"%char (string_of_ident p)
  | xO (xI (xI (xO (xO (xI p))))) => String "C"%char (string_of_ident p)
  | xI (xI (xI (xO (xO (xI p))))) => String "D"%char (string_of_ident p)
  | xO (xO (xO (xI (xO (xI p))))) => String "E"%char (string_of_ident p)
  | xI (xO (xO (xI (xO (xI p))))) => String "F"%char (string_of_ident p)
  | xO (xI (xO (xI (xO (xI p))))) => String "G"%char (string_of_ident p)
  | xI (xI (xO (xI (xO (xI p))))) => String "H"%char (string_of_ident p)
  | xO (xO (xI (xI (xO (xI p))))) => String "I"%char (string_of_ident p)
  | xI (xO (xI (xI (xO (xI p))))) => String "J"%char (string_of_ident p)
  | xO (xI (xI (xI (xO (xI p))))) => String "K"%char (string_of_ident p)
  | xI (xI (xI (xI (xO (xI p))))) => String "L"%char (string_of_ident p)
  | xO (xO (xO (xO (xI (xI p))))) => String "M"%char (string_of_ident p)
  | xI (xO (xO (xO (xI (xI p))))) => String "N"%char (string_of_ident p)
  | xO (xI (xO (xO (xI (xI p))))) => String "O"%char (string_of_ident p)
  | xI (xI (xO (xO (xI (xI p))))) => String "P"%char (string_of_ident p)
  | xO (xO (xI (xO (xI (xI p))))) => String "Q"%char (string_of_ident p)
  | xI (xO (xI (xO (xI (xI p))))) => String "R"%char (string_of_ident p)
  | xO (xI (xI (xO (xI (xI p))))) => String "S"%char (string_of_ident p)
  | xI (xI (xI (xO (xI (xI p))))) => String "T"%char (string_of_ident p)
  | xO (xO (xO (xI (xI (xI p))))) => String "U"%char (string_of_ident p)
  | xI (xO (xO (xI (xI (xI p))))) => String "V"%char (string_of_ident p)
  | xO (xI (xO (xI (xI (xI p))))) => String "W"%char (string_of_ident p)
  | xI (xI (xO (xI (xI (xI p))))) => String "X"%char (string_of_ident p)
  | xO (xO (xI (xI (xI (xI p))))) => String "Y"%char (string_of_ident p)
  | xI (xO (xI (xI (xI (xI p))))) => String "Z"%char (string_of_ident p)
  | xO (xI (xI (xI (xI (xI p))))) => String "_"%char (string_of_ident p)
  | xI (xI (xI (xI (xI (xI p))))) => decode_8_bits string_of_ident p
  | _ => EmptyString
  end.

Lemma string_of_ident_of_string:
  forall s, string_of_ident (ident_of_string s) = s.
Proof.
  induction s as [ | c s]; simpl.
- auto.
- rewrite <- IHs at 2. destruct c as [[] [] [] [] [] [] [] []]; reflexivity.
Qed.

Corollary ident_of_string_injective:
  forall s1 s2, ident_of_string s1 = ident_of_string s2 -> s1 = s2.
Proof.
  intros. rewrite <- (string_of_ident_of_string s1), <- (string_of_ident_of_string s2).
  congruence.
Qed.

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
