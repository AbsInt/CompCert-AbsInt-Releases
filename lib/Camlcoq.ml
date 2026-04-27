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

(* Library of useful Caml <-> Coq conversions *)

open Datatypes
open BinNums
open BinNat
open BinInt
open BinPos
open! Floats

exception Overflow of string * coq_Z

(* Coq's [nat] type and some of its operations *)

module Nat = struct

  (*- E_COMPCERT_CODE_Camlcoq_Nat_t_001 *)
  (*- #Justify_Derived "Type definition" *)
  type t = nat = O | S of t
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Nat_to_int_001 *)
  (*- #Justify_Derived "Utility function" *)
  let rec to_int = function
  | O -> 0
  | S n -> let n = succ (to_int n) in
    assert (n >= 0);
    n
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Nat_to_int32_001 *)
  (*- #Justify_Derived "Utility function" *)
  let rec to_int32 = function
  | O -> 0l
  | S n ->
    let n = Int32.succ (to_int32 n) in
    assert (n >= 0l);
    n
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Nat_of_int_001 *)
  (*- #Justify_Derived "Utility function" *)
  let rec of_int n =
    assert (n >= 0);
    if n = 0 then O else S (of_int (pred n))
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Nat_of_int32_001 *)
  (*- #Justify_Derived "Utility function" *)
  let rec of_int32 n =
    assert (n >= 0l);
    if n = 0l then O else S (of_int32 (Int32.pred n))
  (*- #End *)

end


(* Coq's [positive] type and some of its operations *)

module P = struct

  (*- E_COMPCERT_CODE_Camlcoq_P_t_001 *)
  (*- #Justify_Derived "Type definition" *)
  type t = positive = Coq_xI of t | Coq_xO of t | Coq_xH
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_P_one_001 *)
  (*- #Justify_Derived "Utility constant" *)
  let one = Coq_xH
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_P_succ_001 *)
  (*- #Justify_Derived "Utility function" *)
  let succ = Pos.succ
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_P_pred_001 *)
  (*- #Justify_Derived "Utility function" *)
  let pred = Pos.pred
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_P_eq_001 *)
  (*- #Justify_Derived "Utility function" *)
  let eq x y = (Pos.compare x y = Eq)
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_P_lt_001 *)
  (*- #Justify_Derived "Utility function" *)
  let lt x y = (Pos.compare x y = Lt)
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_P_gt_001 *)
  (*- #Justify_Derived "Utility function" *)
  let gt x y = (Pos.compare x y = Gt)
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_P_le_001 *)
  (*- #Justify_Derived "Utility function" *)
  let le x y = (Pos.compare x y <> Gt)
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_P_ge_001 *)
  (*- #Justify_Derived "Utility function" *)
  let ge x y = (Pos.compare x y <> Lt)
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_P_compare_001 *)
  (*- #Justify_Derived "Utility function" *)
  let compare x y = match Pos.compare x y with Lt -> -1 | Eq -> 0 | Gt -> 1
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_P_of_int_001 *)
  (*- #Justify_Derived "Utility function" *)
  let rec of_int n =
    if n land 1 = 0 then
      if n = 0 then assert false else Coq_xO (of_int (n lsr 1))
    else
      if n = 1 then Coq_xH else Coq_xI (of_int (n lsr 1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_P_to_int_mod_001 *)
  (*- #Justify_Derived "Utility function" *)
  let rec to_int_mod = function
  | Coq_xI p -> let n = to_int_mod p in n + n + 1
  | Coq_xO p -> let n = to_int_mod p in n + n
  | Coq_xH -> 1
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_P_to_int_001 *)
  (*- #Justify_Derived "Utility function" *)
  let to_int =
    let m = of_int max_int in
    fun x ->
      if le x m then to_int_mod x else raise(Overflow("P.to_int", Zpos x))
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_P_of_int32_001 *)
  (*- #Justify_Derived "Utility function" *)
  let rec of_int32 n =
    if Int32.logand n 1l = 0l then
      if n = 0l
      then assert false
      else Coq_xO (of_int32 (Int32.shift_right_logical n 1))
    else
      if n = 1l
      then Coq_xH
      else Coq_xI (of_int32 (Int32.shift_right_logical n 1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_P_to_int32_mod_001 *)
  (*- #Justify_Derived "Utility function" *)
  let rec to_int32_mod = function
  | Coq_xI p -> Int32.add (Int32.shift_left (to_int32_mod p) 1) 1l
  | Coq_xO p -> Int32.shift_left (to_int32_mod p) 1
  | Coq_xH -> 1l
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_P_to_int32_001 *)
  (*- #Justify_Derived "Utility function" *)
  let to_int32 =
    let m = of_int32 Int32.max_int in
    fun x ->
      if le x m then to_int32_mod x else raise(Overflow("P.to_int32", Zpos x))
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_P_to_uint32_001 *)
  (*- #Justify_Derived "Utility function" *)
  let to_uint32 =
    let m = of_int32 (-1l) in
    fun x ->
      if le x m then to_int32_mod x else raise(Overflow("P.to_uint32", Zpos x))
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_P_of_int64_001 *)
  (*- #Justify_Derived "Utility function" *)
  let rec of_int64 n =
    if Int64.logand n 1L = 0L then
      if n = 0L
      then assert false
      else Coq_xO (of_int64 (Int64.shift_right_logical n 1))
    else
      if n = 1L
      then Coq_xH
      else Coq_xI (of_int64 (Int64.shift_right_logical n 1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_P_to_int64_mod_001 *)
  (*- #Justify_Derived "Utility function" *)
  let rec to_int64_mod = function
  | Coq_xI p -> Int64.add (Int64.shift_left (to_int64_mod p) 1) 1L
  | Coq_xO p -> Int64.shift_left (to_int64_mod p) 1
  | Coq_xH -> 1L
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_P_to_int64_001 *)
  (*- #Justify_Derived "Utility function" *)
  let to_int64 =
    let m = of_int64 Int64.max_int in
    fun x ->
      if le x m then to_int64_mod x else raise(Overflow("P.to_int64", Zpos x))
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_P_to_uint64_001 *)
  (*- #Justify_Derived "Utility function" *)
  let to_uint64 =
    let m = of_int64 (-1L) in
    fun x ->
      if le x m then to_int64_mod x else raise(Overflow("P.to_uint64", Zpos x))
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_P_op_eq_001 *)
  (*- #Justify_Derived "Utility function" *)
  let (=) = eq
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_P_op_lt_001 *)
  (*- #Justify_Derived "Utility function" *)
  let (<) = lt
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_P_op_le_001 *)
  (*- #Justify_Derived "Utility function" *)
  let (<=) = le
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_P_op_gt_001 *)
  (*- #Justify_Derived "Utility function" *)
  let (>) = gt
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_P_op_ge_001 *)
  (*- #Justify_Derived "Utility function" *)
  let (>=) = ge
  (*- #End *)

end

(* Coq's [N] type and some of its operations *)

module N = struct

  (*- E_COMPCERT_CODE_Camlcoq_N_t_001 *)
  (*- #Justify_Derived "Type definition" *)
  type t = coq_N = N0 | Npos of positive
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_N_zero_001 *)
  (*- #Justify_Derived "Utility constant" *)
  let zero = N0
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_N_one_001 *)
  (*- #Justify_Derived "Utility constant" *)
  let one = Npos Coq_xH
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_N_eq_001 *)
  (*- #Justify_Derived "Utility function" *)
  let eq x y = (N.compare x y = Eq)
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_N_lt_001 *)
  (*- #Justify_Derived "Utility function" *)
  let lt x y = (N.compare x y = Lt)
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_N_gt_001 *)
  (*- #Justify_Derived "Utility function" *)
  let gt x y = (N.compare x y = Gt)
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_N_le_001 *)
  (*- #Justify_Derived "Utility function" *)
  let le x y = (N.compare x y <> Gt)
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_N_ge_001 *)
  (*- #Justify_Derived "Utility function" *)
  let ge x y = (N.compare x y <> Lt)
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_N_compare_001 *)
  (*- #Justify_Derived "Utility function" *)
  let compare x y = match N.compare x y with Lt -> -1 | Eq -> 0 | Gt -> 1
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_N_of_int_001 *)
  (*- #Justify_Derived "Utility function" *)
  let of_int n =
    if n = 0 then N0 else Npos (P.of_int n)
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_N_to_int_mod_001 *)
  (*- #Justify_Derived "Utility function" *)
  let to_int_mod = function
  | N0 -> 0
  | Npos p -> P.to_int_mod p
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_N_to_int_001 *)
  (*- #Justify_Derived "Utility function" *)
  let to_int =
    let m = of_int max_int in
    fun x ->
      if le x m then to_int_mod x else raise(Overflow("N.to_int", Z.of_N x))
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_N_of_int32_001 *)
  (*- #Justify_Derived "Utility function" *)
  let of_int32 n =
    if n = 0l then N0 else Npos (P.of_int32 n)
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_N_to_int32_mod_001 *)
  (*- #Justify_Derived "Utility function" *)
  let to_int32_mod = function
  | N0 -> 0l
  | Npos p -> P.to_int32_mod p
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_N_to_int32_001 *)
  (*- #Justify_Derived "Utility function" *)
  let to_int32 =
    let m = of_int32 Int32.max_int in
    fun x ->
      if le x m then to_int32_mod x else raise(Overflow("N.to_int32", Z.of_N x))
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_N_to_uint32_001 *)
  (*- #Justify_Derived "Utility function" *)
  let to_uint32 =
    let m = of_int32 (-1l) in
    fun x ->
      if le x m then to_int32_mod x else raise(Overflow("N.to_uint32", Z.of_N x))
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_N_of_int64_001 *)
  (*- #Justify_Derived "Utility function" *)
  let of_int64 n =
    if n = 0L then N0 else Npos (P.of_int64 n)
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_N_to_int64_mod_001 *)
  (*- #Justify_Derived "Utility function" *)
  let to_int64_mod = function
  | N0 -> 0L
  | Npos p -> P.to_int64_mod p
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_N_to_int64_001 *)
  (*- #Justify_Derived "Utility function" *)
  let to_int64 =
    let m = of_int64 Int64.max_int in
    fun x ->
      if le x m then to_int64_mod x else raise(Overflow("N.to_int64", Z.of_N x))
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_N_to_uint64_001 *)
  (*- #Justify_Derived "Utility function" *)
  let to_uint64 =
    let m = of_int64 (-1L) in
    fun x ->
      if le x m then to_int64_mod x else raise(Overflow("N.to_uint64", Z.of_N x))
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_N_op_eq_001 *)
  (*- #Justify_Derived "Utility function" *)
  let (=) = eq
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_N_op_lt_001 *)
  (*- #Justify_Derived "Utility function" *)
  let (<) = lt
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_N_op_le_001 *)
  (*- #Justify_Derived "Utility function" *)
  let (<=) = le
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_N_op_gt_001 *)
  (*- #Justify_Derived "Utility function" *)
  let (>) = gt
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_N_op_ge_001 *)
  (*- #Justify_Derived "Utility function" *)
  let (>=) = ge
  (*- #End *)
end

(* Coq's [Z] type and some of its operations *)

module Z = struct

  (*- E_COMPCERT_CODE_Camlcoq_Z_t_001 *)
  (*- #Justify_Derived "Type definition" *)
  type t = coq_Z = Z0 | Zpos of positive | Zneg of positive
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_zero_001 *)
  (*- #Justify_Derived "Utility constant" *)
  let zero = Z0
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_one_001 *)
  (*- #Justify_Derived "Utility constant" *)
  let one = Zpos Coq_xH
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_mone_001 *)
  (*- #Justify_Derived "Utility constant" *)
  let mone = Zneg Coq_xH
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_succ_001 *)
  (*- #Justify_Derived "Utility function" *)
  let succ = Z.succ
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_pred_001 *)
  (*- #Justify_Derived "Utility function" *)
  let pred = Z.pred
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_neg_001 *)
  (*- #Justify_Derived "Utility function" *)
  let neg = Z.opp
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_add_001 *)
  (*- #Justify_Derived "Utility function" *)
  let add = Z.add
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_sub_001 *)
  (*- #Justify_Derived "Utility function" *)
  let sub = Z.sub
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_mul_001 *)
  (*- #Justify_Derived "Utility function" *)
  let mul = Z.mul
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_div_001 *)
  (*- #Justify_Derived "Utility function" *)
  let div = Z.div
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_modulo_001 *)
  (*- #Justify_Derived "Utility function" *)
  let modulo = Z.modulo
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_eq_001 *)
  (*- #Justify_Derived "Utility function" *)
  let eq x y = (Z.compare x y = Eq)
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_lt_001 *)
  (*- #Justify_Derived "Utility function" *)
  let lt x y = (Z.compare x y = Lt)
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_gt_001 *)
  (*- #Justify_Derived "Utility function" *)
  let gt x y = (Z.compare x y = Gt)
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_le_001 *)
  (*- #Justify_Derived "Utility function" *)
  let le x y = (Z.compare x y <> Gt)
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_ge_001 *)
  (*- #Justify_Derived "Utility function" *)
  let ge x y = (Z.compare x y <> Lt)
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_compare_001 *)
  (*- #Justify_Derived "Utility function" *)
  let compare x y = match Z.compare x y with Lt -> -1 | Eq -> 0 | Gt -> 1
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_of_sint_001 *)
  (*- #Justify_Derived "Utility function" *)
  let of_sint n =
    if n = 0 then Z0 else
    if n > 0 then Zpos (P.of_int n)
    (* if n is min_int then -n wraps around to min_int again *)
    else Zneg (P.of_int (-n))
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_of_uint_001 *)
  (*- #Justify_Derived "Utility function" *)
  let of_uint n =
    if n = 0 then Z0 else Zpos (P.of_int n)
  (*- #End *)


  (*- E_COMPCERT_CODE_Camlcoq_Z_to_int_mod_001 *)
  (*- #Justify_Derived "Utility function" *)
  let to_int_mod = function
  | Z0 -> 0
  | Zpos p -> P.to_int_mod p
  (* Special case if we convert the minimal value represantable as an OCaml
     integer. The conversion P.to_int_mod p with return the minimal value and the
     negation wraps around again to the minimal value *)
  | Zneg p -> - (P.to_int_mod p)
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_to_int_001 *)
  (*- #Justify_Derived "Utility function" *)
  let to_int =
    let min = of_sint min_int and max = of_sint max_int in
    fun x ->
      if le x max && ge x min
      then to_int_mod x
      else raise(Overflow("Z.to_int", x))
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_of_sint32_001 *)
  (*- #Justify_Derived "Utility function" *)
  let of_sint32 n =
    if n = 0l then Z0 else
    if n > 0l then Zpos (P.of_int32 n)
    else Zneg (P.of_int32 (Int32.neg n))
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_of_uint32_001 *)
  (*- #Justify_Derived "Utility function" *)
  let of_uint32 n =
    if n = 0l then Z0 else Zpos (P.of_int32 n)
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_to_int32_mod_001 *)
  (*- #Justify_Derived "Utility function" *)
  let to_int32_mod = function
  | Z0 -> 0l
  | Zpos p -> P.to_int32_mod p
  | Zneg p -> Int32.neg (P.to_int32_mod p)
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_to_int32_001 *)
  (*- #Justify_Derived "Utility function" *)
  let to_int32 =
    let min = of_sint32 Int32.min_int and max = of_sint32 Int32.max_int in
    fun x ->
      if le x max && ge x min
      then to_int32_mod x
      else raise(Overflow("Z.to_int32", x))
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_to_uint32_001 *)
  (*- #Justify_Derived "Utility function" *)
  let to_uint32 =
    let min = zero and max = of_uint32 (-1l) in
    fun x ->
      if le x max && ge x min
      then to_int32_mod x
      else raise(Overflow("Z.to_uint32", x))
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_of_sint64_001 *)
  (*- #Justify_Derived "Utility function" *)
  let of_sint64 n =
    if n = 0L then Z0 else
    if n > 0L then Zpos (P.of_int64 n)
    else Zneg (P.of_int64 (Int64.neg n))
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_of_uint64_001 *)
  (*- #Justify_Derived "Utility function" *)
  let of_uint64 n =
    if n = 0L then Z0 else Zpos (P.of_int64 n)
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_to_int64_mod_001 *)
  (*- #Justify_Derived "Utility function" *)
  let to_int64_mod = function
  | Z0 -> 0L
  | Zpos p -> P.to_int64_mod p
  | Zneg p -> Int64.neg (P.to_int64_mod p)
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_to_int64_001 *)
  (*- #Justify_Derived "Utility function" *)
  let to_int64 =
    let min = of_sint64 Int64.min_int and max = of_sint64 Int64.max_int in
    fun x ->
      if le x max && ge x min
      then to_int64_mod x
      else raise(Overflow("Z.to_int64", x))
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_to_uint64_001 *)
  (*- #Justify_Derived "Utility function" *)
  let to_uint64 =
    let min = zero and max = of_uint64 (-1L) in
    fun x ->
      if le x max && ge x min
      then to_int64_mod x
      else raise(Overflow("Z.to_uint64", x))
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_of_N_001 *)
  (*- #Justify_Derived "Utility function" *)
  let of_N = Z.of_N
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_to_string_rec_001 *)
  (*- #Justify_Derived "Utility function" *)
  let rec to_string_rec base buff x =
    if x = Z0 then () else begin
      let (q, r) = Z.div_eucl x base in
      to_string_rec base buff q;
      let d = to_int r in
      Buffer.add_char buff (Char.chr
        (if d < 10 then Char.code '0' + d
                         else Char.code 'A' + d - 10))
    end
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_to_string_aux_001 *)
  (*- #Justify_Derived "Utility function" *)
  let to_string_aux base x =
    match x with
    | Z0 -> "0"
    | Zpos _ ->
        let buff = Buffer.create 10 in
        to_string_rec base buff x;
        Buffer.contents buff
    | Zneg p ->
        let buff = Buffer.create 10 in
        Buffer.add_char buff '-';
        to_string_rec base buff (Zpos p);
        Buffer.contents buff
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_dec_001 *)
  (*- #Justify_Derived "Utility function" *)
  let dec = to_string_aux (of_uint 10)
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_hex_001 *)
  (*- #Justify_Derived "Utility function" *)
  let hex = to_string_aux (of_uint 16)
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_to_string_001 *)
  (*- #Justify_Derived "Utility function" *)
  let to_string = dec
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_is_power2_001 *)
  (*- #Justify_Derived "Utility function" *)
  let is_power2 x =
    gt x zero && eq (Z.coq_land x (pred x)) zero
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_op_add_001 *)
  (*- #Justify_Derived "Utility function" *)
  let (+) = add
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_op_sub_001 *)
  (*- #Justify_Derived "Utility function" *)
  let (-) = sub
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_op_mul_001 *)
  (*- #Justify_Derived "Utility function" *)
  let ( * ) = mul
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_op_div_001 *)
  (*- #Justify_Derived "Utility function" *)
  let ( / ) = div
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_op_eq_001 *)
  (*- #Justify_Derived "Utility function" *)
  let (=) = eq
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_op_lt_001 *)
  (*- #Justify_Derived "Utility function" *)
  let (<) = lt
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_op_le_001 *)
  (*- #Justify_Derived "Utility function" *)
  let (<=) = le
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_op_gt_001 *)
  (*- #Justify_Derived "Utility function" *)
  let (>) = gt
  (*- #End *)

  (*- E_COMPCERT_CODE_Camlcoq_Z_op_ge_001 *)
  (*- #Justify_Derived "Utility function" *)
  let (>=) = ge
  (*- #End *)

end

(* Rename/reexport names from CompCert's Integers module to avoid conflicts with OCaml's Int/Int64 modules. *)
module I32 = Integers.Int
module I64 = Integers.Int64
module Ptrofs = Integers.Ptrofs
(*- E_COMPCERT_CODE_Camlcoq_comparison_001 *)
(*- #Justify_Derived "Type definition" *)
type comparison = Integers.comparison = Ceq | Cne | Clt | Cle | Cgt | Cge
(*- #End *)

(*- E_COMPCERT_CODE_Camlcoq_init_001 *)
(*- #Justify_Derived "Initializer" *)
let _ =
  Printexc.register_printer
    (function 
      | Overflow(fn, arg) ->
          Some(Printf.sprintf "Overflow in %s on %s" fn (Z.to_string arg))
      | _ -> None)
(*- #End *)

(* Conversion functions for the 32- and 64-bit machine integers
   defined in module Integers.  These functions never overflow, since
   the range of these integers is known and enforced by the Coq type checker.
   The resulting OCaml int32 / int64 integers still have to be interpreted 
   as signed or unsigned, depending on the intended use. *)

(*- E_COMPCERT_CODE_Camlcoq_camlint_of_coqint_001 *)
(*- #Justify_Derived "Utility function" *)
let camlint_of_coqint (x: Integers.Int.int) : int32 =
  Z.to_int32_mod (Integers.Int.unsigned x)
(*- #End *)
(*- E_COMPCERT_CODE_Camlcoq_coqint_of_camlint_001 *)
(*- #Justify_Derived "Utility function" *)
let coqint_of_camlint (x: int32) : Integers.Int.int =
  Integers.Int.repr (Z.of_uint32 x)

(*- #End *)
(*- E_COMPCERT_CODE_Camlcoq_camlint64_of_coqint_001 *)
(*- #Justify_Derived "Utility function" *)
let camlint64_of_coqint (x: Integers.Int64.int) : int64 =
  Z.to_int64_mod (Integers.Int64.unsigned x)
(*- #End *)
(*- E_COMPCERT_CODE_Camlcoq_coqint_of_camlint64_001 *)
(*- #Justify_Derived "Utility function" *)
let coqint_of_camlint64 (x: int64) : Integers.Int64.int =
  Integers.Int64.repr (Z.of_uint64 x)
(*- #End *)

(* Integers.Ptrofs.int is either 32-bit or 64-bit wide, depending on the
   target platform.  It is always safe to treat it as an OCaml int64.
   It can be treated as an int32 on 32-bit target platforms. *)

(*- E_COMPCERT_CODE_Camlcoq_camlint64_of_ptrofs_001 *)
(*- #Justify_Derived "Utility function" *)
let camlint64_of_ptrofs (x: Integers.Ptrofs.int) : int64 =
  Z.to_int64_mod (Integers.Ptrofs.signed x)
(*- #End *)
let camlint_of_ptrofs (x: Integers.Ptrofs.int) : int32 =
  assert (not Archi.ptr64); Z.to_int32_mod (Integers.Ptrofs.signed x)

(* Atoms (positive integers representing strings) *)

(*- E_COMPCERT_CODE_Camlcoq_atom_001 *)
(*- #Justify_Derived "Type definition of 'atom', a positive integer representing strings" *)
type atom = positive
(*- #End *)

(*- E_COMPCERT_CODE_Camlcoq_atom_of_string_001 *)
(*- #Justify_Derived "Variable for global state" *)
let atom_of_string = (Hashtbl.create 17 : (string, atom) Hashtbl.t)
(*- #End *)

(*- E_COMPCERT_CODE_Camlcoq_string_of_atom_001 *)
(*- #Justify_Derived "Variable for global state" *)
let string_of_atom = (Hashtbl.create 17 : (atom, string) Hashtbl.t)
(*- #End *)

(*- E_COMPCERT_CODE_Camlcoq_next_atom_001 *)
(*- #Justify_Derived "Variable for local state" *)
let next_atom = ref Coq_xH
(*- #End *)

(*- E_COMPCERT_CODE_Camlcoq_use_canonical_atoms_001 *)
(*- #Justify_Derived "Variable for local state" *)
let use_canonical_atoms = ref false
(*- #End *)

(* If [use_canonical_atoms] is false, strings are numbered from 1 up
   in the order in which they are encountered.  This produces small
   numbers, and is therefore efficient, but the number for a given
   string may differ between the compilation of different units.

   If [use_canonical_atoms] is true, strings are Huffman-encoded as bit
   sequences, which are then encoded as positive numbers.  The same
   string is always represented by the same number in all compilation
   units.  However, the numbers are bigger than in the first
   implementation.  Also, this places a hard limit on the number of
   fresh identifiers that can be generated starting with
   [first_unused_ident]. *)


(*- E_COMPCERT_CODE_Camlcoq_append_bits_pos_001 *)
(*- #Justify_Derived "Utility function" *)
let rec append_bits_pos nbits n p =
  if nbits <= 0 then p else
  if n land 1 = 0
  then Coq_xO (append_bits_pos (nbits - 1) (n lsr 1) p)
  else Coq_xI (append_bits_pos (nbits - 1) (n lsr 1) p)
(*- #End *)

(* The encoding of strings as bit sequences is optimized for C identifiers:
   - numbers are encoded as a 6-bit integer between 0 and 9
   - lowercase letters are encoded as a 6-bit integer between 10 and 35
   - uppercase letters are encoded as a 6-bit integer between 36 and 61
   - the underscore character is encoded as the 6-bit integer 62
   - all other characters are encoded as 6 "one" bits followed by
     the 8-bit encoding of the character. *)

(*- E_COMPCERT_CODE_Camlcoq_append_char_pos_001 *)
(*- #Justify_Derived "Utility function" *)
let append_char_pos c p =
  match c with
  | '0'..'9' -> append_bits_pos 6 (Char.code c - Char.code '0') p
  | 'a'..'z' -> append_bits_pos 6 (Char.code c - Char.code 'a' + 10) p
  | 'A'..'Z' -> append_bits_pos 6 (Char.code c - Char.code 'A' + 36) p
  | '_'      -> append_bits_pos 6 62 p
  | _        -> append_bits_pos 6 63 (append_bits_pos 8 (Char.code c) p)
(*- #End *)

(* The empty string is represented as the positive "1", that is, [xH]. *)

(*- E_COMPCERT_CODE_Camlcoq_pos_of_string_001 *)
(*- #Justify_Derived "Utility function" *)
let pos_of_string s =
  let rec encode i accu =
    if i < 0 then accu else encode (i - 1) (append_char_pos s.[i] accu)
  in encode (String.length s - 1) Coq_xH
(*- #End *)

(*- E_COMPCERT_CODE_Camlcoq_fresh_atom_001 *)
(*- #Justify_Derived "Utility function" *)
let fresh_atom () =
  let a = !next_atom in
  next_atom := Pos.succ !next_atom;
  a
(*- #End *)

(*- E_COMPCERT_CODE_Camlcoq_intern_string_001 *)
(*- #Justify_Derived "Utility function" *)
let intern_string s =
  try
    Hashtbl.find atom_of_string s
  with Not_found ->
    let a =
      if !use_canonical_atoms then pos_of_string s else fresh_atom () in
    Hashtbl.add atom_of_string s a;
    Hashtbl.add string_of_atom a s;
    a
(*- #End *)

(*- E_COMPCERT_CODE_Camlcoq_extern_atom_001 *)
(*- #Justify_Derived "Utility function" *)
let extern_atom a =
  try
    Hashtbl.find string_of_atom a
  with Not_found ->
    Printf.sprintf "$%d" (P.to_int a)
(*- #End *)

(* Ignoring the terminating "1" bit, canonical encodings of strings can
   be viewed as lists of bits, formed by concatenation of 6-bit fragments
   (for letters, numbers, and underscore) and 14-bit fragments (for other
   characters).  Hence, not all positive numbers are canonical encodings:
   only those whose log2 is of the form [6n + 14m].

   Here are the first intervals of positive numbers corresponding to strings:
   - [1, 1] for the empty string
   - [2^6, 2^7-1] for one "compact" character
   - [2^12, 2^13-1] for two "compact" characters
   - [2^14, 2^14-1] for one "escaped" character

   Hence, between 2^7 and 2^12 - 1, we have 3968 consecutive positive
   numbers that cannot be the encoding of a string.  These are the positive
   numbers we'll use as temporaries in the SimplExpr pass if canonical
   atoms are in use.

   If short atoms are used, we just number the temporaries consecutively
   starting one above the last generated atom.
*)

(*- E_COMPCERT_CODE_Camlcoq_first_unused_ident_001 *)
(*- #Justify_Derived "Utility function" *)
let first_unused_ident () =
  if !use_canonical_atoms
  then P.of_int 128
  else !next_atom
(*- #End *)

(* Floats *)

(*- E_COMPCERT_CODE_Camlcoq_coqfloat_of_camlfloat_001 *)
(*- #Justify_Derived "Utility function" *)
let coqfloat_of_camlfloat f =
  Float.of_bits(coqint_of_camlint64(Int64.bits_of_float f))
(*- #End *)

(*- E_COMPCERT_CODE_Camlcoq_camlfloat_of_coqfloat_001 *)
(*- #Justify_Derived "Utility function" *)
let camlfloat_of_coqfloat f =
  Int64.float_of_bits(camlint64_of_coqint(Float.to_bits f))
(*- #End *)

(*- E_COMPCERT_CODE_Camlcoq_coqfloat32_of_camlfloat_001 *)
(*- #Justify_Derived "Utility function" *)
let coqfloat32_of_camlfloat f =
  Float32.of_bits(coqint_of_camlint(Int32.bits_of_float f))
(*- #End *)

(*- E_COMPCERT_CODE_Camlcoq_camlfloat_of_coqfloat32_001 *)
(*- #Justify_Derived "Utility function" *)
let camlfloat_of_coqfloat32 f =
  Int32.float_of_bits(camlint_of_coqint(Float32.to_bits f))
(*- #End *)

(*- E_COMPCERT_CODE_Camlcoq_coqfloat32_of_camlint_001 *)
(*- #Justify_Derived "Utility function" *)
let coqfloat32_of_camlint i =
  Float32.of_bits (coqint_of_camlint i)
(*- #End *)
(*- E_COMPCERT_CODE_Camlcoq_coqfloat64_of_camlint_001 *)
(*- #Justify_Derived "Utility function" *)
let coqfloat64_of_camlint i =
  Float.of_bits (coqint_of_camlint64 i)
(*- #End *)

(* Usefull constants *)

(*- E_COMPCERT_CODE_Camlcoq_constants_001 *)
(*- #Justify_Derived "Utility constants" *)
let _0  = Z.zero
let _1  = Z.one
let _2  = Z.of_uint 2
let _4  = Z.of_uint 4
let _8  = Z.of_uint 8
let _16  = Z.of_uint 16
let _96 = Z.of_uint 96
let _176 = Z.of_uint 176
let _192 = Z.of_uint 192
let _m1 = Z.of_sint (-1)

let _0l = I32.zero
let _1l = I32.one
let _2l = coqint_of_camlint 2l
let _3l = coqint_of_camlint 3l
let _4l = coqint_of_camlint 4l
let _6l = coqint_of_camlint 6l
let _8l = coqint_of_camlint 8l
let _9l = coqint_of_camlint 9l
let _11l = coqint_of_camlint 11l
let _16l = coqint_of_camlint 16l
let _21l = coqint_of_camlint 21l
let _24l = coqint_of_camlint 24l
let _31l = coqint_of_camlint 31l
let _32l = coqint_of_camlint 32l
let _40l = coqint_of_camlint 40l
let _48l = coqint_of_camlint 48l
let _51l = coqint_of_camlint 51l
let _52l = coqint_of_camlint 52l
let _56l = coqint_of_camlint 56l
let _63l = coqint_of_camlint 63l
let _64l = coqint_of_camlint 64l
let _96l = coqint_of_camlint 96l
let _255l = coqint_of_camlint 255l
let _1024l = coqint_of_camlint 1024l
let _3328l = coqint_of_camlint 3328l
let _4096l = coqint_of_camlint 4096l
let _32768l = coqint_of_camlint 32768l
let _65280l = coqint_of_camlint 65280l
let _m1l = coqint_of_camlint (-1l)
let _m4l = coqint_of_camlint (-4l)
let _m5l = coqint_of_camlint (-5l)
let _m6l = coqint_of_camlint (-6l)
let _m7l = coqint_of_camlint (-7l)
let _m8l = coqint_of_camlint (-8l)
let _m16l = coqint_of_camlint (-16l)
let _m128l = coqint_of_camlint (-128l)
let _m32768l = coqint_of_camlint (-32768l)
let _m2147483648l = coqint_of_camlint (-2147483648l)


let _0L = I64.zero
let _1L = coqint_of_camlint64 1L
let _2L = coqint_of_camlint64 2L
let _4L = coqint_of_camlint64 4L
let _8L = coqint_of_camlint64 8L
let _16L = coqint_of_camlint64 16L
let _24L = coqint_of_camlint64 24L
let _28L = coqint_of_camlint64 28L
let _32L = coqint_of_camlint64 32L
let _64L = coqint_of_camlint64 64L
let _128L = coqint_of_camlint64 128L
let _255L = coqint_of_camlint64 255L
let _m1L = coqint_of_camlint64 (-1L)

let _0p = Ptrofs.zero
let _1p = Ptrofs.repr (Z.of_uint 1)
let _2p = Ptrofs.repr (Z.of_uint 2)
let _3p = Ptrofs.repr (Z.of_uint 3)
let _4p = Ptrofs.repr (Z.of_uint 4)
let _8p = Ptrofs.repr (Z.of_uint 8)
let _12p = Ptrofs.repr (Z.of_uint 12)
let _16p = Ptrofs.repr (Z.of_uint 16)
let _19p = Ptrofs.repr (Z.of_uint 19)
let _27p = Ptrofs.repr (Z.of_uint 27)
let _32p = Ptrofs.repr (Z.of_uint 32)
let _35p = Ptrofs.repr (Z.of_uint 35)
let _51p = Ptrofs.repr (Z.of_uint 51)
let _64p = Ptrofs.repr (Z.of_uint 64)
let _128p = Ptrofs.repr (Z.of_uint 128)
let _512p = Ptrofs.repr (Z.of_uint 512)
let _2048p = Ptrofs.repr (Z.of_uint 2048)
let _m1p = Ptrofs.repr (Z.of_sint (-1))
let _m8p = Ptrofs.repr (Z.of_sint (-8))
let _m16p = Ptrofs.repr (Z.of_sint (-16))
let _m128p = Ptrofs.repr (Z.of_sint (-128))
let _m2048p = Ptrofs.repr (Z.of_sint (-2048))
(*- #End *)
