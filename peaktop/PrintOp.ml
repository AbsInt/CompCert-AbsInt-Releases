(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  AbsInt Angewandte Informatik GmbH. All rights reserved. This file  *)
(*  is distributed under the terms of the INRIA Non-Commercial         *)
(*  License Agreement.                                                 *)
(*                                                                     *)
(* *********************************************************************)

(** Pretty-printing of operators, conditions, addressing modes *)

open Printf
open Camlcoq
open Integers
open Op

let comparison_name = function
  | Ceq -> "=="
  | Cne -> "!="
  | Clt -> "<"
  | Cle -> "<="
  | Cgt -> ">"
  | Cge -> ">="

let print_condition reg pp = function
  | (Ccomp c, [r1;r2]) ->
    fprintf pp "%a %ss %a" reg r1 (comparison_name c) reg r2
  | (Ccompu c, [r1;r2]) ->
    fprintf pp "%a %su %a" reg r1 (comparison_name c) reg r2
  | (Ccompimm (c, n), [r1]) ->
    fprintf pp "%a %ss %ld" reg r1 (comparison_name c) (camlint_of_coqint n)
  | (Ccompuimm (c, n), [r1]) ->
    fprintf pp "%a %su %ld" reg r1 (comparison_name c) (camlint_of_coqint n)
  | (Ccompf c, [r1;r2]) ->
    fprintf pp "%a %sf %a" reg r1 (comparison_name c) reg r2
  | (Cnotcompf c, [r1;r2]) ->
    fprintf pp "%a not(%sf) %a" reg r1 (comparison_name c) reg r2
  | (Ccompfs c, [r1;r2]) ->
    fprintf pp "%a %sfs %a" reg r1 (comparison_name c) reg r2
  | (Cnotcompfs c, [r1;r2]) ->
    fprintf pp "%a not(%sfs) %a" reg r1 (comparison_name c) reg r2
  | _ ->
    fprintf pp "<bad condition>"

let print_operation reg pp = function
  | Omove, [r1] -> reg pp r1
  | Ointconst n, [] -> fprintf pp "%ld" (camlint_of_coqint n)
  | Ofloatconst n, [] -> fprintf pp "%.15F" (camlfloat_of_coqfloat n)
  | Osingleconst n, [] -> fprintf pp "%.15Ff" (camlfloat_of_coqfloat32 n)
  | Oaddrsymbol(id, ofs), [] ->
    fprintf pp "\"%s\" + %ld" (extern_atom id) (camlint_of_coqint ofs)
  | Oaddrstack ofs, [] ->
    fprintf pp "stack(%ld)" (camlint_of_coqint ofs)
  | Ocast8signed, [r1] -> fprintf pp "int8signed(%a)" reg r1
  | Ocast16signed, [r1] -> fprintf pp "int16signed(%a)" reg r1
  | Oadd, [r1;r2] -> fprintf pp "%a + %a" reg r1 reg r2
  | Oaddimm n, [r1] -> fprintf pp "%a + %ld" reg r1 (camlint_of_coqint n)
  | Osub, [r1;r2] -> fprintf pp "%a - %a" reg r1 reg r2
  | Osubimm n, [r1] -> fprintf pp "%a - %ld" reg r1 (camlint_of_coqint n)
  | Omul, [r1;r2] -> fprintf pp "%a * %a" reg r1 reg r2
  | Omulimm n, [r1] -> fprintf pp "%a * %ld" reg r1 (camlint_of_coqint n)
  | Omulhs, [r1;r2] -> fprintf pp "%a *hs %a" reg r1 reg r2
  | Omulhu, [r1;r2] -> fprintf pp "%a *hu %a" reg r1 reg r2
  | Odiv, [r1;r2] -> fprintf pp "%a /s %a" reg r1 reg r2
  | Odivu, [r1;r2] -> fprintf pp "%a /u %a" reg r1 reg r2
  | Omod, [r1;r2] -> fprintf pp "%a %%s %a" reg r1 reg r2
  | Omodu, [r1;r2] -> fprintf pp "%a %%u %a" reg r1 reg r2
  | Oor, [r1;r2] -> fprintf pp "%a | %a" reg r1 reg r2
  | Oorimm n, [r1] ->  fprintf pp "%a | %ld" reg r1 (camlint_of_coqint n)
  | Oand, [r1;r2] -> fprintf pp "%a & %a" reg r1 reg r2
  | Oandimm n, [r1] -> fprintf pp "%a & %ld" reg r1 (camlint_of_coqint n)
  | Onand, [r1;r2] -> fprintf pp "not(%a & %a)" reg r1 reg r2
  | Onandimm n, [r1] -> fprintf pp "not(%a & %ld)" reg r1 (camlint_of_coqint n)
  | Oxor, [r1;r2] -> fprintf pp "%a ^ %a" reg r1 reg r2
  | Oxorimm n, [r1] -> fprintf pp "%a ^ %ld" reg r1 (camlint_of_coqint n)
  | Oshr, [r1;r2] -> fprintf pp "%a >>s %a" reg r1 reg r2
  | Oshrimm n, [r1] -> fprintf pp "%a >>s %ld" reg r1 (camlint_of_coqint n)
  | Oshrximm n, [r1] -> fprintf pp "%a >>x %ld" reg r1 (camlint_of_coqint n)
  | Oshl, [r1;r2] -> fprintf pp "%a << %a" reg r1 reg r2
  | Oshlimm n, [r1] -> fprintf pp "%a << %ld" reg r1 (camlint_of_coqint n)
  | Oshru, [r1;r2] -> fprintf pp "%a >>u %a" reg r1 reg r2
  | Oshruimm n, [r1] -> fprintf pp "%a >>u %ld" reg r1 (camlint_of_coqint n)
  | Ororimm n, [r1] -> fprintf pp "(%a ror %ld)" reg r1 (camlint_of_coqint n)
  | Omakelong, [r1;r2] -> fprintf pp "makelong(%a,%a)" reg r1 reg r2
  | Olowlong, [r1] -> fprintf pp "lowlong(%a)" reg r1
  | Ohighlong, [r1] -> fprintf pp "highlong(%a)" reg r1
  | Onegf, [r1] -> fprintf pp "negf(%a)" reg r1
  | Oabsf, [r1] -> fprintf pp "absf(%a)" reg r1
  | Oaddf, [r1;r2] -> fprintf pp "%a +f %a" reg r1 reg r2
  | Osubf, [r1;r2] -> fprintf pp "%a -f %a" reg r1 reg r2
  | Omulf, [r1;r2] -> fprintf pp "%a *f %a" reg r1 reg r2
  | Odivf, [r1;r2] -> fprintf pp "%a /f %a" reg r1 reg r2
  | Onegfs, [r1] -> fprintf pp "negfs(%a)" reg r1
  | Oabsfs, [r1] -> fprintf pp "absfs(%a)" reg r1
  | Oaddfs, [r1;r2] -> fprintf pp "%a +fs %a" reg r1 reg r2
  | Osubfs, [r1;r2] -> fprintf pp "%a -fs %a" reg r1 reg r2
  | Omulfs, [r1;r2] -> fprintf pp "%a *fs %a" reg r1 reg r2
  | Odivfs, [r1;r2] -> fprintf pp "%a /fs %a" reg r1 reg r2
  | Osingleoffloat, [r1] -> fprintf pp "singleoffloat(%a)" reg r1
  | Ofloatofsingle, [r1] -> fprintf pp "floatofsingle(%a)" reg r1
  | Osingleofint, [r1] -> fprintf pp "singleofint(%a)" reg r1
  | Osingleofintu, [r1] -> fprintf pp "singleofintu(%a)" reg r1
  | Ointofsingle, [r1] -> fprintf pp "intofsingle(%a)" reg r1
  | Ointuofsingle, [r1] -> fprintf pp "intuofsingle(%a)" reg r1
  | Ocmp c, args -> print_condition reg pp (c, args)
  | _ -> fprintf pp "<bad operator>"

let print_addressing reg pp = function
  | Aindexed n, [r1] -> fprintf pp "%a + %Ld" reg r1 (camlint64_of_ptrofs n)
  | Aglobal(id, ofs), [] ->
    fprintf pp "\"%s\" + %Ld" (extern_atom id) (camlint64_of_ptrofs ofs)
  | Ainstack ofs, [] -> fprintf pp "stack(%Ld)" (camlint64_of_ptrofs ofs)
  | _ -> fprintf pp "<bad addressing>"
