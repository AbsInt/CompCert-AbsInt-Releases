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
  | (Ccompimm(c, n), [r1]) ->
      fprintf pp "%a %ss %ld" reg r1 (comparison_name c) (camlint_of_coqint n)
  | (Ccompuimm(c, n), [r1]) ->
      fprintf pp "%a %su %ld" reg r1 (comparison_name c) (camlint_of_coqint n)
  | (Ccompf c, [r1;r2]) ->
      fprintf pp "%a %sf %a" reg r1 (comparison_name c) reg r2
  | (Cnotcompf c, [r1;r2]) ->
      fprintf pp "%a not(%sf) %a" reg r1 (comparison_name c) reg r2
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

  | Oadd, [r1;r2] -> fprintf pp "%a + %a" reg r1 reg r2
  | Oaddimm n, [r1] -> fprintf pp "%a + %ld" reg r1 (camlint_of_coqint n)
  | Orsubimm n, [r1] ->
    fprintf pp "%ld - %a" (camlint_of_coqint n) reg r1
  | Osub, [r1;r2] -> fprintf pp "%a - %a" reg r1 reg r2

  | Oand, [r1;r2] -> fprintf pp "%a & %a" reg r1 reg r2
  | Oandimm n, [r1] -> fprintf pp "%a & %ld" reg r1 (camlint_of_coqint n)
  | Oandn, [r1;r2] -> fprintf pp "%a & not (%a)" reg r1 reg r2
  | Onand, [r1;r2] -> fprintf pp "not(%a & %a)" reg r1 reg r2
  | Onandimm n, [r1;] -> fprintf pp "not(%a & %ld)" reg r1 (camlint_of_coqint n)
  | Oneg, [r1] -> fprintf pp "-(%a)" reg r1
  | Onor, [r1;r2] -> fprintf pp "not(%a | %a)" reg r1 reg r2
  | Onorimm n, [r1] ->
    fprintf pp "not(%a | %ld)" reg r1 (camlint_of_coqint n)
  | Onot, [r1] -> fprintf pp "not(%a)" reg r1
  | Oor, [r1;r2] -> fprintf pp "%a | %a" reg r1 reg r2
  | Oorimm n, [r1] ->  fprintf pp "%a | %ld" reg r1 (camlint_of_coqint n)
  | Oorn, [r1;r2] -> fprintf pp "not(%a | %a)" reg r1 reg r2
  | Oxnor, [r1;r2] -> fprintf pp "not(%a ^ %a)" reg r1 reg r2
  | Oxnorimm n, [r1] -> fprintf pp "not(%a ^ %ld)" reg r1 (camlint_of_coqint n)
  | Oxor, [r1;r2] -> fprintf pp "%a ^ %a" reg r1 reg r2
  | Oxorimm n, [r1] -> fprintf pp "%a ^ %ld" reg r1 (camlint_of_coqint n)

  | Osl, [r1;r2] -> fprintf pp "%a << %a" reg r1 reg r2
  | Oslimm n, [r1] -> fprintf pp "%a << %ld" reg r1 (camlint_of_coqint n)
  | Oasr, [r1;r2] -> fprintf pp "%a >>s %a" reg r1 reg r2
  | Oasrimm n, [r1] -> fprintf pp "%a >>s %ld" reg r1 (camlint_of_coqint n)
  | Olsr, [r1;r2] -> fprintf pp "%a >>u %a" reg r1 reg r2
  | Olsrimm n, [r1] -> fprintf pp "%a >>u %ld" reg r1 (camlint_of_coqint n)
  | Oshrximm n, [r1] -> fprintf pp "%a >>x %ld" reg r1 (camlint_of_coqint n)

  | Osel (c, ty), r1::r2::args ->
      fprintf pp "%a ?%s %a : %a"
         (print_condition reg) (c, args)
         (PrintAST.name_of_type ty) reg r1 reg r2
  | Ocmp c, args -> print_condition reg pp (c, args)

  | Odiv, [r1;r2] -> fprintf pp "%a /s %a" reg r1 reg r2
  | Odivu, [r1;r2] -> fprintf pp "%a /u %a" reg r1 reg r2
  | Omod, [r1;r2] -> fprintf pp "%a %%s %a" reg r1 reg r2
  | Omodu, [r1;r2] -> fprintf pp "%a %%u %a" reg r1 reg r2

  | Oextr (p, w), [r1] ->
    fprintf pp "extr(%ld, %ld, %a)"
      (camlint_of_coqint p) (camlint_of_coqint w) reg r1
  | Oextru (p, w), [r1] ->
    fprintf pp "extru(%ld, %ld, %a)"
      (camlint_of_coqint p) (camlint_of_coqint w) reg r1
  | Oinsert (p, w), [r1;r2] ->
    fprintf pp "insert(%ld, %ld, %a, %a)"
      (camlint_of_coqint p) (camlint_of_coqint w) reg r1 reg r2
  | Oinsertimm (p, w, n), [r1] ->
    fprintf pp "insert(%ld, %ld, %a, %ld)"
      (camlint_of_coqint p) (camlint_of_coqint w)
      reg r1 (camlint_of_coqint n)

  | Omadd, [r1;r2;r3] ->
    fprintf pp "%a + (%a * %a)" reg r1 reg r2 reg r3
  | Omaddimm n, [r1;r2] ->
    fprintf pp "%a + (%a * %ld)" reg r1 reg r2 (camlint_of_coqint n)
  | Omsub, [r1;r2;r3] ->
    fprintf pp "%a - (%a * %a)" reg r1 reg r2 reg r3
  | Omsubimm n, [r1;r2] ->
    fprintf pp "%a - (%a * %ld)" reg r1 reg r2 (camlint_of_coqint n)
  | Omul, [r1;r2] -> fprintf pp "%a * %a" reg r1 reg r2
  | Omulimm n, [r1] -> fprintf pp "%a * %ld" reg r1 (camlint_of_coqint n)
  | Omulhs, [r1;r2] -> fprintf pp "mulhs(%a,%a)" reg r1 reg r2
  | Omulhu, [r1;r2] -> fprintf pp "mulhu(%a,%a)" reg r1 reg r2

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
  | Ointoffloat, [r1] -> fprintf pp "intoffloat(%a)" reg r1
  | Ointuoffloat, [r1] -> fprintf pp "intuoffloat(%a)" reg r1
  | Ofloatofint, [r1] -> fprintf pp "floatofint(%a)" reg r1
  | Ofloatofintu, [r1] -> fprintf pp "floatofintu(%a)" reg r1
  | Osingleofint, [r1] -> fprintf pp "singleofint(%a)" reg r1
  | Osingleofintu, [r1] -> fprintf pp "singleofintu(%a)" reg r1

  | _ -> fprintf pp "<bad operator>"



let print_addressing reg pp = function
  | Aindexed n, [r1] -> fprintf pp "%a + %ld" reg r1 (camlint_of_coqint n)
  | Aglobal(id, ofs), [] -> fprintf pp "%s + %ld" (extern_atom id) (camlint_of_coqint ofs)
  | Ainstack ofs, [] -> fprintf pp "stack(%ld)" (camlint_of_coqint ofs)
  | _ -> fprintf pp "<bad addressing>"
