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

(* Printing TriCore assembly code in asm syntax *)

open Printf
open Sections
open Asm
open PrintAsmaux
open Camlcoq
open Fileinfo
open AisAnnot
open AST

module Target : TARGET =
struct

  (* Basic printing functions **)

  let comment = "#"

  let symbol = elf_symbol
  let symbol_offset = elf_symbol_offset

  let label = elf_label
  let print_label oc lbl = label oc (transl_label lbl)

  let dreg_name = function
    | D0  -> "%d0"  | D1  -> "%d1"  | D2  -> "%d2"  | D3  -> "%d3"
    | D4  -> "%d4"  | D5  -> "%d5"  | D6  -> "%d6"  | D7  -> "%d7"
    | D8  -> "%d8"  | D9  -> "%d9"  | D10 -> "%d10" | D11 -> "%d11"
    | D12 -> "%d12" | D13 -> "%d13" | D14 -> "%d14" | D15 -> "%d15"

  let areg_name = function
    | A0  -> "%a0"  | A1  -> "%a1"  | A2  -> "%a2"  | A3  -> "%a3"
    | A4  -> "%a4"  | A5  -> "%a5"  | A6  -> "%a6"  | A7  -> "%a7"
    | A8  -> "%a8"  | A9  -> "%a9"  | A10 -> "%a10" | A11 -> "%a11"
    | A12 -> "%a12" | A13 -> "%a13" | A14 -> "%a14" | A15 -> "%a15"

  let dreg oc r = output_string oc (dreg_name r)

  let areg oc r = output_string oc (areg_name r)

  let preg_asm oc ty = function
    | DREG d -> dreg oc d
    | AREG a -> areg oc a
    | _ -> assert false

  let preg_annot = function
    | DREG d -> dreg_name d
    | AREG a -> areg_name a
    | _ -> assert false

(* Names of sections *)
  (* TODO check *)
  let is_comm_section = default_is_comm_section

  (* TODO small data support*)
  let name_of_section = function
    | Section_text         -> ".text"
    | Section_data i | Section_small_data i ->
      variable_section ~sec:".data" ~bss:".section	.bss" i
    | Section_const i | Section_small_const i ->
      variable_section ~sec:".section	.rodata,\"a\",@progbits" i
    | Section_string sz ->
      elf_mergeable_string_section sz ".section	.rodata"
    | Section_literal sz ->
          elf_mergeable_literal_section sz ".section	.rodata"
    | Section_jumptable -> ".text"
    | Section_user(s, wr, ex) ->
      sprintf ".section	\"%s\",\"a%s%s\",@progbits"
        s (if wr then "w" else "") (if ex then "x" else "")
    | Section_debug_info _ -> ".section	.debug_info,\"\",@progbits"
    | Section_debug_abbrev -> ".section	.debug_abbrev,\"\",@progbits"
    | Section_debug_loc -> ".section	.debug_loc,\"\",@progbits"
    | Section_debug_line _ ->  ".section	.debug_line,\"\",@progbits"
    | Section_debug_ranges -> ".section	.debug_ranges,\"\",@progbits"
    | Section_debug_str -> ".section	.debug_str,\"MS\",@progbits,1"
    | Section_ais_annotation -> sprintf ".section	\"__compcert_ais_annotations\",\"\",@note"

    let section oc sec =
      fprintf oc "	%s\n" (name_of_section sec)

    let print_file_line oc file line =
      print_file_line oc comment file line

    let high_half oc (id, ofs) =
       fprintf oc "hi:%a" symbol_offset (id, ofs)

    let print_instruction oc = function
      | Pmov (d1, d2) -> fprintf oc "	mov	%a, %a\n" dreg d1 dreg d2
      | Pmov_aa (a1, a2) -> fprintf oc "	mov.aa	%a, %a\n" areg a1 areg a2
      | Pmov_a (a1, d2) -> fprintf oc "	mov.a	%a, %a\n" areg a1 dreg d2
      | Pmov_d (d1, a2) -> fprintf oc "	mov.d	%a, %a\n" dreg d1 areg a2
      | Pmovh (d1, imm) ->
        fprintf oc "	movh	%a, %ld\n" dreg d1 (camlint_of_coqint imm)
      | Pmovh_s (d1, id, ofs) ->
        fprintf oc "	movh	%a, %a\n" dreg d1 high_half (id, ofs)
      | Pmovh_as (a1, id) ->
        fprintf oc "	movh.a	%a, %a\n" areg a1 high_half (id, Integers.Int.zero)
      | Pmovh_ao (a1, imm) ->
        fprintf oc "	movh.a	%a, %ld\n" areg a1 (camlint_of_coqint imm)
      | Pmovi (d1, imm) ->
        fprintf oc "	mov	%a, %ld\n" dreg d1 (camlint_of_coqint imm)
      | Plea_s (a1, a2, id) ->
        fprintf oc "	lea	%a, [%a], lo:%a\n" areg a1 areg a2 symbol id
      | Plea_sc16 (a1, a2, imm) ->
        fprintf oc "	lea	%a, [%a], %ld\n" areg a1 areg a2 (camlint_of_coqint imm)
      | Peq (rd, d1, d2) ->
        fprintf oc "	eq	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Peq_sc9 (rd, d, imm) ->
        fprintf oc "	eq	%a, %a, %ld\n" dreg rd dreg d (camlint_of_coqint imm)
      | Pne (rd, d1, d2) ->
        fprintf oc "	ne	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Pne_sc9 (rd, d, imm) ->
        fprintf oc "	ne	%a, %a, %ld\n" dreg rd dreg d (camlint_of_coqint imm)
      | Plt (rd, d1, d2) ->
        fprintf oc "	lt	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Plt_sc9 (rd, d, imm) ->
        fprintf oc "	lt	%a, %a, %ld\n" dreg rd dreg d (camlint_of_coqint imm)
      | Pltu (rd, d1, d2) ->
        fprintf oc "	lt.u	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Pltu_uc9 (rd, d, imm) ->
        fprintf oc "	lt.u	%a, %a, %ld\n" dreg rd dreg d (camlint_of_coqint imm)
      | Pge (rd, d1, d2) ->
        fprintf oc "	ge	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Pge_sc9 (rd, d, imm) ->
        fprintf oc "	ge	%a, %a, %ld\n" dreg rd dreg d (camlint_of_coqint imm)
      | Pgeu (rd, d1, d2) ->
        fprintf oc "	ge.u	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Pgeu_uc9 (rd, d, imm) ->
        fprintf oc "	ge.u	%a, %a, %ld\n" dreg rd dreg d (camlint_of_coqint imm)
      | Padd (rd, d1, d2) ->
        fprintf oc "	add	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Padd_sc4 (rd, imm) ->
        fprintf oc "	add	%a, %ld\n" dreg rd (camlint_of_coqint imm)
      | Padd_rr (rd, d) ->
        fprintf oc "	add	%a, %a\n" dreg rd dreg d
      | Paddi (rd, d, imm) ->
        fprintf oc "	addi	%a, %a, %ld\n" dreg rd dreg d (camlint_of_coqint imm)
      | Paddi_ls (rd, d, id, ofs) ->
        fprintf oc "	addi	%a, %a, lo:%a\n" dreg rd dreg d symbol_offset (id, ofs)
      | Paddc (rd, d1, d2) ->
        fprintf oc "	addc	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Paddx (rd, d1, d2) ->
        fprintf oc "	addx	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Paddih (rd, d, imm) ->
        fprintf oc "	addih	%a, %a, %ld\n" dreg rd dreg d (camlint_of_coqint imm)
      | Padd_a (rd, a1, a2) ->
        fprintf oc "	add.a	%a, %a, %a\n" areg rd areg a1 areg a2
      | Padd_asc4 (rd, imm) ->
        fprintf oc "	add.a	%a, %ld\n" areg rd (camlint_of_coqint imm)
      | Padd_aa (rd, a) ->
        fprintf oc "	add.a	%a, %a\n" areg rd areg a
      | Paddsc_a (rd, a, d, imm) ->
        fprintf oc "	add.a	%a, %a, %a %ld\n"
          areg rd areg a dreg d (camlint_of_coqint imm)
      | Paddih_a (rd, a, imm) ->
        fprintf oc "	addih.a	%a, %a, %ld\n"
          areg rd areg a (camlint_of_coqint imm)
      | Pcadd_sc9 (rd, c, d, imm) ->
        fprintf oc "	cadd	%a, %a, %a, %ld\n"
          dreg rd dreg c dreg d (camlint_of_coqint imm)
      | Psub (rd, d1, d2) ->
        fprintf oc "	sub	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Psub_rr (rd, d) ->
        fprintf oc "	sub	%a, %a\n" dreg rd dreg d
      | Prsub (rd, d ,imm) ->
        fprintf oc "	rsub	%a, %a, %ld\n"
          dreg rd dreg d (camlint_of_coqint imm)
      | Prsub_r rd ->
        fprintf oc "	rsub	%a\n" dreg rd
      | Pcsub (rd, c, d1, d2) ->
        fprintf oc "	csub	%a, %a, %a, %a\n" dreg rd dreg c dreg d1 dreg d2
      | Psubc (rd, d1, d2) ->
        fprintf oc "	subc	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Psubx (rd, d1, d2) ->
        fprintf oc "	subx	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Pmul (rd, d1, d2) ->
        fprintf oc "	mul	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Pmul_rr (rd, d) ->
        fprintf oc "	mul	%a, %a\n" dreg rd dreg d
      | Pmul_sc9 (rd, d , imm) ->
        fprintf oc "	mul	%a, %a, %ld\n"
          dreg rd dreg d (camlint_of_coqint imm)
      | Pmadd (rd, d1, d2, d3) ->
        fprintf oc "	madd	%a, %a, %a, %a\n" dreg rd dreg d1 dreg d2 dreg d3
      | Pmadd_sc9 (rd, d1, d2, imm) ->
        fprintf oc "	madd	%a, %a, %a, %ld\n"
          dreg rd dreg d1 dreg d2 (camlint_of_coqint imm)
      | Pmsub (rd, d1, d2, d3) ->
        fprintf oc "	msub	%a, %a, %a, %a\n" dreg rd dreg d1 dreg d2 dreg d3
      | Pmsub_sc9 (rd, d1, d2, imm) ->
        fprintf oc "	msub	%a, %a, %a, %ld\n"
          dreg rd dreg d1 dreg d2 (camlint_of_coqint imm)
      | Pmul_e (d1, d2) ->
        fprintf oc "	mul	%%e4, %a, %a\n" dreg d1 dreg d2
      | Pmulu (d1, d2) ->
        fprintf oc "	mul.u	%%e4, %a, %a\n" dreg d1 dreg d2
      | Pdiv (d1, d2) ->
        fprintf oc "	div	%%e4, %a, %a\n" dreg d1 dreg d2
      | Pdivu (d1, d2) ->
        fprintf oc "	div.u	%%e4, %a, %a\n" dreg d1 dreg d2
      | Pnot rd ->
        fprintf oc "	not	%a\n" dreg rd
      | Pand (rd, d1, d2) ->
        fprintf oc "	and	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Pand_rr (rd, d) ->
        fprintf oc "	and	%a, %a\n" dreg rd dreg d
      | Pand_ruc9 (rd, d , imm) ->
        fprintf oc "	and	%a, %a, %ld\n"
          dreg rd dreg d (camlint_of_coqint imm)
      | Pand_d15uc8 imm ->
        fprintf oc "	and	%%d15, %ld\n" (camlint_of_coqint imm)
      | Pandn (rd, d1, d2) ->
        fprintf oc "	andn	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Pandn_uc9 (rd, d , imm) ->
        fprintf oc "	andn	%a, %a, %ld\n"
          dreg rd dreg d (camlint_of_coqint imm)
      | Pnand (rd, d1, d2) ->
        fprintf oc "	nand	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Pnand_uc9 (rd, d , imm) ->
        fprintf oc "	nand	%a, %a, %ld\n"
          dreg rd dreg d (camlint_of_coqint imm)
      | Por (rd, d1, d2) ->
        fprintf oc "	or	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Por_rr (rd, d) ->
        fprintf oc "	or	%a, %a\n" dreg rd dreg d
      | Por_ruc9 (rd, d , imm) ->
        fprintf oc "	or	%a, %a, %ld\n"
          dreg rd dreg d (camlint_of_coqint imm)
      | Por_d15uc8 imm ->
        fprintf oc "	or	%%d15, %ld\n" (camlint_of_coqint imm)
      | Porn (rd, d1, d2) ->
        fprintf oc "	orn	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Porn_uc9 (rd, d , imm) ->
        fprintf oc "	orn	%a, %a, %ld\n"
          dreg rd dreg d (camlint_of_coqint imm)
      | Pnor (rd, d1, d2) ->
        fprintf oc "	nor	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Pnor_uc9 (rd, d , imm) ->
        fprintf oc "	nor	%a, %a, %ld\n"
          dreg rd dreg d (camlint_of_coqint imm)
      | Pxor (rd, d1, d2) ->
        fprintf oc "	xor	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Pxor_rr (rd, d) ->
        fprintf oc "	xor	%a, %a\n" dreg rd dreg d
      | Por_t (rd, d1, p1, d2, p2) ->
        fprintf oc "	or.t	%a, %a, %ld, %a, %ld\n"
          dreg rd dreg d1 (camlint_of_coqint p1) dreg d2 (camlint_of_coqint p2)
      | Pnor_t (rd, d1, p1, d2, p2) ->
        fprintf oc "	nor.t	%a, %a, %ld, %a, %ld\n"
          dreg rd dreg d1 (camlint_of_coqint p1) dreg d2 (camlint_of_coqint p2)
      | Pxor_ruc9 (rd, d , imm) ->
        fprintf oc "	xor	%a, %a, %ld\n"
          dreg rd dreg d (camlint_of_coqint imm)
      | Pxnor (rd, d1, d2) ->
        fprintf oc "	xnor	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Pxnor_uc9 (rd, d , imm) ->
        fprintf oc "	xnor	%a, %a, %ld\n"
          dreg rd dreg d (camlint_of_coqint imm)
      | Psh (rd, d1, d2) ->
        fprintf oc "	sh	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Psh_sc9 (rd, d , imm) ->
        fprintf oc "	sh	%a, %a, %ld\n"
          dreg rd dreg d (camlint_of_coqint imm)
      | Psh_sc4 (rd, imm) ->
        fprintf oc "	sh	%a, %ld\n" dreg rd  (camlint_of_coqint imm)
      | Psha (rd, d1, d2) ->
        fprintf oc "	sha	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Psha_sc9 (rd, d , imm) ->
        fprintf oc "	sha	%a, %a, %ld\n"
          dreg rd dreg d (camlint_of_coqint imm)
      | Psha_sc4 (rd, imm) ->
        fprintf oc "	sha	%a, %ld\n" dreg rd  (camlint_of_coqint imm)
      | Pextr (rd, d, pos, width) ->
        fprintf oc "	extr	%a, %a, %ld, %ld\n"
          dreg rd dreg d (camlint_of_coqint pos) (camlint_of_coqint width)
      | Pextru (rd, d, pos, width) ->
        fprintf oc "	extr.u	%a, %a, %ld, %ld\n"
          dreg rd dreg d (camlint_of_coqint pos) (camlint_of_coqint width)
      | Pdextr (rd, r1, r2, pos) ->
        fprintf oc "	dextr	%a, %a, %a, %ld\n"
          dreg rd dreg r1 dreg r2 (camlint_of_coqint pos)
      | Pinsert (rd, d1, d2, pos, width) ->
        fprintf oc "	insert	%a, %a, %a, %ld, %ld\n"
          dreg rd dreg d1 dreg d2 (camlint_of_coqint pos) (camlint_of_coqint width)
      | Pinsert_uc4 (rd, d, imm, pos, width) ->
        fprintf oc "	insert	%a, %a, %ld, %ld, %ld\n"
          dreg rd dreg d
          (camlint_of_coqint imm) (camlint_of_coqint pos) (camlint_of_coqint width)
      | Pinsn_t (rd, r1, r2, pos1, pos2) ->
        fprintf oc "	insn.t	%a, %a, %ld, %a, %ld\n"
          dreg rd dreg r1 (camlint_of_coqint pos1) dreg r2 (camlint_of_coqint pos2)
      | Psel (rd, c, d1, d2) ->
        fprintf oc "	sel	%a, %a, %a, %a\n"
          dreg rd dreg c dreg d1 dreg d2
      | Pnegf (rd, d) -> fprintf oc "	neg.f	%a, %a\n" dreg rd dreg d
      | Pabsf (rd, d) -> fprintf oc "	abs.f	%a, %a\n" dreg rd dreg d
      | Paddf (rd, d1, d2) ->
        fprintf oc "	add.f	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Psubf (rd, d1, d2) ->
        fprintf oc "	sub.f	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Pmulf (rd, d1, d2) ->
        fprintf oc "	mul.f	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Pdivf (rd, d1, d2) ->
        fprintf oc "	div.f	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Pcmpf (rd, d1, d2) ->
        fprintf oc "	cmp.f	%a, %a, %a\n" dreg rd dreg d1 dreg d2
      | Pftoiz (rd, d) -> fprintf oc "	ftoiz	%a, %a\n" dreg rd dreg d
      | Pftouz (rd, d) -> fprintf oc "	ftouz	%a, %a\n" dreg rd dreg d
      | Pitof (rd, d) -> fprintf oc "	itof	%a, %a\n" dreg rd dreg d
      | Putof (rd, d) -> fprintf oc "	utof	%a, %a\n" dreg rd dreg d
      | Pj_l lbl -> fprintf oc "	j	%a\n" print_label lbl
      | Pj_s (id, sg) -> fprintf oc "	j	%a\n" symbol id
      | Pji (rd, sg) ->  fprintf oc "	ji	%a\n" areg rd
      | Pcall (id, sg) -> fprintf oc "	call	%a\n" symbol id
      | Pcalli (rd, sg) ->  fprintf oc "	calli	%a\n" areg rd
      | Pret -> fprintf oc "	ret\n"
      | Pjeq (d1, d2, lbl) ->
        fprintf oc "	jeq	%a, %a, %a\n" dreg d1 dreg d2 print_label lbl
      | Pjeq_sc4 (d, imm, lbl) ->
        fprintf oc "	jeq	%a, %ld, %a\n"
          dreg d (camlint_of_coqint imm) print_label lbl
      | Pjge (d1, d2, lbl) ->
        fprintf oc "	jge	%a, %a, %a\n" dreg d1 dreg d2 print_label lbl
      | Pjge_sc4 (d, imm, lbl) ->
        fprintf oc "	jge	%a, %ld, %a\n"
          dreg d (camlint_of_coqint imm) print_label lbl
      | Pjgeu (d1, d2, lbl) ->
        fprintf oc "	jge.u	%a, %a, %a\n" dreg d1 dreg d2 print_label lbl
      | Pjgeu_sc4 (d, imm, lbl) ->
        fprintf oc "	jge.u	%a, %ld, %a\n"
          dreg d (camlint_of_coqint imm) print_label lbl
      | Pjlt (d1, d2, lbl) ->
        fprintf oc "	jlt	%a, %a, %a\n" dreg d1 dreg d2 print_label lbl
      | Pjlt_sc4 (d, imm, lbl) ->
        fprintf oc "	jlt	%a, %ld, %a\n"
          dreg d (camlint_of_coqint imm) print_label lbl
      | Pjltu (d1, d2, lbl) ->
        fprintf oc "	jlt.u	%a, %a, %a\n" dreg d1 dreg d2 print_label lbl
      | Pjltu_sc4 (d, imm, lbl) ->
        fprintf oc "	jlt.u	%a, %ld, %a\n"
          dreg d (camlint_of_coqint imm) print_label lbl
      | Pjne (d1, d2, lbl) ->
        fprintf oc "	jne	%a, %a, %a\n" dreg d1 dreg d2 print_label lbl
      | Pjne_sc4 (d, imm, lbl) ->
        fprintf oc "	jne	%a, %ld, %a\n"
          dreg d (camlint_of_coqint imm) print_label lbl
      | Pjnz_t (d, b, lbl) ->
        fprintf oc "	jnz.t	%a, %ld, %a\n"
          dreg d (camlint_of_coqint b) print_label lbl
      | Pjz_t (d, b, lbl) ->
        fprintf oc "	jz.t	%a, %ld, %a\n"
          dreg d (camlint_of_coqint b) print_label lbl
      | Pldb (rd, base, imm) ->
        fprintf oc "	ld.b	%a, [%a]%ld\n"
          dreg rd areg base (camlint_of_coqint imm)
      | Pldb_rr (rd, base) ->
        fprintf oc "	ld.b	%a, [%a]\n" dreg rd areg base
      | Pldbu (rd, base, imm) ->
        fprintf oc "	ld.bu	%a, [%a]%ld\n"
          dreg rd areg base (camlint_of_coqint imm)
      | Pldbu_rr (rd, base) ->
        fprintf oc "	ld.bu	%a, [%a]\n" dreg rd areg base
      | Pldh (rd, base, imm) ->
        fprintf oc "	ld.h	%a, [%a]%ld\n"
          dreg rd areg base (camlint_of_coqint imm)
      | Pldh_rr (rd, base) ->
        fprintf oc "	ld.h	%a, [%a]\n" dreg rd areg base
      | Pldhu (rd, base, imm) ->
        fprintf oc "	ld.hu	%a, [%a]%ld\n"
          dreg rd areg base (camlint_of_coqint imm)
      | Pldhu_rr (rd, base) ->
        fprintf oc "	ld.hu	%a, [%a]\n" dreg rd areg base
      | Pldw (rd, base, imm)
      | Pfldw (rd, base, imm)
      | Pldw_a (rd, base, imm) ->
        fprintf oc "	ld.w	%a, [%a]%ld\n"
          dreg rd areg base (camlint_of_coqint imm)
      | Pldw_rr (rd, base)
      | Pfldw_rr (rd, base)
      | Pldw_a_rr (rd, base) ->
        fprintf oc "	ld.w	%a, [%a]\n" dreg rd areg base
      | Plda (rd, base, imm) ->
        fprintf oc "	ld.a	%a, [%a]%ld\n"
          areg rd areg base (camlint_of_coqint imm)
      | Plda_rr (rd, base) ->
        fprintf oc "	ld.a	%a, [%a]\n" areg rd areg base
      | Pstb (src, base, imm) ->
        fprintf oc "	st.b	[%a]%ld, %a\n"
          areg base (camlint_of_coqint imm) dreg src
      | Pstb_rr (src, base) ->
        fprintf oc "	st.b	[%a], %a\n" areg base dreg src
      | Psth (src, base, imm) ->
        fprintf oc "	st.h	[%a]%ld, %a\n"
          areg base (camlint_of_coqint imm) dreg src
      | Psth_rr (src, base) ->
        fprintf oc "	st.h	[%a], %a\n" areg base dreg src
      | Pstw (src, base, imm)
      | Pfstw (src, base, imm)
      | Pstw_a (src, base, imm) ->
        fprintf oc "	st.w	[%a]%ld, %a\n"
          areg base (camlint_of_coqint imm) dreg src
      | Pstw_rr (src, base)
      | Pfstw_rr (src, base)
      | Pstw_a_rr (src, base) ->
        fprintf oc "	st.w	[%a], %a\n" areg base dreg src
      | Psta (src, base, imm) ->
        fprintf oc "	st.a	[%a]%ld, %a\n"
          areg base (camlint_of_coqint imm) areg src
      | Psta_rr (src, base) ->
        fprintf oc "	st.a	[%a], %a\n" areg base areg src
      | Ploadsi _
      | Pallocframe _
      | Pfreeframe _ -> assert false (* should be expanded in Asmexpand *)
      | Plabel lbl ->
        fprintf oc "%a:\n" print_label lbl
      | Pbtbl (r, tbl) ->
        let lbl = new_label () in
        fprintf oc "	movh.a	%%a14, hi:%a\n" label lbl;
        fprintf oc "	lea	%%a14, [%%a14], lo:%a\n" label lbl;
        fprintf oc "	addsc.a	%%a14, %%a14, %a, 2\n" dreg r;
        fprintf oc "	ji	%%a14\n";
        fprintf oc "	.p2align	2\n";
        fprintf oc "%a:\n" label lbl;
        List.iter (fun lbl ->
            fprintf oc "	.code32\n";
            fprintf oc "	j	%a\n" print_label lbl) tbl;
      | Pbuiltin(ef, args, res) ->
         begin match ef with
           | EF_annot(kind,txt, targs) ->
             begin match (P.to_int kind) with
               | 1 -> let annot = annot_text preg_annot "a10" (camlstring_of_coqstring txt) args  in
                 fprintf oc "%s annotation: %S\n" comment annot
               | 2 -> let lbl = new_label () in
                 fprintf oc "%a:\n" label lbl;
                 add_ais_annot lbl preg_annot "a10" (camlstring_of_coqstring txt) args
               | _ -> assert false
             end
          | EF_debug(kind, txt, targs) ->
              print_debug_info comment print_file_line preg_annot "a10" oc
                               (P.to_int kind) (extern_atom txt) args
          | EF_inline_asm(txt, sg, clob) ->
              fprintf oc "%s begin inline assembly\n\t" comment;
              print_inline_asm preg_asm oc (camlstring_of_coqstring txt) sg args res;
              fprintf oc "%s end inline assembly\n" comment
          | _ ->
              assert false
         end
      | Pshuffle (rd, d, imm) ->
        fprintf oc "	shuffle	%a, %a, %ld\n"
          dreg rd dreg d (camlint_of_coqint imm)
      | Pclz (rd, d) -> fprintf oc "	clz	%a, %a\n" dreg rd dreg d
      | Pldbu_prr (rd, a) -> fprintf oc "	ld.bu	%a, [%a+]\n" dreg rd areg a
      | Pstb_prr (rd, a) -> fprintf oc "	st.b	[%a+], %a\n" areg a  dreg rd
      | Ploop (c, lbl) -> fprintf oc "	loop	%a, %a\n" areg c print_label lbl
      | Pnop -> fprintf oc "	nop\n"

    let address = ".long"

    let default_falignment = 2

    let print_align oc alignment =
      fprintf oc "	.balign %d\n" alignment


    let print_prologue oc =
      if !Clflags.option_g then begin
        section oc Section_text;
      end

    let print_epilogue oc =
      if !Clflags.option_g then begin
        Debug.compute_gnu_file_enum (fun f -> ignore (print_file oc f));
        section oc Section_text;
      end

    let print_comm_symb oc sz name align =
      if C2C.atom_is_static name then
        fprintf oc "	.local	%a\n" symbol name;
      fprintf oc "	.comm	%a, %s, %d\n"
        symbol name
        (Z.to_string sz)
        align

    let cfi_startproc oc = ()
    let cfi_endproc oc = ()

    let print_optional_fun_info _ = ()

    let print_fun_info = elf_print_fun_info

    let print_var_info = elf_print_var_info

    let print_instructions oc fn =
      current_function_sig := fn.fn_sig;
      List.iter (print_instruction oc) fn.fn_code

    let print_jumptable _ _ = ()

  end


let sel_target () =
  (module Target:TARGET)
