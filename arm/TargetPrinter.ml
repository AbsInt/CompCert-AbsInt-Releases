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

(* Printing ARM assembly code in asm syntax *)

open Printf
open Camlcoq
open Sections
open AST
open Asm
open PrintAsmaux
open Fileinfo

(* Module type for the options *)

(*- E_COMPCERT_CODE_TargetPrinter_PRINTER_OPTIONS_001 *)
(*- #Justify_Derived "Type definitions" *)
module type PRINTER_OPTIONS =
sig
  val vfpv3: bool
end
(*- #End *)

(* Basic printing functions *)

(*- E_COMPCERT_CODE_TargetPrinter_int_reg_name_001 *)
(*- #Justify_Derived "Utility function" *)
let int_reg_name = function
  | IR0 -> "r0" | IR1 -> "r1" | IR2 -> "r2" | IR3 -> "r3"
  | IR4 -> "r4" | IR5 -> "r5" | IR6 -> "r6" | IR7 -> "r7"
  | IR8 -> "r8" | IR9 -> "r9" | IR10 -> "r10" | IR11 -> "r11"
  | IR12 -> "r12" | IR13 -> "sp" | IR14 -> "lr"
(*- #End *)

(*- E_COMPCERT_CODE_TargetPrinter_single_reg_name_001 *)
(*- #Justify_Derived "Utility function" *)
let single_reg_name = function
  | FR0 -> "s0"   | FR1 -> "s1"   | FR2 -> "s2"   | FR3 -> "s3"
  | FR4 -> "s4"   | FR5 -> "s5"   | FR6 -> "s6"   | FR7 -> "s7"
  | FR8 -> "s8"   | FR9 -> "s9"   | FR10 -> "s10" | FR11 -> "s11"
  | FR12 -> "s12" | FR13 -> "s13" | FR14 -> "s14" | FR15 -> "s15"
  | FR16 -> "s16" | FR17 -> "s17" | FR18 -> "s18" | FR19 -> "s19"
  | FR20 -> "s20" | FR21 -> "s21" | FR22 -> "s22" | FR23 -> "s23"
  | FR24 -> "s24" | FR25 -> "s25" | FR26 -> "s26" | FR27 -> "s27"
  | FR28 -> "s28" | FR29 -> "s29" | FR30 -> "s30" | FR31 -> "s31"
(*- #End *)

(*- E_COMPCERT_CODE_TargetPrinter_double_reg_name_001 *)
(*- #Justify_Derived "Utility function" *)
let double_reg_name = function
  | FR1, FR0 -> "d0"    | FR3, FR2 -> "d1"    | FR5, FR4 -> "d2"
  | FR7, FR6 -> "d3"    | FR9, FR8 -> "d4"    | FR11, FR10 -> "d5"
  | FR13, FR12 -> "d6"  | FR15, FR14 -> "d7"  | FR17, FR16 -> "d8"
  | FR19, FR18 -> "d9"  | FR21, FR20 -> "d10" | FR23, FR22 -> "d11"
  | FR25, FR24 -> "d12" | FR27, FR26 -> "d13" | FR29, FR28 -> "d14"
  | FR31, FR30 -> "d15" | x, y -> (printf "%s, %s" (single_reg_name x) (single_reg_name y); assert false)
(*- #End *)

(*- E_COMPCERT_CODE_TargetPrinter_single_float_reg_name_001 *)
(*- #Justify_Derived "Utility function" *)
let single_float_reg_name = function
  | FR1, FR0 -> "s0"    | FR3, FR2 -> "s2"    | FR5, FR4 -> "s4"
  | FR7, FR6 -> "s6"    | FR9, FR8 -> "s8"    | FR11, FR10 -> "s10"
  | FR13, FR12 -> "s12"  | FR15, FR14 -> "s14"  | FR17, FR16 -> "s16"
  | FR19, FR18 -> "s18"  | FR21, FR20 -> "s20" | FR23, FR22 -> "s22"
  | FR25, FR24 -> "s24" | FR27, FR26 -> "s26" | FR29, FR28 -> "s28"
  | FR31, FR30 -> "s30" | _, _ -> assert false
(*- #End *)

(*- E_COMPCERT_CODE_TargetPrinter_preg_annot_001 *)
(*- #Justify_Derived "Utility function" *)
let preg_annot = function
  | One (IR r) -> int_reg_name r
  | Two (FR hi, FR lo) -> double_reg_name (hi, lo)
  | One (FR r) -> single_reg_name r
  | _ -> assert false
(*- #End *)

(*- E_COMPCERT_CODE_TargetPrinter_condition_name_001 *)
(*- #Justify_Derived "Utility function" *)
let condition_name = function
  | TCeq -> "eq"
  | TCne -> "ne"
  | TChs -> "hs"
  | TClo -> "lo"
  | TCmi -> "mi"
  | TCpl -> "pl"
  | TChi -> "hi"
  | TCls -> "ls"
  | TCge -> "ge"
  | TClt -> "lt"
  | TCgt -> "gt"
  | TCle -> "le"
(*- #End *)

(*- E_COMPCERT_CODE_TargetPrinter_neg_condition_name_001 *)
(*- #Justify_Derived "Utility function" *)
let neg_condition_name = function
  | TCeq -> "ne"
  | TCne -> "eq"
  | TChs -> "lo"
  | TClo -> "hs"
  | TCmi -> "pl"
  | TCpl -> "mi"
  | TChi -> "ls"
  | TCls -> "hi"
  | TCge -> "lt"
  | TClt -> "ge"
  | TCgt -> "le"
  | TCle -> "gt"
(*- #End *)


(* Module containing the printing functions *)

module Target (Opt: PRINTER_OPTIONS) : TARGET =
struct

  (* Basic printing functions *)

  (*- E_COMPCERT_CODE_TargetPrinter_label_001 *)
  (*- #Justify_Derived "Utility function" *)
  let label = elf_label
  (*- #End *)

  (*- E_COMPCERT_CODE_TargetPrinter_print_label_001 *)
  (*- #Justify_Derived "Utility function" *)
  let print_label oc lbl = elf_label oc (transl_label lbl)
  (*- #End *)

  (*- E_COMPCERT_CODE_TargetPrinter_comment_001 *)
  (*- #Justify_Derived "Utility constant" *)
  let comment = "@"
  (*- #End *)

  (*- E_COMPCERT_CODE_TargetPrinter_symbol_001 *)
  (*- #Justify_Derived "Utility function" *)
  let symbol = elf_symbol
  (*- #End *)

  (*- E_COMPCERT_CODE_TargetPrinter_symbol_paren_001 *)
  (*- #Justify_Derived "Utility function" *)
  let symbol_paren oc symb =
    let s = extern_atom symb in
    if String.length s > 0 && s.[0] = '$'
    then fprintf oc "(%s)" s
    else fprintf oc "%s" s
  (*- #End *)

  (*- E_COMPCERT_CODE_TargetPrinter_symbol_offset_001 *)
  (*- #Justify_Derived "Utility function" *)
  let symbol_offset oc (symb, ofs) =
    if Ptrofs.eq ofs Ptrofs.zero then
      symbol_paren oc symb
    else
      fprintf oc "(%a + %a)" symbol symb ptrofs ofs
  (*- #End *)

  (*- E_COMPCERT_CODE_TargetPrinter_ireg_001 *)
  (*- #Justify_Derived "Utility function" *)
  let ireg oc r = output_string oc (int_reg_name r)
  (*- #End *)

  (*- E_COMPCERT_CODE_TargetPrinter_freg_pair_001 *)
  (*- #Justify_Derived "Utility function" *)
  let freg_pair oc p = output_string oc (double_reg_name p)
  (*- #End *)

  (*- E_COMPCERT_CODE_TargetPrinter_freg_001 *)
  (*- #Justify_Derived "Utility function" *)
  let freg oc r = output_string oc (single_reg_name r)
  (*- #End *)

  (*- E_COMPCERT_CODE_TargetPrinter_single_of_pair_001 *)
  (*- #Justify_Derived "Utility function" *)
  let single_of_pair oc p = output_string oc (single_float_reg_name p)
  (*- #End *)

  (*- E_COMPCERT_CODE_TargetPrinter_preg_asm_001 *)
  (*- #Justify_Derived "Utility function" *)
  let preg_asm oc ty = function
    | One (IR r) -> ireg oc r
    | Two (FR hi, FR lo) -> freg_pair oc (hi, lo)
    | One (FR r) -> freg oc r
    | _    -> assert false
  (*- #End *)

  (* In Thumb2 mode, some arithmetic instructions have shorter encodings
     if they carry the "S" flag (update condition flags):
         add   (but not sp + imm)
         and
         asr
         bic
         eor
         lsl
         lsr
         mvn
         orr
         rsb
         sub    (but not sp - imm)
     On the other hand, "mov rd, rs" and "mov rd, #imm" have shorter
     encodings if they do not have the "S" flag.  Moreover, the "S"
     flag is not supported if rd or rs is sp.

     The proof of Asmgen shows that CompCert-generated code behaves the
     same whether flags are updated or not by those instructions.  The
     following printing function adds a "S" suffix if we are in Thumb2
     mode. *)

  (*- E_COMPCERT_CODE_TargetPrinter_thumbS_001 *)
  (*- #Justify_Derived "Utility function" *)
  let thumbS oc =
    if !Clflags.option_mthumb then output_char oc 's'
  (*- #End *)

  (* Names of sections *)

  (*- E_COMPCERT_CODE_TargetPrinter_is_comm_section_001 *)
  (*- #Justify_Derived "Utility function" *)
  let is_comm_section = default_is_comm_section
  (*- #End *)

  (*- E_COMPCERT_CODE_TargetPrinter_name_of_section_001 *)
  (*- #Justify_Derived "Utility function" *)
  let name_of_section = function
    | Section_text -> ".text"
    | Section_data i | Section_small_data i ->
        variable_section ~sec:".data" ~bss:".bss" i
    | Section_const i | Section_small_const i ->
        variable_section
          ~sec:".section      .rodata"
          ~reloc:".section    .data.rel.ro,\"aw\",%progbits"
          i
    | Section_string _ -> ".section	.rodata"
    | Section_literal _ -> ".text"
    | Section_jumptable -> ".text"
    | Section_user(s, wr, ex) ->
      sprintf ".section	\"%s\",\"a%s%s\",%%progbits"
        s (if wr then "w" else "") (if ex then "x" else "")
    | Section_debug_info _ -> ".section	.debug_info,\"\",%progbits"
    | Section_debug_loc -> ".section	.debug_loc,\"\",%progbits"
    | Section_debug_abbrev -> ".section	.debug_abbrev,\"\",%progbits"
    | Section_debug_line _ -> ".section	.debug_line,\"\",%progbits"
    | Section_debug_ranges -> ".section	.debug_ranges,\"\",%progbits"
    | Section_debug_str -> ".section	.debug_str,\"MS\",%progbits,1"
    | Section_ais_annotation ->  sprintf ".section	\"__compcert_ais_annotations\",\"\",%%note"
  (*- #End *)

  (*- E_COMPCERT_CODE_TargetPrinter_section_001 *)
  (*- #Justify_Derived "Utility function" *)
  let section oc sec =
    fprintf oc "	%s\n" (name_of_section sec)
  (*- #End *)

  (* Emit .file / .loc debugging directives *)

  (*- E_COMPCERT_CODE_TargetPrinter_print_file_line_001 *)
  (*- #Justify_Derived "Utility function" *)
  let print_file_line oc file line =
    print_file_line oc comment file line
  (*- #End *)


  (* Printing of instructions *)

  (*- E_COMPCERT_CODE_TargetPrinterprint_literal64_001 *)
  (*- #Justify_Derived "Utility function" *)
  let print_literal64 oc n lbl =
    let bfhi = Int64.shift_right_logical n 32
    and bflo = Int64.logand n 0xFFFF_FFFFL in
    if Archi.big_endian
    then fprintf oc ".L%d:	.word	0x%Lx, 0x%Lx\n" lbl bfhi bflo
    else fprintf oc ".L%d:	.word	0x%Lx, 0x%Lx\n" lbl bflo bfhi
  (*- #End *)

  (*- E_COMPCERT_CODE_TargetPrinter_print_constants_001 *)
  (*- #Justify_Derived "Utility function" *)
  let print_constants oc = function
    | Float32 (lbl,c) ->
      let c = camlint_of_coqint (Floats.Float32.to_bits c) in
      fprintf oc "%a:	.word	0x%lx\n"  print_label lbl c
    | Float64 (lbl,bf) ->
      let bf = camlint64_of_coqint (Floats.Float.to_bits  bf)
      and lbl = transl_label lbl in
      print_literal64 oc bf lbl
    | Symbol (lbl,id,ofs) ->
      fprintf oc "%a:	.word	%a\n" print_label lbl symbol_offset (id, ofs)
  (*- #End *)

  (*- E_COMPCERT_CODE_TargetPrinter_shift_op_001 *)
  (*- #Justify_Derived "Utility function" *)
  let shift_op oc = function
    | SOimm n -> fprintf oc "#%a" coqint n
    | SOreg r -> ireg oc r
    | SOlsl(r, n) -> fprintf oc "%a, lsl #%a" ireg r coqint n
    | SOlsr(r, n) -> fprintf oc "%a, lsr #%a" ireg r coqint n
    | SOasr(r, n) -> fprintf oc "%a, asr #%a" ireg r coqint n
    | SOror(r, n) -> fprintf oc "%a, ror #%a" ireg r coqint n
  (*- #End *)

  (*- E_COMPCERT_CODE_TargetPrinter_print_instruction_001 *)
  let print_instruction oc = function
    (* Core instructions *)
    | Padc (r1,r2,so) ->
      fprintf oc "	adc	%a, %a, %a\n" ireg r1 ireg r2 shift_op so
    | Padd(r1, r2, so) ->
      fprintf oc "	add%s	%a, %a, %a\n"
        (if !Clflags.option_mthumb && r2 <> IR13 then "s" else "")
        ireg r1 ireg r2 shift_op so
    | Padds (r1,r2,so) ->
      fprintf oc "	adds	%a, %a, %a\n" ireg r1 ireg r2 shift_op so
    | Pand(r1, r2, so) ->
      fprintf oc "	and%t	%a, %a, %a\n"
        thumbS ireg r1 ireg r2 shift_op so
    | Pasr(r1, r2, so) ->
      fprintf oc "	asr%t	%a, %a, %a\n"
        thumbS ireg r1 ireg r2 shift_op so
    | Pb lbl ->
      fprintf oc "	b	%a\n" print_label lbl
    | Pbc(bit, lbl) ->
      fprintf oc "	b%s	%a\n" (condition_name bit) print_label lbl
    | Pbne lbl ->
      fprintf oc "	bne	%a\n" print_label lbl
    | Pbsymb(id, sg) ->
      fprintf oc "	b	%a\n" symbol_paren id
    | Pbreg(r, sg) ->
      fprintf oc "	bx	%a\n" ireg r
    | Pblsymb(id, sg) ->
      fprintf oc "	bl	%a\n" symbol_paren id
    | Pblreg(r, sg) ->
      fprintf oc "	blx	%a\n" ireg r
    | Pbic(r1, r2, so) ->
      fprintf oc "	bic%t	%a, %a, %a\n"
        thumbS ireg r1 ireg r2 shift_op so
    | Pclz (r1,r2) ->
      fprintf oc "	clz	%a, %a\n" ireg r1 ireg r2
    | Pcmp(r1, so) ->
      fprintf oc "	cmp	%a, %a\n" ireg r1 shift_op so
    | Pcmn(r1, so) ->
      fprintf oc "	cmn	%a, %a\n" ireg r1 shift_op so
    | Pdmb ->
      fprintf oc "	dmb\n"
    | Pdsb ->
      fprintf oc "	dsb\n"
    |  Peor(r1, r2, so) ->
      fprintf oc "	eor%t	%a, %a, %a\n"
        thumbS ireg r1 ireg r2 shift_op so
    | Pisb ->
      fprintf oc "	isb\n"
    | Pldm(r1, rl) ->
      let first = ref true in
      let sep () = if !first then first := false else output_string oc ", " in
      fprintf oc "	ldm	%a!, {%a}\n" ireg r1
        (fun oc rl -> List.iter (fun ir -> sep (); ireg oc ir) rl ) rl
    | Pldr(r1, r2, sa) | Pldr_a(r1, r2, sa) ->
      fprintf oc "	ldr	%a, [%a, %a]\n" ireg r1 ireg r2 shift_op sa
    | Pldrb(r1, r2, sa) ->
      fprintf oc "	ldrb	%a, [%a, %a]\n" ireg r1 ireg r2 shift_op sa
    | Pldrh(r1, r2, sa) ->
      fprintf oc "	ldrh	%a, [%a, %a]\n" ireg r1 ireg r2 shift_op sa
    | Pldr_p(r1, r2, sa)  ->
      fprintf oc "	ldr	%a, [%a], %a\n" ireg r1 ireg r2 shift_op sa
    | Pldrb_p(r1, r2, sa) ->
      fprintf oc "	ldrb	%a, [%a], %a\n" ireg r1 ireg r2 shift_op sa
    | Pldrh_p(r1, r2, sa) ->
      fprintf oc "	ldrh	%a, [%a], %a\n" ireg r1 ireg r2 shift_op sa
    | Pldrsb(r1, r2, sa) ->
      fprintf oc "	ldrsb	%a, [%a, %a]\n" ireg r1 ireg r2 shift_op sa
    | Pldrsh(r1, r2, sa) ->
      fprintf oc "	ldrsh	%a, [%a, %a]\n" ireg r1 ireg r2 shift_op sa
    | Plsl(r1, r2, r3) ->
      fprintf oc "	lsl%t	%a, %a, %a\n"
        thumbS ireg r1 ireg r2 ireg r3
    | Plsr(r1, r2, sa) ->
      fprintf oc "	lsr%t	%a, %a, %a\n"
        thumbS ireg r1 ireg r2 shift_op sa
    | Plsrs(r1, r2, sa) ->
      fprintf oc "	lsrs	%a, %a, %a\n"
        ireg r1 ireg r2 shift_op sa
    | Pmla(r1, r2, r3, r4) ->
      fprintf oc "	mla	%a, %a, %a, %a\n" ireg r1 ireg r2 ireg r3 ireg r4
    | Pmov(r1, SOreg reg) ->
      (* No S flag even in Thumb2 mode *)
      fprintf oc "	mov	%a, %a\n" ireg r1 ireg reg
    | Pmov(r1, so) ->
      fprintf oc "	mov%t	%a, %a\n" thumbS ireg r1 shift_op so
    | Pmovw(r1, n) ->
      fprintf oc "	movw	%a, #%a\n" ireg r1 coqint n
    | Pmovt(r1, n) ->
      fprintf oc "	movt	%a, #%a\n" ireg r1 coqint n
    | Pmul(r1, r2, r3) ->
      fprintf oc "	mul	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
    | Pmvn'(r1, r2) ->
      (* [mvn r1 r2] preserves the carry flag even if an thumbS is used
         if the second operand is an register that is not shifted.
         For shifted registers the thumbS would override the carry flag *)
      fprintf oc "	mvn%t	%a, %a\n" thumbS ireg r1 ireg r2
    | Pmvn(r1, so) ->
      fprintf oc "	mvn%t	%a, %a\n" thumbS ireg r1 shift_op so
    | Porr(r1, r2, so) ->
      fprintf oc "	orr%t	%a, %a, %a\n"
        thumbS ireg r1 ireg r2 shift_op so
    | Prev (r1,r2) ->
      fprintf oc "	rev	%a, %a\n" ireg r1 ireg r2
    | Prev16 (r1,r2) ->
      fprintf oc "	rev16	%a, %a\n" ireg r1 ireg r2
    | Prrx (r1, r2) ->
      fprintf oc "	rrx	%a, %a\n" ireg r1 ireg r2
    | Prsb(r1, r2, so) ->
      fprintf oc "	rsb%t	%a, %a, %a\n"
        thumbS ireg r1 ireg r2 shift_op so
    | Prsbs(r1, r2, so) ->
      fprintf oc "	rsbs	%a, %a, %a\n"
        ireg r1 ireg r2 shift_op so
    | Prsc (r1,r2,so) ->
      fprintf oc "	rsc	%a, %a, %a\n" ireg r1 ireg r2 shift_op so
    | Pfsqrt (f1,f2) ->
      assert (Configuration.has_double);
      fprintf oc "	vsqrt.f64 %a, %a\n" freg_pair f1 freg_pair f2
    | Psbc (r1,r2,sa) ->
      fprintf oc "	sbc	%a, %a, %a\n" ireg r1 ireg r2 shift_op sa
    | Psbcs (r1,r2,sa) ->
      fprintf oc "	sbcs	%a, %a, %a\n" ireg r1 ireg r2 shift_op sa
    | Pnop ->
      fprintf oc "	nop\n"
    | Pstm(r1, rl) ->
      let first = ref true in
      let sep () = if !first then first := false else output_string oc ", " in
      fprintf oc "	stm	%a!, {%a}\n" ireg r1
        (fun oc rl -> List.iter (fun ir -> sep (); ireg oc ir) rl ) rl
    | Pstr(r1, r2, sa) | Pstr_a(r1, r2, sa) ->
      fprintf oc "	str	%a, [%a, %a]\n" ireg r1 ireg r2 shift_op sa
    | Pstrb(r1, r2, sa) ->
      fprintf oc "	strb	%a, [%a, %a]\n" ireg r1 ireg r2 shift_op sa
    | Pstrh(r1, r2, sa) ->
      fprintf oc "	strh	%a, [%a, %a]\n" ireg r1 ireg r2 shift_op sa
    | Pstr_p(r1, r2, sa) ->
      fprintf oc "	str	%a, [%a], %a\n" ireg r1 ireg r2 shift_op sa
    | Pstrb_p(r1, r2, sa) ->
      fprintf oc "	strb	%a, [%a], %a\n" ireg r1 ireg r2 shift_op sa
    | Pstrh_p(r1, r2, sa) ->
      fprintf oc "	strh	%a, [%a], %a\n" ireg r1 ireg r2 shift_op sa
    (*- #Link_to E_COMPCERT_TR_Function_PRINT_PSDIV_001 *)
    | Psdiv (r, r1, r2) ->
      if Archi.hardware_idiv () then
        fprintf oc "	sdiv	%a, %a, %a\n" ireg r ireg r1 ireg r2
      else
        fprintf oc "	bl	__aeabi_idiv\n"
    | Psbfx(r1, r2, lsb, sz) ->
      fprintf oc "	sbfx	%a, %a, #%a, #%a\n" ireg r1 ireg r2 coqint lsb coqint sz
    | Psmull(r1, r2, r3, r4) ->
      fprintf oc "	smull	%a, %a, %a, %a\n" ireg r1 ireg r2 ireg r3 ireg r4
    | Psub(r1, r2, so) ->
      fprintf oc "	sub%s	%a, %a, %a\n"
        (if !Clflags.option_mthumb && r2 <> IR13 then "s" else "")
        ireg r1 ireg r2 shift_op so
    | Psubs(r1, r2, so) ->
      fprintf oc "	subs	%a, %a, %a\n"
        ireg r1 ireg r2 shift_op so
    (*- #Link_to E_COMPCERT_TR_Function_PRINT_PUDIV_001 *)
    | Pudiv (r, r1, r2) ->
      if Archi.hardware_idiv () then
        fprintf oc "	udiv	%a, %a, %a\n" ireg r ireg r1 ireg r2
      else
         fprintf oc "	bl	__aeabi_uidiv\n"
    | Pumull(r1, r2, r3, r4) ->
      fprintf oc "	umull	%a, %a, %a, %a\n" ireg r1 ireg r2 ireg r3 ireg r4

    (* Floating-point VFD instructions *)

    | Pfcpyd(r1, r2) ->
      assert (Configuration.has_double);
      fprintf oc "	vmov.f64 %a, %a\n" freg_pair r1 freg_pair r2
    | Pfabsd(r1, r2) ->
      assert (Configuration.has_double);
      fprintf oc "	vabs.f64 %a, %a\n" freg_pair r1 freg_pair r2
    | Pfnegd(r1, r2) ->
      assert (Configuration.has_double);
      fprintf oc "	vneg.f64 %a, %a\n" freg_pair r1 freg_pair r2
    | Pfaddd(r1, r2, r3) ->
      assert (Configuration.has_double);
      fprintf oc "	vadd.f64 %a, %a, %a\n" freg_pair r1 freg_pair r2 freg_pair r3
    | Pfdivd(r1, r2, r3) ->
      assert (Configuration.has_double);
      fprintf oc "	vdiv.f64 %a, %a, %a\n" freg_pair r1 freg_pair r2 freg_pair r3
    | Pfmuld(r1, r2, r3) ->
      assert (Configuration.has_double);
      fprintf oc "	vmul.f64 %a, %a, %a\n" freg_pair r1 freg_pair r2 freg_pair r3
    | Pfsubd(r1, r2, r3) ->
      assert (Configuration.has_double);
      fprintf oc "	vsub.f64 %a, %a, %a\n" freg_pair r1 freg_pair r2 freg_pair r3
    | Pflid(r1, f) -> assert false (* Should be eliminated in expand constants *)
    (*- #Link_to E_COMPCERT_TR_Function_PRINT_PFCMPD_001 *)
    | Pfcmpd(r1, r2) ->
      assert (Configuration.has_double);
      fprintf oc "	vcmp.f64 %a, %a\n" freg_pair r1 freg_pair r2;
      fprintf oc "	vmrs APSR_nzcv, FPSCR\n"
    (*- #Link_to E_COMPCERT_TR_Function_PRINT_PFCMPZD_001 *)
    | Pfcmpzd(r1) ->
      assert (Configuration.has_double);
      fprintf oc "	vcmp.f64 %a, #0\n" freg_pair r1;
      fprintf oc "	vmrs APSR_nzcv, FPSCR\n"
    (*- #Link_to E_COMPCERT_TR_Function_PRINT_PFSITOD_001 *)
    | Pfsitod(r1, r2) ->
      assert (Configuration.has_double);
      fprintf oc "	vmov	%a, %a\n" single_of_pair r1 ireg r2;
      fprintf oc "	vcvt.f64.s32 %a, %a\n" freg_pair r1 single_of_pair r1
    (*- #Link_to E_COMPCERT_TR_Function_PRINT_PFUITOD_001 *)
    | Pfuitod(r1, r2) ->
      assert (Configuration.has_double);
      fprintf oc "	vmov	%a, %a\n" single_of_pair r1 ireg r2;
      fprintf oc "	vcvt.f64.u32 %a, %a\n" freg_pair r1 single_of_pair r1
    (*- #Link_to E_COMPCERT_TR_Function_PRINT_PFTOSIZD_001 *)
    | Pftosizd(r1, r2) ->
      assert (Configuration.has_double);
      fprintf oc "	vcvt.s32.f64 %a, %a\n" freg FR12 freg_pair r2;
      fprintf oc "	vmov	%a, %a\n" ireg r1 freg FR12
    (*- #Link_to E_COMPCERT_TR_Function_PRINT_PFTOUIZD_001 *)
    | Pftouizd(r1, r2) ->
      assert (Configuration.has_double);
      fprintf oc "	vcvt.u32.f64 %a, %a\n" freg FR12 freg_pair r2;
      fprintf oc "	vmov	%a, %a\n" ireg r1 freg FR12
    | Pfcpys(r1, r2) ->
      fprintf oc "	vmov.f32 %a, %a\n" freg r1 freg r2
    | Pfabss(r1, r2) ->
      fprintf oc "	vabs.f32 %a, %a\n" freg r1 freg r2
    | Pfnegs(r1, r2) ->
      fprintf oc "	vneg.f32 %a, %a\n" freg r1 freg r2
    | Pfadds(r1, r2, r3) ->
      fprintf oc "	vadd.f32 %a, %a, %a\n" freg r1 freg r2 freg r3
    | Pfdivs(r1, r2, r3) ->
      fprintf oc "	vdiv.f32 %a, %a, %a\n" freg r1 freg r2 freg r3
    | Pfmuls(r1, r2, r3) ->
      fprintf oc "	vmul.f32 %a, %a, %a\n" freg r1 freg r2 freg r3
    | Ppush rl ->
      let first = ref true in
      let sep () = if !first then first := false else output_string oc ", " in
      fprintf oc "	push	{%a}\n"  (fun oc rl -> List.iter (fun ir -> sep (); ireg oc ir) rl) rl
    | Pfsubs(r1, r2, r3) ->
      fprintf oc "	vsub.f32 %a, %a, %a\n" freg r1 freg r2 freg r3
    | Pflis(r1, f) -> assert false (* Should be eliminated in expand constants *)
    (*- #Link_to E_COMPCERT_TR_Function_PRINT_PFCMPS_001 *)
    | Pfcmps(r1, r2) ->
      fprintf oc "	vcmp.f32 %a, %a\n" freg r1 freg r2;
      fprintf oc "	vmrs APSR_nzcv, FPSCR\n"
    (*- #Link_to E_COMPCERT_TR_Function_PRINT_PFCMPZS_001 *)
    | Pfcmpzs(r1) ->
      fprintf oc "	vcmp.f32 %a, #0\n" freg r1;
      fprintf oc "	vmrs APSR_nzcv, FPSCR\n"
    (*- #Link_to E_COMPCERT_TR_Function_PRINT_PFSITOS_001 *)
    | Pfsitos(r1, r2) ->
      fprintf oc "	vmov	%a, %a\n" freg r1 ireg r2;
      fprintf oc "	vcvt.f32.s32 %a, %a\n" freg r1 freg r1
    (*- #Link_to E_COMPCERT_TR_Function_PRINT_PFUITOS_001 *)
    | Pfuitos(r1, r2) ->
      fprintf oc "	vmov	%a, %a\n" freg r1 ireg r2;
      fprintf oc "	vcvt.f32.u32 %a, %a\n" freg r1 freg r1
    (*- #Link_to E_COMPCERT_TR_Function_PRINT_PFTOSIZS_001 *)
    | Pftosizs(r1, r2) ->
      fprintf oc "	vcvt.s32.f32 %a, %a\n" freg FR12 freg r2;
      fprintf oc "	vmov	%a, %a\n" ireg r1 freg FR12
    (*- #Link_to E_COMPCERT_TR_Function_PRINT_PFTOUIZS_001 *)
    | Pftouizs(r1, r2) ->
      fprintf oc "	vcvt.u32.f32 %a, %a\n" freg FR12 freg r2;
      fprintf oc "	vmov	%a, %a\n" ireg r1 freg FR12
    | Pfcvtsd(r1, r2) ->
      assert (Configuration.has_double);
      fprintf oc "	vcvt.f32.f64 %a, %a\n" freg r1 freg_pair r2
    | Pfcvtds(r1, r2) ->
      assert (Configuration.has_double);
      fprintf oc "	vcvt.f64.f32 %a, %a\n" freg_pair r1 freg r2
    | Pfldd(r1, r2, n) | Pfldd_a(r1, r2, n) ->
      fprintf oc "	vldr	%a, [%a, #%a]\n" freg_pair r1 ireg r2 coqint n
    | Pflds(r1, r2, n) | Pflds_a(r1, r2, n) ->
      fprintf oc "	vldr	%a, [%a, #%a]\n" freg r1 ireg r2 coqint n
    | Pfldm(r1, rl) ->
      let first = ref true in
      let sep () = if !first then first := false else output_string oc ", " in
      fprintf oc "	vldm	%a, {%a}\n" ireg r1
        (fun oc rl -> List.iter (fun fr -> sep (); freg_pair oc fr) rl ) rl
    | Pfstd(r1, r2, n) | Pfstd_a(r1, r2, n) ->
      fprintf oc "	vstr	%a, [%a, #%a]\n" freg_pair r1 ireg r2 coqint n
    | Pfsts(r1, r2, n) | Pfsts_a(r1, r2, n) ->
      fprintf oc "	vstr	%a, [%a, #%a]\n" freg r1 ireg r2 coqint n
    | Pfstm(r1, rl) ->
      let first = ref true in
      let sep () = if !first then first := false else output_string oc ", " in
      fprintf oc "	vstm	%a, {%a}\n" ireg r1
        (fun oc rl -> List.iter (fun fr -> sep (); freg_pair oc fr) rl ) rl
    (* Pseudo-instructions *)
    | Pallocframe(sz, ofs) ->
      assert false
    | Pfreeframe(sz, ofs) ->
      assert false
    | Plabel lbl ->
      fprintf oc "%a:\n" print_label lbl
    | Ploadsymbol(r1, id, ofs) -> assert false (* Should be eliminated in expand constants *)

    (*- #Link_to E_COMPCERT_TR_Function_PRINT_PMOVITE_001 *)
    (*- #Link_to E_COMPCERT_TR_Function_EXPAND_SEL_001 *)
    | Pmovite(cond, r1, ifso, ifnot) ->
      fprintf oc "	ite	%s\n" (condition_name cond);
      fprintf oc "	mov%s	%a, %a\n"
        (condition_name cond) ireg r1 shift_op ifso;
      fprintf oc "	mov%s	%a, %a\n"
        (neg_condition_name cond) ireg r1 shift_op ifnot

    (*- #Link_to E_COMPCERT_TR_Function_PRINT_PFMOVITED_001 *)
    (*- #Link_to E_COMPCERT_TR_Function_EXPAND_SEL_001 *)
    | Pfmovited(cond, r1, ifso, ifnot) ->
      assert (Configuration.has_double);
      fprintf oc "	ite	%s\n" (condition_name cond);
      fprintf oc "	vmov%s.f64	%a, %a\n"
        (condition_name cond) freg_pair r1 freg_pair ifso;
      fprintf oc "	vmov%s.f64	%a, %a\n"
        (neg_condition_name cond) freg_pair r1 freg_pair ifnot

    (*- #Link_to E_COMPCERT_TR_Function_PRINT_PFMOVITES_001 *)
    (*- #Link_to E_COMPCERT_TR_Function_EXPAND_SEL_001 *)
    | Pfmovites(cond, r1, ifso, ifnot) ->
      fprintf oc "	ite	%s\n" (condition_name cond);
      fprintf oc "	vmov%s.f32	%a, %a\n"
        (condition_name cond) freg r1 freg ifso;
      fprintf oc "	vmov%s.f32	%a, %a\n"
        (neg_condition_name cond) freg r1 freg ifnot

    (*- #Link_to E_COMPCERT_TR_Function_PRINT_PBTBL_001 *)
    | Pbtbl(r, tbl) ->
      if !Clflags.option_mthumb then begin
        fprintf oc "	lsl	r14, %a, #2\n" ireg r;
        fprintf oc "	add	pc, r14\n";   (* 16-bit encoding *)
        fprintf oc "	nop\n";            (* 16-bit encoding *)
        List.iter
          (fun l -> fprintf oc "	b.w	%a\n" print_label l)
          tbl
      end else begin
        fprintf oc "	add	pc, pc, %a, lsl #2\n" ireg r;
        fprintf oc "	nop\n";
        List.iter
          (fun l -> fprintf oc "	b	%a\n" print_label l)
          tbl
      end

    (*- #Link_to E_COMPCERT_TR_Function_PRINT_PBUILTIN_001 *)
    | Pbuiltin(ef, args, res) ->
      begin match ef with
        | EF_annot(kind,txt, targs) ->
            begin match (P.to_int kind) with
              | 1 -> let annot = annot_text preg_annot "sp" (camlstring_of_coqstring txt) args in
                fprintf oc "%s annotation: %S\n" comment annot
              | 2 -> let lbl = new_label () in
                fprintf oc "%a:\n" label lbl;
                AisAnnot.add_ais_annot lbl preg_annot "r13" (camlstring_of_coqstring txt) args
              | _ -> assert false
            end
        | EF_debug(kind, txt, targs) ->
          print_debug_info comment print_file_line preg_annot "sp" oc
            (P.to_int kind) (extern_atom txt) args
        | EF_inline_asm(txt, sg, clob) ->
          fprintf oc "%s begin inline assembly\n\t" comment;
          print_inline_asm preg_asm oc (camlstring_of_coqstring txt) sg args res;
          fprintf oc "%s end inline assembly\n" comment
        | _ ->
          assert false
      end
    | Pcfi_adjust sz -> cfi_adjust oc sz
    | Pcfi_rel_offset ofs -> cfi_rel_offset oc "lr" ofs
    (* Fixup instructions for calling conventions *)
    | Pfcpy_fii (r1, r2, r3) ->
      fprintf oc "	vmov	%a, %a, %a\n" freg_pair r1 ireg r2 ireg r3
    | Pfcpy_fi (r1, r2) ->
      fprintf oc "	vmov	%a, %a\n" freg r1 ireg r2
    | Pfcpy_iif (r1, r2, r3) ->
      fprintf oc "	vmov	%a, %a, %a\n" ireg r1 ireg r2 freg_pair r3
    |  Pfcpy_if (r1, r2) ->
      fprintf oc "	vmov	%a, %a\n" ireg r1 freg r2
    | Pconstants consts ->
      fprintf oc "	.balign	4\n";
      List.iter (print_constants oc) consts
    (*- #Link_to E_COMPCERT_TR_Function_PRINT_PLOADSYMBOL_IMM_001 *)
    | Ploadsymbol_imm (r1,id,ofs) ->
        fprintf oc "	movw	%a, #:lower16:%a\n"
        ireg r1 symbol_offset (id, ofs);
        fprintf oc "	movt	%a, #:upper16:%a\n"
          ireg r1 symbol_offset (id, ofs)
    | Pflid_lbl (r1,lbl,f) ->
      let f = camlint64_of_coqint(Floats.Float.to_bits f) in
      fprintf oc "	vldr	%a, %a %s %.12g\n"
        freg_pair r1 print_label lbl comment (Int64.float_of_bits f)
    | Pflis_lbl (r1,lbl,f) ->
      let f = camlint_of_coqint(Floats.Float32.to_bits f) in
      fprintf oc "	vldr	%a, %a %s %.12g\n"
        freg r1 print_label lbl comment (Int32.float_of_bits f)
    | Pflid_imm (r1,f) ->
      let f = camlint64_of_coqint(Floats.Float.to_bits f) in
      assert (Configuration.has_double);
      fprintf oc "	vmov.f64 %a, #%.15F\n"
        freg_pair r1 (Int64.float_of_bits f)
    | Pflis_imm (r1,f) ->
      let f = camlint_of_coqint(Floats.Float32.to_bits f) in
       fprintf oc "	vmov.f32 %a, #%.15F\n"
         freg r1 (Int32.float_of_bits f)
    | Ploadsymbol_lbl (r1,lbl,id,ofs) ->
      fprintf oc "	ldr	%a, %a %s %a\n"
        ireg r1 print_label lbl comment symbol_offset (id, ofs)
    (*- #End *)

  (*- E_COMPCERT_CODE_TargetPrinter_print_align_001 *)
  (*- #Justify_Derived "Utility function" *)
  let print_align oc alignment =
    fprintf oc "	.balign %d\n" alignment
  (*- #End *)

  (*- E_COMPCERT_CODE_TargetPrinter_print_jumptable_001 *)
  (*- #Justify_Derived "Utility function" *)
  let print_jumptable _ _ = ()
  (*- #End *)

  (*- E_COMPCERT_CODE_TargetPrinter_print_optional_fun_info_001 *)
  (*- #Justify_Derived "Utility function" *)
  let print_optional_fun_info oc =
    if !Clflags.option_mthumb then
      fprintf oc "	.thumb_func\n"
  (*- #End *)

  (*- E_COMPCERT_CODE_TargetPrinter_print_fun_info_001 *)
  (*- #Justify_Derived "Utility function" *)
  let print_fun_info oc name =
    fprintf oc "	.type	%a, %%function\n" symbol name;
    fprintf oc "	.size	%a, . - %a\n" symbol name symbol name
  (*- #End *)

  (*- E_COMPCERT_CODE_TargetPrinter_print_var_info_001 *)
  (*- #Justify_Derived "Utility function" *)
  let print_var_info oc name =
    fprintf oc "	.type	%a, %%object\n" symbol name;
    fprintf oc "	.size	%a, . - %a\n" symbol name symbol name
  (*- #End *)

  (*- E_COMPCERT_CODE_TargetPrinter_print_comm_symb_001 *)
  (*- #Justify_Derived "Utility function" *)
  let print_comm_symb oc sz name align =
    if C2C.atom_is_static name then
      fprintf oc "	.local	%a\n" symbol name;
    fprintf oc "	.comm	%a, %s, %d\n"
      symbol name
      (Z.to_string sz)
      align
  (*- #End *)

  (*- E_COMPCERT_CODE_TargetPrinter_print_instructions_001 *)
  (*- #Justify_Derived "Utility function" *)
  let print_instructions oc fn =
    List.iter (print_instruction oc) fn.fn_code
  (*- #End *)


  (* Data *)

  (*- E_COMPCERT_CODE_TargetPrinter_print_prologue_001 *)
  (*- #Link_to E_COMPCERT_TR_Function_PRINT_ASM_002 *)
  let print_prologue oc =
    fprintf oc "	.syntax	unified\n";
    fprintf oc "	.arch	%s\n"
      (match Configuration.model with
       | "armv6"   -> "armv6"
       | "armv6t2" -> "armv6t2"
       | "armv7a"  -> "armv7-a"
       | "armv7r"  -> "armv7-r"
       | "armv7m"  -> "armv7-m"
       | _ -> "armv7");
    fprintf oc "	.fpu	%s\n"
      (if Opt.vfpv3 then "vfpv3-d16" else "vfpv2");
    fprintf oc "	.eabi_attribute Tag_ABI_VFP_args, %d\n"
      (match Configuration.abi with
       | "hardfloat" -> 1
       | _ -> 0);
    (* We must print that we use the idiv arch extension if we are either:
       * armv7a and the midiv option is set
       * armv7r and the midiv option is set but we are not in thumb mode *)
    (match Configuration.model with
     | "armv7a" -> if !Clflags.option_midiv then
       fprintf oc "	.arch_extension idiv\n"
     | "armv7r" -> if (!Clflags.option_midiv && (not !Clflags.option_mthumb)) then
       fprintf oc "	.arch_extension idiv\n"
     | _ -> ());
    fprintf oc "	.%s\n"
      (if !Clflags.option_mthumb then "thumb" else "arm");
    if !Clflags.option_g then begin
      section oc Section_text;
      cfi_section oc
    end
  (*- #End *)

  (*- E_COMPCERT_CODE_TargetPrinter_print_epilogue_001 *)
  (*- #Link_to E_COMPCERT_TR_Function_PRINT_ASM_003 *)
  let print_epilogue oc =
    if !Clflags.option_g then begin
      Debug.compute_gnu_file_enum (fun f -> ignore (print_file oc f));
      section oc Section_text;
    end
  (*- #End *)

  (*- E_COMPCERT_CODE_TargetPrinter_default_falignment_001 *)
  (*- #Justify_Derived "Utility constant" *)
  let default_falignment = 4
  (*- #End *)

  (*- E_COMPCERT_CODE_TargetPrinter_address_001 *)
  (*- #Justify_Derived "Utility constant" *)
  let address = if Archi.ptr64 then ".quad" else ".4byte"
  (*- #End *)
end

(*- E_COMPCERT_CODE_TargetPrinter_sel_target_001 *)
(*- #Justify_Derived "Utility function" *)
let sel_target () =
  let module S : PRINTER_OPTIONS = struct

    let vfpv3 = Configuration.model >= "armv7"

  end in
  (module Target(S):TARGET)
(*- #End *)
