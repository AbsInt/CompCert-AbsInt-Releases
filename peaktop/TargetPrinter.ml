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

(* Printing Peaktop assembly code in asm syntax *)

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

  (* Basic printing functions *)

  let comment = "#"

  let symbol = elf_symbol
  let label = elf_label

  let print_label oc lbl = label oc (transl_label lbl)

  let reg_name = function
    | Reg0 -> "reg0"   | Reg1 -> "reg1"   | Reg2 -> "reg2"   | Reg3 -> "reg3"
    | Reg4 -> "reg4"   | Reg5 -> "reg5"   | Reg6 -> "reg6"   | Reg7 -> "reg7"
    | Reg8 -> "reg8"   | Reg9 -> "reg9"   | Reg10 -> "reg10" | Reg11 -> "reg11"
    | Reg12 -> "reg12" | Reg13 -> "reg13" | Reg14 -> "reg14" | Reg15 -> "reg15"
    | Reg16 -> "reg16" | Reg17 -> "reg17" | Reg18 -> "reg18" | Reg19 -> "reg19"
    | Reg20 -> "reg20" | Reg21 -> "reg21" | Reg22 -> "reg22" | Reg23 -> "reg23"
    | Reg24 -> "reg24" | Reg25 -> "reg25" | Reg26 -> "reg26" | Reg27 -> "reg27"
    | Reg28 -> "reg28" | Reg29 -> "reg29" | Reg30 -> "reg30" | Reg31 -> "reg31"

  let reg oc r = output_string oc (reg_name r)

  let preg_asm oc = function
    | GPR r -> reg oc r
    | CRP -> fprintf oc "spc21"
    | _    -> assert false

  let preg_annot = function
    | GPR r -> reg_name r
    | _ -> assert false

(* Names of sections *)

    let is_comm_section = default_is_comm_section

    let name_of_section = function
      | Section_text         -> ".text"
      | Section_data i | Section_small_data i ->
        variable_section ~sec:".data" ~bss:".section	.bss" i
      | Section_const i | Section_small_const i ->
        variable_section ~sec:".section	.rodata" i
      | Section_string _     -> ".section	.rodata"
      | Section_literal _    -> ".section	.rodata"
      | Section_jumptable    -> ".section	.rodata"
      | Section_debug_info _ -> ".section	.debug_info,\"\",%progbits"
      | Section_debug_loc    -> ".section	.debug_loc,\"\",%progbits"
      | Section_debug_abbrev -> ".section	.debug_abbrev,\"\",%progbits"
      | Section_debug_line _ -> ".section	.debug_line,\"\",%progbits"
      | Section_debug_ranges -> ".section	.debug_ranges,\"\",%progbits"
      | Section_debug_str    -> ".section	.debug_str,\"MS\",%progbits,1"
      | Section_user(s, wr, ex) ->
          sprintf ".section	\"%s\",\"a%s%s\",%%progbits"
            s (if wr then "w" else "") (if ex then "x" else "")
      | Section_ais_annotation -> sprintf ".section	\"__compcert_ais_annotations\",\"\",@note"

    let section oc sec =
      fprintf oc "	%s\n" (name_of_section sec)

(* Emit .file / .loc debugging directives *)

    let cfi_startproc oc = ()
    let cfi_endproc oc = ()
    let cfi_adjust oc delta = ()
    let cfi_rel_offset oc reg ofs = ()

    let print_file_line oc file line =
      print_file_line oc comment file line

(* Printing of instructions *)

    let addressing oc = function
      | ADimm (base,off) -> fprintf oc "%a[%a]" reg base coqint off
      | ADreg (base,r) -> fprintf oc "%a[%a]" reg base reg r
      | ADregpostincr r ->  fprintf oc "[%a++]" reg r

    let print_instruction oc = function
      (* Moves *)
      | Pmov_rr (rd, r) ->
        fprintf oc "	MOV_W	%a, %a\n" reg rd reg r
      | Pmov_ri (rd, imm) ->
        fprintf oc "	MOV_W	%a, %a\n" reg rd coqint imm
      | Pmovu_ri (rd, imm) ->
        fprintf oc "	MOV_WU	%a, %a\n" reg rd coqint imm
      | Pmov_fcrp rd ->
        fprintf oc "	MOV_W	%a, spc21\n" reg rd
      | Pmov_tcrp rd ->
        fprintf oc "	MOV_W	spc21, %a\n" reg rd
      | Pmov_fucr rd ->
        fprintf oc "	MOV_W	%a, spc20\n" reg rd
      | Pmov_tucr rd ->
        fprintf oc "	MOV_W	spc20, %a\n" reg rd
      | Pmov_rs (rd, c) ->
        assert false
      (* Load/Store variants of move *)
      | Pmov_mr (rd, a)
      | Pmov_mr_a (rd, a)->
        fprintf oc "	MOV_W	%a, %a\n" reg rd addressing a
      | Pmovh_mr (rd, a)->
        fprintf oc "	MOV_H	%a, %a\n" reg rd addressing a
      | Pmovsh_mr _ ->
        assert false (* should be removed in Asmexpand *)
      | Pmovb_mr (rd, a) ->
        fprintf oc "	MOV_B	%a, %a\n" reg rd addressing a
      | Pmovsb_mr _ ->
        assert false (* should be removed in Asmexpand *)
      | Pfmov_mr (rd, a)
      | Pfmov_mr_a (rd, a) ->
        fprintf oc "	MOV_W	%a, %a\n" reg rd addressing a
      | Pmov_rm (a, rd)
      | Pmov_rm_a (a, rd) ->
        fprintf oc "	MOV_W	%a, %a\n" addressing a reg rd
      | Pmovh_rm (a, rd) ->
        fprintf oc "	MOV_H	%a, %a\n" addressing a reg rd
      | Pmovb_rm (a, rd) ->
        fprintf oc "	MOV_B	%a, %a\n" addressing a reg rd
      | Pfmov_rm (a, rd)
      | Pfmov_rm_a (a, rd) ->
        fprintf oc "	MOV_W	%a, %a\n" addressing a reg rd
      (* Integer arithmetic *)
      | Padd (rd, r) ->
        fprintf oc "	ADD_W	%a, %a\n" reg rd reg r
      | Paddi (rd, imm) ->
        fprintf oc "	ADD_W	%a, %a\n" reg rd coqint imm
      | Psub (rd, r) ->
        fprintf oc "	SUB_W	%a, %a\n" reg rd reg r
      | Psubi (rd, imm) ->
        fprintf oc "	SUB_W	%a, %a\n" reg rd coqint imm
      | Pmul (rd, r) ->
        fprintf oc "	MUL_W	%a, %a\n" reg rd reg r
      | Pmul_u (rd, r) ->
        fprintf oc "	MUL_WU	%a, %a\n" reg rd reg r
      | Pmuli (rd, imm) ->
        fprintf oc "	MUL_W	%a, %a\n" reg rd coqint imm
      | Pmulh (rd, r) ->
        (* Mul writes a pair of registers, with lower register contains the
           result of the multiplication and the upper register containing the
           high half of the result. We enforce that the results is in Reg4. *)
        assert (rd = Reg3);
        fprintf oc "	MUL_W	reg3, %a\n" reg r;
        fprintf oc "	MOV_W	reg3, reg4\n"
      | Pmulhu (rd, r) ->
        (* Mul writes a pair of registers, with lower register contains the
           result of the multiplication and the upper register containing the
           high half of the result. We enforce that the results is in Reg4. *)
        assert (rd = Reg3);
        fprintf oc "	MUL_WU	reg3, %a\n" reg r;
        fprintf oc "	MOV_W	reg3, reg4\n"
      | Pdiv (rd, r) ->
        fprintf oc "	DIV_W	%a, %a\n" reg rd reg r
      | Pdivu (rd, r) ->
        fprintf oc "	DIV_WU	%a, %a\n" reg rd reg r
      | Prem (rd, r) ->
        assert (rd = Reg3);
        fprintf oc "	DIV_W	reg3, %a\n" reg r;
        fprintf oc "	MOV_W	reg3, reg4\n"
      | Premu (rd, r) ->
        fprintf oc "	DIV_WU	reg3, %a\n" reg r;
        fprintf oc "	MOV_W	reg3, reg4\n"
      | Psll (rd, r) ->
        fprintf oc "	SL_W	%a, %a\n" reg rd reg r
      | Pslil (rd, imm) ->
        fprintf oc "	SL_W	%a, %a\n" reg rd coqint imm
      | Psrl (rd, r) ->
        fprintf oc "	SR_W	%a, %a\n" reg rd reg r
      | Psril (rd, imm) ->
        fprintf oc "	SR_W	%a, %a\n" reg rd coqint imm
      | Psra (rd, r) ->
        fprintf oc "	SR_AW	%a, %a\n" reg rd reg r
      | Psrai (rd, imm) ->
        fprintf oc "	SR_AW	%a, %a\n" reg rd coqint imm
      | Prr (rd, r) ->
        fprintf oc "	RR_W	%a, %a\n" reg rd reg r
      | Prri (rd, imm) ->
        fprintf oc "	RR_W	%a, %a\n" reg rd coqint imm
      | Pand (rd, r) ->
        fprintf oc "	AND_W	%a, %a\n" reg rd reg r
      | Pandi (rd, imm) ->
        fprintf oc "	AND_W	%a, %a\n" reg rd coqint imm
      | Pnand (rd, r) ->
        fprintf oc "	NAND_W	%a, %a\n" reg rd reg r
      | Pnandi (rd, imm) ->
        fprintf oc "	NAND_W	%a, %a\n" reg rd coqint imm
      | Por (rd, r) ->
        fprintf oc "	OR_W	%a, %a\n" reg rd reg r
      | Pori (rd, imm) ->
        fprintf oc "	OR_W	%a, %a\n" reg rd coqint imm
      | Porui (rd, imm) ->
        fprintf oc "	OR_WU	%a, %a\n" reg rd coqint imm
      | Pxor (rd, r) ->
        fprintf oc "	XOR_W	%a, %a\n" reg rd reg r
      | Pxori (rd, imm) ->
        fprintf oc "	XOR_W	%a, %a\n" reg rd coqint imm
      | Pcmp_eq (rd, r1, r2) ->
        assert false (* should be removed in Asmexpand *)
      | Pcmpu_eq (rd, r1, r2) ->
        assert false (* should be removed in Asmexpand *)
      | Pcmp_lt (rd, r1, r2) ->
        assert false (* should be removed in Asmexpand *)
      | Pcmpu_lt (rd, r1, r2) ->
        assert false (* should be removed in Asmexpand *)
      | Pmad (rd, r1, r2) ->
        fprintf oc "	MAD_W	%a, %a, %a\n" reg rd reg r1 reg r2
      | Pmsu (rd, r1, r2) ->
        fprintf oc "	MSU_W	%a, %a, %a\n" reg rd reg r1 reg r2
      (* 32-bit (single-precision) floating point *)
      | Pfadds (rd, r) ->
        fprintf oc "	FADD	%a, %a\n" reg rd reg r
      | Pfsubs (rd, r) ->
        fprintf oc "	FSUB	%a, %a\n" reg rd reg r
      | Pfmuls (rd, r) ->
        fprintf oc "	FMUL	%a, %a\n" reg rd reg r
      | Pfdivs (rd, r) ->
        fprintf oc "	FDIV	%a, %a\n" reg rd reg r
      | Pfcmp (rd, r) ->
        fprintf oc "	FCMP	%a, %a\n" reg rd reg r
      | Pfsqr rd ->
        fprintf oc "	FSQR	%a\n" reg rd
      | Pfabs rd ->
        fprintf oc "	FABS	%a\n" reg rd
      | Pfneg rd ->
        fprintf oc "	FNEG	%a\n" reg rd
      | Pff2i rd ->
        fprintf oc "	FF2I_W	%a\n" reg rd
      | Pff2iu rd ->
        fprintf oc "	FF2I_WU	%a\n" reg rd
      | Pfi2f rd ->
        fprintf oc "	FI2F_W	%a\n" reg rd
      | Pfiu2f rd ->
        fprintf oc "	FI2F_WU	%a\n" reg rd
      | Pfmad (rd, rs1, rs2) ->
        fprintf oc "	FMAD	%a, %a, %a\n" reg rd reg rs1 reg rs2
      | Pfmsu (rd, rs1, rs2) ->
        fprintf oc "	FMSU	%a, %a, %a\n" reg rd reg rs1 reg rs2
      (* Branches *)
      | Pjmp_l lbl ->
        fprintf oc "	JMP	%a\n" label (transl_label lbl)
      | Pjmp (r, sg) ->
        fprintf oc "	JMP_A	%a\n" reg r
      | Pjmp_s (id, sg) ->
        assert false (* should be removed in Asmexpand *)
      | Pjmp_p (r, sg) ->
        fprintf oc "	JMP_AP	%a\n" reg r
      | Pjmp_sp (id, sg) ->
        assert false (* should be removed in Asmexpand *)
      | Pbz (r, lbl) ->
        fprintf oc "	BZ_W	%a, %a\n" reg r label (transl_label lbl)
      | Pbnz (r, lbl) ->
        fprintf oc "	BNZ_W	%a, %a\n" reg r label (transl_label lbl)
      | Pbm (r, lbl) ->
        fprintf oc "	BM_W	%a, %a\n" reg r label (transl_label lbl)
      | Pbmz (r, lbl) ->
        fprintf oc "	BMZ_W	%a, %a\n" reg r label (transl_label lbl)
      | Pbnm (r, lbl) ->
        fprintf oc "	BNM_W	%a, %a\n" reg r label (transl_label lbl)
      | Pret ->
        fprintf oc "	RET\n"
      (* Pseudo-instructions that remain *)
      | Pallocframe (sz, ofs) ->
        assert false (* should be removed in Asmexpand *)
      | Pfreeframe (sz, ofs) ->
        assert false (* should be removed in Asmexpand *)
      | Plabel lbl ->
        fprintf oc "%a:\n" print_label lbl
      | Ploadsymbol (rd, id, ofs) ->
        let ofs = camlint_of_coqint ofs in
        fprintf oc "	MOV_WU	%a, hi18(%a+%ld)\n" reg rd symbol id ofs;
        fprintf oc "	SL_W	%a, 14\n" reg rd;
        fprintf oc "	ADD_WU	%a, lo14(%a+%ld)\n" reg rd symbol id ofs;
      | Pnop ->
        assert false (* should be removed in Asmexpand *)
      | Pcfi_adjust sz ->
        cfi_adjust oc (camlint_of_coqint sz)
      | Pcfi_rel_offset ofs ->
        cfi_rel_offset oc "Reg2" (camlint_of_coqint ofs)
      | Pbtbl (r1, tbl) ->
        fprintf oc "	MOV_W	%a, %a\n" reg Reg1 reg r1;
        fprintf oc "	ADD_W	%a, %d\n" reg Reg1 1;
        fprintf oc "	JMP	%a\n" reg Reg1;
        List.iter (fun l -> fprintf oc "	JMP	%a\n" label (transl_label l)) tbl
      | Pbuiltin (ef, args, res) ->
        begin match ef with
          | EF_annot (kind, txt, targs) ->
            begin match (P.to_int kind) with
              | 1 ->
                let annot = annot_text preg_annot "Reg0" (camlstring_of_coqstring txt) args in
                fprintf oc "%s annotation: %S\n" comment annot
              | 2 -> let lbl = new_label () in
                fprintf oc "%a:\n" label lbl;
                add_ais_annot lbl preg_annot "Reg0" (camlstring_of_coqstring txt) args
            | _ -> assert false
            end
          | EF_debug(kind, txt, targs) ->
            print_debug_info comment print_file_line preg_annot "Reg0" oc
              (P.to_int kind) (extern_atom txt) args
          | EF_inline_asm(txt, sg, clob) ->
            fprintf oc "%s begin inline assembly\n\t" comment;
            print_inline_asm (fun oc ty r -> preg_asm oc r) oc (camlstring_of_coqstring txt) sg args res;
            fprintf oc "%s end inline assembly\n" comment
          | _ ->
            assert false
        end
      | Ptbi (rd, imm) ->
        fprintf oc "	TB_W	%a, %a\n" reg rd coqint imm
      | Ptb (rd, r) ->
        fprintf oc "	TB_W	%a, %a\n" reg rd reg r
      | Prvbi (rd, imm) ->
        fprintf oc "	RVB_W	%a, %a\n" reg rd coqint imm
      | Psb (rd, imm) ->
        fprintf oc "	SB_W	%a, %a\n" reg rd coqint imm
      | Prb (rd, imm) ->
        fprintf oc "	RB_W	%a, %a\n" reg rd coqint imm

    let print_align oc alignment =
      fprintf oc "	.balign %d\n" alignment

    let print_jumptable oc _jmptbl =
      let print_tbl oc (lbl, tbl) =
        fprintf oc "%a:\n" label lbl;
        List.iter
          (fun l -> fprintf oc "	.long	%a - %a\n"
              print_label l label lbl)
          tbl in
      if !jumptables <> [] then
        begin
          section oc Section_jumptable;
          fprintf oc "	.balign 4\n";
          List.iter (print_tbl oc) !jumptables;
          jumptables := []
        end
    let print_fun_info = elf_print_fun_info

    let print_optional_fun_info _ = ()

    let print_var_info = elf_print_var_info

    let print_comm_symb oc sz name align =
      if C2C.atom_is_static name then
        fprintf oc "	.local	%a\n" symbol name;
      fprintf oc "	.comm	%a, %s, %d\n"
        symbol name
        (Z.to_string sz)
        align

    let print_instructions oc fn =
      current_function_sig := fn.fn_sig;
      List.iter (print_instruction oc) fn.fn_code

    (* Data *)

    let address = ".long"

    let print_prologue oc =
      if !Clflags.option_g then begin
        section oc Section_text;
      end

    let print_epilogue oc =
      if !Clflags.option_g then begin
        Debug.compute_gnu_file_enum (fun f -> ignore (print_file oc f));
        section oc Section_text;
      end

    let default_falignment = 2

  end


let sel_target () =
  (module Target:TARGET)
