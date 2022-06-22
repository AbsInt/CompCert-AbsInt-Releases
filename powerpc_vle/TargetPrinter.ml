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

(* Printing PPC assembly code in asm syntax *)

open Printf
open Fileinfo
open Maps
open Camlcoq
open Sections
open AST
open Asm
open PrintAsmaux
open AisAnnot

(* Recognition of target ABI and asm syntax *)

(*- E_COMPCERT_CODE_TargetPrinter_SYSTEM_001 *)
(*- #Justify_Derived "Type definitions" *)
module type SYSTEM =
    sig
      val comment: string
      val constant: out_channel -> constant -> unit
      val ireg: out_channel -> ireg -> unit
      val name_of_section: section_name -> string
      val is_comm_section: section_name -> bool
      val creg: out_channel -> int -> unit
      val print_file_line: out_channel -> string -> int -> unit
      val cfi_startproc: out_channel -> unit
      val cfi_endproc: out_channel -> unit
      val cfi_adjust: out_channel -> int32 -> unit
      val cfi_rel_offset: out_channel -> string -> int32 -> unit
      val print_prologue: out_channel -> unit
      val print_epilogue: out_channel -> unit
      val section: out_channel -> section_name -> unit
      val debug_section: out_channel -> section_name -> unit
      val address: string
    end
(*- #End *)

(*- E_COMPCERT_CODE_TargetPrinter_symbol_001 *)
(*- #Justify_Derived "Utility function" *)
let symbol = elf_symbol
(*- #End *)

(*- E_COMPCERT_CODE_TargetPrinter_symbol_offset_001 *)
(*- #Justify_Derived "Utility function" *)
let symbol_offset = elf_symbol_offset
(*- #End *)

(*- E_COMPCERT_CODE_TargetPrinter_symbol_fragment_001 *)
(*- #Justify_Derived "Utility function" *)
let symbol_fragment oc s n op =
      fprintf oc "(%a)%s" symbol_offset (s, n) op
(*- #End *)

let sreg_name = function
  | GPR0 -> "0"  | GPR1 -> "1"  | GPR2 -> "2"  | GPR3 -> "3"
  | GPR4 -> "4"  | GPR5 -> "5"  | GPR6 -> "6"  | GPR7 -> "7"
  | GPR24 -> "24" | GPR25 -> "25" | GPR26 -> "26" | GPR27 -> "27"
  | GPR28 -> "28" | GPR29 -> "29" | GPR30 -> "30" | GPR31 -> "31"

let areg_name = function
  | GPR8 -> "8"  | GPR9 -> "9"  | GPR10 -> "10" | GPR11 -> "11"
  | GPR12 -> "12" | GPR13 -> "13" | GPR14 -> "14" | GPR15 -> "15"
  | GPR16 -> "16" | GPR17 -> "17" | GPR18 -> "18" | GPR19 -> "19"
  | GPR20 -> "20" | GPR21 -> "21" | GPR22 -> "22" | GPR23 -> "23"

(*- E_COMPCERT_CODE_TargetPrinter_int_reg_name_001 *)
(*- #Justify_Derived "Utility function" *)
let int_reg_name = function
  | Sreg r -> sreg_name r
  | Areg r -> areg_name r
(*- #End *)


(*- E_COMPCERT_CODE_TargetPrinter_num_crbit_001 *)
(*- #Justify_Derived "Utility function" *)
let num_crbit = function
  | CRbit_0 -> 0
  | CRbit_1 -> 1
  | CRbit_2 -> 2
  | CRbit_3 -> 3
  | CRbit_5 -> 5
  | CRbit_6 -> 6
(*- #End *)

(*- E_COMPCERT_CODE_TargetPrinter_label_001 *)
(*- #Justify_Derived "Utility function" *)
let label = elf_label
(*- #End *)

module Linux_System : SYSTEM =
  struct

    (*- E_COMPCERT_CODE_TargetPrinter_comment_001 *)
    (*- #Justify_Derived "Utility constant" *)
    let comment = "#"
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_constant_001 *)
    (*- #Justify_Derived "Utility function" *)
    let constant oc cst =
      match cst with
      | Cint n ->
          fprintf oc "%ld" (camlint_of_coqint n)
      | Csymbol_low(s, n) ->
          symbol_fragment oc s n "@l"
      | Csymbol_high(s, n) ->
          symbol_fragment oc s n "@ha"
      | Csymbol_sda(s, n) ->
          symbol_fragment oc s n "@sda21"
            (* 32-bit relative addressing is supported by the Diab tools but not by
               GNU binutils.  In the latter case, for testing purposes, we treat
               them as absolute addressings.  The default base register being GPR0,
               this produces correct code, albeit with absolute addresses. *)
      | Csymbol_rel_low(s, n) ->
          symbol_fragment oc s n "@l"
      | Csymbol_rel_high(s, n) ->
          symbol_fragment oc s n "@ha"
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_ireg_001 *)
    (*- #Justify_Derived "Utility function" *)
    let ireg oc r =
      output_string oc (int_reg_name r)
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_creg_001 *)
    (*- #Justify_Derived "Utility function" *)
    let creg oc r =
      fprintf oc "%d" r
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_is_comm_section_001 *)
    (*- #Justify_Derived "Utility function" *)
    let is_comm_section = default_is_comm_section
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_name_of_section_001 *)
    (*- #Justify_Derived "Utility function" *)
    let name_of_section = function
      | Section_text -> ".text"
      | Section_data i ->
          variable_section ~sec:".data" ~bss:".section	.bss" i
      | Section_small_data i ->
          variable_section
            ~sec:".section	.sdata,\"aw\",@progbits"
            ~bss:".section	.sbss,\"aw\",@nobits"
            i
      | Section_const i ->
          variable_section ~sec:".rodata" i
      | Section_small_const i ->
          variable_section ~sec:".section	.sdata2,\"a\",@progbits" i
      | Section_string -> ".rodata"
      | Section_literal -> ".section	.rodata.cst8,\"aM\",@progbits,8"
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
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_section_001 *)
    (*- #Justify_Derived "Utility function" *)
    let section oc sec =
      let name = name_of_section sec in
      assert (name <> "COMM");
      fprintf oc "	%s\n" name
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_print_file_line_001 *)
    (*- #Justify_Derived "Utility function" *)
    let print_file_line oc file line =
      print_file_line oc comment file line
    (*- #End *)

    (* Emit .cfi directives *)
    (*- E_COMPCERT_CODE_TargetPrinter_cfi_001 *)
    (*- #Justify_Derived "Utility functions" *)
    let cfi_startproc = cfi_startproc

    let cfi_endproc = cfi_endproc

    let cfi_adjust = cfi_adjust

    let cfi_rel_offset = cfi_rel_offset
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_print_prologue_001 *)
    (*- #Link_to E_COMPCERT_TR_Function_PRINT_ASM_A_002 *)
    let print_prologue oc =
      if !Clflags.option_g then  begin
        section oc Section_text;
        cfi_section oc
      end
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_print_epilogue_001 *)
    (*- #Link_to E_COMPCERT_TR_Function_PRINT_ASM_A_003 *)
    let print_epilogue oc =
      if !Clflags.option_g then
        begin
          Debug.compute_gnu_file_enum (fun f -> ignore (print_file oc f));
          section oc Section_text;
        end
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_debug_section_001 *)
    (*- #Justify_Derived "Utility function" *)
    let debug_section _ _ = ()
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_address_001 *)
    (*- #Justify_Derived "Utility constant" *)
    let address = if Archi.ptr64 then ".quad" else ".4byte"
    (*- #End *)
  end

(*- E_COMPCERT_CODE_module_diab_001 *)
(*- #Justify_Derived "Unused Diab Module" *)
module Diab_System : SYSTEM =
  struct

    let comment = ";"

    let constant oc cst =
      match cst with
      | Cint n ->
          fprintf oc "%ld" (camlint_of_coqint n)
      | Csymbol_low(s, n) ->
          symbol_fragment oc s n "@l"
      | Csymbol_high(s, n) ->
          symbol_fragment oc s n "@ha"
      | Csymbol_sda(s, n) ->
          symbol_fragment oc s n "@sdarx"
      | Csymbol_rel_low(s, n) ->
          symbol_fragment oc s n "@sdax@l"
      | Csymbol_rel_high(s, n) ->
          symbol_fragment oc s n "@sdarx@ha"

    let ireg oc r =
      output_char oc 'r';
      output_string oc (int_reg_name r)

    let creg oc r =
      fprintf oc "cr%d" r

    (* Only non initialized variables that should be placed in Section_data
       can be emitted as common symbol for diab data. *)
    let is_comm_section = function
      | Section_data i -> !Clflags.option_fcommon && (i = Uninit)
      | _ -> false

    let name_of_section = function
      | Section_text -> ".text"
      | Section_data i ->
          variable_section ~sec:".data" ~bss:".bss" i
      | Section_small_data i ->
          variable_section ~sec:".sdata" ~bss:".sbss" i
      | Section_const _ -> ".text"
      | Section_small_const _ -> ".sdata2"
      | Section_string -> ".text"
      | Section_literal -> ".text"
      | Section_jumptable -> ".text"
      | Section_user(s, wr, ex) ->
          sprintf ".section	\"%s\",,%c"
               s
            (match wr, ex with
            | true, true -> 'm'                 (* text+data *)
            | true, false -> 'd'                (* data *)
            | false, true -> 'c'                (* text *)
            | false, false -> 'r')              (* const *)
      | Section_debug_info (Some s) ->
          sprintf ".section	.debug_info%s,,n" s
      | Section_debug_info None ->
          sprintf ".section	.debug_info,,n"
      | Section_debug_abbrev -> ".section	.debug_abbrev,,n"
      | Section_debug_loc -> ".section	.debug_loc,,n"
      | Section_debug_line (Some s) ->
          sprintf ".section	.debug_line.%s,,n\n" s
      | Section_debug_line None ->
          sprintf ".section	.debug_line,,n\n"
      | Section_debug_ranges
      | Section_debug_str -> assert false (* Should not be used *)
      | Section_ais_annotation -> sprintf ".section	\"__compcert_ais_annotations\",,n"

    let section oc sec =
      let name = name_of_section sec in
      assert (name <> "COMM");
      match sec with
      | Section_debug_info (Some s) ->
          fprintf oc "	%s\n" name;
          fprintf oc "	.sectionlink	.debug_info\n"
      | _ ->
          fprintf oc "	%s\n" name

    let print_file_line oc file line =
      print_file_line_d2 oc comment file line

    (* Emit .cfi directives *)
    let cfi_startproc oc = ()

    let cfi_endproc oc = ()

    let cfi_adjust oc delta = ()

    let cfi_rel_offset oc reg ofs = ()

    let debug_section oc sec =
      match sec with
      | Section_debug_abbrev
      | Section_debug_info _
      | Section_debug_str
      | Section_debug_loc -> ()
      | sec ->
          let name = match sec with
          | Section_user (name,_,_) -> name
          | _ -> name_of_section sec in
          if not (Debug.exists_section sec) then
            let line_start = new_label ()
            and low_pc = new_label ()
            and debug_info = new_label () in
            Debug.add_diab_info sec line_start debug_info low_pc;
            let line_name = ".debug_line" ^(if name <> ".text" then name else "") in
            section oc (Section_debug_line (if name <> ".text" then Some name else None));
            fprintf oc "	.section	%s,,n\n" line_name;
            if name <> ".text" then
              fprintf oc "	.sectionlink	.debug_line\n";
            fprintf oc "%a:\n" label line_start;
            section oc sec;
            fprintf oc "%a:\n" label low_pc;
            fprintf oc "	.0byte	%a\n" label debug_info;
            fprintf oc "	.d2_line_start	%s\n" line_name
          else
            ()

    let print_prologue oc =
      fprintf oc "	.xopt	align-fill-text=0x60000000\n";
      debug_section oc Section_text

    let print_epilogue oc =
      let end_label sec =
        fprintf oc "\n";
        section oc sec;
        let label_end = new_label () in
        fprintf oc "%a:\n" label label_end;
        label_end
      and entry_label f =
        let label = new_label () in
        fprintf oc ".L%d:	.d2filenum \"%s\"\n" label f;
        label
      and end_line () =   fprintf oc "	.d2_line_end\n" in
      Debug.compute_diab_file_enum end_label entry_label end_line

    let address = assert (not Archi.ptr64); ".4byte"

  end
(*- #End *)

module Target (System : SYSTEM):TARGET =
  struct
    include System

    (* Basic printing functions *)
    (*- E_COMPCERT_CODE_TargetPrinter_symbol_002 *)
    (*- #Justify_Derived "Utility function" *)
    let symbol = symbol
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_label_002 *)
    (*- #Justify_Derived "Utility function" *)
    let label = label
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_label_low_001 *)
    (*- #Justify_Derived "Utility function" *)
    let label_low oc lbl =
      fprintf oc ".L%d@l" lbl
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_label_high_001 *)
    (*- #Justify_Derived "Utility function" *)
    let label_high oc lbl =
      fprintf oc ".L%d@ha" lbl
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_crbit_001 *)
    (*- #Justify_Derived "Utility function" *)
    let crbit oc bit =
      fprintf oc "%d" (num_crbit bit)
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_preg_asm_001 *)
    (*- #Justify_Derived "Utility function" *)
    let preg_asm oc ty = function
      | IR r -> ireg oc r
      | _    -> assert false
    (*- #End *)

    let sreg oc r = ireg oc (Sreg r)

    let areg oc r = ireg oc (Areg r)

    (* For printing annotations, use the full register names [rN] and [fN]
       to avoid ambiguity with constants. *)
    (*- E_COMPCERT_CODE_TargetPrinter_preg_annot_001 *)
    (*- #Justify_Derived "Utility function" *)
    let preg_annot = function
      | IR r -> sprintf "r%s" (int_reg_name r)
      | _    -> assert false
    (*- #End *)

    (* Encoding masks for rlwinm instructions *)

    (*- E_COMPCERT_CODE_TargetPrinter_rolm_mask_001 *)
    (*- #Justify_Derived "Utility function" *)
    let rolm_mask n =
      let mb = ref 0       (* location of last 0->1 transition *)
      and me = ref 32      (* location of last 1->0 transition *)
      and last = ref ((Int32.logand n 1l) <> 0l)  (* last bit seen *)
      and count = ref 0    (* number of transitions *)
      and mask = ref 0x8000_0000l in
      for mx = 0 to 31 do
        if Int32.logand n !mask <> 0l then
          if !last then () else (incr count; mb := mx; last := true)
        else
          if !last then (incr count; me := mx; last := false) else ();
        mask := Int32.shift_right_logical !mask 1
      done;
      if !me = 0 then me := 32;
      assert (!count = 2 || (!count = 0 && !last));
      (!mb, !me-1)
    (*- #End *)

    (* Determine if the displacement of a conditional branch fits the short form *)

    (*- E_COMPCERT_CODE_TargetPrinter_short_cond_branch_001 *)
    (*- #Justify_Derived "Utility function" *)
    let short_cond_branch tbl pc lbl_dest =
      match PTree.get lbl_dest tbl with
      | None -> assert false
      | Some pc_dest ->
          let disp = pc_dest - pc in -0x2000 <= disp && disp < 0x2000
    (*- #End *)

    (* Printing of instructions *)

    (*- E_COMPCERT_CODE_TargetPrinter_print_instruction_001 *)
    let print_instruction oc tbl pc fallthrough = function
      | Padd(r1, r2, r3) ->
          fprintf oc "	add	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pse_add (r1, r2) ->
          fprintf oc "	se_add	%a, %a\n" sreg r1 sreg r2
      | Paddc(r1, r2, r3) ->
          fprintf oc "	addc	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Padde(r1, r2, r3) ->
          fprintf oc "	adde	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Paddze(r1, r2) ->
          fprintf oc "	addze	%a, %a\n" ireg r1 ireg r2
      | Pallocframe(sz, ofs, _) ->
          assert false
      | Pand_(r1, r2, r3) ->
          fprintf oc "	and.	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pse_and_(r1, r2) ->
          fprintf oc "	se_and.	%a, %a\n" sreg r1 sreg r2
      | Pse_andc(r1, r2) ->
          fprintf oc "	se_andc	%a, %a\n" sreg r1 sreg r2
      | Pandc(r1, r2, r3) ->
          fprintf oc "	andc	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pbdnz lbl ->
          fprintf oc "	e_bdnz	%a\n" label (transl_label lbl)

      (*- #Link_to E_COMPCERT_TR_Function_PRINT_ASM_B_001 *)
      | Pbf(bit, lbl) ->
          if !Clflags.option_faligncondbranchs > 0 then
            fprintf oc "	.balign	%d\n" !Clflags.option_faligncondbranchs;
          if short_cond_branch tbl pc lbl then
            fprintf oc "	e_bf	%a, %a\n" crbit bit label (transl_label lbl)
          else begin
            let next = new_label() in
            fprintf oc "	e_bt	%a, %a\n" crbit bit label next;
            fprintf oc "	e_b	%a\n" label (transl_label lbl);
            fprintf oc "%a:\n" label next
          end

      (*- #Link_to E_COMPCERT_TR_Function_PRINT_ASM_B_002 *)
      | Pbt(bit, lbl) ->
          if !Clflags.option_faligncondbranchs > 0 then
            fprintf oc "	.balign	%d\n" !Clflags.option_faligncondbranchs;
          if short_cond_branch tbl pc lbl then
            fprintf oc "	e_bt	%a, %a\n" crbit bit label (transl_label lbl)
          else begin
            let next = new_label() in
            fprintf oc "	e_bf	%a, %a\n" crbit bit label next;
            fprintf oc "	e_b	%a\n" label (transl_label lbl);
            fprintf oc "%a:\n" label next
          end

      (*- #Link_to E_COMPCERT_TR_Function_PRINT_ASM_B_003 *)
      | Pbtbl(r, tbl) ->
          let lbl = new_label() in
          fprintf oc "%s begin pseudoinstr btbl(%a)\n" comment ireg r;
          fprintf oc "%s jumptable [ " comment;
          List.iter (fun l -> fprintf oc "%a " label (transl_label l)) tbl;
          fprintf oc "]\n";
          fprintf oc "	e_slwi    %a, %a, 2\n" ireg (Areg GPR12) ireg r;
          fprintf oc "	e_add2is	%a, %a\n" ireg (Areg GPR12) label_high lbl;
          fprintf oc "	e_lwz	%a, %a(%a)\n" ireg (Areg GPR12) label_low lbl ireg (Areg GPR12);
          fprintf oc "	se_mfar	%a, %a\n" ireg (Sreg GPR0) ireg (Areg GPR12);
          fprintf oc "	se_mtctr	%a\n" ireg (Sreg GPR0);
          fprintf oc "	se_bctr\n";
          jumptables := (lbl, tbl) :: !jumptables;
          fprintf oc "%s end pseudoinstr btbl\n" comment

      | Pcmplw(r1, r2) ->
          fprintf oc "	cmplw	%a, %a, %a\n" creg 0 ireg r1 ireg r2
      | Pcmpw(r1, r2) ->
          fprintf oc "	cmpw	%a, %a, %a\n" creg 0 ireg r1 ireg r2
      | Pcntlzw(r1, r2) ->
          fprintf oc "	cntlzw	%a, %a\n" ireg r1 ireg r2
      | Pe_creqv(c1, c2, c3) ->
          fprintf oc "	e_creqv	%a, %a, %a\n" crbit c1 crbit c2 crbit c3
      | Pe_cror(c1, c2, c3) ->
          fprintf oc "	e_cror	%a, %a, %a\n" crbit c1 crbit c2 crbit c3
      | Pe_crxor(c1, c2, c3) ->
          fprintf oc "	e_crxor	%a, %a, %a\n" crbit c1 crbit c2 crbit c3
      | Pdcbf (r1,r2) ->
          fprintf oc "	dcbf	%a, %a\n" ireg r1 ireg r2
      | Pdcbi (r1,r2) ->
          fprintf oc "	dcbi	%a, %a\n" ireg r1 ireg r2
      | Pdcbt (c,r1,r2) ->
          fprintf oc "	dcbt	%ld, %a, %a\n" (camlint_of_coqint c) ireg r1  ireg r2
      | Pdcbtst (c,r1,r2) ->
          fprintf oc "	dcbtst	%ld, %a, %a\n"  (camlint_of_coqint c) ireg r1 ireg r2
      | Pdcbtls (c,r1,r2) ->
          fprintf oc "	dcbtls	%ld, %a, %a\n" (camlint_of_coqint c) ireg r1 ireg r2
      | Pdcbz (r1,r2) ->
          fprintf oc "	dcbz	%a, %a\n" ireg r1 ireg r2
      | Pdivw(r1, r2, r3) ->
          fprintf oc "	divw	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pdivwu(r1, r2, r3) ->
          fprintf oc "	divwu	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Peqv(r1, r2, r3) ->
          fprintf oc "	eqv	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pextsb(r1, r2) ->
          fprintf oc "	extsb	%a, %a\n" ireg r1 ireg r2
      | Pextsh(r1, r2) ->
          fprintf oc "	extsh	%a, %a\n" ireg r1 ireg r2
      | Pfreeframe(sz, ofs) ->
          assert false
      | Pisel (r1,r2,r3,cr) ->
          fprintf oc "	isel	%a, %a, %a, %a\n" ireg r1 ireg r2 ireg r3 crbit cr
      | Picbi (r1,r2) ->
          fprintf oc "	icbi	%a, %a\n" ireg r1 ireg r2
      | Picbtls (n,r1,r2) ->
          fprintf oc "	icbtls	%ld, %a, %a\n" (camlint_of_coqint n) ireg r1 ireg r2
      | Pse_isync ->
          fprintf oc "	se_isync\n"
      | Plbzx(r1, r2, r3) ->
          fprintf oc "	lbzx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Plhax(r1, r2, r3) ->
          fprintf oc "	lhax	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Plhbrx(r1, r2, r3) ->
          fprintf oc "	lhbrx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Plhzx(r1, r2, r3) ->
          fprintf oc "	lhzx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3


      | Plwbrx(r1, r2, r3) ->
          fprintf oc "	lwbrx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Plwzx(r1, r2, r3) | Plwzx_a(r1, r2, r3)  | Pflwzx(r1, r2, r3) ->
          fprintf oc "	lwzx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pmfcr(r1) ->
          fprintf oc "	mfcr	%a\n" ireg r1
      | Pmfcrbit(r1, bit) ->
          assert false
      | Pse_mflr(r1) ->
          fprintf oc "	se_mflr	%a\n" sreg r1
      | Pmfspr(rd, spr) ->
          fprintf oc "	mfspr	%a, %ld\n" ireg rd (camlint_of_coqint spr)
      | Pmtspr(spr, rs) ->
          fprintf oc "	mtspr	%ld, %a\n" (camlint_of_coqint spr) ireg rs
      | Pmr(r1, r2) ->
          fprintf oc "	mr	%a, %a\n" ireg r1 ireg r2
      | Pmullw(r1, r2, r3) ->
          fprintf oc "	mullw	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pse_mullw(r1, r2) ->
          fprintf oc "	se_mullw	%a, %a\n" sreg r1 sreg r2
      | Pe_mulli (r1, r2 , imm) ->
          fprintf oc "	e_mulli	%a, %a, %ld\n" ireg r1 ireg r2 (camlint_of_coqint imm)
      | Pe_mull2i (r , imm) ->
          fprintf oc "	e_mull2i	%a, %ld\n" ireg r (camlint_of_coqint imm)
      | Pmulhw(r1, r2, r3) ->
          fprintf oc "	mulhw	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pmulhwu(r1, r2, r3) ->
          fprintf oc "	mulhwu	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pnand(r1, r2, r3) ->
          fprintf oc "	nand	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pnor(r1, r2, r3) ->
          fprintf oc "	nor	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Por(r1, r2, r3) ->
          fprintf oc "	or	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pse_or(r1, r2) ->
          fprintf oc "	se_or	%a, %a\n" sreg r1 sreg r2
      | Porc(r1, r2, r3) ->
          fprintf oc "	orc	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pslw(r1, r2, r3) ->
          fprintf oc "	slw	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pse_slw(r1, r2) ->
          fprintf oc "	se_slw	%a, %a\n" sreg r1 sreg r2
      | Psraw(r1, r2, r3) ->
          fprintf oc "	sraw	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pse_sraw(r1, r2) ->
          fprintf oc "	se_sraw	%a, %a\n" sreg r1 sreg r2
      | Psrawi(r1, r2, n) ->
          fprintf oc "	srawi	%a, %a, %ld\n" ireg r1 ireg r2 (camlint_of_coqint n)
      | Psrw(r1, r2, r3) ->
          fprintf oc "	srw	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pse_srw(r1, r2) ->
          fprintf oc "	se_srw	%a, %a\n" sreg r1 sreg r2
      | Pstbx(r1, r2, r3) ->
          fprintf oc "	stbx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Psthx(r1, r2, r3) ->
          fprintf oc "	sthx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Psthbrx(r1, r2, r3) ->
          fprintf oc "	sthbrx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pstwx(r1, r2, r3) | Pstwx_a(r1, r2, r3) | Pfstwx(r1, r2, r3) ->
          fprintf oc "	stwx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pstwux(r1, r2, r3) ->
          fprintf oc "	stwux	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pstwbrx(r1, r2, r3) ->
          fprintf oc "	stwbrx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pse_sub(r1, r2) ->
          fprintf oc "	se_sub	%a, %a\n" sreg r1 sreg r2
      | Pse_subi(r1, n) ->
          fprintf oc "	se_subi	%a, %ld\n" sreg r1 (camlint_of_coqint n)
      | Pse_subf(r1, r2) ->
          fprintf oc "	se_subf	%a, %a\n" sreg r1 sreg r2
      | Psubfc(r1, r2, r3) ->
          fprintf oc "	subfc	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Psubfe(r1, r2, r3) ->
          fprintf oc "	subfe	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Psubfze(r1, r2) ->
          fprintf oc "	subfze	%a, %a\n" ireg r1 ireg r2
      | Psync ->
          fprintf oc "	sync\n"
      | Pxor(r1, r2, r3) ->
          fprintf oc "	xor	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Plabel lbl ->
          if (not fallthrough) && !Clflags.option_falignbranchtargets > 0 then
            fprintf oc "	.balign	%d\n" !Clflags.option_falignbranchtargets;
          fprintf oc "%a:\n" label (transl_label lbl)

      (*- #Link_to E_COMPCERT_TR_Function_PRINT_ASM_B_007 *)
      | Pbuiltin(ef, args, res) ->
        begin match ef with
          | EF_annot(kind,txt, targs) ->
            begin match (P.to_int kind) with
              | 1 -> let annot = annot_text preg_annot "sp" (camlstring_of_coqstring txt) args in
                fprintf oc "%s annotation: %S\n" comment annot

              | 2 -> let lbl = new_label () in
                fprintf oc "%a:\n" label lbl;
                add_ais_annot lbl preg_annot "r1" (camlstring_of_coqstring txt) args
              | _ -> assert false
              end
          | EF_debug(kind, txt, targs) ->
              print_debug_info comment print_file_line preg_annot "r1" oc
                               (P.to_int kind) (extern_atom txt) args
          | EF_inline_asm(txt, sg, clob) ->
              fprintf oc "%s begin inline assembly\n\t" comment;
              print_inline_asm preg_asm oc (camlstring_of_coqstring txt) sg args res;
              fprintf oc "%s end inline assembly\n" comment
          | _ ->
              assert false
          end

      | Pcfi_adjust n ->
          cfi_adjust oc (camlint_of_coqint n)
      | Pcfi_rel_offset n ->
          cfi_rel_offset oc "lr" (camlint_of_coqint n)
      (* VLE instructions *)
      | Pse_mr (rd, r1) ->
          fprintf oc "	se_mr	%a, %a\n" sreg rd sreg r1
      | Pse_mtar (rd, r1) ->
        fprintf oc "	se_mtar	%a, %a\n" areg rd sreg r1
      | Pse_mfar (rd, r1) ->
        fprintf oc "	se_mfar	%a, %a\n" sreg rd areg r1
      | Pe_andi_ (rd, r1, imm) ->
          fprintf oc "	e_andi.	%a, %a, %ld\n" ireg rd ireg r1 (camlint_of_coqint imm)
      | Pe_and2i_ (rd, c) ->
          fprintf oc "	e_and2i.	%a, %a\n" ireg rd constant c
      | Pe_and2is_ (rd, cst) ->
          fprintf oc "	e_and2is.	%a, %a\n" ireg rd constant cst
      | Pe_add16i (r1, r2, c) ->
          fprintf oc "	e_add16i	%a, %a, %a\n" ireg r1 ireg r2 constant c
      | Pe_addi (r1, r2, imm) ->
          fprintf oc "	e_addi	%a, %a, %ld\n" ireg r1 ireg r2 (camlint_of_coqint imm)
      | Pe_add2is (rd, cst) ->
          fprintf oc "	e_add2is	%a, %a\n" ireg rd constant cst
      | Pse_addi (r1, imm) ->
          fprintf oc "	se_addi	%a, %ld\n" sreg r1 (camlint_of_coqint imm)
      | Pe_addic(r1, r2, c) ->
          fprintf oc "	e_addic	%a, %a, %ld\n" ireg r1 ireg r2 (camlint_of_coqint c)
      | Pe_b lbl ->
          fprintf oc "	e_b	%a\n" label (transl_label lbl)
      | Pse_bctr sg ->
          fprintf oc "	se_bctr\n"
      | Pse_bctrl sg ->
          fprintf oc "	se_bctrl\n"
      | Pe_bl(s, sg) ->
          fprintf oc "	e_bl	%a\n" symbol s
      | Pse_blr ->
          fprintf oc "	se_blr\n"
      | Pe_bs(s, sg) ->
          fprintf oc "	e_b	%a\n" symbol s
      | Pse_cmp (rd, r1) ->
          fprintf oc "	se_cmp	%a, %a\n" sreg rd sreg r1
      | Pe_cmp16i (rd, cst) ->
          fprintf oc "	e_cmp16i	%a, %a\n" ireg rd constant cst
      | Pse_cmpi (rd, cst) ->
          fprintf oc "	se_cmpi	%a, %ld\n" sreg rd (camlint_of_coqint cst)
      | Pse_cmpl (rd, r1) ->
          fprintf oc "	se_cmpl	%a, %a\n" sreg rd sreg r1
      | Pe_cmpl16i (rd, cst) ->
          fprintf oc "	e_cmpl16i	%a, %a\n" ireg rd constant cst
      | Pse_extsb r ->
          fprintf oc "	se_extsb	%a\n" sreg r
      | Pse_extsh r ->
          fprintf oc "	se_extsh	%a\n" sreg r
      | Pse_bgeni (rd, c) ->
          fprintf oc "	se_bgeni	%a, %ld\n" sreg rd (camlint_of_coqint c)
      | Pse_li (rd, c) ->
          fprintf oc "	se_li	%a, %ld\n" sreg rd (camlint_of_coqint c)
      | Pe_li (rd, c) ->
          fprintf oc "	e_li	%a, %a\n" ireg rd constant c
      | Pe_lis (rd, c) ->
          fprintf oc "	e_lis	%a, %a\n" ireg rd constant c
      | Pe_lbz (rd, c, r1) ->
          fprintf oc "	e_lbz %a, %a(%a)\n" ireg rd constant c ireg r1
      | Pse_lbz (rd, c, r1) ->
          fprintf oc "  se_lbz %a, %a(%a)\n" sreg rd constant (Cint c) sreg r1
      | Pe_lha (rd, c, r1) ->
          fprintf oc "	e_lha %a, %a(%a)\n" ireg rd constant c ireg r1
      | Pe_lhz (rd, c, r1) ->
          fprintf oc "	e_lhz %a, %a(%a)\n" ireg rd constant c ireg r1
      | Pse_lhz (rd, c, r1) ->
          fprintf oc "  se_lhz %a, %a(%a)\n" sreg rd constant (Cint c) sreg r1
      | Pe_lwz(r1, c, r2) | Pe_lwz_a(r1, c, r2) | Pfe_lwz(r1, c, r2) ->
          fprintf oc "	e_lwz	%a, %a(%a)\n" ireg r1 constant c ireg r2
      | Pse_lwz(r1, c, r2) | Pse_lwz_a(r1, c, r2) | Pfse_lwz (r1, c, r2) ->
          fprintf oc "	se_lwz	%a, %a(%a)\n" sreg r1 constant (Cint c) sreg r2
      | Pe_lwzu(r1, c, r2) ->
          fprintf oc "	e_lwzu	%a, %a(%a)\n" ireg r1 constant c ireg r2
      | Pse_mtctr rd ->
          fprintf oc "	se_mtctr	%a\n" sreg rd
      | Pse_mtlr rd ->
          fprintf oc "	se_mtlr	%a\n" sreg rd
      | Pe_or2i (rd, c) ->
          fprintf oc "	e_or2i	%a, %a\n" ireg rd constant c
      | Pe_ori (rd, r1, imm) ->
          fprintf oc "	e_ori	%a, %a, %ld\n" ireg rd ireg r1 (camlint_of_coqint imm)
      | Pe_or2is (rd, c) ->
           fprintf oc "	e_or2is	%a, %a\n" ireg rd constant c
      | Pe_rlwinm(r1, r2, c1, c2) ->
          let (mb, me) = rolm_mask (camlint_of_coqint c2) in
          fprintf oc "	e_rlwinm	%a, %a, %ld, %d, %d %s 0x%lx\n"
            ireg r1 ireg r2 (camlint_of_coqint c1) mb me
            comment (camlint_of_coqint c2)
      | Pe_rlwimi(r1, r2, c1, c2) ->
          let (mb, me) = rolm_mask (camlint_of_coqint c2) in
          fprintf oc "	e_rlwimi	%a, %a, %ld, %d, %d %s 0x%lx\n"
            ireg r1 ireg r2 (camlint_of_coqint c1) mb me
            comment (camlint_of_coqint c2)
      | Pse_srawi (rd, imm) ->
          fprintf oc "	se_srawi	%a, %ld\n" sreg rd (camlint_of_coqint imm)
      | Pe_stb (r1, c, r2) ->
          fprintf oc "	e_stb  %a, %a(%a)\n" ireg r1 constant c ireg r2
      | Pse_stb (r1, c, r2) ->
          fprintf oc "	se_stb  %a, %a(%a)\n" sreg r1 constant (Cint c) sreg r2
      | Pe_sth (r1, c, r2) ->
          fprintf oc "	e_sth  %a, %a(%a)\n" ireg r1 constant c ireg r2
      | Pse_sth (r1, c, r2) ->
          fprintf oc "	se_sth  %a, %a(%a)\n" sreg r1 constant (Cint c) sreg r2
      | Pe_stw(r1, c, r2) | Pe_stw_a(r1, c, r2)| Pfe_stw(r1, c, r2) ->
          fprintf oc "	e_stw	%a, %a(%a)\n" ireg r1 constant c ireg r2
      | Pse_stw(r1, c, r2) | Pse_stw_a(r1, c, r2)| Pfse_stw(r1, c, r2) ->
          fprintf oc "	se_stw	%a, %a(%a)\n" sreg r1 constant (Cint c) sreg r2
      | Pe_stwu(r1, c, r2) ->
          fprintf oc "	e_stwu	%a, %a(%a)\n" ireg r1 constant c ireg r2
      | Pe_subfic(r1, r2, c) ->
          fprintf oc "	e_subfic	%a, %a, %ld\n" ireg r1 ireg r2 (camlint_of_coqint c)
      | Pe_xori(r1, r2, c) ->
          fprintf oc "	e_xori	%a, %a, %ld\n" ireg r1 ireg r2 (camlint_of_coqint c)
      | Pefsabs (r1, r2) ->
          fprintf oc "	efsabs	%a, %a\n" ireg r1 ireg r2
      | Pefsadd (r1, r2, r3) ->
          fprintf oc "	efsadd	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pefsdiv (r1, r2, r3) ->
          fprintf oc "	efsdiv	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pefsmul (r1, r2, r3) ->
          fprintf oc "	efsmul	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pefsneg (r1, r2) ->
          fprintf oc "	efsneg	%a, %a\n" ireg r1 ireg r2
      | Pefssub (r1, r2, r3) ->
          fprintf oc "	efssub	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Plfis _ -> assert false (* Removed in Asmexpand *)
      | Pefscfsi (r1, r2) ->
          fprintf oc "	efscfsi	%a, %a\n" ireg r1 ireg r2
      | Pefscfui (r1, r2) ->
          fprintf oc "	efscfui	%a, %a\n" ireg r1 ireg r2
      | Pefsctsi (r1, r2) ->
          fprintf oc "	efsctsi	%a, %a\n" ireg r1 ireg r2
      | Pefsctui (r1, r2) ->
          fprintf oc "	efsctui	%a, %a\n" ireg r1 ireg r2
      | Pefscmpeq (r1, r2) ->
          fprintf oc "	efscmpeq	0, %a, %a\n" ireg r1 ireg r2
      | Pefscmpgt (r1, r2) ->
          fprintf oc "	efscmpgt	1, %a, %a\n" ireg r1 ireg r2
      | Pefscmplt (r1, r2) ->
          fprintf oc "	efscmplt	1, %a, %a\n" ireg r1 ireg r2
    (*- #End *)

    (* Determine if an instruction falls through *)

    (*- E_COMPCERT_CODE_TargetPrinter_instr_fall_through_001 *)
    (*- #Justify_Derived "Functional decomposition" *)
    let instr_fall_through = function
      | Pe_b _ -> false
      | Pe_bs _ -> false
      | Pse_bctr _ -> false
      | Pse_blr -> false
      | _ -> true
    (*- #End *)

    (* Estimate the size of an Asm instruction encoding, in number of actual
       PowerPC instructions.  We can over-approximate. *)

    (*- E_COMPCERT_CODE_TargetPrinter_instr_size_001 *)
    (*- #Justify_Derived "Utility function" *)
    let instr_size = function
      | Pbf(bit, lbl) -> 2
      | Pbt(bit, lbl) -> 2
      | Pbtbl(r, tbl) -> 5
      | Plabel lbl -> 0
      | Pbuiltin((EF_annot _ | EF_debug _), args, res) -> 0
      | Pbuiltin(ef, args, res) -> 3
      | Pcfi_adjust _ | Pcfi_rel_offset _ -> 0
      | _ -> 1
    (*- #End *)

   (* Build a table label -> estimated position in generated code.
      Used to predict if relative conditional branches can use the short form. *)

    (*- E_COMPCERT_CODE_TargetPrinter_label_positions_001 *)
    (*- #Justify_Derived "Functional decomposition" *)
    let rec label_positions tbl pc = function
      | [] -> tbl
      | Plabel lbl :: c -> label_positions (PTree.set lbl pc tbl) pc c
      | i :: c -> label_positions tbl (pc + instr_size i) c
    (*- #End *)

    (* Emit a sequence of instructions *)

    (*- E_COMPCERT_CODE_TargetPrinter_print_instructions_001 *)
    (*- #Justify_Derived "Utility function" *)
    let print_instructions oc fn =
      let rec aux  oc tbl pc fallthrough = function
      | [] -> ()
      | i :: c ->
          print_instruction oc tbl pc fallthrough i;
         aux oc tbl (pc + instr_size i) (instr_fall_through i) c in
      aux oc (label_positions PTree.empty 0 fn.fn_code) 0 true fn.fn_code
    (*- #End *)

    (* Print the code for a function *)

    (*- E_COMPCERT_CODE_TargetPrinter_print_literal64_001 *)
    (*- #Justify_Derived "Functional decomposition" *)
    let print_literal64 oc n lbl =
      let nlo = Int64.to_int32 n
      and nhi = Int64.to_int32(Int64.shift_right_logical n 32) in
      fprintf oc "%a:	.long	0x%lx, 0x%lx\n" label lbl nhi nlo
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_print_literal32_001 *)
    (*- #Justify_Derived "Functional decomposition" *)
    let print_literal32 oc n lbl =
      fprintf oc "%a:	.long	0x%lx\n" label lbl n
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_print_fun_info_001 *)
    (*- #Justify_Derived "Utility function" *)
    let print_fun_info = elf_print_fun_info
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_emit_constants_001 *)
    (*- #Justify_Derived "Utility function" *)
    let emit_constants oc lit =
      if exists_constants () then begin
        section oc lit;
        fprintf oc "	.balign 8\n";
        iter_literal64 (print_literal64 oc);
        iter_literal32 (print_literal32 oc);
      end;
      reset_literals ()
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_print_optional_fun_info_001 *)
    (*- #Justify_Derived "Utility function" *)
    let print_optional_fun_info _ = ()
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_get_section_names_001 *)
    (*- #Justify_Derived "Utility function" *)
    let get_section_names name =
      match C2C.atom_sections name with
      | [t;l;j] -> (t, l, j)
      |    _    -> (Section_text, Section_literal, Section_jumptable)
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_print_var_info_001 *)
    (*- #Justify_Derived "Utility function" *)
    let print_var_info = elf_print_var_info
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_print_comm_symb_001 *)
    (*- #Justify_Derived "Utility function" *)
    let print_comm_symb oc sz name align =
      fprintf oc "	%s	%a, %s, %d\n"
        (if C2C.atom_is_static name then ".lcomm" else ".comm")
        symbol name
        (Z.to_string sz)
        align
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_print_align_001 *)
    (*- #Justify_Derived "Utility function" *)
    let print_align oc align  =
      fprintf oc "	.balign	%d\n" align
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_print_jumptable_001 *)
    (*- #Justify_Derived "Utility function" *)
    let print_jumptable oc jmptbl =
      let print_jumptable oc (lbl, tbl) =
        fprintf oc "%a:" label lbl;
        List.iter
          (fun l -> fprintf oc "	.long	%a\n" label (transl_label l))
          tbl in
      if !jumptables <> [] then begin
        section oc jmptbl;
        fprintf oc "	.balign 4\n";
        List.iter (print_jumptable oc) !jumptables;
        jumptables := []
      end
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_default_falignment_001 *)
    (*- #Justify_Derived "Utility constant" *)
    let default_falignment = 4
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_address_002 *)
    (*- #Justify_Derived "Utility function" *)
    let address = address
    (*- #End *)

    (*- E_COMPCERT_CODE_TargetPrinter_section_002 *)
    (*- #Justify_Derived "Utility function" *)
    let section oc sec =
      section oc sec;
      match sec with
      | Section_ais_annotation -> ()
      | _ -> debug_section oc sec
    (*- #End *)
  end

(*- E_COMPCERT_CODE_TargetPrinter_sel_target_001 *)
(*- #Justify_Derived "Utility function" *)
let sel_target () =
  let module S  = (val
    (match Configuration.system with
    | "linux"  -> (module Linux_System:SYSTEM)
    | "diab"   -> (module Diab_System:SYSTEM)
    | _        -> invalid_arg ("System " ^ Configuration.system ^ " not supported")):SYSTEM) in
  (module Target(S):TARGET)
(*- #End *)
