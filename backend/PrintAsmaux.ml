(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open AST
open Asm
open Camlcoq
open Memdata
open Printf
open Sections

(** Auxiliary functions for printing of asm *)

(*- E_COMPCERT_CODE_PrintAsmaux_module_target_001 *)
(*- #Justify_Derived "Type definitions" *)
module type TARGET =
    sig
      val print_prologue: out_channel -> unit
      val print_epilogue: out_channel -> unit
      val print_align: out_channel -> int -> unit
      val print_comm_symb:  out_channel -> Z.t -> P.t -> int -> unit
      val print_var_info: out_channel -> P.t -> unit
      val print_fun_info: out_channel -> P.t -> unit
      val print_file_line: out_channel -> string -> int -> unit
      val print_optional_fun_info: out_channel -> unit
      val cfi_startproc: out_channel -> unit
      val print_instructions: out_channel -> coq_function -> unit
      val cfi_endproc: out_channel -> unit
      val print_jumptable: out_channel -> section_name -> unit
      val section: out_channel -> section_name -> unit
      val name_of_section: section_name -> string
      val comment: string
      val symbol: out_channel -> P.t -> unit
      val default_falignment: int
      val label: out_channel -> int -> unit
      val address: string
      val is_comm_section : section_name -> bool
    end
(*- #End *)

(* On-the-fly label renaming *)

(*- E_COMPCERT_CODE_PrintAsmaux_next_label_001 *)
(*- #Justify_Derived "Variable for global state" *)
let next_label = ref 100
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_new_label_001 *)
(*- #Justify_Derived "Utility function" *)
let new_label () =
  let lbl = !next_label in incr next_label; lbl
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_current_function_labels_001 *)
(*- #Justify_Derived "Variable for global state" *)
let current_function_labels = (Hashtbl.create 39 : (label, int) Hashtbl.t)
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_transl_label_001 *)
(*- #Justify_Derived "Utility function" *)
let transl_label lbl =
  try
    Hashtbl.find current_function_labels lbl
  with Not_found ->
    let lbl' = new_label() in
    Hashtbl.add current_function_labels lbl lbl';
    lbl'
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_elf_label_001 *)
(*- #Justify_Derived "Utility function" *)
let elf_label oc lbl =
  fprintf oc ".L%d" lbl
(*- #End *)

(* List of literals and jumptables used in the code *)

(*- E_COMPCERT_CODE_PrintAsmaux_jumptables_001 *)
(*- #Justify_Derived "Variable for global state" *)
let jumptables : (int * label list) list ref = ref []
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_label_constant_001 *)
(*- #Justify_Derived "Utility function" *)
let label_constant (h: ('a, int) Hashtbl.t) (cst: 'a) =
  try
    Hashtbl.find h cst
  with Not_found ->
    let lbl = new_label() in
    Hashtbl.add h cst lbl;
    lbl
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_literal32_labels_001 *)
(*- #Justify_Derived "Variable for global state" *)
let literal32_labels = (Hashtbl.create 39 : (int32, int) Hashtbl.t)
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_literal64_labels_001 *)
(*- #Justify_Derived "Variable for global state" *)
let literal64_labels   = (Hashtbl.create 39 : (int64, int) Hashtbl.t)
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_label_literal32_001 *)
(*- #Justify_Derived "Utility function" *)
let label_literal32 bf = label_constant literal32_labels bf
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_label_literal64_001 *)
(*- #Justify_Derived "Utility function" *)
let label_literal64 n = label_constant literal64_labels n
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_iter_literal32_001 *)
(*- #Justify_Derived "Utility function" *)
let iter_literal32 f =
  List.iter (fun (n, lbl) -> f n lbl)
    (List.fast_sort (fun (n1, lbl1) (n2, lbl2) -> compare lbl1 lbl2)
       (Hashtbl.fold (fun n lbl accu -> (n, lbl) :: accu) literal32_labels []))
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_iter_literal64_001 *)
(*- #Justify_Derived "Utility function" *)
let iter_literal64 f =
  List.iter (fun (n, lbl) -> f n lbl)
    (List.fast_sort (fun (n1, lbl1) (n2, lbl2) -> compare lbl1 lbl2)
       (Hashtbl.fold (fun n lbl accu -> (n, lbl) :: accu) literal64_labels []))
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_reset_literals_001 *)
(*- #Justify_Derived "Utility function" *)
let reset_literals () =
  Hashtbl.clear literal32_labels;
  Hashtbl.clear literal64_labels
(*- #End *)

(* Variables used for the handling of varargs *)

(*- E_COMPCERT_CODE_PrintAsmaux_current_function_stacksize_001 *)
(*- #Justify_Derived "Variable for global state" *)
let current_function_stacksize = ref 0l
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_current_function_sig_001 *)
(*- #Justify_Derived "Variable for global state" *)
let current_function_sig =
  ref { sig_args = []; sig_res = Tvoid; sig_cc = cc_default }
(*- #End *)

(* Functions for printing of symbol names *)
(*- E_COMPCERT_CODE_PrintAsmaux_elf_symbol_001 *)
(*- #Justify_Derived "Utility function" *)
let elf_symbol oc symb =
  fprintf oc "%s" (extern_atom symb)
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_elf_symbol_offset_001 *)
(*- #Justify_Derived "Utility function" *)
let elf_symbol_offset oc (symb, ofs) =
  elf_symbol oc symb;
  let ofs = camlint64_of_ptrofs ofs in
  if ofs <> 0L then fprintf oc " + %Ld" ofs
(*- #End *)

(* Functions for fun and var info *)
(*- E_COMPCERT_CODE_PrintAsmaux_elf_print_fun_info_001 *)
(*- #Justify_Derived "Utility function" *)
let elf_print_fun_info oc name =
  fprintf oc "	.type	%a, @function\n" elf_symbol name;
  fprintf oc "	.size	%a, . - %a\n" elf_symbol name elf_symbol name
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_elf_print_var_info_001 *)
(*- #Justify_Derived "Utility function" *)
let elf_print_var_info oc name =
  fprintf oc "	.type	%a, @object\n" elf_symbol name;
  fprintf oc "	.size	%a, . - %a\n" elf_symbol name elf_symbol name
(*- #End *)

(* Emit .cfi directives *)
(*- E_COMPCERT_CODE_PrintAsmaux_cfi_startproc_001 *)
(*- #Justify_Derived "Utility function" *)
let cfi_startproc =
  if Configuration.asm_supports_cfi then
    (fun oc -> fprintf oc "	.cfi_startproc\n")
  else
    (fun _ -> ())
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_cfi_endproc_001 *)
(*- #Justify_Derived "Utility function" *)
let cfi_endproc =
  if Configuration.asm_supports_cfi then
    (fun oc -> fprintf oc "	.cfi_endproc\n")
  else
    (fun _ -> ())
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_cfi_adjust_001 *)
(*- #Justify_Derived "Utility function" *)
let cfi_adjust =
  if Configuration.asm_supports_cfi then
       (fun oc delta -> fprintf oc "	.cfi_adjust_cfa_offset	%ld\n" delta)
  else
    (fun _ _ -> ())
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_cfi_rel_offset_001 *)
(*- #Justify_Derived "Utility function" *)
let cfi_rel_offset =
  if Configuration.asm_supports_cfi then
    (fun oc reg ofs -> fprintf oc "	.cfi_rel_offset	%s, %ld\n" reg ofs)
  else
    (fun _ _ _ -> ())
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_cfi_section_001 *)
(*- #Justify_Derived "Utility function" *)
let cfi_section =
  if Configuration.asm_supports_cfi then
    (fun oc -> fprintf oc "	.cfi_sections	.debug_frame\n")
  else
    (fun _ -> ())
(*- #End *)

(* Basic printing functions *)
(*- E_COMPCERT_CODE_PrintAsmaux_print_coq_numbers_001 *)
(*- #Justify_Derived "Utility constant" *)
let coqint oc n =
  fprintf oc "%ld" (camlint_of_coqint n)
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_print_coq_numbers_002 *)
(*- #Justify_Derived "Utility constant" *)
let coqint64 oc n =
  fprintf oc "%Ld" (camlint64_of_coqint n)
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_print_coq_numbers_003 *)
(*- #Justify_Derived "Utility constant" *)
let ptrofs oc n =
  fprintf oc "%Ld" (camlint64_of_ptrofs n)
(*- #End *)

(** Programmer-supplied annotations (__builtin_annot). *)

(*- E_COMPCERT_CODE_PrintAsmaux_re_annot_param_001 *)
(*- #Justify_Derived "Utility constant" *)
let re_annot_param = Str.regexp "%%\\|%[1-9][0-9]*"
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_annot_arg_001 *)
(*- #Justify_Derived "Utility function" *)
let rec annot_arg preg_string sp_reg_name = function
  | BA x -> preg_string x
  | BA_int n -> sprintf "%ld" (camlint_of_coqint n)
  | BA_long n -> sprintf "%Ld" (camlint64_of_coqint n)
  | BA_float n -> sprintf "%.18g" (camlfloat_of_coqfloat n)
  | BA_single n -> sprintf "%.18g" (camlfloat_of_coqfloat32 n)
  | BA_loadstack(chunk, ofs) ->
      sprintf "mem(%s + %ld, %ld)"
         sp_reg_name
         (camlint_of_coqint ofs)
         (camlint_of_coqint (size_chunk chunk))
  | BA_addrstack ofs ->
      sprintf "(%s + %ld)"
         sp_reg_name
         (camlint_of_coqint ofs)
  | BA_loadglobal(chunk, id, ofs) ->
      sprintf "mem(\"%s\" + %ld, %ld)"
         (extern_atom id)
         (camlint_of_coqint ofs)
         (camlint_of_coqint (size_chunk chunk))
  | BA_addrglobal(id, ofs) ->
      sprintf "(\"%s\" + %ld)"
         (extern_atom id)
         (camlint_of_coqint ofs)
  | BA_splitlong(hi, lo) ->
      sprintf "(%s * 0x100000000 + %s)"
        (annot_arg preg_string sp_reg_name hi)
         (annot_arg preg_string sp_reg_name lo)
  | BA_addptr(a1, a2) ->
      sprintf "(%s + %s)"
        (annot_arg preg_string sp_reg_name a1)
        (annot_arg preg_string sp_reg_name a2)
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_annot_text_001 *)
(*- #Justify_Derived "Utility function" *)
let annot_text preg_string sp_reg_name txt args =
  let fragment = function
  | Str.Text s ->
      s
  | Str.Delim "%%" ->
      "%"
  | Str.Delim s ->
      let n = int_of_string (String.sub s 1 (String.length s - 1)) in
      try
        annot_arg preg_string sp_reg_name (List.nth args (n-1))
      with Failure _ ->
        sprintf "<bad parameter %s>" s in
  String.concat "" (List.map fragment (Str.full_split re_annot_param txt))
(*- #End *)

(* Printing of [EF_debug] info.  To be completed. *)

(*- E_COMPCERT_CODE_PrintAsmaux_re_file_line_001 *)
(*- #Justify_Derived "Utility constant" *)
let re_file_line = Str.regexp "#line:\\(.*\\):\\([1-9][0-9]*\\)$"
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_print_debug_info_001 *)
(*- #Justify_Derived "Utility function" *)
let print_debug_info comment print_line preg_string sp_name oc kind txt args =
  let print_debug_args oc args =
    List.iter
      (fun a -> fprintf oc " %s" (annot_arg preg_string sp_name a))
      args in
  match kind with
  | 1 ->  (* line number *)
      if Str.string_match re_file_line txt 0 then
        print_line oc (Str.matched_group 1 txt)
                      (int_of_string (Str.matched_group 2 txt))
  | 2 ->  (* assignment to local variable, not useful *)
      ()
  | 3 ->  (* beginning of live range for local variable *)
      fprintf oc "%s debug: start live range %s =%a\n"
                 comment txt print_debug_args args
  | 4 ->  (* end of live range for local variable *)
      fprintf oc "%s debug: end live range %s\n"
                 comment txt
  | 5 ->  (* local variable preallocated in stack *)
      fprintf oc "%s debug: %s resides at%a\n"
                 comment txt print_debug_args args
  | 6 ->  (* scope annotations *)
      fprintf oc "%s debug: current scopes%a\n"
                 comment print_debug_args args;
  | _ ->
      ()
(*- #End *)

(** Inline assembly *)

(*- E_COMPCERT_CODE_PrintAsmaux_print_asm_argument_001 *)
(*- #Justify_Derived "Utility function" *)
let print_asm_argument print_preg oc modifier typ = function 
  | BA r -> print_preg oc typ r
  | BA_splitlong(BA hi, BA lo) ->
      begin match modifier with
      | "R" -> print_preg oc Tint hi
      | "Q" -> print_preg oc Tint lo
      |  _  -> print_preg oc Tint hi; fprintf oc ":"; print_preg oc Tint lo
               (* This case (printing a split long in full) should never
                  happen because of the checks done in ExtendedAsm.ml *)
      end
  | _ -> failwith "bad asm argument"
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_builtin_arg_of_res_001 *)
(*- #Justify_Derived "Utility function" *)
let builtin_arg_of_res = function
  | BR r -> BA r
  | BR_splitlong(BR hi, BR lo) -> BA_splitlong(BA hi, BA lo)
  | _ -> assert false
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_re_asm_param_1_001 *)
(*- #Justify_Derived "Utility constant" *)
let re_asm_param_1 = Str.regexp "%%\\|%[QR]?[0-9]+"
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_re_asm_param_2_001 *)
(*- #Justify_Derived "Utility constant" *)
let re_asm_param_2 = Str.regexp "%\\([QR]?\\)\\([0-9]+\\)"
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_print_inline_asm_001 *)
(*- #Justify_Derived "Utility function" *)
let print_inline_asm print_preg oc txt sg args res =
  let (operands, ty_operands) =
    match sg.sig_res with
    | Tvoid -> (args, sg.sig_args)
    | tres -> (builtin_arg_of_res res :: args, proj_rettype tres :: sg.sig_args) in
  let print_fragment = function
  | Str.Text s ->
      output_string oc s
  | Str.Delim "%%" ->
      output_char oc '%'
  | Str.Delim s ->
      assert (Str.string_match re_asm_param_2 s 0);
      let modifier = Str.matched_group 1 s
      and number = int_of_string (Str.matched_group 2 s) in
      try
        print_asm_argument print_preg oc modifier
                           (List.nth ty_operands number)
                           (List.nth operands number)
      with Failure _ ->
        fprintf oc "<bad parameter %s>" s in
  List.iter print_fragment (Str.full_split re_asm_param_1 txt);
  fprintf oc "\n"
(*- #End *)

(** Print CompCert version and command-line as asm comment *)

(*- E_COMPCERT_CODE_PrintAsmaux_print_version_and_options_001 *)
(*- #Link_to E_COMPCERT_TR_Function_PRINT_ASM_A_002 *)
let print_version_and_options oc comment =
  let version_string =
    if Version.buildnr <> "" && Version.tag <> "" && Version.branch <> "" then
      sprintf "Release: %s, Build: %s, Tag: %s, Branch: %s" Version.version Version.buildnr Version.tag Version.branch
    else
      Version.version in
  fprintf oc "%s File generated by CompCert %s\n" comment version_string;
  fprintf oc "%s Command line:" comment;
  for i = 1 to Array.length Commandline.argv - 1 do
    fprintf oc " %s" Commandline.argv.(i)
  done;
  fprintf oc "\n"
(*- #End *)

(** Determine the name of the section to use for a variable.
  - [i] is the initialization status of the variable.
  - [sec] is the name of the section to use if initialized (with no
    relocations) or if no other cases apply.
  - [reloc] is the name of the section to use if initialized and
    containing relocations.  If not provided, [sec] is used.
  - [bss] is the name of the section to use if uninitialized and
    common declarations are not used.  If not provided, [sec] is used.
*)

(*- E_COMPCERT_CODE_PrintAsmaux_variable_section_001 *)
(*- #Justify_Derived "Utility function" *)
let variable_section ~sec ?bss ?reloc i =
  match i with
  | Uninit ->
      begin match bss with Some s -> s | None -> sec end
  | Init -> sec
  | Init_reloc ->
      begin match reloc with Some s -> s | None -> sec end
(*- #End *)

 (** Default function for checking whether variables placed in these
     sections should be printed as common symbol instead. *)

(*- E_COMPCERT_CODE_PrintAsmaux_default_is_comm_section_001 *)
(*- #Justify_Derived "Utility function" *)
let default_is_comm_section = function
  | Section_data i  | Section_small_data i
  | Section_const i | Section_small_const i -> !Clflags.option_fcommon && (i = Uninit)
  | _ -> false
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_producer_string_001 *)
(*- #Justify_Derived "Utility constant" *)
let producer_string =
  let version_string =
    if Version.buildnr <> "" && Version.tag <> "" && Version.branch <> "" then
        Printf.sprintf "Release: %s, Build: %s, Tag: %s, Branch: %s" Version.version Version.buildnr Version.tag Version.branch
      else
        Version.version in
  Printf.sprintf "AbsInt Angewandte Informatik GmbH: CompCert Version %s:(%s,%s,%s,%s)"
    version_string Configuration.arch Configuration.system Configuration.abi Configuration.model
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_print_compiler_ident_001 *)
(*- #Justify_Derived "Utility function" *)
let print_compiler_ident oc =
  if Configuration.system <> "macos" then
    Printf.fprintf oc "	.ident	\"%s\"\n" producer_string
(*- #End *)

(** ELF and macOS mergeable section names for literals and strings. *)

(*- E_COMPCERT_CODE_PrintAsmaux_elf_mergeable_literal_section_001 *)
(*- #Justify_Derived "Utility function" *)
let elf_mergeable_literal_section sz sec =
  match sz with
  | 0 -> sec
  | 4 | 8 | 16 -> sprintf "%s.cst%d,\"aM\",@progbits,%d" sec sz sz
  | _ -> assert false
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_elf_mergeable_string_section_001 *)
(*- #Justify_Derived "Utility function" *)
let elf_mergeable_string_section sz sec =
  match sz with
  | 0 -> sec
  | 1 | 2 | 4 -> sprintf "%s.str%d.%d,\"aMS\",@progbits,%d" sec sz sz sz
  | _ -> assert false
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_macos_mergeable_literal_section_001 *)
(*- #Justify_Derived "Utility function" *)
let macos_mergeable_literal_section sz =
  match sz with
  | 0 -> ".const"
  | 4 | 8 | 16 -> sprintf ".literal%d" sz
  | _ -> assert false
(*- #End *)

(*- E_COMPCERT_CODE_PrintAsmaux_macos_mergeable_string_section_001 *)
(*- #Justify_Derived "Utility function" *)
let macos_mergeable_string_section sz =
  match sz with
  | 0 | 2 | 4 -> ".const"
  | 1 -> ".cstring"
  | _ -> assert false
(*- #End *)
