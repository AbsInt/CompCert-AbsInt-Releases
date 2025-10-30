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

From compcert Require Coqlib.
From compcert Require Wfsimpl.
From Coq Require DecidableClass.
From compcert Require Decidableplus.
From compcert Require AST.
From compcert Require Iteration.
From compcert Require Floats.
From compcert Require SelectLong.
From compcert Require Selection.
From compcert Require RTLgen.
From compcert Require Inlining.
From compcert Require ValueDomain.
From compcert Require Tailcall.
From compcert Require Allocation.
From compcert Require Bounds.
From compcert Require Ctypes.
From compcert Require Csyntax.
From compcert Require Ctyping.
From compcert Require Clight.
From compcert Require Compiler.
From compcert Require Parser.
From compcert Require Initializers.

(* Standard lib *)
From Coq Require Import ExtrOcamlBasic ExtrOcamlString.

(* Coqlib *)
Extract Inlined Constant Coqlib.proj_sumbool => "(fun x -> x)".

(* Datatypes *)
Extract Inlined Constant Datatypes.fst => "fst".
Extract Inlined Constant Datatypes.snd => "snd".

(* Decidable *)

Extraction Inline DecidableClass.Decidable_witness DecidableClass.decide
   Decidableplus.Decidable_and Decidableplus.Decidable_or
   Decidableplus.Decidable_not Decidableplus.Decidable_implies.

(* Wfsimpl *)
Extraction Inline Wfsimpl.Fix Wfsimpl.Fixm.

(* Memory - work around an extraction bug. *)
Extraction NoInline Memory.Mem.valid_pointer.

(* Errors *)
Extraction Inline Errors.bind Errors.bind2.

(* Iteration *)

Extract Constant Iteration.GenIter.iterate =>
  "let rec iter f a =
     match f a with Coq_inl b -> Some b | Coq_inr a' -> iter f a'
   in iter".

(* Selection *)

Extract Constant Selection.compile_switch => "Switchaux.compile_switch".
Extract Constant Selection.if_conversion_heuristic => "Selectionaux.if_conversion_heuristic".

(* RTLgen *)
Extract Constant RTLgen.more_likely => "RTLgenaux.more_likely".
Extraction Inline RTLgen.ret RTLgen.error RTLgen.bind RTLgen.bind2.

(* Inlining *)
Extract Inlined Constant Inlining.should_inline => "Inliningaux.should_inline".
Extract Inlined Constant Inlining.inlining_info => "Inliningaux.inlining_info".
Extract Inlined Constant Inlining.inlining_analysis => "Inliningaux.inlining_analysis".
Extraction Inline Inlining.ret Inlining.bind.

(* Base Extraction *)
Extract Constant BaseExtraction.is_small_data_symbol => "C2C.atom_is_small_data".

(* Allocation *)
Extract Constant Allocation.regalloc => "Regalloc.regalloc".

(* Linearize *)
Extract Constant Linearize.enumerate_aux => "Linearizeaux.enumerate_aux".

(* Ctypes *)
Extract Inlined Constant Ctypes.struct_alignment_constraint =>
  "if Configuration.arch = {|tricore|} then Some (Camlcoq.Z.one, Camlcoq.Nat.of_int 1) else None".

(* SimplExpr *)
Extract Constant SimplExpr.first_unused_ident => "Camlcoq.first_unused_ident".
Extraction Inline SimplExpr.ret SimplExpr.error SimplExpr.bind SimplExpr.bind2.

(* Compopts *)
Extract Constant Compopts.optim_for_size =>
  "fun _ -> !Clflags.option_Osize".
Extract Constant Compopts.va_strict =>
  "fun _ -> false".
Extract Constant Compopts.propagate_float_constants =>
  "fun _ -> !Clflags.option_ffloatconstprop >= 1".
Extract Constant Compopts.generate_float_constants =>
  "fun _ -> !Clflags.option_ffloatconstprop >= 2".
Extract Constant Compopts.optim_tailcalls =>
  "fun _ -> !Clflags.option_ftailcalls".
Extract Constant Compopts.optim_constprop =>
  "fun _ -> !Clflags.option_fconstprop".
Extract Constant Compopts.optim_extractaddr =>
  "fun _ -> !Clflags.option_fextractaddr".
Extract Constant Compopts.optim_CSE =>
  "fun _ -> !Clflags.option_fcse".
Extract Constant Compopts.optim_redundancy =>
  "fun _ -> !Clflags.option_fredundancy".
Extract Constant Compopts.thumb =>
  "fun _ -> !Clflags.option_mthumb".
Extract Constant Compopts.debug =>
  "fun _ -> !Clflags.option_g".
Extract Constant Compopts.supports_double => "Configuration.has_double".
Extract Constant Compopts.inlined_runtime => "fun _ -> !Clflags.option_inline_runtime".

(* Compiler *)
Extract Constant Compiler.print_Clight => "PrintClight.print_if".
Extract Constant Compiler.print_Cminor => "PrintCminor.print_if".
Extract Constant Compiler.print_RTL => "PrintRTL.print_if".
Extract Constant Compiler.print_typedRTL => "PrintTypedRTL.print_if".
Extract Constant Compiler.print_LTL => "PrintLTL.print_if".
Extract Constant Compiler.print_Mach => "PrintMach.print_if".
Extract Constant Compiler.print => "fun (f: 'a -> unit) (x: 'a) -> f x; x".
Extract Constant Compiler.time  => "Timing.time_coq".

(*Extraction Inline Compiler.apply_total Compiler.apply_partial.*)

(* Cabs *)
Extract Constant Cabs.loc =>
"{ lineno : int;
   filename: string;
   byteno: int;
   ident : int;
 }".
Extract Inlined Constant Cabs.string => "String.t".
Extract Constant Cabs.char_code => "int64".

(* Processor-specific extraction directives *)

Load extractionMachdep.

(* Avoid name clashes *)
Extraction Blacklist List String Int.

(* Needed in Coq 8.4 to avoid problems with Function definitions. *)
Set Extraction AccessOpaque.

(* Go! *)

(* Cd "extraction". *)

Separate Extraction
   Compiler.transf_c_program
   Cexec.do_initial_state Cexec.do_step Cexec.at_final_state
   Ctypes.build_composite_env
   Ctypes.layout_struct
   Initializers.transl_init Initializers.constval
   Ctyping.typecheck_program
   Ctyping.epostincr Ctyping.epostdecr Ctyping.epreincr Ctyping.epredecr
   Ctyping.eselection
   Clight.type_of_function
   Conventions1
   RTL.instr_defs RTL.instr_uses
   Locations.ploc Locations.inj_loc_ploc Locations.proj_ploc_loc Locations.PLoc
   Machregs.mregs_for_operation Machregs.mregs_for_builtin
   Machregs.two_address_op Machregs.is_stack_reg
   Machregs.destroyed_at_indirect_call
   Machregs.all_mregs
   AST.signature_main
   Floats.Float32.from_parsed Floats.Float.from_parsed
   Integers.Ptrofs.divu Integers.Ptrofs.modu  Integers.Ptrofs.cmp
   Globalenvs.Senv.invert_symbol
   Parser.translation_unit_file.
