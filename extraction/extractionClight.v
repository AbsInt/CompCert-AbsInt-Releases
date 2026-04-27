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
From compcert Require Ctypes.
From compcert Require Csyntax.
From compcert Require Ctyping.
From compcert Require Clight.
From compcert Require Parser.
From compcert Require Initializers.
From compcert Require Compopts.
From compcert Require SimplExpr.
From compcert Require SimplLocals.
From compcert Require Cexec.

(* Standard lib *)
From Coq Require Import ExtrOcamlBasic ExtrOcamlNativeString.

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

(* Ctypes *)
Extract Inlined Constant Ctypes.struct_alignment_constraint =>
  "if Configuration.arch = {|tricore|} then Some (Camlcoq.Z.one, Camlcoq.Nat.of_int 1) else None".

(* SimplExpr *)
Extract Constant SimplExpr.first_unused_ident => "Camlcoq.first_unused_ident".
Extraction Inline SimplExpr.ret SimplExpr.error SimplExpr.bind SimplExpr.bind2.

(* Compopts *)
Extract Constant Compopts.debug =>
  "fun _ -> !Clflags.option_g".
Extract Constant Compopts.supports_double => "Configuration.has_double".
Extract Constant Compopts.inlined_runtime => "false".

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

Load extractionMachdepClight.

(* Avoid name clashes *)
Extraction Blacklist List String Int.

(* Needed in Coq 8.4 to avoid problems with Function definitions. *)
Set Extraction AccessOpaque.

(* Go! *)

Separate Extraction
   SimplLocals.transf_program
   SimplExpr.transl_program
   Cexec.do_initial_state Cexec.do_step Cexec.at_final_state
   Ctypes.build_composite_env Ctypes.precompute_offsets Ctypes.composite_offset_env Ctypes.empty_composite_offset_env Ctypes.field_zero_or_padding Ctypes.name_member
   Ctypes.layout_struct
   Ctypes.signature_of_type
   Initializers.transl_init Initializers.constval
   Ctyping.typecheck_program
   Ctyping.epostincr Ctyping.epostdecr Ctyping.epreincr Ctyping.epredecr
   Ctyping.eselection
   Clight.type_of_function
   Conventions1.is_caller_save
   Floats.Float32.from_parsed Floats.Float.from_parsed
   Globalenvs.Senv.invert_symbol
   PArith.BinPos.Pos.pred
   Machregs.mreg
   Machregs.register_names
   Machregs.register_by_name
   AST.transform_program
   AST.builtin_res
   AST.builtin_arg
   AST.rpair
   AST.ptype
   Parser.translation_unit_file.
