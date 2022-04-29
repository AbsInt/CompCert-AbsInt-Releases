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

Require Coqlib.
Require Wfsimpl.
Require DecidableClass Decidableplus.
Require AST.
Require Iteration.
Require Floats.
Require Ctypes.
Require Csyntax.
Require Ctyping.
Require Clight.
Require Parser.
Require Initializers.
Require Compopts.
Require SimplExpr.
Require SimplLocals.
Require Cexec.

(* Standard lib *)
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

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
Extract Inlined Constant Ctypes.supports_double => "(fun () -> Machine.((!config).supports_double))".

(* SimplExpr *)
Extract Constant SimplExpr.first_unused_ident => "Camlcoq.first_unused_ident".
Extraction Inline SimplExpr.ret SimplExpr.error SimplExpr.bind SimplExpr.bind2.

(* Compopts *)
Extract Constant Compopts.debug =>
  "fun _ -> !Clflags.option_g".

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

(* Cutting the dependency to R. *)
Extract Inlined Constant Defs.F2R => "fun _ -> assert false".
Extract Inlined Constant Binary.FF2R => "fun _ -> assert false".
Extract Inlined Constant Binary.B2R => "fun _ -> assert false".
Extract Inlined Constant Binary.round_mode => "fun _ -> assert false".
Extract Inlined Constant Bracket.inbetween_loc => "fun _ -> assert false".

(* Needed in Coq 8.4 to avoid problems with Function definitions. *)
Set Extraction AccessOpaque.

(* Go! *)

Cd "extraction".

Separate Extraction
   SimplLocals.transf_program
   SimplExpr.transl_program
   Cexec.do_initial_state Cexec.do_step Cexec.at_final_state
   Ctypes.build_composite_env
   Ctypes.typlist_of_typelist
   Ctypes.signature_of_type
   Initializers.transl_init Initializers.constval
   Ctyping.typecheck_program
   Ctyping.epostincr Ctyping.epostdecr Ctyping.epreincr Ctyping.epredecr
   Ctyping.eselection
   Clight.type_of_function
   Conventions1.is_callee_save
   Floats.Float32.from_parsed Floats.Float.from_parsed
   Globalenvs.Senv.invert_symbol
   PArith.BinPos.Pos.pred
   Machregs.mreg
   Machregs.register_names
   Machregs.register_by_name
   AST.transform_program
   AST.builtin_res
   AST.builtin_arg
   Parser.translation_unit_file.
