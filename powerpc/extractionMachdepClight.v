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

(* Additional extraction directives specific to the Frontend part of the
   PowerPC port *)

(* Choice of PPC splitlong *)
Extract Constant Archi.ppc64 =>
  "begin match Configuration.model with
   | ""ppc64"" -> true
   | ""e5500"" -> true
   | _ -> false
   end".

(* Choice of passing of single *)
Extract Constant Archi.single_passed_as_single => "Configuration.gnu_toolchain".
