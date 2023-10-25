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

(* Additional extraction directives specific to the Frontend part of
   the ARM port *)

(* Choice of calling conventions *)
Extract Constant Archi.abi =>
  "begin match Configuration.abi with
   | ""eabi"" -> Softfloat
   | ""hardfloat"" -> Hardfloat
   | _ -> assert false
   end".

(* Choice of endianness *)
Extract Constant Archi.big_endian =>
  "Configuration.is_big_endian".

(* Whether the model is ARMv6T2 or above and hence supports Thumb2. *)
Extract Constant Archi.thumb2_support =>
  "(Configuration.model = ""armv6t2"" || Configuration.model >= ""armv7"")".

(* Whether the model has hardware supports sdiv and udiv *)
Extract Constant Archi.hardware_idiv =>
  "fun () -> begin match  Configuration.model with
   | ""armv7r"" | ""armv7m"" -> !Clflags.option_mthumb
   | _ -> false
   end".
