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


val reset_filenames: unit -> unit

val close_filenames: unit -> unit

val print_file_line: out_channel -> string -> string -> int -> unit

val print_file_line_d2: out_channel -> string -> string -> int -> unit

val print_file: out_channel -> string -> int * Printlines.filebuf option

val find_file: string -> int
