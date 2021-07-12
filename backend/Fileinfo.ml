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

open Printf

(* Printing annotations in asm syntax *)

(*- E_COMPCERT_CODE_Fileinfo_filename_info_001 *)
(*- #Justify_Derived "Variable for global state" *)
let filename_info : (string, int * Printlines.filebuf option) Hashtbl.t
                  = Hashtbl.create 7
(*- #End *)

(*- E_COMPCERT_CODE_Fileinfo_last_file_001 *)
(*- #Justify_Derived "Variable for global state" *)
let last_file = ref ""
(*- #End *)

(*- E_COMPCERT_CODE_Fileinfo_reset_filenames_001 *)
(*- #Justify_Derived "Utility function" *)
let reset_filenames () =
  Hashtbl.clear filename_info; last_file := ""
(*- #End *)

(*- E_COMPCERT_CODE_Fileinfo_close_filenames_001 *)
(*- #Justify_Derived "Utility function" *)
let close_filenames () =
  Hashtbl.iter
    (fun file (num, fb) ->
       match fb with Some b -> Printlines.close b | None -> ())
    filename_info;
  reset_filenames()
(*- #End *)

(*- E_COMPCERT_CODE_Fileinfo_enter_filename_001 *)
(*- #Justify_Derived "Utility function" *)
let enter_filename f =
  let num = Hashtbl.length filename_info + 1 in
  let filebuf =
    if !Clflags.option_S || !Clflags.option_dasm then begin
      try Some (Printlines.openfile f)
      with Sys_error _ -> None
    end else None in
  Hashtbl.add filename_info f (num, filebuf);
  (num, filebuf)
(*- #End *)

(* Add file and line debug location, using GNU assembler-style DWARF2
   directives *)
(*- E_COMPCERT_CODE_Fileinfo_print_file_001 *)
(*- #Justify_Derived "Utility function" *)
let print_file oc file =
  try
    Hashtbl.find filename_info file
  with Not_found ->
    let (filenum, filebuf as res) = enter_filename file in
    fprintf oc "	.file	%d %S\n" filenum file;
    res
(*- #End *)

(*- E_COMPCERT_CODE_Fileinfo_print_file_line_001 *)
(*- #Justify_Derived "Utility function" *)
let print_file_line oc pref file line =
  if !Clflags.option_g && file <> "" then begin
    let (filenum, filebuf) = print_file oc file in
    fprintf oc "	.loc	%d %d\n" filenum line;
    match filebuf with
    | None -> ()
    | Some fb -> Printlines.copy oc pref fb line line
  end
(*- #End *)

(* Add file and line debug location, using DWARF2 directives in the style
   of Diab C 5 *)

(*- E_COMPCERT_CODE_Fileinfo_print_file_line_d2_001 *)
(*- #Justify_Derived "Utility function" *)
let print_file_line_d2 oc pref file line =
  if !Clflags.option_g && file <> "" then begin
    let (_, filebuf) =
      try
        Hashtbl.find filename_info file
      with Not_found ->
        enter_filename file in
    if file <> !last_file then begin
      fprintf oc "	.d2file	%S\n" file;
      last_file := file
    end;
    fprintf oc "	.d2line	%d\n" line;
    match filebuf with
    | None -> ()
    | Some fb -> Printlines.copy oc pref fb line line
  end
(*- #End *)
