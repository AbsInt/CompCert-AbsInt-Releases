(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*        Bernhard Schommer, AbsInt Angewandte Informatik GmbH         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)


{
(* To accumulate the characters in a word or quoted string *)
(*- E_COMPCERT_CODE_Responsefile_buf_001 *)
(*- #Justify_Derived "Variable for local state" *)
let buf = Buffer.create 32
(*- #End *)

(* Add the current contents of buf to the list of words seen so far,
   taking care not to add empty strings unless warranted (e.g. quoted) *)
(*- E_COMPCERT_CODE_Responsefile_stash_001 *)
(*- #Justify_Derived "Utility function" *)
let stash inword words =
  if inword then begin
    let w = Buffer.contents buf in
    Buffer.clear buf;
    w :: words
  end else
    words
(*- #End *)

}

(*- E_COMPCERT_CODE_Responsefile_whitespace_001 *)
(*- #Justify_Derived "Utility constant" *)
let whitespace = [' ' '\t' '\012' '\r' '\n']
(*- #End *)

(*- E_COMPCERT_CODE_Responsefile_backslashes_even_001 *)
(*- #Justify_Derived "Utility constant" *)
let backslashes_even = "\\\\"*        (* an even number of backslashes *)
(*- #End *)

(*- E_COMPCERT_CODE_Responsefile_backslashes_odd_001 *)
(*- #Justify_Derived "Utility constant" *)
let backslashes_odd  = "\\\\"* '\\'   (* an odd number of backslashes *)
(*- #End *)

(* GNU-style quoting *)
(* "Options in file are separated by whitespace.  A whitespace
    character may be included in an option by surrounding the entire
    option in either single or double quotes.  Any character (including
    a backslash) may be included by prefixing the character to be
    included with a backslash.  The file may itself contain additional
    @file options; any such options will be processed recursively." *)

(*- E_COMPCERT_CODE_Responsefile_gnu_unquoted_001 *)
(*- #Justify_Derived "Utility function" *)
rule gnu_unquoted inword words = parse
  | eof           { List.rev (stash inword words) }
  | whitespace+   { gnu_unquoted false (stash inword words) lexbuf }
  | '\''          { gnu_single_quote lexbuf; gnu_unquoted true words lexbuf }
  | '\"'          { gnu_double_quote lexbuf; gnu_unquoted true words lexbuf }
  | ""            { gnu_one_char lexbuf; gnu_unquoted true words lexbuf }
(*- #End *)

(*- E_COMPCERT_CODE_Responsefile_gnu_one_char_001 *)
(*- #Justify_Derived "Utility function" *)
and gnu_one_char = parse
  | '\\' (_ as c) { Buffer.add_char buf c }
  | _ as c        { Buffer.add_char buf c }
(*- #End *)

(*- E_COMPCERT_CODE_Responsefile_gnu_single_quote_001 *)
(*- #Justify_Derived "Utility function" *)
and gnu_single_quote = parse
  | eof           { () (* tolerance *) }
  | '\''          { () }
  | ""            { gnu_one_char lexbuf; gnu_single_quote lexbuf }
(*- #End *)

(*- E_COMPCERT_CODE_Responsefile_gnu_double_quote_001 *)
(*- #Justify_Derived "Utility function" *)
and gnu_double_quote = parse
  | eof           { () (* tolerance *) }
  | '\"'          { () }
  | ""            { gnu_one_char lexbuf; gnu_double_quote lexbuf }
(*- #End *)

{

(*- E_COMPCERT_CODE_Responsefile_re_responsefile_001 *)
(*- #Justify_Derived "Utility constant" *)
let re_responsefile = Str.regexp "@\\(.*\\)$"
(*- #End *)

exception Error of string

(*- E_COMPCERT_CODE_Responsefile_expandargv_001 *)
(*- #Justify_Derived "Utility function" *)
let expandargv argv =
  let rec expand_arg seen arg k =
    if not (Str.string_match re_responsefile arg 0) then
      arg :: k
    else begin
      let filename = Str.matched_group 1 arg in
      if List.mem filename seen then
        (*- #Link_to E_COMPCERT_TR_Robustness_DRIVER_005 *)
        raise (Error ("cycle in response files: " ^ filename));
      let ic = open_in filename in
      let words = gnu_unquoted false [] (Lexing.from_channel ic) in
      close_in ic;
      expand_args (filename :: seen) words k
    end
  and expand_args seen args k =
    match args with
    | [] -> k
    | a1 :: al -> expand_args seen al (expand_arg seen a1 k)
  in
  let args = Array.to_list argv in
   Array.of_list (List.rev (expand_args [] args []))
(*- #End *)

(* This function reimplements quoting of writeargv from libiberty *)
(*- E_COMPCERT_CODE_Responsefile_gnu_quote_001 *)
(*- #Justify_Derived "Utility function" *)
let gnu_quote arg =
  let len = String.length arg in
  let buf = Buffer.create len in
  String.iter (fun c -> begin match c with
    | ' ' | '\t' | '\r' | '\n' | '\\' | '\'' | '"' ->
        Buffer.add_char buf '\\'
    | _ -> () end;
    Buffer.add_char buf c) arg;
  Buffer.contents buf
(*- #End *)

(*- E_COMPCERT_CODE_Responsefile_re_quote_001 *)
(*- #Justify_Derived "Utility constant" *)
let re_quote = Str.regexp ".*[ \t\n\r\"]"
(*- #End *)

(*- E_COMPCERT_CODE_Responsefile_diab_quote_001 *)
(*- #Justify_Derived "Utility function" *)
let diab_quote arg =
  let buf = Buffer.create ((String.length arg) + 8) in
  let doublequote = Str.string_match re_quote arg 0 in
  if doublequote then begin
    Buffer.add_char buf '"';
    String.iter (fun c ->
      if c = '"' then Buffer.add_char buf '\\';
      Buffer.add_char buf c) arg;
    if doublequote then Buffer.add_char buf '"';
    Buffer.contents buf
  end else
    arg
}
(*- #End *)
