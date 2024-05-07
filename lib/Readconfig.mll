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

{

(* Recording key=val bindings *)

(*- E_COMPCERT_CODE_Readconfig_key_val_tbl_001 *)
(*- #Justify_Derived "Variable for local state" *)
let key_val_tbl : (string, string list) Hashtbl.t = Hashtbl.create 17
(*- #End *)

(*- E_COMPCERT_CODE_Readconfig_key_val_001 *)
(*- #Justify_Derived "Utility function" *)
let key_val key =
  Hashtbl.find_opt key_val_tbl key
(*- #End *)

(* Auxiliaries for parsing *)

(*- E_COMPCERT_CODE_Readconfig_buf_001 *)
(*- #Justify_Derived "Variable for local state" *)
let buf = Buffer.create 32
(*- #End *)

(*- E_COMPCERT_CODE_Readconfig_stash_001 *)
(*- #Justify_Derived "Utility function" *)
let stash inword words =
  if inword then begin
    let w = Buffer.contents buf in
    Buffer.clear buf;
    w :: words
  end else
    words
(*- #End *)

(* Error reporting *)

exception Error of string * int * string

(*- E_COMPCERT_CODE_Readconfig_error_001 *)
(*- #Justify_Derived "Utility function" *)
let error msg lexbuf =
  Lexing.(raise (Error(lexbuf.lex_curr_p.pos_fname,
                       lexbuf.lex_curr_p.pos_lnum,
                       msg)))

let ill_formed_line lexbuf = error "ill-formed line" lexbuf
let unterminated_quote lexbuf = error "unterminated quote" lexbuf
let lone_backslash lexbuf = error "lone \\ (backslash) at end of file" lexbuf
(*- #End *)

}

(*- E_COMPCERT_CODE_Readconfig_whitespace_001 *)
(*- #Justify_Derived "Utility constant" *)
let whitespace = [' ' '\t' '\012' '\r']
(*- #End *)

(*- E_COMPCERT_CODE_Readconfig_newline_001 *)
(*- #Justify_Derived "Utility constant" *)
let newline = '\r'* '\n'
(*- #End *)

(*- E_COMPCERT_CODE_Readconfig_ident_001 *)
(*- #Justify_Derived "Utility constant" *)
let ident = ['A'-'Z' 'a'-'z' '_'] ['A'-'Z' 'a'-'z' '0'-'9' '_' '.']*
(*- #End *)

(*- E_COMPCERT_CODE_Readconfig_begline_001 *)
(*- #Justify_Derived "Utility constant" *)
rule begline = parse
  | '#' [^ '\n']* ('\n' | eof)
      { Lexing.new_line lexbuf; begline lexbuf }
  | whitespace* (ident as key) whitespace* '='
      { let words = unquoted false [] lexbuf in
        Hashtbl.add key_val_tbl key (List.rev words);
        begline lexbuf }
  | eof
      { () }
  | _
      (*- #Link_to E_COMPCERT_TR_Robustness_DRIVER_006 *)
      { ill_formed_line lexbuf }
(*- #End *)

(*- E_COMPCERT_CODE_Readconfig_unquoted_001 *)
(*- #Justify_Derived "Utility constant" *)
and unquoted inword words = parse
  (*- #Link_to E_COMPCERT_TR_Robustness_DRIVER_008 *)
  | '\n' | eof    { Lexing.new_line lexbuf; stash inword words }
  | whitespace+   { unquoted false (stash inword words) lexbuf }
  | '\\' newline  { Lexing.new_line lexbuf; unquoted inword words lexbuf }
  | '\\' (_ as c) { Buffer.add_char buf c; unquoted true words lexbuf }
  | '\\' eof      { lone_backslash lexbuf }
  | '\''          { singlequote lexbuf; unquoted true words lexbuf }
  | '\"'          { doublequote lexbuf; unquoted true words lexbuf }
  | _ as c        { Buffer.add_char buf c; unquoted true words lexbuf }
(*- #End *)

(*- E_COMPCERT_CODE_Readconfig_singlequote_001 *)
(*- #Justify_Derived "Utility constant" *)
and singlequote = parse
  (*- #Link_to E_COMPCERT_TR_Robustness_DRIVER_007 *)
  | eof           { unterminated_quote lexbuf }
  | '\''          { () }
  | newline       { Lexing.new_line lexbuf;
                    Buffer.add_char buf '\n'; singlequote lexbuf }
  | _ as c        { Buffer.add_char buf c; singlequote lexbuf }
(*- #End *)

(*- E_COMPCERT_CODE_Readconfig_doublequote_001 *)
(*- #Justify_Derived "Utility constant" *)
and doublequote = parse
  (*- #Link_to E_COMPCERT_TR_Robustness_DRIVER_007 *)
  | eof           { unterminated_quote lexbuf }
  | '\"'          { () }
  | '\\' newline  { Lexing.new_line lexbuf; doublequote lexbuf }
  | '\\' (['$' '`' '\"' '\\'] as c)
                  { Buffer.add_char buf c; doublequote lexbuf }
  | newline       { Lexing.new_line lexbuf;
                    Buffer.add_char buf '\n'; doublequote lexbuf }
  | _ as c        { Buffer.add_char buf c; doublequote lexbuf }
(*- #End *)

{

(* The entry point *)

(*- E_COMPCERT_CODE_Readconfig_read_config_file_001 *)
(*- #Justify_Derived "Utility constant" *)
let read_config_file filename =
  let ic = open_in_bin filename in
  let lexbuf = Lexing.from_channel ic in
  Lexing.(lexbuf.lex_start_p <- {lexbuf.lex_start_p with pos_fname = filename});
  try
    Hashtbl.clear key_val_tbl;
    begline lexbuf;
    close_in ic
  with x ->
    close_in ic; raise x
(*- #End *)

(* Test harness *)
(*
open Printf

let _ =
  Hashtbl.clear key_val_tbl;
  begline (Lexing.from_channel stdin);
  Hashtbl.iter
    (fun key value ->
      printf "%s =" key;
      List.iter (fun v -> printf " |%s|" v) value;
      printf "\n")
    key_val_tbl
*)

}
