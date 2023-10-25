(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Jacques-Henri Jourdan, INRIA Paris-Rocquencourt            *)
(*             Xavier Leroy, Collège de France and Inria               *)
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
open Lexing
open Pre_parser
open Pre_parser_aux

module SSet = Set.Make(String)

(*- E_COMPCERT_CODE_Lexer_lexicon_001 *)
(*- #Justify_Derived "Variable for local state" *)
let lexicon : (string, Cabs.loc -> token) Hashtbl.t = Hashtbl.create 17
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_ignored_keywords_001 *)
(*- #Justify_Derived "Variable for local state" *)
let ignored_keywords : SSet.t ref = ref SSet.empty
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_reserved_keywords_001 *)
(*- #Link_to E_COMPCERT_TR_Function_KEYWORDS_001 *)
(*- #Link_to E_COMPCERT_TR_Robustness_LEXER_011 *)
let reserved_keyword loc id =
  Diagnostics.fatal_error (loc.Cabs.filename, loc.Cabs.lineno)
    "illegal use of reserved keyword `%s'" id
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_init_001 *)
(*- #Link_to E_COMPCERT_TR_Function_KEYWORDS_001 *)
let () =
  List.iter (fun (key, builder) -> Hashtbl.add lexicon key builder)
    [ 
      (*- #Link_to E_COMPCERT_TR_Function_LEXER_010 *)
      ("_Alignas", fun loc -> ALIGNAS loc);
      ("_Alignof", fun loc -> ALIGNOF loc);
      ("_Bool", fun loc -> UNDERSCORE_BOOL loc);
      ("_Generic", fun loc -> GENERIC loc);
      ("_Complex", fun loc -> reserved_keyword loc "_Complex");
      ("_Imaginary", fun loc -> reserved_keyword loc "_Imaginary");
      ("_Static_assert", fun loc -> STATIC_ASSERT loc);
      ("__alignof", fun loc -> ALIGNOF loc);
      ("__alignof__", fun loc -> ALIGNOF loc);
      ("__asm", fun loc -> ASM loc);
      ("__asm__", fun loc -> ASM loc);
      ("__attribute", fun loc -> ATTRIBUTE loc);
      ("__attribute__", fun loc -> ATTRIBUTE loc);
      ("__builtin_va_arg", fun loc -> BUILTIN_VA_ARG loc);
      ("__builtin_offsetof", fun loc -> BUILTIN_OFFSETOF loc);
      ("__const", fun loc -> CONST loc);
      ("__const__", fun loc -> CONST loc);
      ("__inline", fun loc -> INLINE loc);
      ("__inline__", fun loc -> INLINE loc);
      ("__packed__", fun loc -> PACKED loc);
      ("__restrict", fun loc -> RESTRICT loc);
      ("__restrict__", fun loc -> RESTRICT loc);
      ("__signed", fun loc -> SIGNED loc);
      ("__signed__", fun loc -> SIGNED loc);
      ("__volatile", fun loc -> VOLATILE loc);
      ("__volatile__", fun loc -> VOLATILE loc);
      ("asm", fun loc -> ASM loc);
      ("auto", fun loc -> AUTO loc);
      ("break", fun loc -> BREAK loc);
      ("case", fun loc -> CASE loc);
      ("char", fun loc -> CHAR loc);
      ("const", fun loc -> CONST loc);
      ("continue", fun loc -> CONTINUE loc);
      ("default", fun loc -> DEFAULT loc);
      ("do", fun loc -> DO loc);
      ("double", fun loc -> DOUBLE loc);
      ("else", fun loc -> ELSE loc);
      ("enum", fun loc -> ENUM loc);
      ("extern", fun loc -> EXTERN loc);
      ("float", fun loc -> FLOAT loc);
      ("for", fun loc -> FOR loc);
      ("goto", fun loc -> GOTO loc);
      ("if", fun loc -> IF loc);
      ("inline", fun loc -> INLINE loc);
      ("_Noreturn", fun loc -> NORETURN loc);
      ("int", fun loc -> INT loc);
      ("long", fun loc -> LONG loc);
      ("register", fun loc -> REGISTER loc);
      ("restrict", fun loc -> RESTRICT loc);
      ("return", fun loc -> RETURN loc);
      ("short", fun loc -> SHORT loc);
      ("signed", fun loc -> SIGNED loc);
      ("sizeof", fun loc -> SIZEOF loc);
      ("static", fun loc -> STATIC loc);
      ("struct", fun loc -> STRUCT loc);
      ("switch", fun loc -> SWITCH loc);
      ("typedef", fun loc -> TYPEDEF loc);
      ("union", fun loc -> UNION loc);
      ("unsigned", fun loc -> UNSIGNED loc);
      ("void", fun loc -> VOID loc);
      ("volatile", fun loc -> VOLATILE loc);
      ("while", fun loc -> WHILE loc)];
  if Configuration.system <> "diab" then
    (* We can ignore the __extension__ GCC keyword. *)
    ignored_keywords := SSet.add "__extension__" !ignored_keywords
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_init_ctx_001 *)
(*- #Justify_Derived "Utility constant" *)
let init_ctx = SSet.of_list (List.map fst CBuiltins.builtins.C.builtin_typedefs)
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_types_context_001 *)
(*- #Justify_Derived "Utility constant" *)
let types_context : SSet.t ref = ref init_ctx
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_init_002 *)
(*- #Justify_Derived "Initializer" *)
let _ =
  (* See comments in pre_parser_aux.ml *)
  save_context := begin fun () ->
    let save = !types_context in
    fun () -> types_context := save
  end;

  declare_varname := begin fun id ->
    types_context := SSet.remove id !types_context
  end;

  declare_typename := begin fun id ->
    types_context := SSet.add id !types_context
  end
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_init_003 *)
(*- #Justify_Derived "Utility function" *)
let init filename channel : Lexing.lexbuf =
  let lb = Lexing.from_channel channel in
  lb.lex_curr_p <- {lb.lex_curr_p with pos_fname = filename; pos_lnum = 1};
  lb
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_currentLoc_001 *)
(*- #Justify_Derived "Utility function" *)
let currentLoc =
  let nextident = ref 0 in
  let getident () =
    nextident := !nextident + 1;
    !nextident
  in
  fun lb ->
    let p = Lexing.lexeme_start_p lb in
    Cabs.({ lineno   = p.Lexing.pos_lnum;
            filename = p.Lexing.pos_fname;
            byteno   = p.Lexing.pos_cnum;
            ident    = getident ();})
(*- #End *)

(* Error reporting *)

(*- E_COMPCERT_CODE_Lexer_fatal_error_001 *)
(*- #Justify_Derived "Utility function" *)
let fatal_error lb fmt =
  Diagnostics.fatal_error
    (lb.lex_curr_p.pos_fname,lb.lex_curr_p.pos_lnum) fmt
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_error_001 *)
(*- #Justify_Derived "Utility function" *)
let error lb fmt =
  Diagnostics.error
    (lb.lex_curr_p.pos_fname,lb.lex_curr_p.pos_lnum) fmt
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_warning_001 *)
(*- #Justify_Derived "Utility function" *)
let warning lb kind fmt =
  Diagnostics.warning
      (lb.lex_curr_p.pos_fname,lb.lex_curr_p.pos_lnum) kind fmt
(*- #End *)

(* Simple character escapes *)

(*- E_COMPCERT_CODE_Lexer_convert_escape_001 *)
(*- #Justify_Derived "Utility function" *)
let convert_escape = function
  | 'a' -> 7L  (* bell *)
  | 'b' -> 8L  (* backspace  *)
  | 'e' -> 27L (* escape (GCC extension) *)
  | 'f' -> 12L (* form feed *)
  | 'n' -> 10L (* new line *)
  | 'r' -> 13L (* carriage return *)
  | 't' -> 9L  (* horizontal tab *)
  | 'v' -> 11L (* vertical tab *)
  | c   -> Int64.of_int (Char.code c)
(*- #End *)

(* Encodings for character and string literals *)

(*- E_COMPCERT_CODE_Lexer_encoding_of_001 *)
(*- #Justify_Derived "Utility function" *)
let encoding_of = function
  | "" -> Cabs.EncNone
  | "L" -> Cabs.EncWide
  | "u" -> Cabs.EncU16
  | "U" -> Cabs.EncU32
  | "u8" -> Cabs.EncUTF8
  | _ -> assert false
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_combine_encodings_001 *)
(*- #Link_to E_COMPCERT_TR_Robustness_LEXER_012 *)
let combine_encodings loc e1 e2 =
  if e1 = Cabs.EncNone then e2
  else if e2 = Cabs.EncNone then e1
  else if e1 = e2 then e1
  else Diagnostics.fatal_error
           Cabs.(loc.filename, loc.lineno)
           "unsupported non-standard concatenation of string literals"
(*- #End *)

(* Handling of characters and escapes in string and char constants *)

(*- E_COMPCERT_CODE_Lexer_chr_001 *)
(*- #Justify_Derived "Type definition" *)
type chr = Chr of int | Esc of int64
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_check_utf8_001 *)
(*- #Link_to E_COMPCERT_TR_Function_LEXER_013 *)
let check_utf8 lexbuf min x =
  if x > 0x10FFFF || (x >= 0xD800 && x <= 0xDFFF) then
    warning lexbuf Diagnostics.Invalid_UTF8 "Wrong Unicode value U+%X" x;
  if x < min then
    warning lexbuf Diagnostics.Invalid_UTF8
            "Overlong UTF-8 encoding for Unicode value U+%X" x;
  Chr x
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_check_universal_character_001 *)
(*- #Link_to E_COMPCERT_TR_Robustness_LEXER_014 *)
let check_universal_character lexbuf x =
  if x > 0x10FFFF
  || x >= 0xD800 && x <= 0xDFFF
  || x < 0xA0 && x <> 0x24 && x <> 0x40 && x <> 0x60
  then begin
    error lexbuf "Wrong universal character name U+%X" x; Chr 0
  end else
    Chr x
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_add_char_utf8_001 *)
(*- #Justify_Derived "Utility function" *)
let add_char_utf8 x accu =
  if x <= 0x007F then
    Int64.of_int x :: accu
  else if x <= 0x07FF then
    Int64.of_int (0x80 lor (x land 0x3F)) ::
    Int64.of_int (0xC0 lor (x lsr 6)) ::
    accu
  else if x <= 0xFFFF then
    Int64.of_int (0x80 lor (x land 0x3F)) ::
    Int64.of_int (0x80 lor ((x lsr 6) land 0x3F)) ::
    Int64.of_int (0xE0 lor (x lsr 12)) ::
    accu
  else
    Int64.of_int (0x80 lor (x land 0x3F)) ::
    Int64.of_int (0x80 lor ((x lsr 6) land 0x3F)) ::
    Int64.of_int (0x80 lor ((x lsr 12) land 0x3F)) ::
    Int64.of_int (0xF0 lor (x lsr 18)) ::
    accu
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_add_char_utf16_001 *)
(*- #Justify_Derived "Utility function" *)
let add_char_utf16 x accu =
  if x <= 0xFFFF then
    Int64.of_int x :: accu
  else begin
    let x = x - 0x10000 in
    Int64.of_int (0xDC00 lor (x land 0x3FF)) ::
    Int64.of_int (0xD800 lor (x lsr 10)) ::
    accu
  end
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_add_char_001 *)
(*- #Justify_Derived "Utility function" *)
let add_char enc c accu =
  match c, enc with
  | Esc x, _ -> (* Escapes are never encoded *)
      x :: accu
  | Chr x, (Cabs.EncNone | Cabs.EncUTF8) -> (* Characters are encoded in UTF8 *)
      add_char_utf8 x accu
  | Chr x, Cabs.EncU16 -> (* Characters are encoded in UTF16 *)
      add_char_utf16 x accu
  | Chr x, Cabs.EncU32 -> (* Characters are not encoded *)
      Int64.of_int x :: accu
  | Chr x, Cabs.EncWide -> (* Depends on size of wchar_t *)
      if Cutil.sizeof_ikind (Cutil.wchar_ikind ()) = 2
      then add_char_utf16 x accu
      else Int64.of_int x :: accu
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_re_single_backslash_001 *)
(*- #Justify_Derived "Utility constants" *)
let re_double_backslash = Str.regexp_string {|\\|}
(*- #End *)


(* Normalize filenames for the TriCore windows variant. The filenames can
   occur in two variants, with two or four backslashes, we need to normalize
   them to one or two backslashes in order to avoid having one file match to
   both variants resulting in dublicates entries. *)
(*- E_COMPCERT_CODE_Fileinfo_normalize_filename_001 *)
(*- #Justify_Derived "Utility function" *)
let normalize_file file =
  if Sys.win32 && Configuration.arch = "tricore" then begin
    Str.global_replace re_double_backslash {|\\|} file
  end else
    file
(*- #End *)
}

(* Identifiers *)
(*- E_COMPCERT_CODE_Lexer_digit_001 *)
(*- #Link_to E_COMPCERT_TR_Function_IDENTIFIERS_001 *)
let digit = ['0'-'9']
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_hexadecimal_digit_001 *)
(*- #Link_to E_COMPCERT_TR_Function_INTEGER_CONSTANTS_001 *)
let hexadecimal_digit = ['0'-'9' 'A'-'F' 'a'-'f']
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_nondigit_001 *)
(*- #Link_to E_COMPCERT_TR_Function_IDENTIFIERS_001 *)
let nondigit = ['_' 'a'-'z' 'A'-'Z']
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_hex_quad_001 *)
(*- #Link_to E_COMPCERT_TR_Function_LEXICAL_UCN_001 *)
let hex_quad = hexadecimal_digit hexadecimal_digit
                 hexadecimal_digit hexadecimal_digit
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_universal_character_name_001 *)
(*- #Link_to E_COMPCERT_TR_Function_LEXICAL_UCN_001 *)
let universal_character_name =
    "\\u" (hex_quad as n)
  | "\\U" (hex_quad hex_quad as n)
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_identifier_nondigit_001 *)
(*- #Link_to E_COMPCERT_TR_Function_IDENTIFIERS_001 *)
let identifier_nondigit =
    nondigit
(*- #Link_to E_COMPCERT_TR_Function_LEXER_010 *)
(*| universal_character_name*)
  | '$'
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_identifier_001 *)
(*- #Link_to E_COMPCERT_TR_Function_IDENTIFIERS_001 *)
(*- #Link_to E_COMPCERT_TR_Function_ENUMERATION_CONSTANTS_001 *)
let identifier = identifier_nondigit (identifier_nondigit|digit)*
(*- #End *)

(* Whitespaces *)
(*- E_COMPCERT_CODE_Lexer_whitespace_char_no_newline_001 *)
(*- #Justify_Derived "Utility constant" *)
let whitespace_char_no_newline = [' ' '\t'  '\011' '\012' '\r']
(*- #End *)

(* Integer constants *)

(*- E_COMPCERT_CODE_Lexer_nonzero_digit_001 *)
(*- #Link_to E_COMPCERT_TR_Function_INTEGER_CONSTANTS_001 *)
let nonzero_digit = ['1'-'9']
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_decimal_constant_001 *)
(*- #Link_to E_COMPCERT_TR_Function_INTEGER_CONSTANTS_001 *)
let decimal_constant = nonzero_digit digit*
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_octal_digit_001 *)
(*- #Link_to E_COMPCERT_TR_Function_INTEGER_CONSTANTS_001 *)
let octal_digit = ['0'-'7']
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_octal_constant_001 *)
(*- #Link_to E_COMPCERT_TR_Function_INTEGER_CONSTANTS_001 *)
let octal_constant = '0' octal_digit*
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_hexadecimal_prefix_001 *)
(*- #Link_to E_COMPCERT_TR_Function_INTEGER_CONSTANTS_001 *)
let hexadecimal_prefix = "0x" | "0X"
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_hexadecimal_constant_001 *)
(*- #Link_to E_COMPCERT_TR_Function_INTEGER_CONSTANTS_001 *)
let hexadecimal_constant =
  hexadecimal_prefix hexadecimal_digit+
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_unsigned_suffix_001 *)
(*- #Link_to E_COMPCERT_TR_Function_INTEGER_CONSTANTS_001 *)
let unsigned_suffix = ['u' 'U']
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_long_suffix_001 *)
(*- #Link_to E_COMPCERT_TR_Function_INTEGER_CONSTANTS_001 *)
let long_suffix = ['l' 'L']
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_long_long_suffix_001 *)
(*- #Link_to E_COMPCERT_TR_Function_INTEGER_CONSTANTS_001 *)
let long_long_suffix = "ll" | "LL"
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_integer_suffix_001 *)
(*- #Link_to E_COMPCERT_TR_Function_INTEGER_CONSTANTS_001 *)
let integer_suffix =
    unsigned_suffix long_suffix?
  | unsigned_suffix long_long_suffix
  | long_suffix unsigned_suffix?
  | long_long_suffix unsigned_suffix?
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_integer_constant_001 *)
(*- #Link_to E_COMPCERT_TR_Function_INTEGER_CONSTANTS_001 *)
let integer_constant =
    decimal_constant integer_suffix?
  | octal_constant integer_suffix?
  | hexadecimal_constant integer_suffix?
(*- #End *)

(* Floating constants *)
(*- E_COMPCERT_CODE_Lexer_sign_001 *)
(*- #Link_to E_COMPCERT_TR_Function_FLOATING_CONSTANTS_001 *)
let sign = ['-' '+']
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_digit_sequence_001 *)
(*- #Link_to E_COMPCERT_TR_Function_FLOATING_CONSTANTS_001 *)
let digit_sequence = digit+
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_floating_suffix_001 *)
(*- #Link_to E_COMPCERT_TR_Function_FLOATING_CONSTANTS_001 *)
let floating_suffix = ['f' 'l' 'F' 'L'] as suffix
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_fractional_constant_001 *)
(*- #Link_to E_COMPCERT_TR_Function_FLOATING_CONSTANTS_001 *)
let fractional_constant =
    (digit_sequence as intpart)? '.' (digit_sequence as frac)
  | (digit_sequence as intpart) '.'
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_exponent_part_001 *)
(*- #Link_to E_COMPCERT_TR_Function_FLOATING_CONSTANTS_001 *)
let exponent_part =
    'e' ((sign? digit_sequence) as expo)
  | 'E' ((sign? digit_sequence) as expo)
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_decimal_floating_constant_001 *)
(*- #Link_to E_COMPCERT_TR_Function_FLOATING_CONSTANTS_001 *)
let decimal_floating_constant =
    fractional_constant exponent_part? floating_suffix?
  | (digit_sequence as intpart) exponent_part floating_suffix?
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_hexadecimal_digit_sequence_001 *)
(*- #Link_to E_COMPCERT_TR_Function_FLOATING_CONSTANTS_001 *)
let hexadecimal_digit_sequence = hexadecimal_digit+
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_hexadecimal_fractional_constant_001 *)
(*- #Link_to E_COMPCERT_TR_Function_FLOATING_CONSTANTS_001 *)
let hexadecimal_fractional_constant =
    (hexadecimal_digit_sequence as intpart)? '.' (hexadecimal_digit_sequence as frac)
  | (hexadecimal_digit_sequence as intpart) '.'
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_binary_exponent_part_001 *)
(*- #Link_to E_COMPCERT_TR_Function_FLOATING_CONSTANTS_001 *)
let binary_exponent_part =
    'p' ((sign? digit_sequence) as expo)
  | 'P' ((sign? digit_sequence) as expo)
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_hexadecimal_floating_constant_001 *)
(*- #Link_to E_COMPCERT_TR_Function_FLOATING_CONSTANTS_001 *)
let hexadecimal_floating_constant =
    hexadecimal_prefix hexadecimal_fractional_constant
        binary_exponent_part floating_suffix?
  | hexadecimal_prefix (hexadecimal_digit_sequence as intpart)
        binary_exponent_part floating_suffix?
(*- #End *)

(* Preprocessing numbers *)
(*- E_COMPCERT_CODE_Lexer_preprocessing_number_001 *)
(*- #Link_to E_COMPCERT_TR_Function_PPNUMBERS_001 *)
let preprocessing_number =
  '.'? ['0'-'9']
  (['0'-'9' 'A'-'Z' 'a'-'z' '_' '.'] | ['e' 'E' 'p' 'P']['+' '-'])*
(*- #End *)

(* Character and string constants *)
(*- E_COMPCERT_CODE_Lexer_simple_escape_sequence_001 *)
(*- #Link_to E_COMPCERT_TR_Function_CHARACTER_CONSTANTS_001 *)
let simple_escape_sequence =
  '\\' ( ['\''  '\"'  '?'  '\\'  'a'  'b'  'e'  'f'  'n'  'r'  't'  'v'] as c)
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_octal_escape_sequence_001 *)
(*- #Link_to E_COMPCERT_TR_Function_CHARACTER_CONSTANTS_001 *)
let octal_escape_sequence =
  '\\' ((octal_digit
         | octal_digit octal_digit
         | octal_digit octal_digit octal_digit) as n)
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_hexadecimal_escape_sequence_001 *)
(*- #Link_to E_COMPCERT_TR_Function_CHARACTER_CONSTANTS_001 *)
let hexadecimal_escape_sequence = "\\x" (hexadecimal_digit+ as n)
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_rule_initial_001 *)
(*- #Link_to E_COMPCERT_TR_Function_CONSTANTS_001 *)
(*- #Link_to E_COMPCERT_TR_Function_CHARACTER_CONSTANTS_001 *)
(*- #Link_to E_COMPCERT_TR_Function_STRING_LITERALS_001 *)
(*- #Link_to E_COMPCERT_TR_Function_PUNCTUATORS_001 *)
rule initial = parse
  | '\n'                          { new_line lexbuf; initial_linebegin lexbuf }
  | whitespace_char_no_newline +  { initial lexbuf }
  | "/*"                          { multiline_comment lexbuf; initial lexbuf }
  | "//"                          { singleline_comment lexbuf; initial lexbuf }
  | integer_constant as s         { CONSTANT (Cabs.CONST_INT s, currentLoc lexbuf) }
  | decimal_floating_constant     { CONSTANT (Cabs.CONST_FLOAT
                                      {Cabs.isHex_FI = false;
                                       Cabs.integer_FI = intpart;
                                       Cabs.fraction_FI = frac;
                                       Cabs.exponent_FI = expo;
                                       Cabs.suffix_FI =
                                         match suffix with
                                         | None -> None
                                         | Some c -> Some (String.make 1 c) },
                                      currentLoc lexbuf) }
  | hexadecimal_floating_constant { CONSTANT (Cabs.CONST_FLOAT
                                      {Cabs.isHex_FI = true;
                                       Cabs.integer_FI = intpart;
                                       Cabs.fraction_FI = frac;
                                       Cabs.exponent_FI = Some expo;
                                       Cabs.suffix_FI =
                                         match suffix with
                                           | None -> None
                                           | Some c -> Some (String.make 1 c) },
                                      currentLoc lexbuf)}
  (*- #Link_to E_COMPCERT_TR_Robustness_LEXER_003 *)
  | preprocessing_number as s     { error lexbuf "invalid numerical constant '%s'@ These characters form a preprocessor number, but not a constant" s;
                                    CONSTANT (Cabs.CONST_INT "0", currentLoc lexbuf) }
  | (""|"L"|"u"|"U") as e "'"     { let enc = encoding_of e in
                                    let l = char_literal lexbuf.lex_start_p [] lexbuf in
                                    CONSTANT (Cabs.CONST_CHAR(enc, l), currentLoc lexbuf) }
  | (""|"L"|"u"|"U"|"u8") as e "\""
                                  { let enc = encoding_of e in
                                    let l = string_literal lexbuf.lex_start_p enc [] lexbuf in
                                    STRING_LITERAL(enc, l, currentLoc lexbuf) }
  | "..."                         { ELLIPSIS(currentLoc lexbuf) }
  | "+="                          { ADD_ASSIGN(currentLoc lexbuf) }
  | "-="                          { SUB_ASSIGN(currentLoc lexbuf) }
  | "*="                          { MUL_ASSIGN(currentLoc lexbuf) }
  | "/="                          { DIV_ASSIGN(currentLoc lexbuf) }
  | "%="                          { MOD_ASSIGN(currentLoc lexbuf) }
  | "|="                          { OR_ASSIGN(currentLoc lexbuf) }
  | "&="                          { AND_ASSIGN(currentLoc lexbuf) }
  | "^="                          { XOR_ASSIGN(currentLoc lexbuf) }
  | "<<="                         { LEFT_ASSIGN(currentLoc lexbuf) }
  | ">>="                         { RIGHT_ASSIGN(currentLoc lexbuf) }
  | "<<"                          { LEFT(currentLoc lexbuf) }
  | ">>"                          { RIGHT(currentLoc lexbuf) }
  | "=="                          { EQEQ(currentLoc lexbuf) }
  | "!="                          { NEQ(currentLoc lexbuf) }
  | "<="                          { LEQ(currentLoc lexbuf) }
  | ">="                          { GEQ(currentLoc lexbuf) }
  | "="                           { EQ(currentLoc lexbuf) }
  | "<"                           { LT(currentLoc lexbuf) }
  | ">"                           { GT(currentLoc lexbuf) }
  | "++"                          { INC(currentLoc lexbuf) }
  | "--"                          { DEC(currentLoc lexbuf) }
  | "->"                          { PTR(currentLoc lexbuf) }
  | "+"                           { PLUS(currentLoc lexbuf) }
  | "-"                           { MINUS(currentLoc lexbuf) }
  | "*"                           { STAR(currentLoc lexbuf) }
  | "/"                           { SLASH(currentLoc lexbuf) }
  | "%"                           { PERCENT(currentLoc lexbuf) }
  | "!"                           { BANG(currentLoc lexbuf) }
  | "&&"                          { ANDAND(currentLoc lexbuf) }
  | "||"                          { BARBAR(currentLoc lexbuf) }
  | "&"                           { AND(currentLoc lexbuf) }
  | "|"                           { BAR(currentLoc lexbuf) }
  | "^"                           { HAT(currentLoc lexbuf) }
  | "?"                           { QUESTION(currentLoc lexbuf) }
  | ":"                           { COLON(currentLoc lexbuf) }
  | "~"                           { TILDE(currentLoc lexbuf) }
  | "{"|"<%"                      { LBRACE(currentLoc lexbuf) }
  | "}"|"%>"                      { RBRACE(currentLoc lexbuf) }
  | "["|"<:"                      { LBRACK(currentLoc lexbuf) }
  | "]"|":>"                      { RBRACK(currentLoc lexbuf) }
  | "("                           { LPAREN(currentLoc lexbuf) }
  | ")"                           { RPAREN(currentLoc lexbuf) }
  | ";"                           { SEMICOLON(currentLoc lexbuf) }
  | ","                           { COMMA(currentLoc lexbuf) }
  | "."                           { DOT(currentLoc lexbuf) }
  | identifier as id              {
    if SSet.mem id !ignored_keywords then
      (*- #Link_to E_COMPCERT_TR_Function_IDENTIFIERS_001 *)
      initial lexbuf
    else
      try Hashtbl.find lexicon id (currentLoc lexbuf)
      with Not_found -> PRE_NAME id }
  | eof                           { EOF }
  (*- #Link_to E_COMPCERT_TR_Robustness_LEXER_007 *)
  | _ as c                        { fatal_error lexbuf "invalid symbol %C" c }
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_initial_linebegin_001 *)
(*- #Justify_Derived "Utility function" *)
and initial_linebegin = parse
  | '\n'                          { new_line lexbuf; initial_linebegin lexbuf }
  | whitespace_char_no_newline    { initial_linebegin lexbuf }
  | '#'                           { hash lexbuf }
  | ""                            { initial lexbuf }
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_char_001 *)
(*- #Link_to E_COMPCERT_TR_Function_CHARACTER_CONSTANTS_001 *)
and char = parse
  | universal_character_name
      { try
          check_universal_character lexbuf (int_of_string ("0x" ^ n))
        with Failure _ ->
          (*- #Link_to E_COMPCERT_TR_Robustness_LEXER_014 *)
          error lexbuf "overflow in universal character name";
          Chr 0
      }
  | hexadecimal_escape_sequence
      { try
          Esc (Int64.of_string ("0x" ^ n))
        with Failure _ ->
          (*- #Link_to E_COMPCERT_TR_Robustness_LEXER_004 *)
          error lexbuf "overflow in hexadecimal escape sequence";
          Esc 0L
      }
  | octal_escape_sequence
      { Esc (Int64.of_string  ("0o" ^ n)) }
  | simple_escape_sequence
      { Esc (convert_escape c) }
  | "\\u" | "\\U"
      (*- #Link_to E_COMPCERT_TR_Robustness_LEXER_015 *)
      { error lexbuf "incomplete universal character name";
        Chr 0 }
  | '\\' (_ as c)
      (*- #Link_to E_COMPCERT_TR_Robustness_LEXER_005 *)
      { error lexbuf "incorrect escape sequence '\\%c'" c;
        Esc (Int64.of_int (Char.code c)) }
  | ['\x00'-'\x7F'] as c1
      { Chr (Char.code c1) }
  | (['\xC0'-'\xDF'] as c1) (['\x80'-'\xBF'] as c2)
      { check_utf8 lexbuf 0x80
          ( (Char.code c1 land 0b00011111) lsl 6
          + (Char.code c2 land 0b00111111)) }
  | (['\xE0'-'\xEF'] as c1) (['\x80'-'\xBF'] as c2) (['\x80'-'\xBF'] as c3)
      { check_utf8 lexbuf 0x800
          ( (Char.code c1 land 0b00001111) lsl 12
          + (Char.code c2 land 0b00111111) lsl 6
          + (Char.code c3 land 0b00111111) ) }
  | (['\xF0'-'\xF7'] as c1) (['\x80'-'\xBF'] as c2) (['\x80'-'\xBF'] as c3) (['\x80'-'\xBF'] as c4)
     { check_utf8 lexbuf 0x10000
          ( (Char.code c1 land 0b00000111) lsl 18
          + (Char.code c2 land 0b00111111) lsl 12
          + (Char.code c3 land 0b00111111) lsl 6
          + (Char.code c4 land 0b00111111) ) }
  | _ as c
     (*- #Link_to E_COMPCERT_TR_Function_LEXER_013 *)
     { warning lexbuf Diagnostics.Invalid_UTF8
               "Invalid UTF8 encoding: byte 0x%02x" (Char.code c);
       Esc (Int64.of_int (Char.code c)) (* re-encode as-is *)
     }
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_char_literal_001 *)
(*- #Link_to E_COMPCERT_TR_Function_CHARACTER_CONSTANTS_001 *)
and char_literal startp accu = parse
  | '\''       { lexbuf.lex_start_p <- startp;
                 List.rev accu }
  (*- #Link_to E_COMPCERT_TR_Robustness_LEXER_008 *)
  | '\n' | eof { fatal_error lexbuf "missing terminating \"'\" character" }
  | ""         { let c = char lexbuf in char_literal startp (add_char Cabs.EncU32 c accu) lexbuf }
(*- #End *)

(*- E_COMPCERT_CODE_Lexer_string_literal_001 *)
(*- #Link_to E_COMPCERT_TR_Function_STRING_LITERALS_001 *)
and string_literal startp enc accu = parse
  | '\"'       { lexbuf.lex_start_p <- startp;
                 List.rev accu }
  (*- #Link_to E_COMPCERT_TR_Robustness_LEXER_008 *)
  | '\n' | eof { fatal_error lexbuf "missing terminating '\"' character" }
  | ""         { let c = char lexbuf in string_literal startp enc (add_char enc c accu) lexbuf }
(*- #End *)

(* We assume gcc -E syntax but try to tolerate variations. *)
(*- E_COMPCERT_CODE_Lexer_hash_001 *)
and hash = parse
  | whitespace_char_no_newline +
    (digit + as n)
    whitespace_char_no_newline *
    "\"" ([^ '\n' '\"']* as file) "\""
    [^ '\n']* '\n'
      { let n =
          try
            int_of_string n
          with Failure _ ->
            (*- #Link_to E_COMPCERT_TR_Function_LEXER_001 *)
            warning lexbuf Diagnostics.Unnamed "invalid line number";
            lexbuf.lex_curr_p.pos_lnum
        in
        let file = normalize_file file in
        lexbuf.lex_curr_p <- {
          lexbuf.lex_curr_p with
            pos_fname = file;
            pos_lnum = n;
            pos_bol = lexbuf.lex_curr_p.pos_cnum
        };
        initial_linebegin lexbuf }
  | whitespace_char_no_newline *
    "pragma"
    whitespace_char_no_newline +
    ([^ '\n']* as s) '\n'
      { new_line lexbuf; PRAGMA (s, currentLoc lexbuf) }
  | [^ '\n']* '\n'
      (*- #Link_to E_COMPCERT_TR_Function_LEXER_002 *)
      { warning lexbuf Diagnostics.Unnamed "unrecognized '#' line";
        new_line lexbuf; initial_linebegin lexbuf }
  | [^ '\n']* eof
      (*- #Link_to E_COMPCERT_TR_Robustness_LEXER_009 *)
      { fatal_error lexbuf "unexpected end of file" }
  | _ as c
      { fatal_error lexbuf "invalid symbol %C" c }
(*- #End *)

(* Multi-line comment terminated by "*/" *)
(*- E_COMPCERT_CODE_Lexer_multiline_comment_001 *)
(*- #Link_to E_COMPCERT_TR_Function_COMMENTS_001 *)
and multiline_comment = parse
  | "*/"   { () }
  (*- #Link_to E_COMPCERT_TR_Robustness_LEXER_006 *)
  | eof    { error lexbuf "unterminated comment" }
  | '\n'   { new_line lexbuf; multiline_comment lexbuf }
  | _      { multiline_comment lexbuf }
(*- #End *)

(* Single-line comment terminated by a newline *)
(*- E_COMPCERT_CODE_Lexer_singleline_comment_001 *)
(*- #Link_to E_COMPCERT_TR_Function_COMMENTS_002 *)
and singleline_comment = parse
  | '\n'   { new_line lexbuf }
  | eof    { () }
  | _      { singleline_comment lexbuf }
(*- #End *)
{
  open Parser.MenhirLibParser.Inter

  (* This is the main entry point to the lexer. *)

  (*- E_COMPCERT_CODE_Lexer_lexer_001 *)
  (*- #Justify_Derived "Utility function" *)
  let lexer : lexbuf -> Pre_parser.token =
    fun lexbuf ->
      if lexbuf.lex_curr_p.pos_cnum = lexbuf.lex_curr_p.pos_bol then
        initial_linebegin lexbuf
      else
        initial lexbuf
  (*- #End *)

  (* [lexer tokens buffer] is a new lexer, which wraps [lexer], and also: 1-
     records the token stream into the FIFO queue [tokens] and 2- records the
     start and end positions of the last two tokens in the two-place buffer
     [buffer] and 3- duplicates identifier tokens into PRE_NAME and
     VAR/TYPE_NAME. *)

  (*- E_COMPCERT_CODE_Lexer_lexer_002 *)
  (*- #Link_to E_COMPCERT_TR_Function_PRE_NAME_001 *)
  let lexer tokens buffer : lexbuf -> Pre_parser.token =
    let curr_id = ref None in
    types_context := init_ctx;
    fun lexbuf ->
      match !curr_id with
      | Some id ->
        curr_id := None;
        let loc = currentLoc lexbuf in
        let token =
          if SSet.mem id !types_context then Pre_parser.TYPEDEF_NAME (id, ref TypedefId, loc)
          else Pre_parser.VAR_NAME (id, ref VarId, loc)
        in
        Queue.push token tokens;
        token
      | None ->
        let token = lexer lexbuf in
        begin match token with
        | PRE_NAME id -> curr_id := Some id
        | _ -> Queue.push token tokens
        end;
        let startp = lexbuf.lex_start_p
        and endp = lexbuf.lex_curr_p in
        buffer := ErrorReports.update !buffer (startp, endp);
        token
  (*- #End *)

  (* [invoke_pre_parser] is in charge of calling the pre_parser. It uses
     the incremental API, which allows us to do our own error handling. *)

  (*- E_COMPCERT_CODE_Lexer_invoke_pre_parser_001 *)
  (*- #Justify_Derived "Utility function" *)
  let invoke_pre_parser filename text lexer buffer =
    let lexbuf = Lexing.from_string text in
    lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_fname = filename; pos_lnum = 1};
    let module I = Pre_parser.MenhirInterpreter in
    let checkpoint = Pre_parser.Incremental.translation_unit_file lexbuf.lex_curr_p
    and supplier = I.lexer_lexbuf_to_supplier lexer lexbuf
    and succeed () = ()
    and fail checkpoint =
      Diagnostics.fatal_error_raw "%s" (ErrorReports.report text !buffer checkpoint)
    in
    I.loop_handle succeed fail supplier checkpoint
  (*- #End *)

  (* [tokens_stream filename text] runs the pre_parser and produces a stream
     of (appropriately classified) tokens. *)

  (*- E_COMPCERT_CODE_Lexer_tokens_stream_001 *)
  (*- #Link_to E_COMPCERT_TR_Function_LEXER_010 *)
  (*- #Link_to E_COMPCERT_TR_Function_LEX_ELEMENTS_001 *)
  let tokens_stream filename text : buffer =
    let tokens = Queue.create () in
    let buffer = ref ErrorReports.Zero in
    invoke_pre_parser filename text (lexer tokens buffer) buffer;
    let rec compute_buffer () =
      let loop t = Buf_cons (t, Lazy.from_fun compute_buffer) in
      match Queue.pop tokens with
      | Pre_parser.ADD_ASSIGN loc -> loop (Parser.ADD_ASSIGN loc)
      | Pre_parser.AND loc -> loop (Parser.AND loc)
      | Pre_parser.ANDAND loc -> loop (Parser.ANDAND loc)
      | Pre_parser.AND_ASSIGN loc -> loop (Parser.AND_ASSIGN loc)
      | Pre_parser.AUTO loc -> loop (Parser.AUTO loc)
      | Pre_parser.BANG loc -> loop (Parser.BANG loc)
      | Pre_parser.BAR loc -> loop (Parser.BAR loc)
      | Pre_parser.BARBAR loc -> loop (Parser.BARBAR loc)
      | Pre_parser.UNDERSCORE_BOOL loc -> loop (Parser.UNDERSCORE_BOOL loc)
      | Pre_parser.BREAK loc -> loop (Parser.BREAK loc)
      | Pre_parser.BUILTIN_VA_ARG loc -> loop (Parser.BUILTIN_VA_ARG loc)
      | Pre_parser.BUILTIN_OFFSETOF loc -> loop (Parser.BUILTIN_OFFSETOF loc)
      | Pre_parser.CASE loc -> loop (Parser.CASE loc)
      | Pre_parser.CHAR loc -> loop (Parser.CHAR loc)
      | Pre_parser.COLON loc -> loop (Parser.COLON loc)
      | Pre_parser.COMMA loc -> loop (Parser.COMMA loc)
      | Pre_parser.CONST loc -> loop (Parser.CONST loc)
      | Pre_parser.CONSTANT (cst, loc) -> loop (Parser.CONSTANT (cst, loc))
      | Pre_parser.CONTINUE loc -> loop (Parser.CONTINUE loc)
      | Pre_parser.DEC loc -> loop (Parser.DEC loc)
      | Pre_parser.DEFAULT loc -> loop (Parser.DEFAULT loc)
      | Pre_parser.DIV_ASSIGN loc -> loop (Parser.DIV_ASSIGN loc)
      | Pre_parser.DO loc -> loop (Parser.DO loc)
      | Pre_parser.DOT loc -> loop (Parser.DOT loc)
      | Pre_parser.DOUBLE loc -> loop (Parser.DOUBLE loc)
      | Pre_parser.ELLIPSIS loc -> loop (Parser.ELLIPSIS loc)
      | Pre_parser.ELSE loc -> loop (Parser.ELSE loc)
      | Pre_parser.ENUM loc -> loop (Parser.ENUM loc)
      | Pre_parser.EOF -> loop (Parser.EOF ())
      | Pre_parser.EQ loc -> loop (Parser.EQ loc)
      | Pre_parser.EQEQ loc -> loop (Parser.EQEQ loc)
      | Pre_parser.EXTERN loc -> loop (Parser.EXTERN loc)
      | Pre_parser.FLOAT loc -> loop (Parser.FLOAT loc)
      | Pre_parser.FOR loc -> loop (Parser.FOR loc)
      | Pre_parser.GENERIC loc -> loop (Parser.GENERIC loc)
      | Pre_parser.GEQ loc -> loop (Parser.GEQ loc)
      | Pre_parser.GOTO loc -> loop (Parser.GOTO loc)
      | Pre_parser.GT loc -> loop (Parser.GT loc)
      | Pre_parser.HAT loc -> loop (Parser.HAT loc)
      | Pre_parser.IF loc -> loop (Parser.IF_ loc)
      | Pre_parser.INC loc -> loop (Parser.INC loc)
      | Pre_parser.INLINE loc -> loop (Parser.INLINE loc)
      | Pre_parser.INT loc -> loop (Parser.INT loc)
      | Pre_parser.LBRACE loc -> loop (Parser.LBRACE loc)
      | Pre_parser.LBRACK loc -> loop (Parser.LBRACK loc)
      | Pre_parser.LEFT loc -> loop (Parser.LEFT loc)
      | Pre_parser.LEFT_ASSIGN loc -> loop (Parser.LEFT_ASSIGN loc)
      | Pre_parser.LEQ loc -> loop (Parser.LEQ loc)
      | Pre_parser.LONG loc -> loop (Parser.LONG loc)
      | Pre_parser.LPAREN loc -> loop (Parser.LPAREN loc)
      | Pre_parser.LT loc -> loop (Parser.LT loc)
      | Pre_parser.MINUS loc -> loop (Parser.MINUS loc)
      | Pre_parser.MOD_ASSIGN loc -> loop (Parser.MOD_ASSIGN loc)
      | Pre_parser.MUL_ASSIGN loc -> loop (Parser.MUL_ASSIGN loc)
      | Pre_parser.NEQ loc -> loop (Parser.NEQ loc)
      | Pre_parser.NORETURN loc -> loop (Parser.NORETURN loc)
      | Pre_parser.OR_ASSIGN loc -> loop (Parser.OR_ASSIGN loc)
      | Pre_parser.PACKED loc -> loop (Parser.PACKED loc)
      | Pre_parser.PERCENT loc -> loop (Parser.PERCENT loc)
      | Pre_parser.PLUS loc -> loop (Parser.PLUS loc)
      | Pre_parser.PTR loc -> loop (Parser.PTR loc)
      | Pre_parser.QUESTION loc -> loop (Parser.QUESTION loc)
      | Pre_parser.RBRACE loc -> loop (Parser.RBRACE loc)
      | Pre_parser.RBRACK loc -> loop (Parser.RBRACK loc)
      | Pre_parser.REGISTER loc -> loop (Parser.REGISTER loc)
      | Pre_parser.RESTRICT loc -> loop (Parser.RESTRICT loc)
      | Pre_parser.RETURN loc -> loop (Parser.RETURN loc)
      | Pre_parser.RIGHT loc -> loop (Parser.RIGHT loc)
      | Pre_parser.RIGHT_ASSIGN loc -> loop (Parser.RIGHT_ASSIGN loc)
      | Pre_parser.RPAREN loc -> loop (Parser.RPAREN loc)
      | Pre_parser.SEMICOLON loc -> loop (Parser.SEMICOLON loc)
      | Pre_parser.SHORT loc -> loop (Parser.SHORT loc)
      | Pre_parser.SIGNED loc -> loop (Parser.SIGNED loc)
      | Pre_parser.SIZEOF loc -> loop (Parser.SIZEOF loc)
      | Pre_parser.SLASH loc -> loop (Parser.SLASH loc)
      | Pre_parser.STAR loc -> loop (Parser.STAR loc)
      | Pre_parser.STATIC loc -> loop (Parser.STATIC loc)
      | Pre_parser.STATIC_ASSERT loc -> loop (Parser.STATIC_ASSERT loc)
      | Pre_parser.STRING_LITERAL (enc, str, loc) ->
          (* Merge consecutive string literals *)
          let rec doConcat enc str =
            match Queue.peek tokens with
            | Pre_parser.STRING_LITERAL (enc', str', loc') ->
               ignore (Queue.pop tokens);
               let (enc'', str'') = doConcat enc' str' in
               if str'' <> []
               then (combine_encodings loc enc enc'', str @ str'')
               else (enc, str)
            | _ -> (enc, str)
            | exception Queue.Empty -> (enc, str)
          in
          let (enc', str') = doConcat enc str in
          loop (Parser.STRING_LITERAL ((enc', str'), loc))
      | Pre_parser.STRUCT loc -> loop (Parser.STRUCT loc)
      | Pre_parser.SUB_ASSIGN loc -> loop (Parser.SUB_ASSIGN loc)
      | Pre_parser.SWITCH loc -> loop (Parser.SWITCH loc)
      | Pre_parser.TILDE loc -> loop (Parser.TILDE loc)
      | Pre_parser.TYPEDEF loc -> loop (Parser.TYPEDEF loc)
      | Pre_parser.TYPEDEF_NAME (id, typ, loc)
      | Pre_parser.VAR_NAME (id, typ, loc) ->
          begin match !typ with
          | VarId -> loop (Parser.VAR_NAME (id, loc))
          | TypedefId -> loop (Parser.TYPEDEF_NAME (id, loc))
          | OtherId -> loop (Parser.OTHER_NAME (id, loc))
          end
      | Pre_parser.UNION loc -> loop (Parser.UNION loc)
      | Pre_parser.UNSIGNED loc -> loop (Parser.UNSIGNED loc)
      | Pre_parser.VOID loc -> loop (Parser.VOID loc)
      | Pre_parser.VOLATILE loc -> loop (Parser.VOLATILE loc)
      | Pre_parser.WHILE loc -> loop (Parser.WHILE loc)
      | Pre_parser.XOR_ASSIGN loc -> loop (Parser.XOR_ASSIGN loc)
      | Pre_parser.ALIGNAS loc -> loop (Parser.ALIGNAS loc)
      | Pre_parser.ALIGNOF loc -> loop (Parser.ALIGNOF loc)
      | Pre_parser.ATTRIBUTE loc -> loop (Parser.ATTRIBUTE loc)
      | Pre_parser.ASM loc -> loop (Parser.ASM loc)
      | Pre_parser.PRAGMA (s, loc) -> loop (Parser.PRAGMA (s, loc))
      | Pre_parser.PRE_NAME _ -> assert false
    in
    Lazy.from_fun compute_buffer
  (*- #End *)
}
