(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          François Pottier, INRIA Paris-Rocquencourt                 *)
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

open Lexing
open Pre_parser.MenhirInterpreter
module S = MenhirLib.General (* Streams *)

(* -------------------------------------------------------------------------- *)

(* There are places where we may hit an internal error and we would like to fail
   abruptly because "this cannot happen". Yet, it is safer when shipping to
   silently cover up for our internal error. Thus, we typically use an idiom of
   the form [if debug then assert false else <some default value>]. *)

(*- E_COMPCERT_CODE_ErrorReports_debug_001 *)
(*- #Justify_Derived "Utility constant" *)
let debug = false
(*- #End *)

(* -------------------------------------------------------------------------- *)

(* The parser keeps track of the last two tokens in a two-place buffer. *)

(*- E_COMPCERT_CODE_ErrorReports_buffer_001 *)
(*- #Justify_Derived "Type definition" *)
type 'a buffer =
| Zero
| One of 'a
| Two of 'a * (* most recent: *) 'a
(*- #End *)

(* [update buffer x] pushes [x] into [buffer], causing the buffer to slide. *)

(*- E_COMPCERT_CODE_ErrorReports_update_001 *)
(*- #Justify_Derived "Utility function" *)
let update buffer x : _ buffer =
  match buffer, x with
  | Zero, _ ->
      One x
  | One x1, x2
  | Two (_, x1), x2 ->
      Two (x1, x2)
(*- #End *)

(* [show f buffer] prints the contents of the buffer. The function [f] is
   used to print an element. *)

(*- E_COMPCERT_CODE_ErrorReports_show_001 *)
(*- #Justify_Derived "Utility function" *)
let show f buffer : string =
  match buffer with
  | Zero ->
      (* The buffer cannot be empty. If we have read no tokens, we
         cannot have detected a syntax error. *)
      if debug then assert false else ""
  | One invalid ->
      (* It is unlikely, but possible, that we have read just one token. *)
      Printf.sprintf "before '%s'" (f invalid)
  | Two (valid, invalid) ->
      (* In the most likely case, we have read two tokens. *)
      Printf.sprintf "after '%s' and before '%s'" (f valid) (f invalid)
(*- #End *)

(* [last buffer] returns the last element of the buffer (that is, the
   invalid token). *)

(*- E_COMPCERT_CODE_ErrorReports_last_001 *)
(*- #Justify_Derived "Utility function" *)
let last buffer =
  match buffer with
  | Zero ->
      (* The buffer cannot be empty. If we have read no tokens, we
         cannot have detected a syntax error. *)
      assert false
  | One invalid
  | Two (_, invalid) ->
      invalid
(*- #End *)

(* -------------------------------------------------------------------------- *)

(* [extract text (pos1, pos2)] extracts the sub-string of [text] delimited
   by the positions [pos1] and [pos2]. *)

(*- E_COMPCERT_CODE_ErrorReports_extract_001 *)
(*- #Justify_Derived "Utility function" *)
let extract text (pos1, pos2) : string =
  let ofs1 = pos1.pos_cnum
  and ofs2 = pos2.pos_cnum in
  let len = ofs2 - ofs1 in
  try
    String.sub text ofs1 len
  with Invalid_argument _ ->
    (* In principle, this should not happen, but if it does, let's make this
       a non-fatal error. *)
    if debug then assert false else "???"
(*- #End *)

(* -------------------------------------------------------------------------- *)

(* [compress text] replaces every run of at least one whitespace character
   with exactly one space character. *)

(*- E_COMPCERT_CODE_ErrorReports_compress_001 *)
(*- #Justify_Derived "Utility function" *)
let compress text =
  Str.global_replace (Str.regexp "[ \t\n\r]+") " " text
(*- #End *)

(* -------------------------------------------------------------------------- *)

(* [sanitize text] eliminates any special characters from the text [text].
   They are (arbitrarily) replaced with a single dot character. *)

(*- E_COMPCERT_CODE_ErrorReports_sanitize_001 *)
(*- #Justify_Derived "Utility function" *)
let sanitize text =
  String.map (fun c ->
    if Char.code c < 32 || Char.code c >= 127 then '.' else c
  ) text
(*- #End *)

(* -------------------------------------------------------------------------- *)

(* [shorten k text] limits the length of [text] to [2k+3] characters. If the
   text is too long, a fragment in the middle is replaced with an ellipsis. *)

(*- E_COMPCERT_CODE_ErrorReports_shorten_001 *)
(*- #Justify_Derived "Utility function" *)
let shorten k text =
  let n = String.length text in
  if n <= 2 * k + 3 then
    text
  else
    String.sub text 0 k ^
    "..." ^
    String.sub text (n - k) k
(*- #End *)

(* -------------------------------------------------------------------------- *)

(* [stack checkpoint] extracts the parser's stack out of a checkpoint. *)

(*- E_COMPCERT_CODE_ErrorReports_stack_001 *)
(*- #Justify_Derived "Utility function" *)
let stack checkpoint =
  match checkpoint with
  | HandlingError env ->
      stack env
  | _ ->
      assert false (* this cannot happen, I promise *)
(*- #End *)

(* -------------------------------------------------------------------------- *)

(* [state checkpoint] extracts the number of the current state out of a
   parser checkpoint. *)

(*- E_COMPCERT_CODE_ErrorReports_state_001 *)
(*- #Justify_Derived "Utility function" *)
let state checkpoint : int =
  match Lazy.force (stack checkpoint) with
  | S.Nil ->
      (* Hmm... The parser is in its initial state. Its number is
         usually 0. This is a BIG HACK. TEMPORARY *)
      0
  | S.Cons (Element (s, _, _, _), _) ->
      number s
(*- #End *)

(* -------------------------------------------------------------------------- *)

(* TEMPORARY move to MenhirLib.General *)

(*- E_COMPCERT_CODE_ErrorReports_drop_001 *)
(*- #Justify_Derived "Utility function" *)
let rec drop n (xs : 'a S.stream) : 'a S.stream =
  match n, xs with
  | 0, _
  | _, lazy (S.Nil) ->
      xs
  | _, lazy (S.Cons (_, xs)) ->
      drop (n - 1) xs
(*- #End *)

(* -------------------------------------------------------------------------- *)

(* [element checkpoint i] returns the [i]-th cell of the parser stack. The index
   [i] is 0-based. [i] should (ideally) be within bounds; we raise [Not_found]
   if it isn't. *)

(*- E_COMPCERT_CODE_ErrorReports_element_001 *)
(*- #Justify_Derived "Utility function" *)
let element checkpoint i : element =
  match Lazy.force (drop i (stack checkpoint)) with
  | S.Nil ->
      (* [i] is out of range. This could happen if the handwritten error
         messages are out of sync with the grammar, or if a mistake was
         made. We fail in a non-fatal way. *)
      raise Not_found
  | S.Cons (e, _) ->
      e
(*- #End *)

(* -------------------------------------------------------------------------- *)

(* [range text e] converts the stack element [e] to the fragment of the source
   text that corresponds to this stack element. The fragment is placed within
   single quotes and shortened if it is too long. We also ensure that it does
   not contain any special characters. *)

(*- E_COMPCERT_CODE_ErrorReports_width_001 *)
(*- #Justify_Derived "Utility constant" *)
let width = 30
(*- #End *)

(*- E_COMPCERT_CODE_ErrorReports_range_001 *)
(*- #Justify_Derived "Utility function" *)
let range text (e : element) : string =
  (* Extract the start and positions of this stack element. *)
  let Element (_, _, pos1, pos2) = e in
  (* Get the underlying source text fragment. *)
  let fragment = extract text (pos1, pos2) in
  (* Sanitize it and limit its length. Enclose it in single quotes. *)
  "'" ^ shorten width (sanitize (compress fragment)) ^ "'"
(*- #End *)

(* -------------------------------------------------------------------------- *)

(* We allow an error message to contain the special form $i, where is a 0-based
   index into the stack. We replace it with the fragment of the source text that
   corresponds to this stack entry. *)

(*- E_COMPCERT_CODE_ErrorReports_fragment_001 *)
(*- #Justify_Derived "Utility function" *)
let fragment text checkpoint message =
  try
    let i = int_of_string (Str.matched_group 1 message) in
    range text (element checkpoint i)
  with
  | Failure _ ->
      (* In principle, this should not happen, but if it does, let's cover up
         for our internal error. *)
      if debug then assert false else "???"
  | Not_found ->
      (* In principle, this should not happen, but if it does, let's cover up
         for our internal error. *)
      if debug then assert false else "???"
(*- #End *)

(*- E_COMPCERT_CODE_ErrorReports_fragments_001 *)
(*- #Justify_Derived "Utility function" *)
let fragments text checkpoint (message : string) : string =
  Str.global_substitute
    (Str.regexp "\\$\\([0-9]+\\)")
    (fragment text checkpoint)
    message
(*- #End *)

(* -------------------------------------------------------------------------- *)

(* [report text buffer checkpoint] constructs an error message. The C source
   code must be stored in the string [text]. The start and end positions of the
   last two tokens that were read must be stored in [buffer]. The parser state
   (i.e., the automaton's state and stack) must be recorded in the checkpoint
   [checkpoint]. *)

(* The start and end positions of the invalid token are [lexbuf.lex_start_p]
   and [lexbuf.lex_curr_p], since this is the last token that was read. But
   we need not care about that here. *)

(*- E_COMPCERT_CODE_ErrorReports_report_001 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_001 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_002 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_003 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_004 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_005 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_006 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_007 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_008 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_009 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_010 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_011 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_012 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_013 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_014 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_015 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_016 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_017 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_018 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_019 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_020 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_021 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_022 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_023 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_024 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_025 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_026 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_027 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_028 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_029 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_030 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_031 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_032 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_033 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_034 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_035 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_036 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_037 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_038 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_039 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_040 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_041 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_042 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_043 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_044 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_045 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_046 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_047 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_048 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_049 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_050 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_051 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_052 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_053 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_054 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_055 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_056 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_057 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_058 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_059 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_060 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_061 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_062 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_063 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_064 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_065 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_066 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_067 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_068 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_069 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_070 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_071 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_072 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_073 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_074 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_075 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_076 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_077 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_078 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_079 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_080 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_081 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_082 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_083 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_084 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_085 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_086 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_087 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_088 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_089 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_090 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_091 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_092 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_093 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_094 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_095 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_096 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_097 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_098 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_099 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_100 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_101 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_102 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_103 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_104 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_105 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_106 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_107 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_108 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_109 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_110 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_111 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_112 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_113 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_114 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_115 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_116 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_117 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_118 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_119 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_120 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_121 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_122 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_123 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_124 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_125 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_126 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_127 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_128 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_129 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_130 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_131 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_132 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_133 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_134 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_135 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_136 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_137 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_138 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_139 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_140 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_141 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_142 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_143 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_144 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_145 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_146 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_147 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_148 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_149 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_150 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_151 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_152 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_153 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_154 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_155 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_156 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_157 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_158 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_159 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_160 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_161 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_162 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_163 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_164 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_165 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_166 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_167 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_168 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_169 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_170 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_171 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_172 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_173 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_174 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_175 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_176 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_177 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_178 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_179 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_180 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_181 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_182 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_183 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_184 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_185 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_186 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_187 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_188 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_189 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_190 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_191 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_192 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_193 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_194 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_195 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_196 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_197 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_198 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_199 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_200 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_201 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_202 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_203 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_204 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_205 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_206 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_207 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_208 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_209 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_210 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_211 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_212 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_213 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_214 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_215 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_216 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_217 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_218 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_219 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_220 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_221 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_222 *)
(*- #Link_to E_COMPCERT_TR_Robustness_PREPARSER_223 *)
let report text buffer checkpoint : string =
  (* Extract the position where the error occurred, that is, the start
     position of the invalid token. We display it as a filename, a  (1-based)
     line number, and a (1-based) column number. *)
  let (pos, _) = last buffer in
  (* Construct a readable description of where the error occurred, that is,
     after which token and before which token. *)
  let where = show (extract text) buffer in
  (* Find out in which state the parser failed. *)
  let s : int = state checkpoint in
  (* Choose an error message, based on the state number [s].
     Then, customize it, based on dynamic information. *)
  let message = try
    Pre_parser_messages.message s |>
    fragments text checkpoint
  with Not_found ->
    (* If the state number cannot be found -- which, in principle,
       should not happen, since our list of erroneous states is
       supposed to be complete! -- produce a generic message. *)
    Printf.sprintf "This is an unknown syntax error (%d).\n\
                    Please report this problem to the compiler vendor.\n" s
  in
  (* Construct the full error message. *)
  Printf.sprintf "%s:%d:%d: syntax error %s.\n%s"
    pos.pos_fname
    pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1)
    where
    message
(*- #End *)
