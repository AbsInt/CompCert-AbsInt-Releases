(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Print lines from a file *)

(*- E_COMPCERT_CODE_Printlines_filebuf_001 *)
(*- #Justify_Derived "Type definition" *)
type filebuf = {
  chan: in_channel;
  mutable lineno: int                   (* current line number *)
}
(*- #End *)


(* Invariant: the current position of [b.chan] is
   the first character of line number [b.lineno]. *)

(*- E_COMPCERT_CODE_Printlines_openfile_001 *)
(*- #Justify_Derived "Utility function" *)
let openfile f =
  { chan = open_in f;
    lineno = 1 }
(*- #End *)

(*- E_COMPCERT_CODE_Printlines_close_001 *)
(*- #Justify_Derived "Utility function" *)
let close b =
  close_in b.chan
(*- #End *)


(* Position [b] to the beginning of line [dest], which must be greater
   or equal to the current line.
   Return [true] if success, [false] if this line does not exist. *)

(*- E_COMPCERT_CODE_Printlines_forward_001 *)
(*- #Justify_Derived "Utility function" *)
let forward b dest =
  assert (dest >= b.lineno);
  try
    while b.lineno <> dest do
      let c = input_char b.chan in
      if c = '\n' then b.lineno <- b.lineno + 1;
    done;
    true
  with End_of_file ->
    false
(*- #End *)


(* Position [b] to the beginning of line [dest], which must be less than
   the current line. *)

(*- E_COMPCERT_CODE_Printlines_backward_buf_001 *)
(*- #Justify_Derived "Utility constant" *)
let backward_buf = lazy (Bytes.create 65536)
  (* 65536 to match [IO_BUFFER_SIZE] in the OCaml runtime.
     lazy to allocate on demand. *)
(*- #End *)

(*- E_COMPCERT_CODE_Printlines_backward_001 *)
(*- #Justify_Derived "Utility function" *)
let backward b dest =
  assert (1 <= dest && dest < b.lineno);
  let buf = Lazy.force backward_buf in
  let rec backward pos idx =
    (* pos is the file position corresponding to index 0 in buf *)
    (* idx is the current index in buf *)
    if idx <= 0 then begin
      if pos = 0 then begin
        (* beginning of file reached = beginning of line 1. *)
        (* assert (dest = 1 && b.lineno = 1) *)
        seek_in b.chan 0;
        b.lineno <- 1
      end else begin
        let pos' = max 0 (pos - Bytes.length buf) in
        let len = pos - pos' in
        seek_in b.chan pos';
        really_input b.chan buf 0 len;
        backward pos' (pos - pos')
      end
    end else if Bytes.get buf (idx-1) = '\n' then begin
      (* Reached beginning of current line *)
      if b.lineno = dest then begin
        (* Found line number dest *)
        seek_in b.chan (pos + idx)
      end else begin
        (* Move into previous line *)
        b.lineno <- b.lineno - 1;
        backward pos (idx - 1)
      end
    end else
      backward pos (idx - 1)
  in
    backward (pos_in b.chan) 0
(*- #End *)


(* Absolute positioning *)

(*- E_COMPCERT_CODE_Printlines_move_001 *)
(*- #Justify_Derived "Utility function" *)
let move b dest =
  if dest >= b.lineno then forward b dest else (backward b dest; true)
(*- #End *)


(* Main function: copy lines from [first] to [last] to [oc], prefixed
   by [pref]. *)

(*- E_COMPCERT_CODE_Printlines_copy_001 *)
(*- #Justify_Derived "Utility function" *)
let copy oc pref b first last =
  if move b first then begin
    output_string oc pref;
    try
      while b.lineno <= last do
        let c = input_char b.chan in
        output_char oc c;
        if c = '\n' then begin
          b.lineno <- b.lineno + 1;
          if b.lineno <= last then output_string oc pref
        end
      done
    with End_of_file ->
      output_char oc '\n'
  end
(*- #End *)
