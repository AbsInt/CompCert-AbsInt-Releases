(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Jacques-Henri Jourdan, INRIA Paris-Rocquencourt            *)
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

(*- E_COMPCERT_CODE_pre_parseraux_identifier_type_001 *)
(*- #Justify_Derived "Type definition" *)
type identifier_type =
  | VarId
  | TypedefId
  | OtherId
(*- #End *)

(*- E_COMPCERT_CODE_pre_parseraux_save_context_001 *)
(*- #Justify_Derived "Utility function" *)
let save_context:(unit -> (unit -> unit)) ref = ref (fun _ -> assert false)
(*- #End *)

(*- E_COMPCERT_CODE_pre_parseraux_declare_varname_001 *)
(*- #Justify_Derived "Utility function" *)
let declare_varname:(string -> unit) ref = ref (fun _ -> assert false)
(*- #End *)

(*- E_COMPCERT_CODE_pre_parseraux_declare_typename_001 *)
(*- #Justify_Derived "Utility function" *)
let declare_typename:(string -> unit) ref = ref (fun _ -> assert false)
(*- #End *)
