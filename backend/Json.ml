(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  AbsInt Angewandte Informatik GmbH. All rights reserved. This file  *)
(*  is distributed under the terms of the INRIA Non-Commercial         *)
(*  License Agreement.                                                 *)
(*                                                                     *)
(* *********************************************************************)

open Camlcoq


(* Simple functions for JSON printing *)

(* Print a string as json string *)
(*- E_COMPCERT_CODE_Json_pp_jstring_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_jstring oc s =
  output_string oc "\"";
  output_string oc s;
  output_string oc "\""
(*- #End *)

(* Print a bool as json bool *)
(*- E_COMPCERT_CODE_Json_pp_jbool_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_jbool oc b = output_string oc (string_of_bool b)
(*- #End *)

(* Print an int as json int *)
(*- E_COMPCERT_CODE_Json_pp_jint_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_jint oc i = output_string oc (string_of_int i)
(*- #End *)

(* Print an int32 as json int *)
(*- E_COMPCERT_CODE_Json_pp_jint32_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_jint32 oc i = output_string oc (Int32.to_string i)
(*- #End *)

(* Print an int64 as json int *)
(*- E_COMPCERT_CODE_Json_pp_jint64_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_jint64 oc i = output_string oc (Int64.to_string i)
(*- #End *)

(* Print optional value *)
(*- E_COMPCERT_CODE_Json_pp_jopt_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_jopt pp_elem oc = function
  | None -> output_string oc "null"
  | Some i -> pp_elem oc i
(*- #End *)

(* Print opening and closing curly braces for json dictionaries *)
(*- E_COMPCERT_CODE_Json_pp_jobject_start_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_jobject_start pp =
  output_string pp "\n{"
(*- #End *)

(*- E_COMPCERT_CODE_Json_pp_jobject_end_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_jobject_end pp =
  output_string pp "}"
(*- #End *)

(* Print a member of a json dictionary *)
(*- E_COMPCERT_CODE_Json_pp_jmember_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_jmember ?(first=false) pp name pp_mem mem =
  if not first then output_string pp ",";
  output_string pp " ";
  pp_jstring pp name;
  output_string pp " :";
  pp_mem pp mem;
  output_string pp "\n"
(*- #End *)

(* Print singleton object *)
(*- E_COMPCERT_CODE_Json_pp_jsingle_object_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_jsingle_object pp name pp_mem mem =
  pp_jobject_start pp;
  pp_jmember ~first:true pp name pp_mem mem;
  pp_jobject_end pp
(*- #End *)

(* Print a list as json array *)
(*- E_COMPCERT_CODE_Json_pp_jarray_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_jarray elem pp l =
  let pp_sep () = output_string pp ", " in
  output_string pp "[";
  begin match l with
  | []  -> ()
  | hd::tail ->
    elem pp hd;
    List.iter (fun l -> pp_sep (); elem pp l) tail;
  end;
  output_string pp "]"
(*- #End *)

(* Helper functions for printing coq integer and floats *)
(*- E_COMPCERT_CODE_Json_pp_int_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_int pp i =
  pp_jint32 pp (camlint_of_coqint i)
(*- #End *)

(*- E_COMPCERT_CODE_Json_pp_int64_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_int64 pp i =
  pp_jint64 pp (camlint64_of_coqint i)
(*- #End *)

(*- E_COMPCERT_CODE_Json_pp_float32_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_float32 pp f =
  pp_jint32 pp (camlint_of_coqint (Floats.Float32.to_bits f))
(*- #End *)

(*- E_COMPCERT_CODE_Json_pp_float64_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_float64 pp f =
  pp_jint64 pp (camlint64_of_coqint (Floats.Float.to_bits f))
(*- #End *)

(*- E_COMPCERT_CODE_Json_pp_z_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_z pp z =
  output_string pp (Z.to_string z)
(*- #End *)

(* Helper functions for printing assembler constructs *)
(*- E_COMPCERT_CODE_Json_pp_atom_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_atom pp a =
  pp_jstring pp (extern_atom a)
(*- #End *)

(*- E_COMPCERT_CODE_Json_pp_atom_constant_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_atom_constant pp a =
  pp_jsingle_object pp "Atom" pp_atom a
(*- #End *)

(*- E_COMPCERT_CODE_Json_pp_int_constant_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_int_constant pp i =
  pp_jsingle_object pp "Integer" pp_int i
(*- #End *)

(*- E_COMPCERT_CODE_Json_pp_float64_constant_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_float64_constant pp f =
  pp_jsingle_object pp "Float" pp_float64 f
(*- #End *)

(*- E_COMPCERT_CODE_Json_pp_float32_constant_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_float32_constant pp f =
  pp_jsingle_object pp "Float" pp_float32 f
(*- #End *)

(*- E_COMPCERT_CODE_Json_id_001 *)
(*- #Justify_Derived "Variable for global state" *)
let id = ref 0
(*- #End *)

(*- E_COMPCERT_CODE_Json_next_id_001 *)
(*- #Justify_Derived "Utility function" *)
let next_id () =
  let tmp = !id in
  incr id;
  tmp
(*- #End *)

(*- E_COMPCERT_CODE_Json_reset_id_001 *)
(*- #Justify_Derived "Utility function" *)
let reset_id () =
  id := 0
(*- #End *)

(*- E_COMPCERT_CODE_Json_pp_id_const_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_id_const pp () =
  let i = next_id () in
  pp_jsingle_object pp "Integer" pp_jint i
(*- #End *)
