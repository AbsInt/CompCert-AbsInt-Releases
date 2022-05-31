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

(* Utility functions for the dwarf debugging type *)

open DwarfTypes

(* Generate a new entry from a given tag *)
(*- E_COMPCERT_CODE_DwarfUtil_new_entry_001 *)
(*- #Justify_Derived "Utility function" *)
let new_entry id tag =
  {
   tag = tag;
   children = [];
   id = id;
 }
(*- #End *)

(* Add an entry as child to another entry *)
(*- E_COMPCERT_CODE_DwarfUtil_add_child_001 *)
(*- #Justify_Derived "Utility function" *)
let add_child entry child =
  {entry with children = child::entry.children;}
(*- #End *)

(* Add entries as children to another entry *)
(*- E_COMPCERT_CODE_DwarfUtil_add_children_001 *)
(*- #Justify_Derived "Utility function" *)
let add_children entry children =
  {entry with children = entry.children@children;}
(*- #End *)

(*- E_COMPCERT_CODE_DwarfUtil_list_iter_with_next_001 *)
(*- #Justify_Derived "Utility function" *)
let list_iter_with_next f list =
  let rec aux = (function
    | [] -> ()
    | [a] -> f None a
    | a::b::rest -> f (Some b.id) a; aux (b::rest)) in
  aux list
(*- #End *)

(* Iter over the tree and pass the sibling id *)
(*- E_COMPCERT_CODE_DwarfUtil_entry_iter_sib_001 *)
(*- #Justify_Derived "Utility function" *)
let entry_iter_sib f g entry =
  let rec aux sib entry =
    f sib entry;
    list_iter_with_next aux entry.children;
    g entry in
  aux None entry
(*- #End *)

(* Fold over the tree in prefix order *)
(*- E_COMPCERT_CODE_DwarfUtil_entry_fold_001 *)
(*- #Justify_Derived "Utility function" *)
let rec entry_fold f acc entry =
  let acc = f acc entry.tag in
  List.fold_left (entry_fold f) acc entry.children
(*- #End *)

(* Return the code and the corresponding comment for a DW_FORM *)
(*- E_COMPCERT_CODE_DwarfUtil_code_of_dw_form_001 *)
(*- #Justify_Derived "Utility function" *)
let code_of_dw_form = function
  | DW_FORM_addr -> 0x01,"DW_FORM_addr"
  | DW_FORM_block2 -> 0x03,"DW_FORM_block2"
  | DW_FORM_block4 -> 0x04,"DW_FORM_block4"
  | DW_FORM_data2 -> 0x05,"DW_FORM_data2"
  | DW_FORM_data4 -> 0x06,"DW_FORM_data4"
  | DW_FORM_data8 -> 0x07,"DW_FORM_data8"
  | DW_FORM_string -> 0x08,"DW_FORM_string"
  | DW_FORM_block -> 0x09,"DW_FORM_block"
  | DW_FORM_block1 -> 0x0a,"DW_FORM_block1"
  | DW_FORM_data1 -> 0x0b,"DW_FORM_data1"
  | DW_FORM_flag -> 0x0c,"DW_FORM_flag"
  | DW_FORM_sdata -> 0x0d,"DW_FORM_sdata"
  | DW_FORM_strp -> 0x0e,"DW_FORM_strp"
  | DW_FORM_udata -> 0x0f,"DW_FORM_udata"
  | DW_FORM_ref_addr -> 0x10,"DW_FORM_ref_addr"
  | DW_FORM_ref1 -> 0x11,"DW_FORM_ref1"
  | DW_FORM_ref2 -> 0x12,"DW_FORM_ref2"
  | DW_FORM_ref4 -> 0x13,"DW_FORM_ref4"
  | DW_FORM_ref8 -> 0x14,"DW_FORM_ref8"
  | DW_FORM_ref_udata -> 0x15,"DW_FORM_ref_udata"
  | DW_FORM_ref_indirect -> 0x16,"DW_FORM_ref_indirect"
(*- #End *)

(* Attribute form encoding *)
(*- E_COMPCERT_CODE_DwarfUtil_form_encodings_001 *)
(*- #Justify_Derived "Utility function" *)
let dw_form_addr     = 0x01
let dw_form_block2   = 0x03
let dw_form_block4   = 0x04
let dw_form_data2    = 0x05
let dw_form_data4    = 0x06
let dw_form_data8    = 0x07
let dw_form_string   = 0x08
let dw_form_block    = 0x09
let dw_form_block1   = 0x0a
let dw_form_data1    = 0x0b
let dw_form_flag     = 0x0c
let dw_form_sdata    = 0x0d
let dw_form_strp     = 0x0e
let dw_form_udata    = 0x0f
let dw_form_ref_addr = 0x10
let dw_form_ref1     = 0x11
let dw_form_ref2     = 0x12
let dw_form_ref4     = 0x13
let dw_form_ref8     = 0x14
let dw_ref_udata     = 0x15
let dw_ref_indirect  = 0x16
(*- #End *)

(* Operation encoding *)
(*- E_COMPCERT_CODE_DwarfUtil_operation_encodingst_001 *)
(*- #Justify_Derived "Utility function" *)
let dw_op_addr = 0x3
let dw_op_plus_uconst = 0x23
let dw_op_reg0 = 0x50
let dw_op_regx = 0x90
let dw_op_bregx = 0x92
let dw_op_piece = 0x93
(*- #End *)

(* Tag to string function *)
(*- E_COMPCERT_CODE_DwarfUtil_string_of_dw_tag_001 *)
(*- #Justify_Derived "Utility function" *)
let string_of_dw_tag = function
  | DW_TAG_array_type _ -> "DW_TAG_array_type"
  | DW_TAG_compile_unit _ -> "DW_TAG_compile_unit"
  | DW_TAG_base_type _ -> "DW_TAG_base_type"
  | DW_TAG_const_type _ -> "DW_TAG_const_type"
  | DW_TAG_enumeration_type _ -> "DW_TAG_enumeration_type"
  | DW_TAG_enumerator _ -> "DW_TAG_enumerator"
  | DW_TAG_formal_parameter _ -> "DW_TAG_formal_parameter"
  | DW_TAG_label _ -> "DW_TAG_label"
  | DW_TAG_lexical_block _ -> "DW_TAG_lexical_block"
  | DW_TAG_member _ -> "DW_TAG_member"
  | DW_TAG_pointer_type _ -> "DW_TAG_pointer_type"
  | DW_TAG_structure_type _ -> "DW_TAG_structure_type"
  | DW_TAG_subprogram _ -> "DW_TAG_subprogram"
  | DW_TAG_subrange_type _ -> "DW_TAG_subrange_type"
  | DW_TAG_subroutine_type _ -> "DW_TAG_subroutine_type"
  | DW_TAG_typedef _ -> "DW_TAG_typedef"
  | DW_TAG_union_type _ -> "DW_TAG_union_type"
  | DW_TAG_unspecified_parameter _ -> "DW_TAG_unspecified_parameter"
  | DW_TAG_variable _ -> "DW_TAG_variable"
  | DW_TAG_volatile_type _ -> "DW_TAG_volatile_type"
(*- #End *)

(* Sizeof functions for the encoding of uleb128 and sleb128 *)
(*- E_COMPCERT_CODE_DwarfUtil_sizeof_uleb128_001 *)
(*- #Justify_Derived "Utility function" *)
let sizeof_uleb128 value =
  let size = ref 1 in
  let value = ref (value lsr 7) in
  while !value <> 0 do
    value := !value lsr 7;
    incr size;
  done;
  !size
(*- #End *)

(*- E_COMPCERT_CODE_DwarfUtil_sizeof_sleb128_001 *)
(*- #Justify_Derived "Utility function" *)
let sizeof_sleb128 value =
  let size = ref 1 in
  let byte = ref (value land 0x7f) in
  let value = ref (value lsr 7) in
  while not ((!value = 0 && (!byte land 0x40) = 0) || (!value = -1 && ((!byte land 0x40) <> 0))) do
    byte := !value land 0x7f;
    value := !value lsr 7;
    incr size;
  done;
  !size
(*- #End *)

(*- E_COMPCERT_CODE_DwarfUtil_size_of_loc_expr_001 *)
(*- #Justify_Derived "Utility function" *)
let size_of_loc_expr = function
  | DW_OP_bregx (a,b) -> 1 + (sizeof_uleb128 a)  + (sizeof_sleb128 (Int32.to_int b))
  | DW_OP_plus_uconst a
  | DW_OP_piece a -> 1 + (sizeof_uleb128 a)
  | DW_OP_reg i -> if i < 32 then 1 else  1 + (sizeof_uleb128 i)
(*- #End *)
