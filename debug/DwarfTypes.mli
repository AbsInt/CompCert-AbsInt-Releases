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

(* Types used for writing dwarf debug information *)

open Camlcoq
open Sections

(* Basic types for the value of attributes *)

(*- E_COMPCERT_CODE_DwarfTypes_constant_001 *)
(*- #Justify_Derived "Type definition" *)
type constant = int
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_flag_001 *)
(*- #Justify_Derived "Type definition" *)
type flag = bool
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_reference_001 *)
(*- #Justify_Derived "Type definition" *)
type reference = int
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_encoding_001 *)
(*- #Justify_Derived "Type definition" *)
type encoding =
  | DW_ATE_address
  | DW_ATE_boolean
  | DW_ATE_complex_float
  | DW_ATE_float
  | DW_ATE_signed
  | DW_ATE_signed_char
  | DW_ATE_unsigned
  | DW_ATE_unsigned_char
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_address_001 *)
(*- #Justify_Derived "Type definition" *)
type address = int
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_location_expression_001 *)
(*- #Justify_Derived "Type definition" *)
type location_expression =
  | DW_OP_plus_uconst of int64
  | DW_OP_bregx of constant * int64
  | DW_OP_piece of constant
  | DW_OP_bit_piece of constant * constant
  | DW_OP_reg of constant
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_location_value_001 *)
(*- #Justify_Derived "Type definition" *)
type location_value =
  | LocSymbol of atom
  | LocRef of address
  | LocSimple of location_expression
  | LocList of location_expression list
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_data_location_value_001 *)
(*- #Justify_Derived "Type definition" *)
type data_location_value =
  | DataLocBlock of location_expression
  | DataLocRef of reference
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_bound_value_001 *)
(*- #Justify_Derived "Type definition" *)
type bound_value =
  | BoundConst of constant
  | BoundRef of reference
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_string_const_001 *)
(*- #Justify_Derived "Type definition" *)
type string_const =
  | Simple_string of string
  | Offset_string of reference * string
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_file_loc_001 *)
(*- #Justify_Derived "Type definition" *)
type file_loc =
  | Diab_file_loc of constant * constant
  | Gnu_file_loc of constant * constant
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_dw_form_001 *)
(*- #Justify_Derived "Type definition" *)
type dw_form =
  | DW_FORM_addr
  | DW_FORM_data4
  | DW_FORM_data8
  | DW_FORM_string
  | DW_FORM_block
  | DW_FORM_data1
  | DW_FORM_flag
  | DW_FORM_sdata
  | DW_FORM_strp
  | DW_FORM_udata
  | DW_FORM_ref_addr
  | DW_FORM_ref4
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_dw_range_001 *)
(*- #Justify_Derived "Type definition" *)
type dw_range =
  | Pc_pair of reference * reference (* Simple low,high pc *)
  | Offset of constant (* DWARF 3 version for different range *)
  | Empty (* Needed for compilation units only containing variables *)
(*- #End *)

(* Types representing the attribute information per tag value *)

(*- E_COMPCERT_CODE_DwarfTypes_dw_tag_base_type_001 *)
(*- #Justify_Derived "Type definition" *)
type dw_tag_base_type =
    {
     base_type_byte_size: constant;
     base_type_encoding:  encoding      option;
     base_type_name:      string_const;
   }
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_dw_tag_compile_unit_001 *)
(*- #Justify_Derived "Type definition" *)
type dw_tag_compile_unit =
    {
     compile_unit_name:      string_const;
     compile_unit_range:     dw_range;
     compile_unit_dir:       string_const;
     compile_unit_prod_name: string_const;
   }
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_dw_tag_enumeration_type_001 *)
(*- #Justify_Derived "Type definition" *)
type dw_tag_enumeration_type =
    {
     enumeration_file_loc:    file_loc     option;
     enumeration_byte_size:   constant;
     enumeration_declaration: flag         option;
     enumeration_name:        string_const;
   }
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_dw_tag_enumerator_001 *)
(*- #Justify_Derived "Type definition" *)
type dw_tag_enumerator =
    {
     enumerator_value:    constant;
     enumerator_name:     string_const;
   }
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_dw_tag_formal_parameter_001 *)
(*- #Justify_Derived "Type definition" *)
type dw_tag_formal_parameter =
    {
     formal_parameter_artificial:         flag           option;
     formal_parameter_name:               string_const   option;
     formal_parameter_type:               reference;
     formal_parameter_variable_parameter: flag           option;
     formal_parameter_location:           location_value option;
   }
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_dw_tag_member_001 *)
(*- #Justify_Derived "Type definition" *)
type dw_tag_member =
    {
     member_byte_size:            int64               option;
     member_bit_offset:           int64               option;
     member_bit_size:             constant            option;
     member_data_member_location: data_location_value option;
     member_declaration:          flag                option;
     member_name:                 string_const        option;
     member_type:                 reference;
   }
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_dw_tag_structure_type_001 *)
(*- #Justify_Derived "Type definition" *)
type dw_tag_structure_type =
    {
     structure_file_loc:    file_loc     option;
     structure_byte_size:   int64        option;
     structure_declaration: flag         option;
     structure_name:        string_const option;
   }
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_dw_tag_subprogram_001 *)
(*- #Justify_Derived "Type definition" *)
type dw_tag_subprogram =
    {
     subprogram_file_loc:   file_loc;
     subprogram_external:   flag          option;
     subprogram_name:       string_const;
     subprogram_prototyped: flag;
     subprogram_type:       reference     option;
     subprogram_range:      dw_range;
   }
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_dw_tag_subrange_type_001 *)
(*- #Justify_Derived "Type definition" *)
type dw_tag_subrange_type =
    {
     subrange_type:        reference;
     subrange_upper_bound: bound_value option;
   }
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_dw_tag_subroutine_type_001 *)
(*- #Justify_Derived "Type definition" *)
type dw_tag_subroutine_type =
    {
     subroutine_type:       reference option;
     subroutine_prototyped: flag;
   }
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_dw_tag_typedef_001 *)
(*- #Justify_Derived "Type definition" *)
type dw_tag_typedef =
    {
     typedef_file_loc: file_loc option;
     typedef_name:     string_const;
     typedef_type:     reference;
   }
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_dw_tag_union_type_001 *)
(*- #Justify_Derived "Type definition" *)
type dw_tag_union_type =
    {
     union_file_loc:    file_loc     option;
     union_byte_size:   int64        option;
     union_declaration: flag         option;
     union_name:        string_const option;
   }
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_dw_tag_variable_001 *)
(*- #Justify_Derived "Type definition" *)
type dw_tag_variable =
    {
     variable_file_loc:    file_loc;
     variable_declaration: flag           option;
     variable_external:    flag           option;
     variable_name:        string_const;
     variable_type:        reference;
     variable_location:    location_value option;
   }
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_dw_tag_001 *)
(*- #Justify_Derived "Type definition" *)
type dw_tag =
  | DW_TAG_array_type of reference
  | DW_TAG_base_type of dw_tag_base_type
  | DW_TAG_compile_unit of dw_tag_compile_unit
  | DW_TAG_const_type of reference
  | DW_TAG_enumeration_type of dw_tag_enumeration_type
  | DW_TAG_enumerator of dw_tag_enumerator
  | DW_TAG_formal_parameter of dw_tag_formal_parameter
  | DW_TAG_lexical_block of dw_range
  | DW_TAG_member of dw_tag_member
  | DW_TAG_pointer_type of reference
  | DW_TAG_structure_type of dw_tag_structure_type
  | DW_TAG_subprogram of dw_tag_subprogram
  | DW_TAG_subrange_type of dw_tag_subrange_type
  | DW_TAG_subroutine_type of dw_tag_subroutine_type
  | DW_TAG_typedef of dw_tag_typedef
  | DW_TAG_union_type of dw_tag_union_type
  | DW_TAG_unspecified_parameter of flag option
  | DW_TAG_variable of dw_tag_variable
  | DW_TAG_volatile_type of reference
(*- #End *)

(* The type of the entries. *)

(*- E_COMPCERT_CODE_DwarfTypes_dw_entry_001 *)
(*- #Justify_Derived "Type definition" *)
type dw_entry =
    {
     tag:      dw_tag;
     children: dw_entry list;
     id:       reference;
   }
(*- #End *)

(* The type for the location list. *)

(*- E_COMPCERT_CODE_DwarfTypes_location_entry_001 *)
(*- #Justify_Derived "Type definition" *)
type location_entry =
  {
    loc:     (address * address * location_value) list;
    loc_id:  reference;
    loc_sec_begin :  address option;
  }
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_dw_locations_001 *)
(*- #Justify_Derived "Type definition" *)
type dw_locations = location_entry list
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_range_entry_001 *)
(*- #Justify_Derived "Type definition" *)
type range_entry =
  | AddressRange  of (address * address) list
  | OffsetRange of reference * (address * address) list
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_dw_ranges_001 *)
(*- #Justify_Derived "Type definition" *)
type dw_ranges = (int * range_entry) list
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_dw_string_001 *)
(*- #Justify_Derived "Type definition" *)
type dw_string = (int * string) list
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_diab_entry_001 *)
(*- #Justify_Derived "Type definition" *)
type diab_entry =
    {
     section_name: string;
     start_label:  int;
     line_label:   int;
     diab_entry:   dw_entry;
     diab_locs:    dw_locations;
   }
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_diab_entries_001 *)
(*- #Justify_Derived "Type definition" *)
type diab_entries =  diab_entry list
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_gnu_entries_001 *)
(*- #Justify_Derived "Type definition" *)
type gnu_entries =
  {
    string_table: dw_string;
    range_table:  dw_ranges;
    gnu_locs:     dw_locations;
    gnu_entry:    dw_entry;
    several_secs: bool;
  }
(*- #End *)

(*- E_COMPCERT_CODE_DwarfTypes_debug_entries_001 *)
(*- #Justify_Derived "Type definition" *)
type debug_entries =
  | Diab of diab_entries
  | Gnu of gnu_entries
(*- #End *)

(* The target specific functions for printing the debug information *)

(*- E_COMPCERT_CODE_DwarfTypes_Module_DWARF_TARGET_001 *)
(*- #Justify_Derived "Type definition" *)
module type DWARF_TARGET =
  sig
    val label: out_channel -> int -> unit
    val section: out_channel -> section_name -> unit
    val symbol: out_channel -> atom -> unit
    val comment: string
    val address: string
  end
(*- #End *)
