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

open AST
open BinNums
open C
open Camlcoq

(* Types for the information of type info *)
type composite_field =
    {
     cfd_name:        string;
     cfd_atom:        atom option;
     cfd_anon:        bool;
     cfd_typ:         int;
     cfd_bit_size:    int option;
     cfd_bit_offset:  int option;
     cfd_byte_offset: int option;
     cfd_byte_size:   int option;
   }

type composite_type =
    {
     ct_name:        string;
     ct_sou:         struct_or_union;
     ct_file_loc:    location option;
     ct_members:     composite_field list;
     ct_sizeof:      int option;
     ct_declaration: bool;
   }

type arr_size = int64 option list

type typedef = {
    td_file_loc: location option;
    td_name:     string;
    typ:         int option;
  }

type enum_type = {
    enum_name:        string;
    enum_byte_size:   int option;
    enum_file_loc:    location option;
    enum_enumerators: (string * int64) list;
  }

type function_type = {
    fun_type_return_type: int option;
    fun_type_prototyped:  bool;
    fun_type_params:      (int * string) list;
  }

type debug_types =
  | IntegerType of ikind
  | FloatType of fkind
  | PointerType of int
  | ArrayType of int * arr_size
  | CompositeType of composite_type
  | EnumType of enum_type
  | FunctionType of function_type
  | Typedef of typedef
  | ConstType of int
  | VolatileType of int
  | Void

(* Types for global definitions *)

(* Information for a global variable *)
type global_variable_information = {
    gvar_name:        string;
    gvar_atom:        atom option;
    gvar_file_loc:    location;
    gvar_declaration: bool;
    gvar_external:    bool;
    gvar_type:        int;
  }

type parameter_information =
 {
  parameter_name:     string;
  parameter_ident:    int;
  parameter_atom:     atom option;
  parameter_type:     int;
}

type function_information = {
    fun_name:        string;
    fun_atom:        atom option;
    fun_file_loc:    location;
    fun_external:    bool;
    fun_return_type: int option; (* Again the special case of void functions *)
    fun_vararg:      bool;
    fun_parameter:   parameter_information list;
    fun_low_pc:      int option;
    fun_high_pc:     int option;
    fun_scope:       int option;
  }

type definition_type =
  | GlobalVariable of global_variable_information
  | Function of function_information


(* Information for local variables *)
type local_variable_information = {
    lvar_name:    string;
    lvar_atom:    atom option;
    lvar_file_loc:location;
    lvar_type:    int;
    lvar_static:  bool;  (* Static variables are mapped to symbols *)
  }

type local_information =
  | LocalVariable of local_variable_information
  | Scope of int list (* Variable and Scope ids *)


type scope_range =
    {
     start_addr: positive option;
     end_addr: positive option;
   }

type var_range =
    {
     range_start: positive option;
     range_end:   positive option;
     var_loc:     int * int builtin_arg;
   }

type var_location =
  | RangeLoc of var_range list
  | FunctionLoc of  int * int builtin_arg (* Stack allocated variables *)
