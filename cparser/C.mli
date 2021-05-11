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

(* C abstract syntax after elaboration *)

(* Locations *)

(*- E_COMPCERT_CODE_C_location_001 *)
(*- #Justify_Derived "Type definition" *)
type location = string * int            (* filename, line number *)
(*- #End *)

(* Identifiers *)

(*- E_COMPCERT_CODE_C_ident_001 *)
(*- #Justify_Derived "Type definition" *)
type ident =
  { name: string;                       (* name as in the source *)
    stamp: int }                        (* unique ID *)
(*- #End *)

(* Kinds of integers *)

(*- E_COMPCERT_CODE_C_ikind_001 *)
(*- #Justify_Derived "Type definition" *)
type ikind =
  | IBool       (** [_Bool] *)
  | IChar       (** [char] *)
  | ISChar      (** [signed char] *)
  | IUChar      (** [unsigned char] *)
  | IInt        (** [int] *)
  | IUInt       (** [unsigned int] *)
  | IShort      (** [short] *)
  | IUShort     (** [unsigned short] *)
  | ILong       (** [long] *)
  | IULong      (** [unsigned long] *)
  | ILongLong   (** [long long] (or [_int64] on Microsoft Visual C) *)
  | IULongLong  (** [unsigned long long] (or [unsigned _int64] on Microsoft
                    Visual C) *)
(*- #End *)

(** Kinds of floating-point numbers*)

(*- E_COMPCERT_CODE_C_fkind_001 *)
(*- #Justify_Derived "Type definition" *)
type fkind =
    FFloat      (** [float] *)
  | FDouble     (** [double] *)
  | FLongDouble (** [long double] *)
(*- #End *)

(** Constants *)

(*- E_COMPCERT_CODE_C_float_literal_001 *)
(*- #Justify_Derived "Type definition" *)
type float_literal = {
  hex : bool;
  intPart : string;
  fracPart : string;
  exp : string;
}
(*- #End *)

(*- E_COMPCERT_CODE_C_float_cst_001 *)
(*- #Justify_Derived "Type definition" *)
type float_cst =
  | FInfinity of bool (* infinity constant value with sign bit *)
  | FBits of int64 (* Float specified by bits *)
  | FConstant of float_literal
(*- #End *)

(*- E_COMPCERT_CODE_C_constant_001 *)
(*- #Justify_Derived "Type definition" *)
type constant =
  | CInt of int64 * ikind * string      (* as it appeared in the source *)
  | CFloat of float_cst * fkind
  | CStr of string
  | CWStr of int64 list
  | CEnum of ident * int64              (* enum tag, integer value *)
(*- #End *)

(** Attributes *)

(*- E_COMPCERT_CODE_C_attr_arg_001 *)
(*- #Justify_Derived "Type definition" *)
type attr_arg =
  | AIdent of string
  | AInt of int64
  | AString of string
(*- #End *)

(*- E_COMPCERT_CODE_C_attribute_001 *)
(*- #Justify_Derived "Type definition" *)
type attribute =
  | AConst
  | AVolatile
  | ARestrict
  | AAlignas of int                     (* always a power of 2 *)
  | Attr of string * attr_arg list
(*- #End *)

(*- E_COMPCERT_CODE_C_attributes_001 *)
(*- #Justify_Derived "Type definition" *)
type attributes = attribute list
(*- #End *)

(** Storage classes *)

(*- E_COMPCERT_CODE_C_storage_001 *)
(*- #Justify_Derived "Type definition" *)
type storage =
  | Storage_default (* used for toplevel names without explicit storage *)
  | Storage_extern
  | Storage_static
  | Storage_auto    (* used for block-scoped names without explicit storage *)
  | Storage_register
(*- #End *)

(** Unary operators *)

(*- E_COMPCERT_CODE_C_unary_operator_001 *)
(*- #Justify_Derived "Type definition" *)
type unary_operator =
  | Ominus	(* unary "-" *)
  | Oplus	(* unary "+" *)
  | Olognot	(* "!" *)
  | Onot        (* "~" *)
  | Oderef      (* unary "*" *)
  | Oaddrof     (* "&" *)
  | Opreincr    (* "++" prefix *)
  | Opredecr    (* "--" prefix *)
  | Opostincr   (* "++" postfix *)
  | Opostdecr   (* "--" postfix *)
  | Odot of string (* ".field" *)
  | Oarrow of string (* "->field" *)
(*- #End *)

(*- E_COMPCERT_CODE_C_binary_operator_001 *)
(*- #Justify_Derived "Type definition" *)
type binary_operator =
  | Oadd        (* binary "+" *)
  | Osub        (* binary "-" *)
  | Omul        (* binary "*" *)
  | Odiv        (* "/" *)
  | Omod        (* "%" *)
  | Oand        (* "&" *)
  | Oor         (* "|" *)
  | Oxor        (* "^" *)
  | Oshl        (* "<<" *)
  | Oshr        (* ">>" *)
  | Oeq         (* "==" *)
  | One         (* "!=" *)
  | Olt         (* "<" *)
  | Ogt         (* ">" *)
  | Ole         (* "<=" *)
  | Oge         (* ">=" *)
  | Oindex      (* "a[i]" *)
  | Oassign     (* "=" *)
  | Oadd_assign (* "+=" *)
  | Osub_assign (* "-=" *)
  | Omul_assign (* "*=" *)
  | Odiv_assign (* "/=" *)
  | Omod_assign (* "%=" *)
  | Oand_assign (* "&=" *)
  | Oor_assign  (* "|=" *)
  | Oxor_assign (* "^=" *)
  | Oshl_assign (* "<<=" *)
  | Oshr_assign (* ">>=" *)
  | Ocomma      (* "," *)
  | Ologand     (* "&&" *)
  | Ologor      (* "||" *)
(*- #End *)

(** Types *)

(*- E_COMPCERT_CODE_C_typ_001 *)
(*- #Justify_Derived "Type definition" *)
type typ =
  | TVoid of attributes
  | TInt of ikind * attributes
  | TFloat of fkind * attributes
  | TPtr of typ * attributes
  | TArray of typ * int64 option * attributes
  | TFun of typ * (ident * typ) list option * bool * attributes
  | TNamed of ident * attributes
  | TStruct of ident * attributes
  | TUnion of ident * attributes
  | TEnum of ident * attributes
(*- #End *)

(** Struct or union field *)

(*- E_COMPCERT_CODE_C_field_001 *)
(*- #Justify_Derived "Type definition" *)
type field = {
    fld_name: string;
    fld_typ: typ;
    fld_bitfield: int option;
    fld_anonymous: bool;
}
(*- #End *)

(*- E_COMPCERT_CODE_C_struct_or_union_001 *)
(*- #Justify_Derived "Type definition" *)
type struct_or_union =
  | Struct
  | Union
(*- #End *)

(** Expressions *)

(*- E_COMPCERT_CODE_C_exp_001 *)
(*- #Justify_Derived "Type definition" *)
type exp = { edesc: exp_desc; etyp: typ }
(*- #End *)

(*- E_COMPCERT_CODE_C_exp_002 *)
(*- #Justify_Derived "Type definition" *)
and exp_desc =
  | EConst of constant
  | ESizeof of typ
  | EAlignof of typ
  | EVar of ident
  | EUnop of unary_operator * exp
  | EBinop of binary_operator * exp * exp * typ
                           (* the type at which the operation is performed *)
  | EConditional of exp * exp * exp
  | ECast of typ * exp
  | ECompound of typ * init
  | ECall of exp * exp list
(*- #End *)

(** Initializers *)

(*- E_COMPCERT_CODE_C_init_001 *)
(*- #Justify_Derived "Type definition" *)
and init =
  | Init_single of exp
  | Init_array of init list
  | Init_struct of ident * (field * init) list
  | Init_union of ident * field * init
(*- #End *)

(** GCC extended asm *)

(*- E_COMPCERT_CODE_C_asm_operand_001 *)
(*- #Justify_Derived "Type definition" *)
type asm_operand = string option * string * exp
(*- #End *)

(** Statements *)

(*- E_COMPCERT_CODE_C_stmt_001 *)
(*- #Justify_Derived "Type definition" *)
type stmt = { sdesc: stmt_desc; sloc: location }
(*- #End *)

(*- E_COMPCERT_CODE_C_stmt_002 *)
(*- #Justify_Derived "Type definition" *)
and stmt_desc =
  | Sskip
  | Sdo of exp
  | Sseq of stmt * stmt
  | Sif of exp * stmt * stmt
  | Swhile of exp * stmt
  | Sdowhile of stmt * exp
  | Sfor of stmt * exp * stmt * stmt
  | Sbreak
  | Scontinue
  | Sswitch of exp * stmt
  | Slabeled of slabel * stmt
  | Sgoto of string
  | Sreturn of exp option
  | Sblock of stmt list
  | Sdecl of decl
  | Sasm of attributes * string * asm_operand list * asm_operand list * string list
(*- #End *)

(*- E_COMPCERT_CODE_C_slabel_001 *)
(*- #Justify_Derived "Type definition" *)
and slabel =
  | Slabel of string
  | Scase of exp * int64
  | Sdefault
(*- #End *)

(** Declarations *)

(*- E_COMPCERT_CODE_C_decl_001 *)
(*- #Justify_Derived "Type definition" *)
and decl =
  storage * ident * typ * init option
(*- #End *)

(** Function definitions *)

(*- E_COMPCERT_CODE_C_fundef_001 *)
(*- #Justify_Derived "Type definition" *)
type fundef = {
    fd_storage: storage;
    fd_inline: bool;
    fd_name: ident;
    fd_attrib: attributes;
    fd_ret: typ;                   (* return type *)
    fd_params: (ident * typ) list; (* formal parameters *)
    fd_vararg: bool;               (* variable arguments? *)
    fd_locals: decl list;          (* local variables *)
    fd_body: stmt
}
(*- #End *)

(** Element of an enumeration *)

(*- E_COMPCERT_CODE_C_enumerator_001 *)
(*- #Justify_Derived "Type definition" *)
type enumerator = ident * int64 * exp option
(*- #End *)

(** Global declarations *)

(*- E_COMPCERT_CODE_C_globdecl_001 *)
(*- #Justify_Derived "Type definition" *)
type globdecl =
  { gdesc: globdecl_desc; gloc: location }
(*- #End *)

(*- E_COMPCERT_CODE_C_globdecl_002 *)
(*- #Justify_Derived "Type definition" *)
and globdecl_desc =
  | Gdecl of decl           (* variable declaration, function prototype *)
  | Gfundef of fundef                   (* function definition *)
  | Gcompositedecl of struct_or_union * ident * attributes
                                        (* struct/union declaration *)
  | Gcompositedef of struct_or_union * ident * attributes * field list
                                        (* struct/union definition *)
  | Gtypedef of ident * typ             (* typedef *)
  | Genumdef of ident * attributes * enumerator list
                                        (* enum definition *)
  | Gpragma of string                   (* #pragma directive *)
(*- #End *)

(*- E_COMPCERT_CODE_C_program_001 *)
(*- #Justify_Derived "Type definition" *)
type program = globdecl list
(*- #End *)

(** Builtin types and functions *)

(*- E_COMPCERT_CODE_C_builtins_001 *)
(*- #Justify_Derived "Type definition" *)
type builtins = {
  builtin_typedefs: (string * typ) list;
  builtin_functions: (string * (typ * typ list * bool)) list
}
(*- #End *)
