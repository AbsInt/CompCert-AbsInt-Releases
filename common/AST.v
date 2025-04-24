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

(** This file defines a number of data types and operations used in
  the abstract syntax trees of many of the intermediate languages. *)

Require Import String.
Require Import Coqlib Maps Errors Integers Floats.
Require Archi.

Set Implicit Arguments.

(** * Syntactic elements *)

(** Identifiers (names of local variables, of global symbols and functions,
  etc) are represented by the type [positive] of positive integers. *)

(*- E_COMPCERT_FTR_Function_AST_ident_001 *)
(*- #Justify_Derived "Internal type" *)
Definition ident := positive.
(*- #End *)

(*- E_COMPCERT_FTR_Function_AST_ident_eq_001 *)
(*- #Justify_Derived "Internal function" *)
Definition ident_eq := peq.
(*- #End *)

(** The intermediate languages are weakly typed, using the following types: *)

(*- E_COMPCERT_FTR_Function_AST_typ_0_001 *)
(*- #Justify_Derived "Internal type" *)
Inductive typ : Type :=
  | Tint                (**r 32-bit integers or pointers *)
  | Tfloat              (**r 64-bit double-precision floats *)
  | Tlong               (**r 64-bit integers *)
  | Tsingle             (**r 32-bit single-precision floats *)
  | Tany32              (**r any 32-bit value *)
  | Tany64.             (**r any 64-bit value, i.e. any value *)
(*- #End *)

Lemma typ_eq: forall (t1 t2: typ), {t1=t2} + {t1<>t2}.
Proof. decide equality. Defined.
Global Opaque typ_eq.

Definition list_typ_eq: forall (l1 l2: list typ), {l1=l2} + {l1<>l2}
                     := list_eq_dec typ_eq.

(*- E_COMPCERT_FTR_Function_AST_Tptr_001 *)
(*- #Justify_Derived "Internal type" *)
Definition Tptr : typ := if Archi.ptr64 then Tlong else Tint.
(*- #End *)

Definition typesize (ty: typ) : Z :=
  match ty with
  | Tint => 4
  | Tfloat => 8
  | Tlong => 8
  | Tsingle => 4
  | Tany32 => 4
  | Tany64 => 8
  end.

Lemma typesize_pos: forall ty, typesize ty > 0.
Proof. destruct ty; simpl; lia. Qed.

Lemma typesize_Tptr: typesize Tptr = if Archi.ptr64 then 8 else 4.
Proof. unfold Tptr; destruct Archi.ptr64; auto. Qed.

(** All values of size 32 bits are also of type [Tany32].  All values
  are of type [Tany64].  This corresponds to the following subtyping
  relation over types. *)

Definition subtype (ty1 ty2: typ) : bool :=
  match ty1, ty2 with
  | Tint, Tint => true
  | Tlong, Tlong => true
  | Tfloat, Tfloat => true
  | Tsingle, Tsingle => true
  | (Tint | Tsingle | Tany32), Tany32 => true
  | _, Tany64 => true
  | _, _ => false
  end.

Fixpoint subtype_list (tyl1 tyl2: list typ) : bool :=
  match tyl1, tyl2 with
  | nil, nil => true
  | ty1::tys1, ty2::tys2 => subtype ty1 ty2 && subtype_list tys1 tys2
  | _, _ => false
  end.

(** To describe function arguments and function return values,
    we use the more precise types below. *)

(*- E_COMPCERT_FTR_Function_AST_xtype_0_001 *)
(*- #Justify_Derived "Internal type" *)
Inductive xtype : Type :=
  | Xbool               (**r Boolean value (0 or 1) *)
  | Xint8signed         (**r 8-bit signed integer *)
  | Xint8unsigned       (**r 8-bit unsigned integer *)
  | Xint16signed        (**r 16-bit signed integer *)
  | Xint16unsigned      (**r 16-bit unsigned integer *)
  | Xint                (**r 32-bit integers or pointers *)
  | Xfloat              (**r 64-bit double-precision floats *)
  | Xlong               (**r 64-bit integers *)
  | Xsingle             (**r 32-bit single-precision floats *)
  | Xptr                (**r pointers and pointer-sized integers *)
  | Xany32              (**r any 32-bit value *)
  | Xany64              (**r any 64-bit value, i.e. any value *)
  | Xvoid.              (**r no meaningful value *)
(*- #End *)

(*- E_COMPCERT_FTR_Function_AST_Xsize_t_001 *)
(*- #Justify_Derived "Auxiliary definition" *)
Definition Xsize_t := if Archi.ptr64 then Xlong else Xint.
(*- #End *)

(*- E_COMPCERT_FTR_Function_AST_xtype_eq_001 *)
(*- #Justify_Derived "Auxiliary definition" *)
Lemma xtype_eq: forall (t1 t2: xtype), {t1=t2} + {t1<>t2}.
Proof. decide equality. Defined.
Global Opaque xtype_eq.
(*- #End *)

(*- E_COMPCERT_FTR_Function_AST_inj_type_001 *)
(*- #Justify_Derived "Internal function" *)
Definition inj_type (t: typ) : xtype :=
  match t with
  | Tint => Xint
  | Tfloat => Xfloat
  | Tlong => Xlong
  | Tsingle => Xsingle
  | Tany32 => Xany32
  | Tany64 => Xany64
  end.
(*- #End *)

(*- E_COMPCERT_FTR_Function_AST_proj_xtype_001 *)
(*- #Justify_Derived "Internal function" *)
Definition proj_xtype (x: xtype) : typ :=
  match x with
  | Xbool | Xint8signed | Xint8unsigned | Xint16signed | Xint16unsigned | Xint => Tint
  | Xfloat => Tfloat
  | Xlong => Tlong
  | Xsingle => Tsingle
  | Xptr => Tptr
  | Xany32 => Tany32
  | Xany64 => Tany64
  | Xvoid => Tint
  end.
(*- #End *)

Lemma proj_inj_type: forall t, proj_xtype (inj_type t) = t.
Proof.
  destruct t; auto.
Qed.

(** Additionally, function definitions and function calls are annotated
  by function signatures indicating:
- the number and types of arguments;
- the type of the returned value;
- additional information on which calling convention to use.

These signatures are used in particular to determine appropriate
calling conventions for the function. *)

(*- E_COMPCERT_FTR_Function_AST_calling_convention_0_001 *)
(*- #Justify_Derived "Internal type" *)
Record calling_convention : Type := mkcallconv {
  cc_vararg: option Z;  (**r variable-arity function (+ number of fixed args) *)
  cc_unproto: bool;     (**r old-style unprototyped function *)
  cc_structret: bool    (**r function returning a struct  *)
}.
(*- #End *)

(*- E_COMPCERT_FTR_Function_AST_cc_default_001 *)
(*- #Justify_Derived "Internal type" *)
Definition cc_default :=
  {| cc_vararg := None; cc_unproto := false; cc_structret := false |}.
(*- #End *)

(*- E_COMPCERT_FTR_Function_AST_calling_convention_eq_001 *)
(*- #Justify_Derived "Auxiliary definition" *)
Definition calling_convention_eq (x y: calling_convention) : {x=y} + {x<>y}.
Proof.
  decide equality; try (apply bool_dec). decide equality; apply Z.eq_dec.
Defined.
Global Opaque calling_convention_eq.
(*- #End *)

(*- E_COMPCERT_FTR_Function_AST_signature_0_001 *)
(*- #Justify_Derived "Internal type" *)
Record signature : Type := mksignature {
  sig_args: list xtype;
  sig_res: xtype;
  sig_cc: calling_convention
}.
(*- #End *)

(*- E_COMPCERT_FTR_Function_AST_proj_sig_args_001 *)
(*- #Justify_Derived "Internal function" *)
Definition proj_sig_args (s: signature) : list typ := List.map proj_xtype s.(sig_args).
(*- #End *)
(*- E_COMPCERT_FTR_Function_AST_proj_sig_res_001 *)
(*- #Justify_Derived "Internal function" *)
Definition proj_sig_res (s: signature) : typ := proj_xtype s.(sig_res).
(*- #End *)


(*- E_COMPCERT_FTR_Function_AST_signature_eq_001 *)
(*- #Justify_Derived "Auxiliary definition" *)
Definition signature_eq: forall (s1 s2: signature), {s1=s2} + {s1<>s2}.
Proof.
  generalize xtype_eq, list_eq_dec, calling_convention_eq; decide equality.
Defined.
Global Opaque signature_eq.
(*- #End *)

Declare Scope asttyp_scope.
Notation "[ ---> y ]" := (mksignature nil y cc_default) : asttyp_scope.
Notation "[ x ---> y ]" :=
  (mksignature (@cons xtype x nil) y cc_default) : asttyp_scope.
Notation "[ x1 ; x2 ; .. ; xn ---> y ]" :=
  (mksignature (@cons xtype x1 (@cons xtype x2 .. (@cons xtype xn nil) ..)) y cc_default) : asttyp_scope.

Delimit Scope asttyp_scope with asttyp.
Local Open Scope asttyp_scope.

Definition signature_main :=  [ ---> Xint].

(** Memory accesses (load and store instructions) are annotated by
  a ``memory chunk'' indicating the type, size and signedness of the
  chunk of memory being accessed. *)

(*- E_COMPCERT_FTR_Function_AST_memory_chunk_0_001 *)
(*- #Justify_Derived "Internal type" *)
Inductive memory_chunk : Type :=
  | Mbool           (**r 8-bit integer containing 0 or 1 *)
  | Mint8signed     (**r 8-bit signed integer *)
  | Mint8unsigned   (**r 8-bit unsigned integer *)
  | Mint16signed    (**r 16-bit signed integer *)
  | Mint16unsigned  (**r 16-bit unsigned integer *)
  | Mint32          (**r 32-bit integer, or pointer *)
  | Mint64          (**r 64-bit integer *)
  | Mfloat32        (**r 32-bit single-precision float *)
  | Mfloat64        (**r 64-bit double-precision float *)
  | Many32          (**r any value that fits in 32 bits *)
  | Many64.         (**r any value *)
(*- #End *)

Definition chunk_eq: forall (c1 c2: memory_chunk), {c1=c2} + {c1<>c2}.
Proof. decide equality. Defined.
Global Opaque chunk_eq.

(*- E_COMPCERT_FTR_Function_AST_Mptr_001 *)
(*- #Justify_Derived "Internal type" *)
Definition Mptr : memory_chunk := if Archi.ptr64 then Mint64 else Mint32.
(*- #End *)

(** The type (integer/pointer or float) of a chunk. *)

(*- E_COMPCERT_FTR_Function_AST_type_of_chunk_001 *)
(*- #Justify_Derived "Internal function" *)
Definition type_of_chunk (c: memory_chunk) : typ :=
  match c with
  | Mbool => Tint
  | Mint8signed => Tint
  | Mint8unsigned => Tint
  | Mint16signed => Tint
  | Mint16unsigned => Tint
  | Mint32 => Tint
  | Mint64 => Tlong
  | Mfloat32 => Tsingle
  | Mfloat64 => Tfloat
  | Many32 => Tany32
  | Many64 => Tany64
  end.
(*- #End *)

Lemma type_of_Mptr: type_of_chunk Mptr = Tptr.
Proof. unfold Mptr, Tptr; destruct Archi.ptr64; auto. Qed.

(** Same, as an extended type. *)

(*- E_COMPCERT_FTR_Function_AST_xtype_of_chunk_001 *)
(*- #Justify_Derived "Internal function" *)
Definition xtype_of_chunk (c: memory_chunk) : xtype :=
  match c with
  | Mbool => Xbool
  | Mint8signed => Xint8signed
  | Mint8unsigned => Xint8unsigned
  | Mint16signed => Xint16signed
  | Mint16unsigned => Xint16unsigned
  | Mint32 => Xint
  | Mint64 => Xlong
  | Mfloat32 => Xsingle
  | Mfloat64 => Xfloat
  | Many32 => Xany32
  | Many64 => Xany64
  end.
(*- #End *)

Lemma proj_xtype_of_chunk:
  forall chunk, proj_xtype (xtype_of_chunk chunk) = type_of_chunk chunk.
Proof.
  destruct chunk; auto.
Qed.

(** The chunk that is appropriate to store and reload a value of
  the given type, without losing information. *)

(*- E_COMPCERT_FTR_Function_AST_chunk_of_type_001 *)
(*- #Justify_Derived "Internal function" *)
Definition chunk_of_type (ty: typ) :=
  match ty with
  | Tint => Mint32
  | Tfloat => Mfloat64
  | Tlong => Mint64
  | Tsingle => Mfloat32
  | Tany32 => Many32
  | Tany64 => Many64
  end.
(*- #End *)

Lemma chunk_of_Tptr: chunk_of_type Tptr = Mptr.
Proof. unfold Mptr, Tptr; destruct Archi.ptr64; auto. Qed.

(** Initialization data for global variables. *)

(*- E_COMPCERT_FTR_Function_AST_init_data_0_001 *)
(*- #Justify_Derived "Internal type" *)
Inductive init_data: Type :=
  | Init_int8: int -> init_data
  | Init_int16: int -> init_data
  | Init_int32: int -> init_data
  | Init_int64: int64 -> init_data
  | Init_float32: float32 -> init_data
  | Init_float64: float -> init_data
  | Init_space: Z -> init_data
  | Init_addrof: ident -> ptrofs -> init_data.  (**r address of symbol + offset *)
(*- #End *)

(*- E_COMPCERT_FTR_Function_AST_init_data_size_001 *)
(*- #Justify_Derived "Internal function" *)
Definition init_data_size (i: init_data) : Z :=
  match i with
  | Init_int8 _ => 1
  | Init_int16 _ => 2
  | Init_int32 _ => 4
  | Init_int64 _ => 8
  | Init_float32 _ => 4
  | Init_float64 _ => 8
  | Init_addrof _ _ => if Archi.ptr64 then 8 else 4
  | Init_space n => Z.max n 0
  end.
(*- #End *)

(*- E_COMPCERT_FTR_Function_AST_init_data_list_size_001 *)
(*- #Justify_Derived "Internal function" *)
Fixpoint init_data_list_size (il: list init_data) {struct il} : Z :=
  match il with
  | nil => 0
  | i :: il' => init_data_size i + init_data_list_size il'
  end.
(*- #End *)

Lemma init_data_size_pos:
  forall i, init_data_size i >= 0.
Proof.
  destruct i; simpl; try extlia. destruct Archi.ptr64; lia.
Qed.

Lemma init_data_list_size_pos:
  forall il, init_data_list_size il >= 0.
Proof.
  induction il; simpl. lia. generalize (init_data_size_pos a); lia.
Qed.

(** Information attached to global variables. *)

(*- E_COMPCERT_FTR_Function_AST_globvar_0_001 *)
(*- #Justify_Derived "Internal type" *)
Record globvar (V: Type) : Type := mkglobvar {
  gvar_info: V;                    (**r language-dependent info, e.g. a type *)
  gvar_init: list init_data;       (**r initialization data *)
  gvar_readonly: bool;             (**r read-only variable? (const) *)
  gvar_volatile: bool              (**r volatile variable? *)
}.
(*- #End *)

(** Whole programs consist of:
- a collection of global definitions (name and description);
- a set of public names (the names that are visible outside
  this compilation unit);
- the name of the ``main'' function that serves as entry point in the program.

A global definition is either a global function or a global variable.
The type of function descriptions and that of additional information
for variables vary among the various intermediate languages and are
taken as parameters to the [program] type.  The other parts of whole
programs are common to all languages. *)

(*- E_COMPCERT_FTR_Function_AST_globdef_0_001 *)
(*- #Justify_Derived "Internal type" *)
Inductive globdef (F V: Type) : Type :=
  | Gfun (f: F)
  | Gvar (v: globvar V).
(*- #End *)

Arguments Gfun [F V].
Arguments Gvar [F V].

(*- E_COMPCERT_FTR_Function_AST_program_0_001 *)
(*- #Justify_Derived "Internal type" *)
Record program (F V: Type) : Type := mkprogram {
  prog_defs: list (ident * globdef F V);
  prog_public: list ident;
  prog_main: ident
}.
(*- #End *)

Definition prog_defs_names (F V: Type) (p: program F V) : list ident :=
  List.map fst p.(prog_defs).

(** The "definition map" of a program maps names of globals to their definitions.
  If several definitions have the same name, the one appearing last in [p.(prog_defs)] wins. *)

Definition prog_defmap (F V: Type) (p: program F V) : PTree.t (globdef F V) :=
  PTree_Properties.of_list p.(prog_defs).

Section DEFMAP.

Variables F V: Type.
Variable p: program F V.

Lemma in_prog_defmap:
  forall id g, (prog_defmap p)!id = Some g -> In (id, g) (prog_defs p).
Proof.
  apply PTree_Properties.in_of_list.
Qed.

Lemma prog_defmap_dom:
  forall id, In id (prog_defs_names p) -> exists g, (prog_defmap p)!id = Some g.
Proof.
  apply PTree_Properties.of_list_dom.
Qed.

Lemma prog_defmap_unique:
  forall defs1 id g defs2,
  prog_defs p = defs1 ++ (id, g) :: defs2 ->
  ~In id (map fst defs2) ->
  (prog_defmap p)!id = Some g.
Proof.
  unfold prog_defmap; intros. rewrite H. apply PTree_Properties.of_list_unique; auto.
Qed.

Lemma prog_defmap_norepet:
  forall id g,
  list_norepet (prog_defs_names p) ->
  In (id, g) (prog_defs p) ->
  (prog_defmap p)!id = Some g.
Proof.
  apply PTree_Properties.of_list_norepet.
Qed.

End DEFMAP.

(** * Generic transformations over programs *)

(** We now define a general iterator over programs that applies a given
  code transformation function to all function descriptions and leaves
  the other parts of the program unchanged. *)

Section TRANSF_PROGRAM.

Variable A B V: Type.
Variable transf: A -> B.

Definition transform_program_globdef (idg: ident * globdef A V) : ident * globdef B V :=
  match idg with
  | (id, Gfun f) => (id, Gfun (transf f))
  | (id, Gvar v) => (id, Gvar v)
  end.

Definition transform_program (p: program A V) : program B V :=
  mkprogram
    (List.map transform_program_globdef p.(prog_defs))
    p.(prog_public)
    p.(prog_main).

End TRANSF_PROGRAM.

(** The following is a more general presentation of [transform_program]:
- Global variable information can be transformed, in addition to function
  definitions.
- The transformation functions can fail and return an error message.
- The transformation for function definitions receives a global context
  (derived from the compilation unit being transformed) as additiona
  argument.
- The transformation functions receive the name of the global as
  additional argument. *)

Local Open Scope error_monad_scope.

Section TRANSF_PROGRAM_GEN.

Variables A B V W: Type.
Variable transf_fun: ident -> A -> res B.
Variable transf_var: ident -> V -> res W.

Definition transf_globvar (i: ident) (g: globvar V) : res (globvar W) :=
  do info' <- transf_var i g.(gvar_info);
  OK (mkglobvar info' g.(gvar_init) g.(gvar_readonly) g.(gvar_volatile)).

Fixpoint transf_globdefs (l: list (ident * globdef A V)) : res (list (ident * globdef B W)) :=
  match l with
  | nil => OK nil
  | (id, Gfun f) :: l' =>
    match transf_fun id f with
      | Error msg => Error (MSG "In function " :: CTX id :: MSG ": " :: msg)
      | OK tf =>
        do tl' <- transf_globdefs l'; OK ((id, Gfun tf) :: tl')
    end
  | (id, Gvar v) :: l' =>
    match transf_globvar id v with
      | Error msg => Error (MSG "In variable " :: CTX id :: MSG ": " :: msg)
      | OK tv =>
        do tl' <- transf_globdefs l'; OK ((id, Gvar tv) :: tl')
    end
  end.

Definition transform_partial_program2 (p: program A V) : res (program B W) :=
  do gl' <- transf_globdefs p.(prog_defs);
  OK (mkprogram gl' p.(prog_public) p.(prog_main)).

End TRANSF_PROGRAM_GEN.

(** The following is a special case of [transform_partial_program2],
  where only function definitions are transformed, but not variable definitions. *)

Section TRANSF_PARTIAL_PROGRAM.

Variable A B V: Type.
Variable transf_fun: A -> res B.

Definition transform_partial_program (p: program A V) : res (program B V) :=
  transform_partial_program2 (fun i f => transf_fun f) (fun i v => OK v) p.

End TRANSF_PARTIAL_PROGRAM.

Lemma transform_program_partial_program:
  forall (A B V: Type) (transf_fun: A -> B) (p: program A V),
  transform_partial_program (fun f => OK (transf_fun f)) p = OK (transform_program transf_fun p).
Proof.
  intros. unfold transform_partial_program, transform_partial_program2.
  assert (EQ: forall l,
              transf_globdefs (fun i f => OK (transf_fun f)) (fun i (v: V) => OK v) l =
              OK (List.map (transform_program_globdef transf_fun) l)).
  { induction l as [ | [id g] l]; simpl.
  - auto.
  - destruct g; simpl; rewrite IHl; simpl. auto. destruct v; auto.
  }
  rewrite EQ; simpl. auto.
Qed.

(** * External functions *)

(** For most languages, the functions composing the program are either
  internal functions, defined within the language, or external functions,
  defined outside.  External functions include system calls but also
  compiler built-in functions.  We define a type for external functions
  and associated operations. *)

(*- E_COMPCERT_FTR_Function_AST_external_function_0_001 *)
(*- #Justify_Derived "Internal type" *)
Inductive external_function : Type :=
  | EF_external (name: string) (sg: signature)
     (** A system call or library function.  Produces an event
         in the trace. *)
  | EF_builtin (name: string) (sg: signature)
     (** A compiler built-in function.  Behaves like an external, but
         can be inlined by the compiler. *)
  | EF_runtime (name: string) (sg: signature)
     (** A function from the run-time library.  Behaves like an
         external, but must not be redefined. *)
  | EF_vload (chunk: memory_chunk)
     (** A volatile read operation.  If the address given as first argument
         points within a volatile global variable, generate an
         event and return the value found in this event.  Otherwise,
         produce no event and behave like a regular memory load. *)
  | EF_vstore (chunk: memory_chunk)
     (** A volatile store operation.   If the address given as first argument
         points within a volatile global variable, generate an event.
         Otherwise, produce no event and behave like a regular memory store. *)
  | EF_malloc
     (** Dynamic memory allocation.  Takes the requested size in bytes
         as argument; returns a pointer to a fresh block of the given size.
         Produces no observable event. *)
  | EF_free
     (** Dynamic memory deallocation.  Takes a pointer to a block
         allocated by an [EF_malloc] external call and frees the
         corresponding block.
         Produces no observable event. *)
  | EF_memcpy (sz: Z) (al: Z)
     (** Block copy, of [sz] bytes, between addresses that are [al]-aligned. *)
  | EF_annot (kind: positive) (text: string) (targs: list typ)
     (** A programmer-supplied annotation.  Takes zero, one or several arguments,
         produces an event carrying the text and the values of these arguments,
         and returns no value. *)
  | EF_annot_val (kind: positive) (text: string) (targ: typ)
     (** Another form of annotation that takes one argument, produces
         an event carrying the text and the value of this argument,
         and returns the value of the argument. *)
  | EF_inline_asm (text: string) (sg: signature) (clobbers: list string)
     (** Inline [asm] statements.  Semantically, treated like an
         annotation with no parameters ([EF_annot text nil]).  To be
         used with caution, as it can invalidate the semantic
         preservation theorem.  Generated only if [-finline-asm] is
         given. *)
  | EF_debug (kind: positive) (text: ident) (targs: list typ).
     (** Transport debugging information from the front-end to the generated
         assembly.  Takes zero, one or several arguments like [EF_annot].
         Unlike [EF_annot], produces no observable event. *)
(*- #End *)

(** The type signature of an external function. *)

(*- E_COMPCERT_FTR_Function_AST_ef_sig_001 *)
(*- #Justify_Derived "Internal type" *)
Definition ef_sig (ef: external_function): signature :=
  match ef with
  | EF_external name sg => sg
  | EF_builtin name sg => sg
  | EF_runtime name sg => sg
  | EF_vload chunk => [Xptr ---> xtype_of_chunk chunk]
  | EF_vstore chunk => [Xptr; xtype_of_chunk chunk ---> Xvoid]
  | EF_malloc => [Xsize_t ---> Xptr]
  | EF_free => [Xptr ---> Xvoid]
  | EF_memcpy sz al => [Xptr; Xptr ---> Xvoid]
  | EF_annot kind text targs => mksignature (List.map inj_type targs) Xvoid cc_default
  | EF_annot_val kind text targ => [inj_type targ ---> inj_type targ]
  | EF_inline_asm text sg clob => sg
  | EF_debug kind text targs => mksignature (List.map inj_type targs) Xvoid cc_default
  end.
(*- #End *)

(** Whether an external function should be inlined by the compiler. *)

Definition ef_inline (ef: external_function) : bool :=
  match ef with
  | EF_external name sg => false
  | EF_builtin name sg => true
  | EF_runtime name sg => false
  | EF_vload chunk => true
  | EF_vstore chunk => true
  | EF_malloc => false
  | EF_free => false
  | EF_memcpy sz al => true
  | EF_annot kind text targs => true
  | EF_annot_val kind text rg => true
  | EF_inline_asm text sg clob => true
  | EF_debug kind text targs => true
  end.

(** Whether an external function must reload its arguments. *)

Definition ef_reloads (ef: external_function) : bool :=
  match ef with
  | EF_annot kind text targs => false
  | EF_debug kind text targs => false
  | _ => true
  end.

(** Equality between external functions.  Used in module [Allocation]. *)

Definition external_function_eq: forall (ef1 ef2: external_function), {ef1=ef2} + {ef1<>ef2}.
Proof.
  generalize ident_eq string_dec signature_eq chunk_eq typ_eq xtype_eq list_eq_dec zeq Int.eq_dec; intros.
  decide equality.
Defined.
Global Opaque external_function_eq.

(** Function definitions are the union of internal and external functions. *)

(*- E_COMPCERT_FTR_Function_AST_fundef_0_001 *)
(*- #Justify_Derived "Internal type" *)
Inductive fundef (F: Type): Type :=
  | Internal: F -> fundef F
  | External: external_function -> fundef F.
(*- #End *)

Arguments External [F].

Section TRANSF_FUNDEF.

Variable A B: Type.
Variable transf: A -> B.

Definition transf_fundef (fd: fundef A): fundef B :=
  match fd with
  | Internal f => Internal (transf f)
  | External ef => External ef
  end.

End TRANSF_FUNDEF.

Section TRANSF_PARTIAL_FUNDEF.

Variable A B: Type.
Variable transf_partial: A -> res B.

Definition transf_partial_fundef (fd: fundef A): res (fundef B) :=
  match fd with
  | Internal f => do f' <- transf_partial f; OK (Internal f')
  | External ef => OK (External ef)
  end.

End TRANSF_PARTIAL_FUNDEF.

(** * Register pairs *)

Set Contextual Implicit.

(** In some intermediate languages (LTL, Mach), 64-bit integers can be
  split into two 32-bit halves and held in a pair of registers.
  Syntactically, this is captured by the type [rpair] below. *)

(*- E_COMPCERT_FTR_Function_AST_rpair_0_001 *)
(*- #Justify_Derived "Internal type" *)
Inductive rpair (A: Type) : Type :=
  | One (r: A)
  | Two (rhi rlo: A).
(*- #End *)

(*- E_COMPCERT_FTR_Function_AST_map_rpair_001 *)
(*- #Justify_Derived "Internal function" *)
Definition map_rpair (A B: Type) (f: A -> B) (p: rpair A): rpair B :=
  match p with
  | One r => One (f r)
  | Two rhi rlo => Two (f rhi) (f rlo)
  end.
(*- #End *)

Definition fold_right_rpair (A B: Type) (f: B -> A -> B) (p: rpair A) (acc: B): B :=
  match p with
  | One r => f acc r
  | Two r1 r2 => f (f acc r2) r1
  end.

Definition regs_of_rpair (A: Type) (p: rpair A): list A :=
  match p with
  | One r => r :: nil
  | Two rhi rlo => rhi :: rlo :: nil
  end.

Definition regs_of_rpairs (A: Type) (l: list (rpair A)): list A :=
  flat_map (@regs_of_rpair A) l.

Lemma in_regs_of_rpairs:
  forall (A: Type) (r: A) l, In r (regs_of_rpairs l) <-> (exists p, In p l /\ In r (regs_of_rpair p)).
Proof.
  unfold regs_of_rpairs. intros; apply in_flat_map; auto.
Qed.

Lemma regs_of_rpairs_app:
  forall (A: Type) (l1 l2: list (rpair A)), regs_of_rpairs (l1 ++ l2) = regs_of_rpairs l1 ++ regs_of_rpairs l2.
Proof.
  unfold regs_of_rpairs. intros. apply flat_map_app; auto.
Qed.

Lemma fold_right_rpair_preserves: forall A B (f: B -> A -> B) (P: B -> Prop) (p: rpair A) acc,
    (forall a r, P a -> P (f a r)) ->
    P acc ->
    P (fold_right_rpair f p acc).
Proof.
  intros. destruct p; simpl; auto.
Qed.

Definition forall_rpair (A: Type) (P: A -> Prop) (p: rpair A): Prop :=
  match p with
  | One r => P r
  | Two rhi rlo => P rhi /\ P rlo
  end.

Definition forallb_rpair (A: Type) (b: A -> bool) (p: rpair A): bool :=
  match p with
  | One r => b r
  | Two rhi rlo => b rhi && b rlo
  end.

Lemma forall_regs_in_rpair:
  forall A P (p: rpair A) x,
    forall_rpair P p ->
    In x (regs_of_rpair p) ->
    P x.
Proof.
  destruct p; simpl; intros;
  repeat match goal with
  | [ H: _ \/ _ |- _ ] => destruct H
  | [ H: ?X = ?Y |- _ ] => rewrite <- H
  end; intuition.
Qed.

Lemma regs_in_rpair_forall:
  forall A (P: A -> Prop) (p: rpair A),
    (forall x, In x (regs_of_rpair p) -> P x) ->
    forall_rpair P p.
Proof.
  destruct p; simpl; auto.
Qed.

Definition option_single (A: Type) (p: rpair A) :=
  match p with One a => Some a | _ => None end.

Lemma option_single_one:
  forall (A: Type) a (p: rpair A), option_single p = Some a -> p = One a.
Proof.
  destruct p; simpl; intros; inversion H. reflexivity.
Qed.

Definition error_single (A: Type) (p: rpair A) :=
  match p with One a => OK a | _ => Error (msg "pair occured") end.

Lemma error_single_one:
  forall (A: Type) a (p: rpair A), error_single p = OK a -> p = One a.
Proof.
  destruct p; simpl; intros; inversion H. reflexivity.
Qed.

Lemma rpair_eq: forall (A: Type) (eqA_dec: forall a b : A, {a=b} + {a <> b}) (x y: rpair A),
    {x = y} + {x <> y}.
Proof.
  intros. destruct x; destruct y; try (right; congruence);
    [case (eqA_dec r r0); intros;[left; f_equal; assumption | right; congruence]| ];
    case (eqA_dec rhi rhi0); case (eqA_dec rlo rlo0); intros; try (right; congruence);
    left; f_equal; assumption.
Defined.

(** * Arguments and results to builtin functions *)

(*- E_COMPCERT_FTR_Function_AST_builtin_arg_0_001 *)
(*- #Justify_Derived "Internal type" *)
Inductive builtin_arg (A: Type) : Type :=
  | BA (x: A)
  | BA_int (n: int)
  | BA_long (n: int64)
  | BA_float (f: float)
  | BA_single (f: float32)
  | BA_loadstack (chunk: memory_chunk) (ofs: ptrofs)
  | BA_addrstack (ofs: ptrofs)
  | BA_loadglobal (chunk: memory_chunk) (id: ident) (ofs: ptrofs)
  | BA_addrglobal (id: ident) (ofs: ptrofs)
  | BA_splitlong (hi lo: builtin_arg A)
  | BA_addptr (a1 a2: builtin_arg A).
(*- #End *)

(*- E_COMPCERT_FTR_Function_AST_builtin_res_0_001 *)
(*- #Justify_Derived "Internal type" *)
Inductive builtin_res (A: Type) : Type :=
  | BR (x: A)
  | BR_none
  | BR_splitlong (hi lo: builtin_res A).
(*- #End *)

Fixpoint globals_of_builtin_arg (A: Type) (a: builtin_arg A) : list ident :=
  match a with
  | BA_loadglobal chunk id ofs => id :: nil
  | BA_addrglobal id ofs => id :: nil
  | BA_splitlong hi lo => globals_of_builtin_arg hi ++ globals_of_builtin_arg lo
  | BA_addptr a1 a2 => globals_of_builtin_arg a1 ++ globals_of_builtin_arg a2
  | _ => nil
  end.

Definition globals_of_builtin_args (A: Type) (al: list (builtin_arg A)) : list ident :=
  List.fold_right (fun a l => globals_of_builtin_arg a ++ l) nil al.

Fixpoint params_of_builtin_arg (A: Type) (a: builtin_arg A) : list A :=
  match a with
  | BA x => x :: nil
  | BA_splitlong hi lo => params_of_builtin_arg hi ++ params_of_builtin_arg lo
  | BA_addptr a1 a2 => params_of_builtin_arg a1 ++ params_of_builtin_arg a2
  | _ => nil
  end.

Definition params_of_builtin_args (A: Type) (al: list (builtin_arg A)) : list A :=
  List.fold_right (fun a l => params_of_builtin_arg a ++ l) nil al.

Fixpoint params_of_builtin_res (A: Type) (a: builtin_res A) : list A :=
  match a with
  | BR x => x :: nil
  | BR_none => nil
  | BR_splitlong hi lo => params_of_builtin_res hi ++ params_of_builtin_res lo
  end.

Fixpoint map_builtin_arg (A B: Type) (f: A -> B) (a: builtin_arg A) : builtin_arg B :=
  match a with
  | BA x => BA (f x)
  | BA_int n => BA_int n
  | BA_long n => BA_long n
  | BA_float n => BA_float n
  | BA_single n => BA_single n
  | BA_loadstack chunk ofs => BA_loadstack chunk ofs
  | BA_addrstack ofs => BA_addrstack ofs
  | BA_loadglobal chunk id ofs => BA_loadglobal chunk id ofs
  | BA_addrglobal id ofs => BA_addrglobal id ofs
  | BA_splitlong hi lo =>
      BA_splitlong (map_builtin_arg f hi) (map_builtin_arg f lo)
  | BA_addptr a1 a2 =>
      BA_addptr (map_builtin_arg f a1) (map_builtin_arg f a2)
  end.

Fixpoint map_builtin_res (A B: Type) (f: A -> B) (a: builtin_res A) : builtin_res B :=
  match a with
  | BR x => BR (f x)
  | BR_none => BR_none
  | BR_splitlong hi lo =>
      BR_splitlong (map_builtin_res f hi) (map_builtin_res f lo)
  end.

(** Which kinds of builtin arguments are supported by which external function. *)

Inductive builtin_arg_constraint : Type :=
  | OK_default
  | OK_const
  | OK_addrstack
  | OK_addressing
  | OK_all.

(* Helper functions to restrict rpairs to single registers *)
Fixpoint restrict_builtin_res (A: Type) (a: builtin_res (rpair A)) : res (builtin_res A) :=
  match a with
  | BR (One x) => OK (BR x)
  | BR (Two _ _) => Error (msg "Pair occured in builtin res")
  | BR_none => OK (BR_none)
  | BR_splitlong hi lo =>
      match restrict_builtin_res hi, restrict_builtin_res lo with
      | OK x, OK y => OK (BR_splitlong x y)
      | _, _ => Error (msg "Pair occured in builtin res")
      end
  end.

Fixpoint restrict_builtin_arg (A: Type) (a: builtin_arg (rpair A)) : res (builtin_arg A) :=
  match a with
  | BA (One x) => OK (BA x)
  | BA (Two _ _ ) => Error (msg "Pair occured in builtin res")
  | BA_int n => OK (BA_int n)
  | BA_long n => OK (BA_long n)
  | BA_float n => OK (BA_float n)
  | BA_single n => OK (BA_single n)
  | BA_loadstack chunk ofs => OK (BA_loadstack chunk ofs)
  | BA_addrstack ofs => OK (BA_addrstack ofs)
  | BA_loadglobal chunk id ofs => OK (BA_loadglobal chunk id ofs)
  | BA_addrglobal id ofs => OK (BA_addrglobal id ofs)
  | BA_splitlong hi lo =>
      match restrict_builtin_arg hi, restrict_builtin_arg lo with
      | OK x, OK y => OK (BA_splitlong x y)
      | _, _ => Error (msg "Pair occured in builtin res")
      end
  | BA_addptr a1 a2 =>
      match restrict_builtin_arg a1, restrict_builtin_arg a2 with
      | OK x, OK y => OK (BA_addptr x y)
      | _, _ => Error (msg "Pair occured in builtin res")
      end
  end.
