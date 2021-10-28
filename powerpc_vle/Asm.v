(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Abstract syntax and semantics for PowerPC assembly language *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require Import Stacklayout.
Require Import Conventions.

(** * Abstract syntax *)

(** Integer registers, floating-point registers. *)

(** We divide the integer registers into two sets:
    * GPR0 - GPR7 and GPR24 - GPR31
    * GPR8 - GPR23
    since most of the 16 bit vle instructions only allow
    either one of them as arguments.
 *)

Inductive sreg: Type :=
  | GPR0: sreg  | GPR1: sreg  | GPR2: sreg  | GPR3: sreg
  | GPR4: sreg  | GPR5: sreg  | GPR6: sreg  | GPR7: sreg
  | GPR24: sreg | GPR25: sreg | GPR26: sreg | GPR27: sreg
  | GPR28: sreg | GPR29: sreg | GPR30: sreg | GPR31: sreg.

Inductive areg: Type :=
  | GPR8: areg  | GPR9: areg  | GPR10: areg | GPR11: areg
  | GPR12: areg | GPR13: areg | GPR14: areg | GPR15: areg
  | GPR16: areg | GPR17: areg | GPR18: areg | GPR19: areg
  | GPR20: areg | GPR21: areg | GPR22: areg | GPR23: areg.

(*- E_COMPCERT_FTR_Function_Asm_ireg_0_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Inductive ireg: Type :=
  | Sreg: sreg -> ireg
  | Areg: areg -> ireg.
(*- #End *)

Coercion Sreg: sreg >-> ireg.
Coercion Areg: areg >-> ireg.

(*- E_COMPCERT_FTR_Function_Asm_freg_0_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Inductive freg: Type :=
  | ErrorReg: freg.
(*- #End *)

Lemma sreg_eq: forall (x y: sreg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Lemma areg_eq: forall (x y: areg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

(*- E_COMPCERT_FTR_Function_Asm_ireg_eq_001 *)
(*- #Justify_Derived "Internal equality function for integer registers" *)
Lemma ireg_eq: forall (x y: ireg), {x=y} + {x<>y}.
Proof. decide equality; decide equality. Defined.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Asm_freg_eq_001 *)
(*- #Justify_Derived "Internal equality function for floating point registers" *)
Lemma freg_eq: forall (x y: freg), {x=y} + {x<>y}.
Proof. decide equality. Defined.
(*- #End *)

(** The PowerPC has a great many registers, some general-purpose, some very
  specific.  We model only the following registers: *)

(*- E_COMPCERT_FTR_Function_Asm_preg_0_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Inductive preg: Type :=
  | IR: ireg -> preg                    (**r integer registers *)
  | FR: freg -> preg                    (**r float registers *)
  | PC: preg                            (**r program counter *)
  | LR: preg                            (**r link register (return address) *)
  | CTR: preg                           (**r count register, used for some branches *)
  | CARRY: preg                         (**r carry bit of the status register *)
  | CR0_0: preg                         (**r bit 0 of the condition register  *)
  | CR0_1: preg                         (**r bit 1 of the condition register  *)
  | CR0_2: preg                         (**r bit 2 of the condition register  *)
  | CR0_3: preg                         (**r bit 3 of the condition register  *)
  | CR1_1: preg                         (**r bit 5 of the condition register  *)
  | CR1_2: preg.                        (**r bit 6 of the condition register  *)
(*- #End *)

Coercion IR: ireg >-> preg.
Coercion FR: freg >-> preg.

(*- E_COMPCERT_FTR_Function_Asm_preg_eq_001 *)
(*- #Justify_Derived "Internal equality function for all registers" *)
Lemma preg_eq: forall (x y: preg), {x=y} + {x<>y}.
Proof. decide equality. apply ireg_eq. apply freg_eq. Defined.
(*- #End *)

Module PregEq.
(*- E_COMPCERT_FTR_Function_Asm_PregEq_t_001 *)
(*- #Justify_Derived "Internal type used in module for map of all registers" *)
  Definition t := preg.
(*- #End *)
(*- E_COMPCERT_FTR_Function_Asm_PregEq_eq_001 *)
(*- #Justify_Derived "Internal equality function used in module for map of all registers" *)
  Definition eq := preg_eq.
(*- #End *)
End PregEq.

Module Pregmap := EMap(PregEq).

(** Conventional names for stack pointer ([SP]) and return address ([RA]) *)

Notation "'SP'" := GPR1 (only parsing) : asm.
Notation "'RA'" := LR (only parsing) : asm.

(** Symbolic constants.  Immediate operands to an arithmetic instruction
  or an indexed memory access can be either integer literals,
  or the low or high 16 bits of a symbolic reference (the address
  of a symbol plus a displacement), or a 16-bit offset from the
  small data area register.  These symbolic references are
  resolved later by the linker.
*)

(*- E_COMPCERT_FTR_Function_Asm_constant_0_001 *)
(*- #Justify_Derived "Internal type used for constants" *)
Inductive constant: Type :=
  | Cint: int -> constant
  | Csymbol_low: ident -> ptrofs -> constant
  | Csymbol_high: ident -> ptrofs -> constant
  | Csymbol_sda: ident -> ptrofs -> constant
  | Csymbol_rel_low: ident -> ptrofs -> constant
  | Csymbol_rel_high: ident -> ptrofs -> constant.
(*- #End *)

(** A note on constants: while immediate operands to PowerPC
  instructions must be representable in 16 bits (with
  sign extension or left shift by 16 positions for some instructions),
  we do not attempt to capture these restrictions in the
  abstract syntax nor in the semantics.  The assembler will
  emit an error if immediate operands exceed the representable
  range.  Of course, our PPC generator (file [Asmgen]) is
  careful to respect this range. *)

(** Bits in the condition register.  We are only interested in bits
  0, 1, 2, 3, 5 and 6. *)

(*- E_COMPCERT_FTR_Function_Asm_crbit_0_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Inductive crbit: Type :=
  | CRbit_0: crbit
  | CRbit_1: crbit
  | CRbit_2: crbit
  | CRbit_3: crbit
  | CRbit_5: crbit
  | CRbit_6: crbit.
(*- #End *)

(** The instruction set.  Most instructions correspond exactly to
  actual instructions of the PowerPC processor. See the PowerPC
  reference manuals for more details.  Some instructions,
  described below, are pseudo-instructions: they expand to
  canned instruction sequences during the printing of the assembly
  code. *)

(*- E_COMPCERT_FTR_Function_Asm_label_001 *)
(*- #Justify_Derived "Internal type used for assembler labels" *)
Definition label := positive.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Asm_instruction_0_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Inductive instruction : Type :=
  (** Integer arithmetic instruction *)
  | Padd: ireg -> ireg -> ireg -> instruction                 (**r integer addition *)
  | Pse_add: sreg -> sreg -> instruction                      (**r integer addition, short encoding *)
  | Pe_add16i : ireg -> ireg -> constant -> instruction       (**r add immediate *)
  | Pe_add2is : ireg -> constant -> instruction               (**r add immediate high *)
  | Pse_addi : sreg -> int -> instruction                     (**r add immediate short encoding *)
  | Paddc: ireg -> ireg -> ireg -> instruction                (**r integer addition and set carry *)
  | Pe_addic: ireg -> ireg -> int -> instruction              (**r add immediate and set carry *)
  | Padde: ireg -> ireg -> ireg -> instruction                (**r integer addition with carry *)
  | Paddze: ireg -> ireg -> instruction                       (**r add carry *)
  | Pmullw: ireg -> ireg -> ireg -> instruction               (**r integer multiply *)
  | Pse_mullw : sreg -> sreg -> instruction                   (**r integer multiply, short encoding *)
  | Pmulhw: ireg -> ireg -> ireg -> instruction               (**r multiply high signed *)
  | Pmulhwu: ireg -> ireg -> ireg -> instruction              (**r multiply high signed *)
  | Pdivw: ireg -> ireg -> ireg -> instruction                (**r signed division *)
  | Pdivwu: ireg -> ireg -> ireg -> instruction               (**r unsigned division *)
  | Psubfc: ireg -> ireg -> ireg -> instruction               (**r reversed integer subtraction *)
  | Pse_sub: sreg -> sreg -> instruction                      (**r integer subtraction, short encoding *)
  | Psubfe: ireg -> ireg -> ireg -> instruction               (**r reversed integer subtraction with carry *)
  | Pse_subf: sreg -> sreg -> instruction                     (**r reversed integer subtraction, short encoding *)
  | Psubfze: ireg -> ireg -> instruction                      (**r integer opposite with carry *)
  | Pe_subfic: ireg -> ireg -> int -> instruction             (**r integer subtraction from immediate *)
  | Pse_subi : sreg -> int -> instruction                     (**r integer subtraction with immediate, short encoding *)

  (** Bit operations *)
  | Pand_: ireg -> ireg -> ireg -> instruction                (**r bitwise and *)
  | Pse_and_: sreg -> sreg -> instruction                     (**r bitwise and, short encoding *)
  | Pandc: ireg -> ireg -> ireg -> instruction                (**r bitwise and-complement *)
  | Pse_andc: sreg -> sreg -> instruction                     (**r bitwise and-complement, short encoding *)
  | Pe_and2i_: ireg -> constant -> instruction                (**r and immediate and set conditions *)
  | Pe_and2is_: ireg -> constant -> instruction               (**r and immediate high and set conditions *)
  | Pnand: ireg -> ireg -> ireg -> instruction                (**r bitwise not-and *)
  | Pnor: ireg -> ireg -> ireg -> instruction                 (**r bitwise not-or *)
  | Por: ireg -> ireg -> ireg -> instruction                  (**r bitwise or *)
  | Pse_or: sreg -> sreg -> instruction                       (**r bitwise or, short encoding *)
  | Porc: ireg -> ireg -> ireg -> instruction                 (**r bitwise or-complement *)
  | Pe_or2i : ireg -> constant -> instruction                 (**r or immediate *)
  | Pe_or2is : ireg -> constant -> instruction                (**r or immediate shifted *)
  | Pxor: ireg -> ireg -> ireg -> instruction                 (**r bitwise xor *)
  | Pe_xori: ireg -> ireg -> int -> instruction               (**r bitwise xor with immediate *)
  | Peqv: ireg -> ireg -> ireg -> instruction                 (**r bitwise not-xor *)
  | Pextsb: ireg -> ireg -> instruction                       (**r 8-bit sign extension *)
  | Pse_extsb: sreg -> instruction                            (**r 8-bit sign extension, short encoding *)
  | Pextsh: ireg -> ireg -> instruction                       (**r 16-bit sign extension *)
  | Pse_extsh: sreg -> instruction                            (**r 16-bit sign extension, short encoding *)

  (** Shift instructions *)
  | Pslw: ireg -> ireg -> ireg -> instruction                 (**r shift left *)
  | Pse_slw: sreg -> sreg -> instruction                      (**r shift left with, short encoding *)
  | Psraw: ireg -> ireg -> ireg -> instruction                (**r shift right signed *)
  | Pse_sraw: sreg -> sreg -> instruction                     (**r shift right signed with, short encoding *)
  | Psrawi: ireg -> ireg -> int -> instruction                (**r shift right signed immediate *)
  | Pse_srawi: sreg -> int -> instruction                     (**r shift right signed immediate, short encoding *)
  | Psrw: ireg -> ireg -> ireg -> instruction                 (**r shift right unsigned *)
  | Pse_srw: sreg -> sreg -> instruction                      (**r shift right unsigned with, short encoding *)
  | Pe_rlwinm: ireg -> ireg -> int -> int -> instruction      (**r rotate and mask *)
  | Pe_rlwimi: ireg -> ireg -> int -> int -> instruction      (**r rotate and insert *)

  (** Compare instructions *)
  | Pcmplw: ireg -> ireg -> instruction                       (**r unsigned integer comparison *)
  | Pcmpw: ireg -> ireg -> instruction                        (**r signed integer comparison *)
  | Pse_cmp: sreg -> sreg -> instruction                      (**r signed integer comparison, short encoding *)
  | Pe_cmp16i: ireg -> constant -> instruction                (**r signed integer comparison, with immediate argument *)
  | Pse_cmpi: sreg -> int -> instruction                      (**r same, with short immediate argument, short encoding *)
  | Pse_cmpl: sreg -> sreg -> instruction                     (**r unsigned integer comparison, short encoding *)
  | Pe_cmpl16i: ireg -> constant -> instruction               (**r unsigned integer comparison, with immediate argument *)
  | Pisel: ireg -> ireg -> ireg -> crbit -> instruction       (**r integer select *)
  | Pefscmpeq: ireg -> ireg -> instruction                    (**r floating point compare equal *)
  | Pefscmpgt: ireg -> ireg -> instruction                    (**r floating point compare greater than *)
  | Pefscmplt: ireg -> ireg -> instruction                    (**r floating point compare less than *)

  (** Condition register manipulation instructions *)
  | Pe_creqv: crbit -> crbit -> crbit -> instruction          (**r not-xor between condition bits *)
  | Pe_cror: crbit -> crbit -> crbit -> instruction           (**r or between condition bits *)
  | Pe_crxor: crbit -> crbit -> crbit -> instruction          (**r xor between condition bits *)
  | Pse_mtctr: sreg -> instruction                            (**r move ireg to CTR, short encoding *)

  (** Branch instructions *)
  | Pbdnz: label -> instruction                               (**r decrement CTR and branch if not zero *)
  | Pbf: crbit -> label -> instruction                        (**r branch if false *)
  | Pbt: crbit -> label -> instruction                        (**r branch if true *)
  | Pbtbl: ireg -> list label -> instruction                  (**r N-way branch through a jump table (pseudo) *)
  | Pe_b : label -> instruction                               (**r unconditional branch *)
  | Pse_bctr: signature -> instruction                        (**r branch to contents of register CTR, short encoding *)
  | Pse_bctrl: signature -> instruction                       (**r branch to contents of CTR and link, short encoding *)
  | Pe_bl: ident -> signature -> instruction                  (**r branch and link *)
  | Pse_blr: instruction                                      (**r branch to contents of register LR, short encoding *)
  | Pe_bs: ident -> signature -> instruction                  (**r branch to symbol *)
  | Plabel: label -> instruction                              (**r define a code label *)

  (** Load instructions *)
  | Pe_lbz: ireg -> constant -> ireg -> instruction           (**r load 8-bit unsigned int *)
  | Pse_lbz: sreg -> int -> sreg -> instruction               (**r load 8-bit unsigned int, short offset/encoding *)
  | Plbzx: ireg -> ireg -> ireg -> instruction                (**r load 8-bit unsigned int, with 2 index regs *)
  | Pe_lha: ireg -> constant -> ireg -> instruction           (**r load 16-bit signed int *)
  | Plhax: ireg -> ireg -> ireg -> instruction                (**r same, with 2 index regs *)
  | Plhbrx: ireg -> ireg -> ireg -> instruction               (**r load 16-bit int and reverse endianness *)
  | Pe_lhz: ireg -> constant -> ireg -> instruction           (**r load 16-bit unsigned int *)
  | Pse_lhz: sreg -> int -> sreg -> instruction               (**r load 16-bit unsigned int, short offset/encoding *)
  | Plhzx: ireg -> ireg -> ireg -> instruction                (**r load 16-bit unsigned int, with 2 index regs *)
  | Pe_lwz: ireg -> constant -> ireg -> instruction           (**r load 32-bit int *)
  | Pse_lwz: sreg -> int -> sreg -> instruction               (**r load 32-bit int, short offset/encoding *)
  | Pe_lwzu: ireg -> constant -> ireg -> instruction          (**r load 32-bit int with update *)
  | Pe_lwz_a: ireg -> constant -> ireg -> instruction         (**r load 32-bit quantity to int reg *)
  | Pse_lwz_a: sreg -> int -> sreg -> instruction             (**r load 32-bit quantity to int reg, short offset/encoding *)
  | Plwzx: ireg -> ireg -> ireg -> instruction                (**r load 32-bit quantity to int reg, with 2 index regs *)
  | Plwzx_a: ireg -> ireg -> ireg -> instruction              (**r same, with 2 index regs *)
  | Plwbrx: ireg -> ireg -> ireg -> instruction               (**r load 32-bit int and reverse endianness *)
  | Pfe_lwz: ireg -> constant -> ireg -> instruction          (**r load float quantity to int reg *)
  | Pfse_lwz: sreg -> int -> sreg -> instruction              (**r load float quantity to int reg (short offset) *)
  | Pflwzx: ireg -> ireg -> ireg -> instruction               (**r load float quantity to int reg, with 2 index regs *)

  (** Store instructions *)
  | Pe_stb: ireg -> constant -> ireg -> instruction           (**r store 8-bit int *)
  | Pse_stb: sreg -> int -> sreg -> instruction               (**r store 8-bit int, short offset/encoding *)
  | Pstbx: ireg -> ireg -> ireg -> instruction                (**r store 8-bit int, with 2 index regs *)
  | Pe_sth: ireg -> constant -> ireg -> instruction           (**r store 16-bit int *)
  | Pse_sth: sreg -> int -> sreg -> instruction               (**r store 16-bit int, short offset/encoding *)
  | Psthx: ireg -> ireg -> ireg -> instruction                (**r store 16-bit int, with 2 index regs *)
  | Psthbrx: ireg -> ireg -> ireg -> instruction              (**r store 16-bit int with reverse endianness *)
  | Pe_stwu: ireg -> constant -> ireg -> instruction          (**r store 32-bit int with update *)
  | Pe_stw: ireg -> constant -> ireg -> instruction           (**r store 32-bit int *)
  | Pstwx: ireg -> ireg -> ireg -> instruction                (**r same, with 2 index regs *)
  | Pstwx_a: ireg -> ireg -> ireg -> instruction              (**r same, with 2 index regs *)
  | Pse_stw: sreg -> int -> sreg -> instruction               (**r store 32-bit int, short offset/encoding *)
  | Pe_stw_a: ireg -> constant -> ireg -> instruction         (**r store 32-bit quantity from int reg *)
  | Pse_stw_a: sreg -> int -> sreg -> instruction             (**r store 32-bit quantity from int reg, short offset/encoding *)
  | Pstwux: ireg -> ireg -> ireg -> instruction               (**r store 32-bit quantity from int reg, with 2 index regs and update *)
  | Pfe_stw: ireg -> constant -> ireg -> instruction          (**r store 32-bit float quantity from int reg *)
  | Pfse_stw: sreg -> int -> sreg -> instruction              (**r store 32-bit float quantity from int reg (short offset) *)
  | Pfstwx: ireg -> ireg -> ireg -> instruction               (**r store 32-bit float quantity from int reg, with 2 index regs *)

  | Pstwbrx: ireg -> ireg -> ireg -> instruction              (**r store 32-bit int with reverse endianness *)

  (** Move and immediate load *)
  | Pse_bgeni : sreg -> int -> instruction                    (**r bit generate immediate, short encoding *)
  | Pe_li : ireg -> constant -> instruction                   (**r load 20-bit sign extended immediate *)
  | Pe_lis : ireg -> constant -> instruction                  (**r load immediate shifted *)
  | Pse_li : sreg -> int -> instruction                       (**r load 7-bit immediate, short encoding *)
  | Pmr: ireg -> ireg -> instruction                          (**r integer move *)
  | Pse_mr : sreg -> sreg -> instruction                      (**r short encoding for register move, short encoding *)
  | Pse_mtar : areg -> sreg -> instruction                    (**r move to alternate register, short encoding *)
  | Pse_mfar : sreg -> areg -> instruction                    (**r move from alternate register, short encoding *)
  | Pmfcr: ireg -> instruction                                (**r move condition register to reg *)
  | Pmfcrbit: ireg -> crbit -> instruction                    (**r move condition bit to reg (pseudo) *)
  | Pse_mflr: sreg -> instruction                             (**r move LR to reg, short encoding *)
  | Pmfspr: ireg -> int -> instruction                        (**r move from special register *)
  | Pmtspr: int -> ireg -> instruction                        (**r move to special register *)
  | Pse_mtlr: sreg -> instruction                             (**r move ireg to LR, short encoding *)

  (** Floating point instructions *)
  | Pefsabs : ireg -> ireg -> instruction                     (**r float absolute value *)
  | Pefsadd : ireg -> ireg -> ireg -> instruction             (**r float addition *)
  | Pefsdiv : ireg -> ireg -> ireg -> instruction             (**r float division *)
  | Pefsmul : ireg -> ireg -> ireg -> instruction             (**r float multiply *)
  | Pefsneg : ireg -> ireg -> instruction                     (**r float negation *)
  | Pefssub : ireg -> ireg -> ireg -> instruction             (**r float subtraction *)
  | Plfis: ireg -> float32 -> instruction                     (**r load float constant *)

  (** Floating point to integer conversion functions *)
  | Pefscfsi : ireg -> ireg -> instruction                    (**r convert single from signed integer *)
  | Pefscfui : ireg -> ireg -> instruction                    (**r convert single from unsigned integer *)
  | Pefsctsi : ireg -> ireg -> instruction                    (**r convert single to signed integer *)
  | Pefsctui : ireg -> ireg -> instruction                    (**r convert single to unsigned integer *)

  (** Pseudo instructions*)
  | Pallocframe: Z -> ptrofs -> ptrofs -> instruction         (**r allocate new stack frame (pseudo) *)
  | Pcntlzw: ireg -> ireg -> instruction                      (**r count leading zeros *)
  | Pdcbf: ireg -> ireg -> instruction                        (**r data cache flush *)
  | Pdcbi: ireg -> ireg -> instruction                        (**r data cache invalidate *)
  | Pdcbt: int -> ireg -> ireg -> instruction                 (**r data cache block touch *)
  | Pdcbtst: int -> ireg -> ireg -> instruction               (**r data cache block touch *)
  | Pdcbtls: int -> ireg -> ireg -> instruction               (**r data cache block touch and lock *)
  | Pdcbz: ireg -> ireg -> instruction                        (**r data cache block zero *)
  | Pfreeframe: Z -> ptrofs -> instruction                    (**r deallocate stack frame and restore previous frame (pseudo) *)
  | Picbi: ireg -> ireg -> instruction                        (**r instruction cache invalidate *)
  | Picbtls: int -> ireg -> ireg -> instruction               (**r instruction cache block touch and lock set *)
  | Pse_isync: instruction                                    (**r ISYNC barrier, short encoding *)
  | Psync: instruction                                        (**r SYNC barrier *)
  | Pbuiltin: external_function -> list (builtin_arg preg) -> builtin_res preg -> instruction (**r built-in function (pseudo) *)
  | Pcfi_adjust: int -> instruction                           (**r .cfi_adjust debug directive *)
  | Pcfi_rel_offset: int -> instruction.                      (**r .cfi_rel_offset lr debug directive *)
(*- #End *)

(** The pseudo-instructions are the following:

- [Plabel]: define a code label at the current program point
- [Pallocframe sz ofs retofs]: in the formal semantics, this pseudo-instruction
  allocates a memory block with bounds [0] and [sz], stores the value
  of register [r1] (the stack pointer, by convention) at offset [ofs]
  in this block, and sets [r1] to a pointer to the bottom of this
  block.  In the printed PowerPC assembly code, this allocation
  is just a store-decrement of register [r1], assuming that [ofs = 0]:
<<
        e_stwu    r1, -sz(r1)
>>
  This cannot be expressed in our memory model, which does not reflect
  the fact that stack frames are adjacent and allocated/freed
  following a stack discipline.
- [Pfreeframe sz ofs]: in the formal semantics, this pseudo-instruction
  reads the word at offset [ofs] in the block pointed by [r1] (the
  stack pointer), frees this block, and sets [r1] to the value of the
  word at offset [ofs].  In the printed PowerPC assembly code, this
  freeing is just a load of register [r1] relative to [r1] itself:
<<
        e_lwz     r1, ofs(r1)
>>
  Again, our memory model cannot comprehend that this operation
  frees (logically) the current stack frame.
- [Pbtbl reg table]: this is a N-way branch, implemented via a jump table
  as follows:
<<
        e_addis   r12, reg, ha16(lbl)
        e_lwz     r12, lo16(lbl)(r12)
        se_mfar   r0, r12
        se_mtctr   r0
        se_bctr
lbl:    .long   table[0], table[1], ...
>>
  Note that [reg] contains 4 times the index of the desired table entry.
*)

(*- E_COMPCERT_FTR_Function_Asm_code_001 *)
(*- #Justify_Derived "Internal type used for code" *)
Definition code := list instruction.
(*- #End *)
(*- E_COMPCERT_FTR_Function_Asm_function_0_001 *)
(*- #Justify_Derived "Internal type for functions" *)
Record function : Type := mkfunction { fn_sig: signature; fn_code: code }.
(*- #End *)
(*- E_COMPCERT_FTR_Function_Asm_fundef_001 *)
(*- #Justify_Derived "Internal type used for fundefs" *)
Definition fundef := AST.fundef function.
(*- #End *)
(*- E_COMPCERT_FTR_Function_Asm_program_001 *)
(*- #Justify_Derived "Internal type used for a program" *)
Definition program := AST.program fundef unit.
(*- #End *)

(** * Operational semantics *)

(** The semantics operates over a single mapping from registers
  (type [preg]) to values.  We maintain (but do not enforce)
  the convention that integer registers are mapped to values of
  type [Tint], float registers to values of type [Tfloat],
  and boolean registers ([CARRY], [CR0_0], etc) to either
  [Vzero] or [Vone]. *)

(*- E_COMPCERT_FTR_Function_Asm_regset_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_002 *)
Definition regset := Pregmap.t val.
(*- #End *)
(*- E_COMPCERT_FTR_Function_Asm_genv_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_004 *)
Definition genv := Genv.t fundef unit.
(*- #End *)

Notation "a # b" := (a b) (at level 1, only parsing) : asm.
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level) : asm.

Open Scope asm.

(** Undefining some registers *)

(*- E_COMPCERT_FTR_Function_Asm_undef_regs_001 *)
(*- #Justify_Derived "Internal function to set register mapping for a register to undefined" *)
Fixpoint undef_regs (l: list preg) (rs: regset) : regset :=
  match l with
  | nil => rs
  | r :: l' => undef_regs l' (rs#r <- Vundef)
  end.
(*- #End *)

(** Assigning a register pair *)

(*- E_COMPCERT_FTR_Function_Asm_set_pair_001 *)
(*- #Justify_Derived "Internal function to set the value of a register pair in the register mapping" *)
Definition set_pair (p: rpair preg) (v: val) (rs: regset) : regset :=
  match p with
  | One r => rs#r <- v
  | Twolong rhi rlo => rs#rhi <- (Val.hiword v) #rlo <- (Val.loword v)
  end.
(*- #End *)

(** Assigning the result of a builtin *)

(*- E_COMPCERT_FTR_Function_Asm_set_res_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_005 *)
Fixpoint set_res (res: builtin_res preg) (v: val) (rs: regset) : regset :=
  match res with
  | BR r => rs#r <- v
  | BR_none => rs
  | BR_splitlong hi lo => set_res lo (Val.loword v) (set_res hi (Val.hiword v) rs)
  end.
(*- #End *)

Section RELSEM.

(** Looking up instructions in a code sequence by position. *)

(*- E_COMPCERT_FTR_Function_Asm_find_instr_001 *)
(*- #Justify_Derived "Auxiliary function to find an instruction in the code" *)
Fixpoint find_instr (pos: Z) (c: code) {struct c} : option instruction :=
  match c with
  | nil => None
  | i :: il => if zeq pos 0 then Some i else find_instr (pos - 1) il
  end.
(*- #End *)

(** Position corresponding to a label *)

(*- E_COMPCERT_FTR_Function_Asm_is_label_001 *)
(*- #Justify_Derived "Internal function to check whether an instruction is a label" *)
Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Plabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.
(*- #End *)

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Plabel lbl else instr <> Plabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl l); intro; congruence.
Qed.

(*- E_COMPCERT_FTR_Function_Asm_label_pos_001 *)
(*- #Justify_Derived "Internal function to determine the position of a label" *)
Fixpoint label_pos (lbl: label) (pos: Z) (c: code) {struct c} : option Z :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some (pos + 1) else label_pos lbl (pos + 1) c'
  end.
(*- #End *)

(** Some PowerPC instructions treat register GPR0 as the integer literal 0
  when that register is used in argument position. *)

(*- E_COMPCERT_FTR_Function_Asm_gpr_or_zero_001 *)
(*- #Justify_Derived "Helper function to get the value of a register or zero if it is GPR0" *)
Definition gpr_or_zero (rs: regset) (r: ireg) :=
  if ireg_eq r GPR0 then Vint Int.zero else rs#r.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Asm_gpr_or_zero_l_001 *)
(*- #Justify_Derived "Helper function to get the value of a register or zero if it is GPR0" *)
Definition gpr_or_zero_l (rs: regset) (r: ireg) :=
  if ireg_eq r GPR0 then Vlong Int64.zero else rs#r.
(*- #End *)

Variable ge: genv.

(** The two functions below axiomatize how the linker processes
  symbolic references [symbol + offset] and splits their
  actual values into two 16-bit halves. *)

(*- E_COMPCERT_FTR_Function_Asm_low_half_001 *)
(*- #Justify_Derived "Parameter function implemented in OCaml" *)
Parameter low_half: genv -> ident -> ptrofs -> val.
(*- #End *)
(*- E_COMPCERT_FTR_Function_Asm_high_half_001 *)
(*- #Justify_Derived "Parameter function implemented in OCaml" *)
Parameter high_half: genv -> ident -> ptrofs -> val.
(*- #End *)

(** The fundamental property of these operations is that, when applied
  to the address of a symbol, their results can be recombined by
  addition, rebuilding the original address. *)

Axiom low_high_half:
  forall id ofs,
  Val.add (high_half ge id ofs) (low_half ge id ofs) = Genv.symbol_address ge id ofs.

(** We also axiomatize the small data area.  For simplicity, we
  claim that small data symbols can be accessed by absolute 16-bit
  offsets, that is, relative to [GPR0].  In reality, the linker
  rewrites the object code, transforming [symb@sdarx(r0)] addressings
  into [offset(rN)] addressings, where [rN] is the reserved
  register pointing to the base of the small data area containing
  symbol [symb].  We leave this transformation up to the linker. *)

Parameter symbol_is_small_data: ident -> ptrofs -> bool.
(*- E_COMPCERT_FTR_Function_Asm_small_data_area_offset_001 *)
(*- #Justify_Derived "Parameter function implemented in OCaml" *)
Parameter small_data_area_offset: genv -> ident -> ptrofs -> val.
(*- #End *)

Axiom small_data_area_addressing:
  forall id ofs,
  symbol_is_small_data id ofs = true ->
  small_data_area_offset ge id ofs = Genv.symbol_address ge id ofs.

Parameter symbol_is_rel_data: ident -> ptrofs -> bool.

(** Armed with the [low_half] and [high_half] functions,
  we can define the evaluation of a symbolic constant.
  Note that for [const_high], integer constants
  are shifted left by 16 bits, but not symbol addresses:
  we assume (as in the [low_high_half] axioms above)
  that the results of [high_half] are already shifted
  (their 16 low bits are equal to 0). *)

(*- E_COMPCERT_FTR_Function_Asm_const_low_001 *)
(*- #Justify_Derived "Helper function for evaluation of a symbolic constant" *)
Definition const_low (c: constant) :=
  match c with
  | Cint n => Vint n
  | Csymbol_low id ofs => low_half ge id ofs
  | Csymbol_high id ofs => Vundef
  | Csymbol_sda id ofs => small_data_area_offset ge id ofs
  | Csymbol_rel_low id ofs => low_half ge id ofs
  | Csymbol_rel_high id ofs => Vundef
  end.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Asm_const_high_001 *)
(*- #Justify_Derived "Helper function for evaluation of a symbolic constant" *)
Definition const_high (c: constant) :=
  match c with
  | Cint n => Vint (Int.shl n (Int.repr 16))
  | Csymbol_low id ofs => Vundef
  | Csymbol_high id ofs => high_half ge id ofs
  | Csymbol_sda id ofs => Vundef
  | Csymbol_rel_low id ofs => Vundef
  | Csymbol_rel_high id ofs => high_half ge id ofs
  end.
(*- #End *)

(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [OK rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Error] if the processor is stuck. *)

(*- E_COMPCERT_FTR_Function_Asm_outcome_0_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_005 *)
Inductive outcome: Type :=
  | Next: regset -> mem -> outcome
  | Stuck: outcome.
(*- #End *)

(** Manipulations over the [PC] register: continuing with the next
  instruction ([nextinstr]) or branching to a label ([goto_label]). *)

(*- E_COMPCERT_FTR_Function_Asm_nextinstr_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_005 *)
Definition nextinstr (rs: regset) :=
  rs#PC <- (Val.offset_ptr rs#PC Ptrofs.one).
(*- #End *)

(*- E_COMPCERT_FTR_Function_Asm_goto_label_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_005 *)
Definition goto_label (f: function) (lbl: label) (rs: regset) (m: mem) :=
  match label_pos lbl 0 (fn_code f) with
  | None => Stuck
  | Some pos =>
      match rs#PC with
      | Vptr b ofs => Next (rs#PC <- (Vptr b (Ptrofs.repr pos))) m
      | _ => Stuck
    end
  end.
(*- #End *)

(** Auxiliaries for memory accesses, in two forms: one operand
  (plus constant offset) or two operands. *)

(*- E_COMPCERT_FTR_Function_Asm_load1_001 *)
(*- #Justify_Derived "Auxiliary for memory access" *)
Definition load1 (chunk: memory_chunk) (rd: preg)
                 (cst: constant) (r1: ireg) (rs: regset) (m: mem) :=
  match Mem.loadv chunk m (Val.add (gpr_or_zero rs r1) (const_low cst)) with
  | None => Stuck
  | Some v => Next (nextinstr (rs#rd <- v)) m
  end.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Asm_load2_001 *)
(*- #Justify_Derived "Auxiliary for memory access" *)
Definition load2 (chunk: memory_chunk) (rd: preg) (r1 r2: ireg)
                 (rs: regset) (m: mem) :=
  match Mem.loadv chunk m (Val.add (gpr_or_zero rs r1) rs#r2) with
  | None => Stuck
  | Some v => Next (nextinstr (rs#rd <- v)) m
  end.
(*- #End *)

Definition load1_non_zero (chunk: memory_chunk) (rd: preg)
                 (cst: constant) (r1: ireg) (rs: regset) (m: mem) :=
  match Mem.loadv chunk m (Val.add rs#r1 (const_low cst)) with
  | None => Stuck
  | Some v => Next (nextinstr (rs#rd <- v)) m
  end.

(*- E_COMPCERT_FTR_Function_Asm_store1_001 *)
(*- #Justify_Derived "Auxiliary for memory access" *)
Definition store1 (chunk: memory_chunk) (r: preg)
                  (cst: constant) (r1: ireg) (rs: regset) (m: mem) :=
  match Mem.storev chunk m (Val.add (gpr_or_zero rs r1) (const_low cst)) (rs#r) with
  | None => Stuck
  | Some m' => Next (nextinstr rs) m'
  end.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Asm_store2_001 *)
(*- #Justify_Derived "Auxiliary for memory access" *)
Definition store2 (chunk: memory_chunk) (r: preg) (r1 r2: ireg)
                  (rs: regset) (m: mem) :=
  match Mem.storev chunk m (Val.add (gpr_or_zero rs r1) rs#r2) (rs#r) with
  | None => Stuck
  | Some m' => Next (nextinstr rs) m'
  end.
(*- #End *)

Definition store1_non_zero (chunk: memory_chunk) (r: preg)
                  (cst: constant) (r1: ireg) (rs: regset) (m: mem) :=
  match Mem.storev chunk m (Val.add rs#r1 (const_low cst)) (rs#r) with
  | None => Stuck
  | Some m' => Next (nextinstr rs) m'
  end.

(** Operations over condition bits. *)

(*- E_COMPCERT_FTR_Function_Asm_reg_of_crbit_001 *)
(*- #Justify_Derived "Auxiliary function for compare" *)
Definition reg_of_crbit (bit: crbit) :=
  match bit with
  | CRbit_0 => CR0_0
  | CRbit_1 => CR0_1
  | CRbit_2 => CR0_2
  | CRbit_3 => CR0_3
  | CRbit_5 => CR1_1
  | CRbit_6 => CR1_2
  end.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Asm_compare_sint_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_005 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Definition compare_sint (rs: regset) (v1 v2: val) :=
  rs#CR0_0 <- (Val.cmp Clt v1 v2)
    #CR0_1 <- (Val.cmp Cgt v1 v2)
    #CR0_2 <- (Val.cmp Ceq v1 v2)
    #CR0_3 <- Vundef.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Asm_compare_uint_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_005 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Definition compare_uint (rs: regset) (m: mem) (v1 v2: val) :=
  rs#CR0_0 <- (Val.cmpu (Mem.valid_pointer m) Clt v1 v2)
    #CR0_1 <- (Val.cmpu (Mem.valid_pointer m) Cgt v1 v2)
    #CR0_2 <- (Val.cmpu (Mem.valid_pointer m) Ceq v1 v2)
    #CR0_3 <- Vundef.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Asm_compare_slong_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_005 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Definition compare_slong (rs: regset) (v1 v2: val) :=
  rs#CR0_0 <- (Val.of_optbool (Val.cmpl_bool Clt v1 v2))
    #CR0_1 <- (Val.of_optbool (Val.cmpl_bool Cgt v1 v2))
    #CR0_2 <- (Val.of_optbool (Val.cmpl_bool Ceq v1 v2))
    #CR0_3 <- Vundef.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Asm_compare_ulong_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_005 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Definition compare_ulong (rs: regset) (m: mem) (v1 v2: val) :=
  rs#CR0_0 <- (Val.of_optbool (Val.cmplu_bool (Mem.valid_pointer m) Clt v1 v2))
    #CR0_1 <- (Val.of_optbool (Val.cmplu_bool (Mem.valid_pointer m) Cgt v1 v2))
    #CR0_2 <- (Val.of_optbool (Val.cmplu_bool (Mem.valid_pointer m) Ceq v1 v2))
    #CR0_3 <- Vundef.
(*- #End *)


(** Execution of a single instruction [i] in initial state
    [rs] and [m].  Return updated state.  For instructions
    that correspond to actual PowerPC instructions, the cases are
    straightforward transliterations of the informal descriptions
    given in the PowerPC reference manuals.  For pseudo-instructions,
    refer to the informal descriptions given above.  Note that
    we set to [Vundef] the registers used as temporaries by the
    expansions of the pseudo-instructions, so that the PPC code
    we generate cannot use those registers to hold values that
    must survive the execution of the pseudo-instruction.
*)

(*- E_COMPCERT_FTR_Function_Asm_exec_instr_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_006 *)
Definition exec_instr (f: function) (i: instruction) (rs: regset) (m: mem) : outcome :=
  match i with
  | Padd rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.add rs#r1 rs#r2))) m
  | Pse_add rd r1 =>
      Next (nextinstr (rs#rd <- (Val.add rs#rd rs#r1))) m
  | Paddc rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.add rs#r1 rs#r2)
                       #CARRY <- (Val.add_carry rs#r1 rs#r2 Vzero))) m
  | Padde rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.add (Val.add rs#r1 rs#r2) rs#CARRY)
                       #CARRY <- (Val.add_carry rs#r1 rs#r2 rs#CARRY))) m
  | Paddze rd r1 =>
      Next (nextinstr (rs#rd <- (Val.add rs#r1 rs#CARRY)
                       #CARRY <- (Val.add_carry rs#r1 Vzero rs#CARRY))) m
  | Pallocframe sz ofs _ =>
      let (m1, stk) := Mem.alloc m 0 sz in
      let sp := Vptr stk Ptrofs.zero in
      match Mem.storev Mint32 m1 (Val.offset_ptr sp ofs) rs#GPR1 with
      | None => Stuck
      | Some m2 => Next (nextinstr (rs#GPR1 <- sp #GPR0 <- Vundef)) m2
      end
  | Pand_ rd r1 r2 =>
      let v := Val.and rs#r1 rs#r2 in
      Next (nextinstr (compare_sint (rs#rd <- v) v Vzero)) m
  | Pse_and_ rd r1 =>
      let v := Val.and rs#rd rs#r1 in
      Next (nextinstr (compare_sint (rs#rd <- v) v Vzero)) m
  | Pandc rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.and rs#r1 (Val.notint rs#r2)))) m
  | Pse_andc rd r1 =>
      Next (nextinstr (rs#rd <- (Val.and rs#rd (Val.notint rs#r1)))) m
  | Pbf bit lbl =>
      match rs#(reg_of_crbit bit) with
      | Vint n => if Int.eq n Int.zero then goto_label f lbl rs m else Next (nextinstr rs) m
      | _ => Stuck
      end
  | Pbt bit lbl =>
      match rs#(reg_of_crbit bit) with
      | Vint n => if Int.eq n Int.zero then Next (nextinstr rs) m else goto_label f lbl rs m
      | _ => Stuck
      end
  | Pbtbl r tbl =>
      match rs r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => goto_label f lbl (rs #GPR12 <- Vundef #GPR0 <- Vundef #CTR <- Vundef) m
          end
      | _ => Stuck
      end
  | Pcmplw r1 r2 =>
      Next (nextinstr (compare_uint rs m rs#r1 rs#r2)) m
  | Pcmpw r1 r2 =>
      Next (nextinstr (compare_sint rs rs#r1 rs#r2)) m
  | Pe_cror bd b1 b2 =>
      Next (nextinstr (rs#(reg_of_crbit bd) <- (Val.or rs#(reg_of_crbit b1) rs#(reg_of_crbit b2)))) m
  | Pdivw rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.divs rs#r1 rs#r2)))) m
  | Pdivwu rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.divu rs#r1 rs#r2)))) m
  | Peqv rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.notint (Val.xor rs#r1 rs#r2)))) m
  | Pextsb rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 8 rs#r1))) m
  | Pextsh rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 16 rs#r1))) m
  | Pfreeframe sz ofs =>
      match Mem.loadv Mint32 m (Val.offset_ptr rs#GPR1 ofs) with
      | None => Stuck
      | Some v =>
          match rs#GPR1 with
          | Vptr stk ofs =>
              match Mem.free m stk 0 sz with
              | None => Stuck
              | Some m' => Next (nextinstr (rs#GPR1 <- v)) m'
              end
          | _ => Stuck
          end
      end
  | Pisel rd r1 r2 bit =>
      let v :=
          match rs#(reg_of_crbit bit) with
          | Vint n => if Int.eq n Int.zero then rs#r2 else (gpr_or_zero rs r1)
          | _ => Vundef
          end in
      Next (nextinstr (rs #rd <- v #GPR0 <- Vundef)) m
  | Plbzx rd r1 r2 =>
      load2 Mint8unsigned rd r1 r2 rs m
  | Plhax rd r1 r2 =>
      load2 Mint16signed rd r1 r2 rs m
  | Plhzx rd r1 r2 =>
      load2 Mint16unsigned rd r1 r2 rs m
  | Plwzx rd r1 r2 =>
      load2 Mint32 rd r1 r2 rs m
  | Plwzx_a rd r1 r2 =>
      load2 Many32 rd r1 r2 rs m
  | Pmfcrbit rd bit =>
      Next (nextinstr (rs#rd <- (rs#(reg_of_crbit bit)))) m
  | Pse_mflr rd =>
      Next (nextinstr (rs#rd <- (rs#LR))) m
  | Pmr rd r1 =>
      Next (nextinstr (rs#rd <- (rs#r1))) m
  | Pmullw rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.mul rs#r1 rs#r2))) m
  | Pse_mullw rd r1 =>
      Next (nextinstr (rs#rd <- (Val.mul rs#rd rs#r1))) m
  | Pmulhw rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.mulhs rs#r1 rs#r2))) m
  | Pmulhwu rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.mulhu rs#r1 rs#r2))) m
  | Pnand rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.notint (Val.and rs#r1 rs#r2)))) m
  | Pnor rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.notint (Val.or rs#r1 rs#r2)))) m
  | Por rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.or rs#r1 rs#r2))) m
  | Pse_or rd r1 =>
      Next (nextinstr (rs#rd <- (Val.or rs#rd rs#r1))) m
  | Porc rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.or rs#r1 (Val.notint rs#r2)))) m
  | Pslw rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.shl rs#r1 rs#r2))) m
  | Pse_slw rd r1 =>
      Next (nextinstr (rs#rd <- (Val.shl rs#rd rs#r1))) m
  | Psraw rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.shr rs#r1 rs#r2) #CARRY <- (Val.shr_carry rs#r1 rs#r2))) m
  | Pse_sraw rd r1 =>
      Next (nextinstr (rs#rd <- (Val.shr rs#rd rs#r1) #CARRY <- (Val.shr_carry rs#rd rs#r1))) m
  | Psrawi rd r1 n =>
      Next (nextinstr (rs#rd <- (Val.shr rs#r1 (Vint n)) #CARRY <- (Val.shr_carry rs#r1 (Vint n)))) m
  | Psrw rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.shru rs#r1 rs#r2))) m
  | Pse_srw rd r1 =>
      Next (nextinstr (rs#rd <- (Val.shru rs#rd rs#r1))) m
  | Pstbx rd r1 r2 =>
      store2 Mint8unsigned rd r1 r2 rs m
  | Psthx rd r1 r2 =>
      store2 Mint16unsigned rd r1 r2 rs m
  | Pstwx rd r1 r2 =>
      store2 Mint32 rd r1 r2 rs m
  | Pstwx_a rd r1 r2 =>
      store2 Many32 rd r1 r2 rs m
  | Pfstwx rd r1 r2 =>
      store2 Mfloat32 rd r1 r2 rs m
  | Psubfc rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.sub rs#r2 rs#r1)
                       #CARRY <- (Val.add_carry rs#r2 (Val.notint rs#r1) Vone))) m
  | Pse_sub rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sub rs#rd rs#r1))) m
  | Psubfe rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.add (Val.add rs#r2 (Val.notint rs#r1)) rs#CARRY)
                       #CARRY <- (Val.add_carry rs#r2 (Val.notint rs#r1) rs#CARRY))) m
  | Pse_subf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sub rs#r1 rs#rd))) m
  | Pxor rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.xor rs#r1 rs#r2))) m
  | Plabel lbl =>
      Next (nextinstr rs) m
  | Pcfi_rel_offset ofs =>
      Next (nextinstr rs) m
  | Pbuiltin ef args res =>
      Stuck    (**r treated specially below *)
  (** VLE instructions *)
  | Pse_mr rd r1 =>
      Next (nextinstr (rs#rd <- (rs#r1))) m
  | Pse_mtar rd r1 =>
      Next (nextinstr (rs#rd <- (rs#r1))) m
  | Pse_mfar rd r1 =>
      Next (nextinstr (rs#rd <- (rs#r1))) m
  | Pe_and2i_ rd cst =>
      let v := Val.and rs#rd (const_low cst) in
      Next (nextinstr (compare_sint (rs#rd <- v) v Vzero)) m
  | Pe_and2is_ rd cst =>
      let v := Val.and rs#rd (const_high cst) in
      Next (nextinstr (compare_sint (rs#rd <- v) v Vzero)) m
  | Pe_add16i rd r1 cst =>
      Next (nextinstr (rs#rd <- (Val.add rs#r1 (const_low cst)))) m
  | Pe_add2is rd cst =>
      Next (nextinstr (rs#rd <- (Val.add rs#rd (const_high cst)))) m
  | Pse_addi rd imm =>
      Next (nextinstr (rs#rd <- (Val.add rs#rd (Vint imm)))) m
  | Pe_addic rd r1 imm =>
      Next (nextinstr (rs#rd <- (Val.add rs#r1 (Vint imm))
                       #CARRY <- (Val.add_carry rs#r1 (Vint imm) Vzero))) m
  | Pe_b lbl =>
      goto_label f lbl rs m
  | Pse_bctr sg =>
      Next (rs #PC <- (rs#CTR)) m
  | Pse_bctrl sg =>
      Next (rs#LR <- (Val.offset_ptr rs#PC Ptrofs.one) #PC <- (rs#CTR)) m
  | Pe_bl ident sg =>
      Next (rs#LR <- (Val.offset_ptr rs#PC Ptrofs.one) #PC <- (Genv.symbol_address ge ident Ptrofs.zero)) m
  | Pse_blr =>
      Next (rs#PC <- (rs#LR)) m
  | Pe_bs ident sg =>
      Next (rs#PC <- (Genv.symbol_address ge ident Ptrofs.zero)) m
  | Pse_cmp r1 r2 =>
      Next (nextinstr (compare_sint rs rs#r1 rs#r2)) m
  | Pe_cmp16i rd cst =>
      Next (nextinstr (compare_sint rs rs#rd (const_low cst))) m
  | Pse_cmpi rd cst =>
      Next (nextinstr (compare_sint rs rs#rd (Vint cst))) m
  | Pse_cmpl r1 r2 =>
      Next (nextinstr (compare_uint rs m rs#r1 rs#r2)) m
  | Pe_cmpl16i rd cst =>
      Next (nextinstr (compare_uint rs m rs#rd (const_low cst))) m
  | Pse_extsb rd =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 8 rs#rd))) m
  | Pse_extsh rd =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 16 rs#rd))) m
  | Pe_li rd cst =>
      Next (nextinstr (rs#rd <- (const_low cst))) m
  | Pse_bgeni rd n =>
      let amount := Int.sub (Int.repr 31) n in
      Next (nextinstr (rs#rd <- (Val.shl Vone (Vint amount)))) m
  | Pse_li rd cst =>
      Next (nextinstr (rs#rd <- (Vint cst))) m
  | Pe_lis rd cst =>
      Next (nextinstr (rs#rd <- (const_high cst))) m
  | Pe_lbz rd cst r1 =>
      load1 Mint8unsigned rd  cst r1 rs m
  | Pse_lbz rd cst r1 =>
      load1_non_zero Mint8unsigned rd (Cint cst) r1 rs m
  | Pe_lha rd cst r1 =>
      load1 Mint16signed rd cst r1 rs m
  | Pe_lhz rd cst r1 =>
      load1 Mint16unsigned rd cst r1 rs m
  | Pse_lhz rd cst r1 =>
      load1_non_zero Mint16unsigned rd (Cint cst) r1 rs m
  | Pe_lwz rd cst r1 =>
      load1 Mint32 rd cst r1 rs m
  | Pse_lwz rd cst r1 =>
      load1_non_zero Mint32 rd (Cint cst) r1 rs m
  | Pe_lwz_a rd cst r1 =>
      load1 Many32 rd cst r1 rs m
  | Pse_lwz_a rd cst r1 =>
      load1_non_zero Many32 rd (Cint cst) r1 rs m
  | Pfe_lwz rd cst r1 =>
      load1 Mfloat32 rd cst r1 rs m
  | Pfse_lwz rd cst r1 =>
      load1_non_zero Mfloat32 rd (Cint cst) r1 rs m
  | Pflwzx rd r1 r2 =>
      load2 Mfloat32 rd r1 r2 rs m
  | Pse_mtctr r1 =>
      Next (nextinstr (rs#CTR <- (rs#r1))) m
  | Pse_mtlr r1 =>
      Next (nextinstr (rs#LR <- (rs#r1))) m
  | Pe_or2i rd cst =>
      Next (nextinstr (rs#rd <- (Val.or rs#rd (const_low cst)))) m
  | Pe_or2is rd cst =>
      Next (nextinstr (rs#rd <- (Val.or rs#rd (const_high cst)))) m
  | Pse_srawi rd n =>
      Next (nextinstr (rs#rd <- (Val.shr rs#rd (Vint n)) #CARRY <- (Val.shr_carry rs#rd (Vint n)))) m
  | Pe_stb rd cst r1 =>
      store1 Mint8unsigned rd cst r1 rs m
  | Pse_stb rd cst r1 =>
      store1_non_zero Mint8unsigned rd (Cint cst) r1 rs m
  | Pe_sth rd cst r1 =>
      store1 Mint16unsigned rd cst r1 rs m
  | Pse_sth rd cst r1 =>
      store1_non_zero Mint16unsigned rd (Cint cst) r1 rs m
  | Pe_stw rd cst r1 =>
      store1 Mint32 rd cst r1 rs m
  | Pse_stw rd cst r1 =>
      store1_non_zero Mint32 rd (Cint cst) r1 rs m
  | Pe_stw_a rd cst r1 =>
      store1 Many32 rd cst r1 rs m
  | Pse_stw_a rd cst r1 =>
      store1_non_zero Many32 rd (Cint cst) r1 rs m
  | Pfe_stw rd cst r1 =>
      store1 Mfloat32 rd cst r1 rs m
  | Pfse_stw rd cst r1 =>
      store1_non_zero Mfloat32 rd (Cint cst) r1 rs m
  | Pe_subfic rd r1 imm =>
      Next (nextinstr (rs#rd <- (Val.sub (Vint imm) rs#r1)
                       #CARRY <- (Val.add_carry (Vint imm) (Val.notint rs#r1) Vone))) m
  | Pse_subi rd imm =>
      Next (nextinstr (rs#rd <- (Val.sub rs#rd (Vint imm)))) m
  | Pe_rlwinm rd r1 amount mask =>
      Next (nextinstr (rs#rd <- (Val.rolm rs#r1 amount mask))) m
  | Pe_rlwimi rd r1 amount mask =>
      Next (nextinstr (rs#rd <- (Val.or (Val.and rs#rd (Vint (Int.not mask)))
                                     (Val.rolm rs#r1 amount mask)))) m
  | Pe_xori rd r1 cst =>
      Next (nextinstr (rs#rd <- (Val.xor rs#r1 (Vint cst)))) m

  | Pefsabs rd r1 =>
      Next (nextinstr (rs#rd <- (Val.absfs rs#r1))) m
  | Pefsadd rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.addfs rs#r1 rs#r2))) m
  | Pefsdiv rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.divfs rs#r1 rs#r2))) m
  | Pefsmul rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.mulfs rs#r1 rs#r2))) m
  | Pefsneg rd r1 =>
      Next (nextinstr (rs#rd <- (Val.negfs rs#r1))) m
  | Pefssub rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.subfs rs#r1 rs#r2))) m
  | Plfis rd f =>
      Next (nextinstr (rs#rd <- (Vsingle f))) m
  | Pefscfsi rd r =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleofint rs#r)))) m
  | Pefscfui rd r =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleofintu rs#r)))) m
  | Pefsctsi rd r =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intofsingle rs#r)))) m
  | Pefsctui rd r =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intuofsingle rs#r)))) m
  | Pefscmpeq rd r =>
      Next (nextinstr (rs#CR0_0 <- Vundef
                       #CR0_1 <- (Val.cmpfs Ceq (rs#rd) (rs#r))
                       #CR0_2 <- Vundef
                       #CR0_3 <- Vundef)) m
  | Pefscmpgt rd r =>
      Next (nextinstr (rs#CR1_1 <- (Val.cmpfs Cgt (rs#rd) (rs#r))
                       #CR1_2 <- Vundef)) m
  | Pefscmplt rd r =>
      Next (nextinstr (rs#CR1_1 <- (Val.cmpfs Clt (rs#rd) (rs#r))
                       #CR1_2 <- Vundef)) m
  (** The following instructions and directives are not generated
      directly by [Asmgen], so we do not model them. *)
  | Pbdnz _
  | Pcntlzw _ _
  | Pe_creqv _ _ _
  | Pe_crxor _ _ _
  | Pdcbf _ _
  | Pdcbi _ _
  | Pdcbt _ _ _
  | Pdcbtst _ _ _
  | Pdcbtls _ _ _
  | Pdcbz _ _
  | Pe_lwzu _ _ _
  | Plwbrx _ _ _
  | Picbi _ _
  | Picbtls _ _ _
  | Pse_isync
  | Plhbrx _ _ _
  | Pmfcr _
  | Pmfspr _ _
  | Pmtspr _ _
  | Pstwbrx _ _ _
  | Psthbrx _ _ _
  | Pe_stwu _ _ _
  | Pstwux _ _ _
  | Psubfze _ _
  | Psync
  | Pcfi_adjust _ =>
      Stuck
  end.
(*- #End *)

(** Translation of the LTL/Linear/Mach view of machine registers
  to the PPC view.  Note that no LTL register maps to [GPR0].
  This register is reserved as a temporary to be used
  by the generated PPC code.  *)

(*- E_COMPCERT_FTR_Function_Asm_preg_of_001 *)
(*- #Justify_Derived "Auxiliary function for translating a Mach to an ASM register" *)
Definition preg_of (r: mreg) : preg :=
  match r with
  | R3 => GPR3  | R4 => GPR4  | R5 => GPR5  | R6 => GPR6
  | R7 => GPR7  | R8 => GPR8  | R9 => GPR9  | R10 => GPR10
  | R11 => GPR11 | R12 => GPR12
  | R14 => GPR14 | R15 => GPR15 | R16 => GPR16
  | R17 => GPR17 | R18 => GPR18 | R19 => GPR19 | R20 => GPR20
  | R21 => GPR21 | R22 => GPR22 | R23 => GPR23 | R24 => GPR24
  | R25 => GPR25 | R26 => GPR26 | R27 => GPR27 | R28 => GPR28
  | R29 => GPR29 | R30 => GPR30 | R31 => GPR31
  | Machregs.ErrorReg => ErrorReg
  end.
(*- #End *)

(** Undefine all registers except SP and callee-save registers *)

(*- E_COMPCERT_FTR_Function_Asm_undef_caller_save_regs_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_005 *)
Definition undef_caller_save_regs (rs: regset) : regset :=
  fun r =>
    if preg_eq r SP
    || In_dec preg_eq r (List.map preg_of (List.filter is_callee_save all_mregs))
    then rs r
    else Vundef.
(*- #End *)

(** Extract the values of the arguments of an external call.
    We exploit the calling conventions from module [Conventions], except that
    we use PPC registers instead of locations. *)

(*- E_COMPCERT_FTR_Function_Asm_extcall_arg_0_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_005 *)
Inductive extcall_arg (rs: regset) (m: mem): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m (R r) (rs (preg_of r))
  | extcall_arg_stack: forall ofs ty bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv (chunk_of_type ty) m
                (Val.offset_ptr (rs (IR GPR1)) (Ptrofs.repr bofs)) = Some v ->
      extcall_arg rs m (S Outgoing ofs ty) v.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Asm_extcall_arg_pair_0_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_005 *)
Inductive extcall_arg_pair (rs: regset) (m: mem): rpair loc -> val -> Prop :=
  | extcall_arg_one: forall l v,
      extcall_arg rs m l v ->
      extcall_arg_pair rs m (One l) v
  | extcall_arg_twolong: forall hi lo vhi vlo,
      extcall_arg rs m hi vhi ->
      extcall_arg rs m lo vlo ->
      extcall_arg_pair rs m (Twolong hi lo) (Val.longofwords vhi vlo).
(*- #End *)

(*- E_COMPCERT_FTR_Function_Asm_extcall_arguments_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_005 *)
Definition extcall_arguments
    (rs: regset) (m: mem) (sg: signature) (args: list val) : Prop :=
  list_forall2 (extcall_arg_pair rs m) (loc_arguments sg) args.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Asm_loc_external_result_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_005 *)
Definition loc_external_result (sg: signature) : rpair preg :=
  map_rpair preg_of (loc_result sg).
(*- #End *)

(** Execution of the instruction at [rs#PC]. *)

(*- E_COMPCERT_FTR_Function_Asm_state_0_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_001 *)
Inductive state: Type :=
  | State: regset -> mem -> state.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Asm_step_0_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_005 *)
Inductive step: state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some i ->
      exec_instr f i rs m = Next rs' m' ->
      step (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs GPR1) m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = nextinstr
              (set_res res vres
                (undef_regs (IR GPR0 :: map preg_of (destroyed_by_builtin ef)) rs)) ->
      step (State rs m) t (State rs' m')
  | exec_step_external:
      forall b ef args res rs m t rs' m',
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      external_call ef ge args m t res m' ->
      extcall_arguments rs m (ef_sig ef) args ->
      rs' = (set_pair (loc_external_result (ef_sig ef)) res (undef_caller_save_regs rs)) #PC <- (rs RA) ->
      step (State rs m) t (State rs' m').

(*- #End *)
End RELSEM.

(** Execution of whole programs. *)

(*- E_COMPCERT_FTR_Function_Asm_initial_state_0_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_002 *)
Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0,
      Genv.init_mem p = Some m0 ->
      let ge := Genv.globalenv p in
      let rs0 :=
        (Pregmap.init Vundef)
        # PC <- (Genv.symbol_address ge p.(prog_main) Ptrofs.zero)
        # LR <- Vnullptr
        # GPR1 <- Vnullptr in
      initial_state p (State rs0 m0).
(*- #End *)

(*- E_COMPCERT_FTR_Function_Asm_final_state_0_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_003 *)
Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs#PC = Vnullptr ->
      rs#GPR3 = Vint r ->
      final_state (State rs m) r.
(*- #End *)

(*- E_COMPCERT_FTR_Function_Asm_semantics_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEMANTIC_PRESERVATION_001 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEMANTIC_PRESERVATION_002 *)
(*- #Link_to E_COMPCERT_TOR_Function_SEM_ASM_001 *)
Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).
(*- #End *)

(** Determinacy of the [Asm] semantics. *)

Remark extcall_arguments_determ:
  forall rs m sg args1 args2,
  extcall_arguments rs m sg args1 -> extcall_arguments rs m sg args2 -> args1 = args2.
Proof.
  intros until m.
  assert (A: forall l v1 v2,
             extcall_arg rs m l v1 -> extcall_arg rs m l v2 -> v1 = v2).
  { intros. inv H; inv H0; congruence. }
  assert (B: forall p v1 v2,
             extcall_arg_pair rs m p v1 -> extcall_arg_pair rs m p v2 -> v1 = v2).
  { intros. inv H; inv H0.
    eapply A; eauto.
    f_equal; eapply A; eauto. }
  assert (C: forall ll vl1, list_forall2 (extcall_arg_pair rs m) ll vl1 ->
             forall vl2, list_forall2 (extcall_arg_pair rs m) ll vl2 -> vl1 = vl2).
  {
    induction 1; intros vl2 EA; inv EA.
    auto.
    f_equal; eauto. }
  intros. eapply C; eauto.
Qed.

Lemma semantics_determinate: forall p, determinate (semantics p).
Proof.
Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.
  intros; constructor; simpl; intros.
(* determ *)
  inv H; inv H0; Equalities.
  split. constructor. auto.
  discriminate.
  discriminate.
  assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst vargs0.
  exploit external_call_determ. eexact H5. eexact H11. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
  assert (args0 = args) by (eapply extcall_arguments_determ; eauto). subst args0.
  exploit external_call_determ. eexact H3. eexact H8. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
(* trace length *)
  red; intros. inv H; simpl.
  lia.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
(* initial states *)
  inv H; inv H0. f_equal. congruence.
(* final no step *)
  inv H. red; intros; red; intros. inv H; rewrite H0 in *; discriminate.
(* final states *)
  inv H; inv H0. congruence.
Qed.

(** Classification functions for processor registers (used in Asmgenproof). *)

Definition data_preg (r: preg) : bool :=
  match r with
  | IR GPR0 => false
  | PC => false    | LR => false    | CTR => false
  | CR0_0 => false | CR0_1 => false | CR0_2 => false | CR0_3 => false | CR1_1 => false |  CR1_2 => false
  | CARRY => false
  | _ => true
  end.
