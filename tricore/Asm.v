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

(** Abstract syntax and semantics for TriCore assembly language *)
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
Require Stacklayout.
Require Import Conventions.

(** Integer registers and address registers. *)

Inductive dreg : Type :=
  | D0  : dreg | D1  : dreg | D2  : dreg | D3  : dreg
  | D4  : dreg | D5  : dreg | D6  : dreg | D7  : dreg
  | D8  : dreg | D9  : dreg | D10 : dreg | D11 : dreg
  | D12 : dreg | D13 : dreg | D14 : dreg | D15 : dreg.

Inductive areg : Type :=
  | A0  : areg | A1  : areg | A2  : areg | A3  : areg
  | A4  : areg | A5  : areg | A6  : areg | A7  : areg
  | A8  : areg | A9  : areg | A10 : areg | A11 : areg
  | A12 : areg | A13 : areg | A14 : areg | A15 : areg.

Lemma dreg_eq: forall (x y: dreg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Lemma areg_eq: forall (x y: areg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Inductive preg: Type :=
  | PC             (**r program counter *)
  | DREG (r: dreg) (**r data register *)
  | AREG (r: areg) (**r address register *)
  | PSW_C          (**r carry bit of the program status word register *)
  | ErrorReg.      (**r hack need for non-existing double registers *)

Coercion DREG: dreg >-> preg.
Coercion AREG: areg >-> preg.

Lemma preg_eq: forall (x y: preg), {x=y} + {x<>y}.
Proof. decide equality. apply dreg_eq. apply areg_eq.  Defined.

Module PregEq.
  Definition t  := preg.
  Definition eq := preg_eq.
End PregEq.

Module Pregmap := EMap(PregEq).

(** Conventional names for stack pointer ([SP]) and temp register ([TMP]). *)

Declare Scope asm.
Notation "'SP'" := A10 (only parsing) : asm.
Notation "'RA'" := A11 (only parsing) : asm.
Notation "'TMP'" := D0 (only parsing) : asm.
Notation "'TMPA'" := A14 (only parsing) : asm.

(** ** Instruction set. *)

Definition is_in_signed_range (n: Z) amount :=
  Int.lt (Int.repr (-two_p (n - 1) - 1)) amount && Int.lt amount (Int.repr (two_p (n - 1) )).

Record signed_const_n (n: Z) : Type := {
  s_amount :> int;
  s_range :  is_in_signed_range n s_amount = true /\ 0 < n < 31 }.

Record unsigned_const_n (n: Z) : Type := {
  u_amount :> int;
  u_range :  Int.ltu u_amount (Int.repr (two_p n)) = true /\ 0 < n < Int.zwordsize }.

Definition sconst4 := signed_const_n 4.
Definition sconst9 := signed_const_n 9.
Definition sconst16 := signed_const_n 16.

Definition uconst2 := unsigned_const_n 2.
Definition uconst4 := unsigned_const_n 4.
Definition uconst5 := unsigned_const_n 5.
Definition uconst8 := unsigned_const_n 8.
Definition uconst9 := unsigned_const_n 9.
Definition uconst16 := unsigned_const_n 16.

Program Definition sconst16_zero : sconst16 := {|s_amount := Int.zero|}.
Next Obligation.
unfold is_in_signed_range. split; try auto; lia.
Qed.

Definition label := positive.

(** Instructions. *)

Inductive instruction: Type :=
  (** Moves *)
  | Pmov (rd: dreg) (r: dreg)                 (**r move data register to data register *)
  | Pmov_aa (rd: areg) (r: areg)              (**r move address register to address register *)
  | Pmov_a (rd: areg) (r: dreg)               (**r move data register to address register *)
  | Pmov_d (rd: dreg) (r: areg)               (**r move address register to data register *)
  (** Constant moves etc. *)
  | Pmovh (rd: dreg) (imm: uconst16)          (**r move high [rd = (imm << 16)] *)
  | Pmovh_s (rd: dreg) (id: ident)
            (ofs: ptrofs)                     (**r move high part of symbol [rd = high_half(id,ofs)] *)
  | Pmovh_as (rd: areg) (id: ident)           (**r move high part of symbol [rd = high_half(id,0)] *)
  | Pmovh_ao (rd: areg) (imm: uconst16)       (**r move high [rd = (imm << 16)] *)
  | Pmovi (rd: dreg) (imm: sconst16)          (**r move offset into register [rd = offset] *)
  | Plea_s (rd r: areg) (id: ident)           (**r load effective address [rd = r + (low_half id)] *)
  | Plea_sc16 (rd r: areg) (imm: sconst16)    (**r load effective address [rd = r + imm] *)
  (** Comparison operations *)
  | Peq (rd r1 r2: dreg)                      (**r integer equal [rd = r1 == r2] *)
  | Peq_sc9 (rd r: dreg) (imm: sconst9)       (**r integer eqaul [rd = r == imm] *)
  | Pne (rd r1 r2: dreg)                      (**r integer equal [rd = r1 != r2] *)
  | Pne_sc9 (rd r: dreg) (imm: sconst9)       (**r integer eqaul [rd = r != imm] *)
  | Plt (rd r1 r2: dreg)                      (**r integer less than [rd = r1 < r2] *)
  | Plt_sc9 (rd r: dreg) (imm: sconst9)       (**r integer less than [rd = r < imm] *)
  | Pltu (rd r1 r2: dreg)                     (**r integer unsigned less than [rd = r1 < r2] *)
  | Pltu_uc9 (rd r: dreg) (imm: uconst9)      (**r integer unsigned less than [rd = r < imm] *)
  | Pge (rd r1 r2: dreg)                      (**r integer greater equal [rd = r1 >= r2] *)
  | Pge_sc9 (rd r: dreg) (imm: sconst9)       (**r integer greater equal [rd = r >= imm] *)
  | Pgeu (rd r1 r2: dreg)                     (**r integer unsigned greater equal [rd = r1 >= r2] *)
  | Pgeu_uc9 (rd r: dreg) (imm: uconst9)      (**r integer unsigned greater equal [rd = r >= imm] *)
  (** Integer add instructions *)
  | Padd (rd r1 r2: dreg)                     (**r integer add [rd = r1 + r2] *)
  | Padd_sc4 (rd: dreg) (imm: sconst4)        (**r integer add [rd = rd + imm] *)
  | Padd_rr (rd r: dreg)                      (**r integer add [rd = rd + r] *)
  | Paddi (rd r: dreg) (imm: sconst16)        (**r integer add [rd = r + imm] *)
  | Paddi_ls (rd r: dreg) (id: ident)
             (ofs: ptrofs)                    (**r integer add low half [rd = r + low_half(id,ofs)]*)
  | Paddc (rd r1 r2: dreg)                    (**r integer add with carry [rd = r1 + r2 + PSW.C] *)
  | Paddx (rd r1 r2: dreg)                    (**r integer add and set carry [rd = r1 + r2, PSW.C = carry(r1 + r2)] *)
  | Paddih (rd r: dreg) (imm: uconst16)       (**r integer add high [rd = r + (imm << 16)] *)
  | Padd_a (rd r1 r2: areg)                   (**r address add [rd = r1 + r2] *)
  | Padd_asc4 (rd: areg) (imm: sconst4)       (**r address add [rd = rd + imm] *)
  | Padd_aa (rd r: areg)                      (**r address add [rd = r1 + r2] *)
  | Paddsc_a (rd r1: areg) (r2: dreg)
             (imm: uconst2)                   (**r address scaled index [rd = r1 + (r2 << imm)] *)
  | Paddih_a (rd r: areg) (imm: uconst16)     (**r integer add high [rd = r # (imm << 16)] *)
  | Pcadd_sc9 (rd c d: dreg) (imm: sconst9)   (**r conditional sub [rd = c != 0 ? d1 - d2 : d1 ] *)
  (** Integer sub instructions *)
  | Psub (rd r1 r2: dreg)                     (**r integer sub [rd = r1 - r2] *)
  | Psub_rr (rd r: dreg)                      (**r integer sub [rd = rd - r1] *)
  | Prsub (rd r: dreg) (imm: sconst9)         (**r integer reverse sub [rd = imm - r] *)
  | Prsub_r (rd: dreg)                        (**r integer neg [rd = 0 - rd] *)
  | Pcsub (rd c d1 d2: dreg)                  (**r conditional sub [rd = c != 0 ? d1 - d2 : d1 ] *)
  (** Integer mul instructions *)
  | Pmul (rd r1 r2: dreg)                     (**r integer mul [rd = r1 * r2] *)
  | Pmul_rr (rd r: dreg)                      (**r integer mul [rd = rd * r] *)
  | Pmul_sc9 (rd r: dreg) (imm: sconst9)      (**r integer mul [rd = r * imm] *)
  | Pmadd (rd r1 r2 r3: dreg)                 (**r integer mul and add [rd = r1 + (r2 * r3)] *)
  | Pmadd_sc9 (rd r1 r2: dreg) (imm: sconst9) (**r integer mul and add [rd = r1 + (r2 * imm)] *)
  | Pmsub (rd r1 r2 r3: dreg)                 (**r integer mul and sub [rd = r1 - (r2 * r3)] *)
  | Pmsub_sc9 (rd r1 r2: dreg) (imm: sconst9) (**r integer mul and sub [rd = r1 - (r2 * imm)] *)
  | Pmul_e (r1 r2: dreg)                      (**r integer mul with full 64 bit result [D4, D5 = r1 * r2] *)
  | Pmulu (r1 r2: dreg)                       (**r integer unsigned mul with full 64 bit result [D4, D5 = r1 * r2] *)
  (** Integer div/rem instructions *)
  | Pdiv (r1 r2: dreg)                        (**r integer signed div and mod [D4 = r1 / r2, D5 = r1 % r2] *)
  | Pdivu (r1 r2: dreg)                       (**r integer unsigned div and mod [D4 = r1 / r2, D5 = r1 % r2] *)
  (** Integer not *)
  | Pnot (rd: dreg)                           (**r integer not [rd = ~rd] *)
  (** Integer and *)
  | Pand (rd r1 r2: dreg)                     (**r integer and [rd = r1 & r2] *)
  | Pand_rr (rd r: dreg)                      (**r integer and [rd = rd & r] *)
  | Pand_ruc9 (rd r: dreg) (imm: uconst9)     (**r integer and [rd = r & imm] *)
  | Pand_d15uc8 (imm: uconst8)                (**r integer and [d15 = d15 & imm] *)
  | Pandn (rd r1 r2: dreg)                    (**r integer and not [rd = r1 & ~r2] *)
  | Pandn_uc9 (rd r: dreg) (imm: uconst9)     (**r integer and not [rd = r & ~imm] *)
  | Pnand (rd r1 r2: dreg)                    (**r integer not and [rd = ~(r1 & r2)]*)
  | Pnand_uc9 (rd r: dreg) (imm: uconst9)     (**r integer not and [rd = ~(r & imm)]*)
  (** Integer or *)
  | Por (rd r1 r2: dreg)                      (**r integer or [rd = r1 | r2] *)
  | Por_rr (rd r: dreg)                       (**r integer or [rd = rd | r] *)
  | Por_ruc9 (rd r: dreg) (imm: uconst9)      (**r integer or [rd = r | imm] *)
  | Por_d15uc8 (imm: uconst8)                 (**r integer or [d15 = d15 | imm] *)
  | Porn (rd r1 r2: dreg)                     (**r integer or not [rd = r1 | ~r2] *)
  | Porn_uc9 (rd r: dreg) (imm: uconst9)      (**r integer or not [rd = r | ~imm] *)
  | Pnor (rd r1 r2: dreg)                     (**r integer not or [rd = ~(r1 | r2)]*)
  | Pnor_uc9 (rd r: dreg) (imm: uconst9)      (**r integer not or [rd = ~(r | imm)]*)
  | Por_t (rd : dreg)
          (r1: dreg) (pos1: uconst5)
          (r2: dreg) (pos2: uconst5)          (**r integer bitwise or [rd = r1[pos1] | r2[pos2]] *)
  | Pnor_t (rd : dreg)
          (r1: dreg) (pos1: uconst5)
          (r2: dreg) (pos2: uconst5)          (**r integer bitwise nor [rd = r1[pos1] | r2[pos2]] *)
  (** Integer xor*)
  | Pxor (rd r1 r2: dreg)                     (**r integer or [rd = r1 ^ r2] *)
  | Pxor_rr (rd r: dreg)                      (**r integer or [rd = rd ^ r] *)
  | Pxor_ruc9 (rd r: dreg) (imm: uconst9)     (**r integer or [rd = r ^ imm] *)
  | Pxnor (rd r1 r2: dreg)                    (**r integer not or [rd = ~(r1 ^ r2)] *)
  | Pxnor_uc9 (rd r: dreg) (imm: uconst9)     (**r integer not or [rd = ~(r ^ imm)] *)
  (** Integer shifts *)
  | Psh (rd r1 r2: dreg)                      (**r integer shift [rd = (r2 >= 0) ? r1 << r2 : r1 >> -r2] *)
  | Psh_sc9 (rd r : dreg) (imm: sconst9)      (**r integer shift [rd = (imm >= 0) ? r1 << imm : r1 >> -imm] *)
  | Psh_sc4 (rd: dreg) (imm: sconst4)         (**r integer shift [rd = (imm >= 0) ? rd << imm : rd >> -imm] *)
  | Psha (rd r1 r2: dreg)                     (**r integer arith shift [rd = (r2 >= 0) ? r1 << r2 : r1 >> -r2] *)
  | Psha_sc9 (rd r : dreg) (imm: sconst9)     (**r integer arith shift [rd = (imm >= 0) ? r1 << imm : r1 >> -imm] *)
  | Psha_sc4 (rd: dreg) (imm: sconst4)        (**r integer arith shift [rd = (imm >= 0) ? rd << imm : rd >> -imm] *)
  (** Integer Bit Field operations *)
  | Pextr (rd r: dreg) (pos width: uconst5)   (**r integer signed extract bit field *)
  | Pextru (rd r: dreg) (pos width: uconst5)  (**r integer unsigned extract bit field *)
  | Pdextr (rd r1 r2: dreg) (pos: uconst5)    (**r integer extract from double register *)
  | Pinsert (rd r1 r2: dreg)
            (pos width: uconst5)              (**r integer insert bit field *)
  | Pinsert_uc4 (rd r: dreg) (imm: uconst4)
                (pos width: uconst5)          (**r integer insert bit field immediate *)
  | Pinsn_t (rd r1 r2: dreg)
            (pos1 pos2: uconst5)              (**r integer insert negated bit *)
  (** Integer selection *)
  | Psel (rd cr r1 r2: dreg)                  (**r integer selection [rd = (cr != 0) ? r1 : r2] *)
  (** Float instructions *)
  | Pnegf (rd r: dreg)                        (**r single neg [rd = -r] *)
  | Pabsf (rd r: dreg)                        (**r single abs [rd = abs(r)] *)
  | Paddf (rd r1 r2: dreg)                    (**r single add [rd = r1 + r2] *)
  | Psubf (rd r1 r2: dreg)                    (**r single sub [rd = r1 + r2] *)
  | Pmulf (rd r1 r2: dreg)                    (**r single mul [rd = r1 * r2] *)
  | Pdivf (rd r1 r2: dreg)                    (**r single div [rd = r1 / r2] *)
  | Pcmpf (rd r1 r2: dreg)                    (**r single comparison [rd = cmpfs(r1, r2)] *)
  | Pftoiz (rd r: dreg)                       (**r single to signed integer *)
  | Pftouz (rd r: dreg)                       (**r single to unsigned integer *)
  | Pitof (rd r: dreg)                        (**r signed integer to single *)
  | Putof (rd r: dreg)                        (**r unsigned integer to single *)
  (** Unconditional jumps *)
  | Pj_l (lbl: label)                         (**r jump to label *)
  | Pj_s (symb: ident) (sg: signature)        (**r jump to symbol *)
  | Pji  (r: areg) (sg: signature)            (**r jump to register *)
  | Pcall (symb: ident) (sg: signature)       (**r call instruction *)
  | Pcalli (r: areg) (sg: signature)          (**r call instruction *)
  | Pret                                      (**r return instruction *)
  (** Conditional Branches *)
  | Pjeq (r1 r2: dreg) (lbl: label)           (**r branch if equal *)
  | Pjeq_sc4 (r: dreg)
             (imm: sconst4) (lbl: label)      (**r branch if equal with immediate *)
  | Pjge (r1 r2: dreg) (lbl: label)           (**r branch if greater equal *)
  | Pjge_sc4 (r: dreg)
             (imm: sconst4) (lbl: label)      (**r branch if greater equal with immediate *)
  | Pjgeu (r1 r2: dreg) (lbl: label)          (**r branch if unsigned greater equal *)
  | Pjgeu_sc4 (r: dreg)
             (imm: uconst4) (lbl: label)      (**r branch if unsigned greater equal with immediate *)
  | Pjlt (r1 r2: dreg) (lbl: label)           (**r branch if less than *)
  | Pjlt_sc4 (r: dreg)
             (imm: sconst4) (lbl: label)      (**r branch if less than with immediate *)
  | Pjltu (r1 r2: dreg) (lbl: label)          (**r branch if unsigned less than *)
  | Pjltu_sc4 (r: dreg)
             (imm: uconst4) (lbl: label)      (**r branch if unsigned less than with immediate *)
  | Pjne (r1 r2: dreg) (lbl: label)           (**r branch if not equal *)
  | Pjne_sc4 (r: dreg)
             (imm: sconst4) (lbl: label)      (**r branch if not equal with immediate *)
  | Pjnz_t (r: dreg)
           (n: uconst5) (lbl: label)          (**r branch if bit is not equal zero *)
  | Pjz_t (r: dreg)
           (n: uconst5) (lbl: label)          (**r branch if bit is not equal zero *)
  (** Loads and stores *)
  | Pldb (rd: dreg) (r: areg) (ofs: sconst16) (**r load signed int8 *)
  | Pldb_rr (rd: dreg) (r: areg)              (**r load signed int8 *)
  | Pldbu(rd: dreg) (r: areg) (ofs: sconst16) (**r load unsigned int8 *)
  | Pldbu_rr (rd: dreg) (r: areg)             (**r load unsigned int8 *)
  | Pldh (rd: dreg) (r: areg) (ofs: sconst16) (**r load signed int16 *)
  | Pldh_rr (rd: dreg) (r: areg)              (**r load signed int16 *)
  | Pldhu(rd: dreg) (r: areg) (ofs: sconst16) (**r load unsigned int16 *)
  | Pldhu_rr (rd: dreg) (r: areg)             (**r load unsigned int16 *)
  | Pldw (rd: dreg) (r: areg) (ofs: sconst16) (**r load int32 *)
  | Pldw_rr (rd: dreg) (r: areg)              (**r load int32 *)
  | Pfldw (rd: dreg) (r: areg)
          (ofs: sconst16)                     (**r load single *)
  | Pfldw_rr (rd: dreg) (r: areg)             (**r load single *)
  | Pldw_a (rd: dreg) (r: areg)
          (ofs: sconst16)                     (**r load any32 *)
  | Pldw_a_rr (rd: dreg) (r: areg)            (**r load any32 *)
  | Plda (rd: areg) (r: areg) (ofs: sconst16) (**r load int32 to address register *)
  | Plda_rr (rd: areg) (r: areg)              (**r load int32 to address register *)
  | Pstb (rd: dreg) (r: areg) (ofs: sconst16) (**r store signed int8 *)
  | Pstb_rr (rd: dreg) (r: areg)              (**r store signed int8 *)
  | Psth (rd: dreg) (r: areg) (ofs: sconst16) (**r store signed int16 *)
  | Psth_rr (rd: dreg) (r: areg)              (**r store signed int16 *)
  | Pstw (rd: dreg) (r: areg) (ofs: sconst16) (**r store int32 *)
  | Pstw_rr (rd: dreg) (r: areg)              (**r store int32 *)
  | Pfstw (rd: dreg) (r: areg) (ofs: sconst16)(**r store single *)
  | Pfstw_rr (rd: dreg) (r: areg)             (**r store single *)
  | Pstw_a (rd: dreg) (r: areg)
          (ofs: sconst16)                     (**r store any32 *)
  | Pstw_a_rr (rd: dreg) (r: areg)            (**r store any32 *)
  | Psta (rd: areg) (r: areg) (ofs: sconst16) (**r store int32 from address register *)
  | Psta_rr (rd: areg) (r: areg)              (**r store int32 from address register *)
  (** Pseudo-instructions *)
  | Ploadsi (rd: dreg) (f: float32)           (**r load a single immediate *)
  | Pallocframe (sz: Z) (linkofs: ptrofs)     (**r allocate new stack frame *)
  | Pfreeframe (sz: Z) (linkofs: ptrofs)      (**r deallocate stack frame and restore previous frame *)
  | Plabel (lbl: label)                       (**r define a code label *)
  | Pbtbl   (r: dreg)  (tbl: list label)      (**r N-way branch through a jump table *)
  | Pbuiltin (ef: external_function)
             (args: list (builtin_arg preg))
             (res: builtin_res preg)          (**r built-in function (pseudo) *)
  | Pshuffle (rd d: dreg) (imm: uconst9)      (**r shuffle the bits according to the immediate *)
  | Pclz (rd d: dreg)                         (**r count leading zeros *)
  | Psubc (rd d1 d2: dreg)                    (**r sub with carry *)
  | Psubx (rd d1 d2: dreg)                    (**r sub with carry and set carry *)
  | Pldbu_prr (rd: dreg) (r: areg)            (**r load unsigned int8 post increment *)
  | Pstb_prr (rd: dreg) (r: areg)             (**r store signed int8 post increment *)
  | Ploop (c: areg) (lbl: label)              (**r loop instruction *)
  | Pnop                                      (**r nop instruction *)
.

Definition code := list instruction.
Record function : Type := mkfunction { fn_sig: signature; fn_code: code }.
Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

(** * Operational semantics *)

(** The semantics operates over a single mapping from registers
  (type [preg]) to values. *)

Definition regset := Pregmap.t val.
Definition genv := Genv.t fundef unit.

(** Concise notations for accessing and updating the values of registers. *)

Notation "a # b" := (a b) (at level 1, only parsing) : asm.
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level) : asm.

Open Scope asm.

(** Undefining some registers *)

Fixpoint undef_regs (l: list preg) (rs: regset) : regset :=
  match l with
  | nil => rs
  | r :: l' => undef_regs l' (rs#r <- Vundef)
  end.

(** Assigning a register pair *)

Definition set_pair (p: rpair preg) (v: val) (rs: regset) : regset :=
  match p with
  | One r => rs#r <- v
  | Twolong rhi rlo => rs#rhi <- (Val.hiword v) #rlo <- (Val.loword v)
  end.

(** Assigning the result of a builtin *)

Fixpoint set_res (res: builtin_res preg) (v: val) (rs: regset) : regset :=
  match res with
  | BR r => rs#r <- v
  | BR_none => rs
  | BR_splitlong hi lo => set_res lo (Val.loword v) (set_res hi (Val.hiword v) rs)
  end.

Section RELSEM.

Variable ge: genv.

(** The two functions below axiomatize how the linker processes
  symbolic references [symbol + offset)] and splits their
  actual values into a 16-bit high part [%hi(symbol + offset)] and
  a 16-bit low part [%lo(symbol + offset)]. *)

Parameter low_half: genv -> ident -> ptrofs -> val.
Parameter high_half: genv -> ident -> ptrofs -> val.

(** The fundamental property of these operations is that, when applied
  to the address of a symbol, their results can be recombined by
  addition, rebuilding the original address. *)

Axiom low_high_half:
  forall id ofs,
  Val.add (high_half ge id ofs) (low_half ge id ofs) = Genv.symbol_address ge id ofs.

(** Looking up instructions in a code sequence by position. *)

Fixpoint find_instr (pos: Z) (c: code) {struct c} : option instruction :=
  match c with
  | nil => None
  | i :: il => if zeq pos 0 then Some i else find_instr (pos - 1) il
  end.

(** Position corresponding to a label *)

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Plabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Plabel lbl else instr <> Plabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate. destruct (peq lbl lbl0); congruence.
Qed.

Fixpoint label_pos (lbl: label) (pos: Z) (c: code) {struct c} : option Z :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some (pos + 1) else label_pos lbl (pos + 1) c'
  end.

(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [Next rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Stuck] if the processor is stuck. *)

Inductive outcome: Type :=
  | Next:  regset -> mem -> outcome
  | Stuck: outcome.

(** Manipulations over the [PC] register: continuing with the next
  instruction ([nextinstr]) or branching to a label ([goto_label]). *)

Definition nextinstr (rs: regset) :=
  rs#PC <- (Val.offset_ptr rs#PC Ptrofs.one).

Definition goto_label (f: function) (lbl: label) (rs: regset) (m: mem) :=
  match label_pos lbl 0 (fn_code f) with
  | None => Stuck
  | Some pos =>
      match rs#PC with
      | Vptr b ofs => Next (rs#PC <- (Vptr b (Ptrofs.repr pos))) m
      | _          => Stuck
      end
  end.

(** Auxiliaries for memory accesses *)

Definition exec_load (chunk: memory_chunk) (rs: regset) (m: mem)
                     (d: preg) (a: areg) (ofs: sconst16) :=
  match Mem.loadv chunk m (Val.offset_ptr (rs a) (Ptrofs.of_int ofs)) with
  | None => Stuck
  | Some v => Next (nextinstr (rs#d <- v)) m
  end.

Definition exec_store (chunk: memory_chunk) (rs: regset) (m: mem)
                      (s: preg) (a: areg) (ofs: sconst16) :=
  match Mem.storev chunk m (Val.offset_ptr (rs a) (Ptrofs.of_int ofs)) (rs s) with
  | None => Stuck
  | Some m' => Next (nextinstr rs) m'
  end.

(** Evaluating a branch *)

Definition eval_branch (f: function) (l: label) (rs: regset) (m: mem) (res: option bool) : outcome :=
  match res with
    | Some true  => goto_label f l rs m
    | Some false => Next (nextinstr rs) m
    | None => Stuck
  end.

(** Shift functions *)

Definition sh (v1 v2: val) : val :=
  match v1, v2 with
  | Vint i1, Vint i2 =>
      if Int.lt i2 Int.zero then
        Vint (Int.shru i1 (Int.neg i2))
      else
        Vint (Int.shl i1 i2)
  | _, _ => Vundef
  end.

Definition sha (v1 v2: val) : val :=
  match v1, v2 with
  | Vint i1, Vint i2 =>
      if Int.lt i2 Int.zero then
        Vint (Int.shr i1 (Int.neg i2))
      else
        Vint (Int.shl i1 i2)
  | _, _ => Vundef
  end.


(** Auxiliary for compare *)

(* Sets the results bits:
   * bit[0] = v1 < v2
   * bit[1] = v1 == v2
   * bit[2] = v1 > v2
   * bit[3] = Unordered
   The two bits not modeled are:
   * bit[4] = v1 is subnormal
   * bit[5] = v2 is subnormal
   The rest are cleared
 *)
Definition cmpfs (v1 v2: val) :=
  match v1, v2 with
  | Vsingle f1, Vsingle f2 =>
      if Float32.cmp Ceq f1 f2
      then Vint (Int.shl Int.one Int.one)
      else if Float32.cmp Cgt f1 f2
      then Vint (Int.shl Int.one (Int.repr 2))
      else if Float32.cmp Clt f1 f2
      then Vint (Int.shl Int.one Int.zero)
      else Vint (Int.shl Int.one (Int.repr 3))
  | _, _ => Vundef
  end.

Definition tb (v: val) (n: int): val :=
  Val.cmp Cne (Val.and v (Vint (Int.shl Int.one n))) Vzero.

Definition tb_bool (v: val) (n: int) : option bool :=
  Val.cmp_bool Cne (Val.and v (Vint (Int.shl Int.one n))) Vzero.

Definition tbz_bool (v: val) (n: int) : option bool :=
  Val.cmp_bool Ceq (Val.and v (Vint (Int.shl Int.one n))) Vzero.

Definition or_t (v1 v2: val) (pos1 pos2 : int) : val :=
    let v1 := tb v1 pos1 in
    let v2 := tb v2 pos2 in
    Val.or v1 v2.

Definition exec_instr (f: function) (i: instruction) (rs: regset) (m: mem) : outcome :=
  match i with
  | Pmov rd r => Next (nextinstr (rs#rd <- (rs r))) m
  | Pmov_aa rd r => Next (nextinstr (rs#rd <- (rs r))) m
  | Pmov_a rd r => Next (nextinstr (rs#rd <- (rs r))) m
  | Pmov_d rd r => Next (nextinstr (rs#rd <- (rs r))) m
  | Pmovh rd imm => Next (nextinstr (rs#rd <- (Vint (Int.shl imm (Int.repr 16))))) m
  | Pmovh_s rd id ofs => Next (nextinstr (rs#rd <- (high_half ge id ofs))) m
  | Pmovh_as rd id => Next (nextinstr (rs#rd <- (high_half ge id Ptrofs.zero))) m
  | Pmovh_ao rd imm => Next (nextinstr (rs#rd <- (Vint (Int.shl imm (Int.repr 16))))) m
  | Pmovi rd imm => Next (nextinstr (rs#rd <- (Vint imm))) m
  | Plea_s rd r id => Next (nextinstr (rs#rd <- (Val.add rs#r (low_half ge id Ptrofs.zero)))) m
  | Plea_sc16 rd r imm => Next (nextinstr (rs#rd <- (Val.add rs#r (Vint imm)))) m
  | Peq rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.cmpu (Mem.valid_pointer m) Ceq rs#r1 rs#r2))) m
  | Peq_sc9 rd r imm =>
      Next (nextinstr (rs#rd <- (Val.cmpu (Mem.valid_pointer m) Ceq rs#r (Vint imm)))) m
  | Pne rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.cmpu (Mem.valid_pointer m) Cne rs#r1 rs#r2))) m
  | Pne_sc9 rd r imm =>
      Next (nextinstr (rs#rd <- (Val.cmpu (Mem.valid_pointer m) Cne rs#r (Vint imm)))) m
  | Plt rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.cmp Clt rs#r1 rs#r2))) m
  | Plt_sc9 rd r imm =>
      Next (nextinstr (rs#rd <- (Val.cmp Clt rs#r (Vint imm)))) m
  | Pltu rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.cmpu (Mem.valid_pointer m) Clt rs#r1 rs#r2))) m
  | Pltu_uc9 rd r imm =>
      Next (nextinstr (rs#rd <- (Val.cmpu (Mem.valid_pointer m) Clt rs#r (Vint imm)))) m
  | Pge rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.cmp Cge rs#r1 rs#r2))) m
  | Pge_sc9 rd r imm =>
      Next (nextinstr (rs#rd <- (Val.cmp Cge rs#r (Vint imm)))) m
  | Pgeu rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.cmpu (Mem.valid_pointer m) Cge rs#r1 rs#r2))) m
  | Pgeu_uc9 rd r imm =>
      Next (nextinstr (rs#rd <- (Val.cmpu (Mem.valid_pointer m) Cge rs#r (Vint imm)))) m
  | Padd rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.add rs#r1 rs#r2))) m
  | Padd_sc4 rd imm => Next (nextinstr (rs#rd <- (Val.add rs#rd (Vint imm)))) m
  | Padd_rr rd r =>
      Next (nextinstr (rs#rd <- (Val.add rs#rd rs#r))) m
  | Paddi rd r1 imm => Next (nextinstr (rs#rd <- (Val.add rs#r1 (Vint imm)))) m
  | Paddi_ls rd r1 id ofs => Next (nextinstr (rs#rd <- (Val.add rs#r1 (low_half ge id ofs)))) m
  | Paddc rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.add (Val.add rs#r1 rs#r2) rs#PSW_C)
                         #PSW_C <- (Val.add_carry rs#r1 rs#r2 rs#PSW_C))) m
  | Paddx rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.add rs#r1 rs#r2)
                         #PSW_C <- (Val.add_carry rs#r1 rs#r2 Vzero))) m
  | Paddih rd r1 imm =>
      Next (nextinstr (rs#rd <- (Val.add rs#r1 (Vint (Int.shl imm (Int.repr 16)))))) m
  | Padd_a rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.add rs#r1 rs#r2))) m
  | Padd_asc4 rd imm => Next (nextinstr (rs#rd <- (Val.add rs#rd (Vint imm)))) m
  | Padd_aa rd r =>
      Next (nextinstr (rs#rd <- (Val.add rs#rd rs#r))) m
  | Paddsc_a rd r1 r2 imm =>
      (Next (nextinstr (rs#rd <- (Val.add rs#r1 (Val.shl rs#r2 (Vint imm)))))) m
  | Paddih_a rd r1 imm =>
      Next (nextinstr (rs#rd <- (Val.add rs#r1 (Vint (Int.shl imm (Int.repr 16)))))) m
  | Pcadd_sc9 rd c d imm =>
      let v :=
        match rs#c with
        | Vint n => if Int.eq n Int.zero then rs#d else Val.add rs#d (Vint imm)
        | _ => Vundef
        end in
      Next (nextinstr (rs#rd <- v)) m
  | Psub rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.sub rs#r1 rs#r2))) m
  | Psub_rr rd r =>
      Next (nextinstr (rs#rd <- (Val.sub rs#rd rs#r))) m
  | Prsub rd r imm =>
      Next (nextinstr (rs#rd <- (Val.sub (Vint imm) rs#r))) m
  | Prsub_r rd =>
      Next (nextinstr (rs#rd <- (Val.negint rs#rd))) m
  | Pcsub rd c d1 d2 =>
      let v :=
        match rs#c with
        | Vint n => if Int.eq n Int.zero then rs#d1 else Val.sub rs#d1 rs#d2
        | _ => Vundef
        end in
      Next (nextinstr (rs#rd <- v)) m
  (**r conditional sub [rd = c != 0 ? d1 - d2 : d1 ] *)
  | Pmul rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.mul rs#r1 rs#r2))) m
  | Pmul_rr rd r =>
      Next (nextinstr (rs#rd <- (Val.mul rs#rd rs#r))) m
  | Pmul_sc9 rd r imm =>
      Next (nextinstr (rs#rd <- (Val.mul rs#r (Vint imm)))) m
  | Pmadd rd r1 r2 r3 =>
      Next (nextinstr (rs#rd <- (Val.add rs#r1 (Val.mul rs#r2 rs#r3)))) m
  | Pmadd_sc9 rd r1 r2 imm =>
      Next (nextinstr (rs#rd <- (Val.add rs#r1 (Val.mul rs#r2 (Vint imm))))) m
  | Pmsub rd r1 r2 r3 =>
      Next (nextinstr (rs#rd <- (Val.sub rs#r1 (Val.mul rs#r2 rs#r3)))) m
  | Pmsub_sc9 rd r1 r2 imm =>
      Next (nextinstr (rs#rd <- (Val.sub rs#r1 (Val.mul rs#r2 (Vint imm))))) m
  | Pmul_e r1 r2 =>
      let v1 := Val.mul rs#r1 rs#r2 in
      let v2 := Val.mulhs rs#r1 rs#r2 in
      Next (nextinstr (rs#D4 <- v1 # D5 <- v2)) m
  | Pmulu r1 r2 =>
      let v1 := Val.mul rs#r1 rs#r2 in
      let v2 := Val.mulhu rs#r1 rs#r2 in
      Next (nextinstr (rs#D4 <- v1 # D5 <- v2)) m
  | Pdiv r1 r2 =>
      let v1 := Val.maketotal (Val.divs rs#r1 rs#r2) in
      let v2 := Val.maketotal (Val.mods rs#r1 rs#r2) in
      Next (nextinstr (rs#D4 <- v1 # D5 <- v2)) m
  | Pdivu r1 r2 =>
      let v1 := Val.maketotal (Val.divu rs#r1 rs#r2) in
      let v2 := Val.maketotal (Val.modu rs#r1 rs#r2) in
      Next (nextinstr (rs#D4 <- v1 # D5 <- v2)) m
  | Pnot rd =>
      Next (nextinstr (rs#rd <- (Val.notint rs#rd))) m
  | Pand rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.and rs#r1 rs#r2))) m
  | Pand_rr rd r =>
      Next (nextinstr (rs#rd <- (Val.and rs#rd rs#r))) m
  | Pand_ruc9 rd r imm =>
      Next (nextinstr (rs#rd <- (Val.and rs#r (Vint imm)))) m
  | Pand_d15uc8  imm =>
      Next (nextinstr (rs#D15 <- (Val.and rs#D15 (Vint imm)))) m
  | Pandn rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.and rs#r1 (Val.notint rs#r2)))) m
  | Pandn_uc9 rd r imm =>
      Next (nextinstr (rs#rd <- (Val.and rs#r (Vint (Int.not imm))))) m
  | Pnand rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.notint (Val.and rs#r1 rs#r2)))) m
  | Pnand_uc9 rd r imm =>
      Next (nextinstr (rs#rd <- (Val.notint (Val.and rs#r (Vint imm))))) m
  | Por rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.or rs#r1 rs#r2))) m
  | Por_rr rd r =>
      Next (nextinstr (rs#rd <- (Val.or rs#rd rs#r))) m
  | Por_ruc9 rd r imm =>
      Next (nextinstr (rs#rd <- (Val.or rs#r (Vint imm)))) m
  | Por_d15uc8  imm =>
      Next (nextinstr (rs#D15 <- (Val.or rs#D15 (Vint imm)))) m
  | Porn rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.or rs#r1 (Val.notint rs#r2)))) m
  | Porn_uc9 rd r imm =>
      Next (nextinstr (rs#rd <- (Val.or rs#r (Vint (Int.not imm))))) m
  | Pnor rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.notint (Val.or rs#r1 rs#r2)))) m
  | Pnor_uc9 rd r imm =>
      Next (nextinstr (rs#rd <- (Val.notint (Val.or rs#r (Vint imm))))) m
  | Por_t rd r1 pos1 r2 pos2 =>
      Next (nextinstr (rs#rd <- (or_t (rs#r1) (rs#r2) pos1 pos2))) m
  | Pnor_t rd r1 pos1 r2 pos2 =>
      Next (nextinstr (rs#rd <- (Val.notbool (or_t (rs#r1) (rs#r2) pos1 pos2)))) m
  | Pxor rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.xor rs#r1 rs#r2))) m
  | Pxor_rr rd r =>
      Next (nextinstr (rs#rd <- (Val.xor rs#rd rs#r))) m
  | Pxor_ruc9 rd r imm =>
      Next (nextinstr (rs#rd <- (Val.xor rs#r (Vint imm)))) m
  | Pxnor rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.notint (Val.xor rs#r1 rs#r2)))) m
  | Pxnor_uc9 rd r imm =>
      Next (nextinstr (rs#rd <- (Val.notint (Val.xor rs#r (Vint imm))))) m
  | Psh rd r1 r2 =>
      Next (nextinstr (rs#rd <- (sh rs#r1 rs#r2))) m
  | Psh_sc9 rd r imm =>
      Next (nextinstr (rs#rd <- (sh rs#r (Vint imm)))) m
  | Psh_sc4 rd imm =>
      Next (nextinstr (rs#rd <- (sh rs#rd (Vint imm)))) m
  | Psha rd r1 r2 =>
      Next (nextinstr (rs#rd <- (sha rs#r1 rs#r2))) m
  | Psha_sc9 rd r imm =>
      Next (nextinstr (rs#rd <- (sha rs#r (Vint imm)))) m
  | Psha_sc4 rd imm =>
      Next (nextinstr (rs#rd <- (sha rs#rd (Vint imm)))) m
  | Pextr rd r pos width =>
      Next (nextinstr (rs#rd <- (Op.extr pos width rs#r))) m
  | Pextru rd r pos width =>
      Next (nextinstr (rs#rd <- (Op.extru pos width rs#r))) m
  | Pinsert rd r1 r2 pos width =>
      Next (nextinstr (rs#rd <- (Op.insert_bits pos width rs#r1 rs#r2))) m
  | Pinsert_uc4 rd r imm pos width =>
      Next (nextinstr (rs#rd <- (Op.insert_bits pos width rs#r (Vint imm)))) m
  | Pinsn_t rd r1 r2 pos1 pos2 =>
      (* Extract bit from r2 at pos 2*)
      let bit := Val.notint (tb (rs#r2) pos2) in
      (* Use the insert instruction to put bit into r1 at pos1 with length 1*)
      Next (nextinstr (rs#rd <- (Op.insert_bits pos1 Int.one rs#r1 bit))) m
  | Psel rd cr r1 r2 =>
      let v :=
        match rs#cr with
        | Vint n => if Int.eq n Int.zero then rs#r2 else rs#r1
        | _ => Vundef
        end in
      Next (nextinstr rs#rd <- v) m
  | Pnegf rd r =>
      Next (nextinstr (rs#rd <- (Val.negfs rs#r))) m
  | Pabsf rd r =>
      Next (nextinstr (rs#rd <- (Val.absfs rs#r))) m
  | Paddf rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.addfs rs#r1 rs#r2))) m
  | Psubf rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.subfs rs#r1 rs#r2))) m
  | Pmulf rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.mulfs rs#r1 rs#r2))) m
  | Pdivf rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.divfs rs#r1 rs#r2))) m
  | Pcmpf rd r1 r2 =>
      Next (nextinstr (rs#rd <- (cmpfs rs#r1 rs#r2))) m
  | Pftoiz rd r =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intofsingle rs#r)))) m
  | Pftouz rd r =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intuofsingle rs#r)))) m
  | Pitof rd r =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleofint rs#r)))) m
  | Putof rd r =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleofintu rs#r)))) m
  | Pj_l lbl =>
      goto_label f lbl rs m
  | Pj_s s sg =>
      Next (rs#PC <- (Genv.symbol_address ge s Ptrofs.zero)) m
  | Pji r sg =>
      Next (rs#PC <- (rs#r)) m
  | Pcall s sg =>
      Next (rs#RA <- (Val.offset_ptr rs#PC Ptrofs.one)
              #PC <- (Genv.symbol_address ge s Ptrofs.zero)
           ) m
  | Pcalli r sg =>
      Next (rs#RA <- (Val.offset_ptr rs#PC Ptrofs.one)
             #PC <- (rs#r)
           ) m
  | Pret =>
      Next (rs#PC <- (rs#RA)) m
  | Pjeq r1 r2 lbl =>
      eval_branch f lbl rs m (Val.cmpu_bool (Mem.valid_pointer m) Ceq rs#r1 rs#r2)
  | Pjeq_sc4 r imm lbl =>
      eval_branch f lbl rs m (Val.cmpu_bool (Mem.valid_pointer m) Ceq rs#r (Vint imm))
  | Pjge r1 r2 lbl =>
      eval_branch f lbl rs m (Val.cmp_bool Cge rs#r1 rs#r2)
  | Pjge_sc4 r imm lbl =>
      eval_branch f lbl rs m (Val.cmp_bool Cge rs#r (Vint imm))
  | Pjgeu r1 r2 lbl =>
      eval_branch f lbl rs m (Val.cmpu_bool (Mem.valid_pointer m) Cge rs#r1 rs#r2)
  | Pjgeu_sc4 r imm lbl =>
      eval_branch f lbl rs m (Val.cmpu_bool (Mem.valid_pointer m) Cge rs#r (Vint imm))
  | Pjlt r1 r2 lbl =>
      eval_branch f lbl rs m (Val.cmp_bool Clt rs#r1 rs#r2)
  | Pjlt_sc4 r imm lbl =>
      eval_branch f lbl rs m (Val.cmp_bool Clt rs#r (Vint imm))
  | Pjltu r1 r2 lbl =>
      eval_branch f lbl rs m (Val.cmpu_bool (Mem.valid_pointer m) Clt rs#r1 rs#r2)
  | Pjltu_sc4 r imm lbl =>
      eval_branch f lbl rs m (Val.cmpu_bool (Mem.valid_pointer m) Clt rs#r (Vint imm))
  | Pjne r1 r2 lbl =>
      eval_branch f lbl rs m (Val.cmpu_bool (Mem.valid_pointer m) Cne rs#r1 rs#r2)
  | Pjne_sc4 r imm lbl =>
      eval_branch f lbl rs m (Val.cmpu_bool (Mem.valid_pointer m) Cne rs#r (Vint imm))
  | Pjnz_t r n lbl =>
      eval_branch f lbl rs m (tb_bool rs#r n)
  | Pjz_t r n lbl =>
      eval_branch f lbl rs m (tbz_bool rs#r n)
  | Pldb d a ofs =>
      exec_load Mint8signed rs m d a ofs
  | Pldb_rr d a =>
      exec_load Mint8signed rs m d a sconst16_zero
  | Pldbu d a ofs =>
      exec_load Mint8unsigned rs m d a ofs
  | Pldbu_rr d a =>
      exec_load Mint8unsigned rs m d a sconst16_zero
  | Pldh d a ofs =>
      exec_load Mint16signed rs m d a ofs
  | Pldh_rr d a =>
      exec_load Mint16signed rs m d a sconst16_zero
  | Pldhu d a ofs =>
      exec_load Mint16unsigned rs m d a ofs
  | Pldhu_rr d a =>
      exec_load Mint16unsigned rs m d a sconst16_zero
  | Pldw d a ofs =>
      exec_load Mint32 rs m d a ofs
  | Pldw_rr d a =>
      exec_load Mint32 rs m d a sconst16_zero
  | Pfldw d a ofs =>
      exec_load Mfloat32 rs m d a ofs
  | Pfldw_rr d a =>
      exec_load Mfloat32 rs m d a sconst16_zero
  | Pldw_a d a ofs =>
      exec_load Many32 rs m d a ofs
  | Pldw_a_rr d a =>
      exec_load Many32 rs m d a sconst16_zero
  | Plda d a ofs =>
      exec_load Mint32 rs m d a ofs
  | Plda_rr d a =>
      exec_load Mint32 rs m d a sconst16_zero
  | Pstb d a ofs =>
      exec_store Mint8unsigned rs m d a ofs
  | Pstb_rr d a =>
      exec_store Mint8unsigned rs m d a sconst16_zero
  | Psth d a ofs =>
      exec_store Mint16unsigned rs m d a ofs
  | Psth_rr d a =>
      exec_store Mint16unsigned rs m d a sconst16_zero
  | Pstw d a ofs =>
      exec_store Mint32 rs m d a ofs
  | Pstw_rr d a =>
      exec_store Mint32 rs m d a sconst16_zero
  | Pfstw d a ofs =>
      exec_store Mfloat32 rs m d a ofs
  | Pfstw_rr d a =>
      exec_store Mfloat32 rs m d a sconst16_zero
  | Pstw_a d a ofs =>
      exec_store Many32 rs m d a ofs
  | Pstw_a_rr d a =>
      exec_store Many32 rs m d a sconst16_zero
  | Psta d a ofs =>
      exec_store Mint32 rs m d a ofs
  | Psta_rr d a =>
      exec_store Mint32 rs m d a sconst16_zero
  | Ploadsi rd f =>
      Next (nextinstr (rs#rd <- (Vsingle f))) m
  | Pallocframe sz pos =>
      let (m1, stk) := Mem.alloc m 0 sz in
      let sp := (Vptr stk Ptrofs.zero) in
      match Mem.storev Mint32 m1 (Val.offset_ptr sp pos) rs#SP with
      | None => Stuck
      | Some m2 => Next (nextinstr (rs# A12 <- (rs#SP)# SP <- sp)) m2
      end
  | Pfreeframe sz pos =>
      match Mem.loadv Mint32 m (Val.offset_ptr rs#SP pos) with
      | None => Stuck
      | Some v =>
          match rs#SP with
          | Vptr stk ofs =>
              match Mem.free m stk 0 sz with
              | None => Stuck
              | Some m' => Next (nextinstr (rs#SP <- v)) m'
              end
          | _ => Stuck
          end
      end
  | Plabel lbl =>
      Next (nextinstr rs) m
  | Pbtbl r tbl =>
      match rs r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => goto_label f lbl (rs#TMPA <- Vundef) m
          end
      | _ => Stuck
      end
  | Pbuiltin ef args res => Stuck    (**r treated specially below *)
  | Pdextr _ _ _ _
  | Pshuffle _ _ _
  | Pclz _ _
  | Psubc _ _ _
  | Psubx _ _ _
  | Pldbu_prr _ _
  | Pstb_prr _ _
  | Ploop _ _
  | Pnop => Stuck
  end.

(** Translation of the LTL/Linear/Mach view of machine registers to
  the TriCore view. *)

Definition preg_of (r: mreg) : preg :=
  match r with
  | P2 => A2   | P3 => A3   | P4 => A4   | P5 => A5
  | P6 => A6   | P7 => A7   | P12 => A12
  | R1  => D1  | R2  => D2  | R3  => D3  | R4  => D4
  | R5  => D5  | R6  => D6  | R7  => D7  | R8  => D8
  | R9  => D9  | R10 => D10 | R11 => D11 | R12 => D12
  | R13 => D13 | R14 => D14 | R15 => D15
  | Machregs.ErrorReg => ErrorReg
  end.

Definition undef_caller_save_regs (rs: regset) : regset :=
  fun r =>
    if preg_eq r SP
    || In_dec preg_eq r (List.map preg_of (List.filter is_callee_save all_mregs))
    then rs r
    else Vundef.

(** Extract the values of the arguments of an external call.
    We exploit the calling conventions from module [Conventions], except that
    we use TriCore registers instead of locations. *)

Inductive extcall_arg (rs: regset) (m: mem): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m (R r) (rs (preg_of r))
  | extcall_arg_stack: forall ofs ty bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv (chunk_of_type ty) m
                (Val.offset_ptr (rs SP) (Ptrofs.repr bofs)) = Some v ->
      extcall_arg rs m (S Outgoing ofs ty) v.

Inductive extcall_arg_pair (rs: regset) (m: mem): rpair loc -> val -> Prop :=
  | extcall_arg_one: forall l v,
      extcall_arg rs m l v ->
      extcall_arg_pair rs m (One l) v
  | extcall_arg_twolong: forall hi lo vhi vlo,
      extcall_arg rs m hi vhi ->
      extcall_arg rs m lo vlo ->
      extcall_arg_pair rs m (Twolong hi lo) (Val.longofwords vhi vlo).

Definition extcall_arguments
    (rs: regset) (m: mem) (sg: signature) (args: list val) : Prop :=
  list_forall2 (extcall_arg_pair rs m) (loc_arguments sg) args.

Definition loc_external_result (sg: signature) : rpair preg :=
  map_rpair preg_of (loc_result sg).

(** Execution of the instruction at [rs#PC]. *)

Inductive state: Type :=
  | State: regset -> mem -> state.

Inductive step: state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      exec_instr f i rs m = Next rs' m' ->
      step (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs SP) m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = nextinstr
              (set_res res vres
                (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
      step (State rs m) t (State rs' m')
  | exec_step_external:
      forall b ef args res rs m t rs' m',
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      external_call ef ge args m t res m' ->
      extcall_arguments rs m (ef_sig ef) args ->
      rs' = (set_pair (loc_external_result (ef_sig ef) ) res (undef_caller_save_regs rs))#PC <- (rs RA) ->
      step (State rs m) t (State rs' m').

End RELSEM.

(** Execution of whole programs. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0,
      let ge := Genv.globalenv p in
      let rs0 :=
        (Pregmap.init Vundef)
        # PC <- (Genv.symbol_address ge p.(prog_main) Ptrofs.zero)
        # SP <- Vnullptr
        # RA <- Vnullptr in
      Genv.init_mem p = Some m0 ->
      initial_state p (State rs0 m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs PC = Vnullptr ->
      rs D2 = Vint r ->
      final_state (State rs m) r.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

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
- (* determ *)
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
- (* trace length *)
  red; intros. inv H; simpl.
  lia.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
- (* initial states *)
  inv H; inv H0. f_equal. congruence.
- (* final no step *)
  assert (NOTNULL: forall b ofs, Vnullptr <> Vptr b ofs).
  { intros; unfold Vnullptr; destruct Archi.ptr64; congruence. }
  inv H. unfold Vzero in H0. red; intros; red; intros.
  inv H; rewrite H0 in *; eelim NOTNULL; eauto.
- (* final states *)
  inv H; inv H0. congruence.
Qed.


(** Classification functions for processor registers (used in Asmgenproof). *)

Definition data_preg (r: preg) : bool :=
  match r with
  | DREG D0 => false
  | DREG _ => true
  | AREG A11 => false
  | AREG A14 => false
  | AREG _ => true
  | PC     => false
  | PSW_C => false
  | ErrorReg => true
  end.
