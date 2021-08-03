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

(** Abstract syntax and semantics for PEAKTOP assembly language. *)

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

(** Registers, floating-point registers. *)

Inductive reg : Type :=
  | Reg0: reg  | Reg1: reg  | Reg2: reg  | Reg3: reg
  | Reg4: reg  | Reg5: reg  | Reg6: reg  | Reg7: reg
  | Reg8: reg  | Reg9: reg  | Reg10: reg | Reg11: reg
  | Reg12: reg | Reg13: reg | Reg14: reg | Reg15: reg
  | Reg16: reg | Reg17: reg | Reg18: reg | Reg19: reg
  | Reg20: reg | Reg21: reg | Reg22: reg | Reg23: reg
  | Reg24: reg | Reg25: reg | Reg26: reg | Reg27: reg
  | Reg28: reg | Reg29: reg | Reg30: reg | Reg31: reg.

Lemma reg_eq: forall (x y: reg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Inductive preg: Type :=
  | PC              (**r program counter *)
  | GPR  (r: reg)   (**r general purpose register *)
  | CRP             (**r call return pointer *)
  | ErrorReg.       (**r hack need for non-existing double registers *)

Coercion GPR: reg >-> preg.

Lemma preg_eq: forall (x y: preg), {x=y} + {x<>y}.
Proof. decide equality. apply reg_eq.  Defined.

Module PregEq.
  Definition t  := preg.
  Definition eq := preg_eq.
End PregEq.

Module Pregmap := EMap(PregEq).

(** Conventional names for stack pointer ([SP]) and temp register ([TMP]). *)

Notation "'SP'" := Reg0 (only parsing) : asm.
Notation "'TMP'" := Reg1 (only parsing) : asm.

(** ** Instruction set. *)

Definition label := positive.

(** Addressing modes that are possible *)
Inductive addressing : Type :=
  | ADimm (base: reg) (n : int) (**r base plus immediate offset *)
  | ADreg (base: reg) (r: reg) (**r base plus reg *)
  | ADregpostincr (r: reg).     (**r register is incremented afterwards *)


(** Instructions. *)

Inductive instruction: Type :=
  (** Moves *)
  | Pmov_rr (rd: reg) (r1: reg)          (**r move register to register *)
  | Pmov_ri (rd: reg) (n: int)           (**r load immediate to register *)
  | Pmovu_ri (rd: reg) (n: int)          (**r load unsigned immediate to register *)
  | Pmov_rs (rd: reg) (f: float32)       (**r load single immediate to register *)
  | Pmov_fcrp (rd: reg)                  (**r move CRP to reg *)
  | Pmov_tcrp (rd: reg)                  (**r move reg to CRP *)
  (** Load/Store variants of move *)
  | Pmov_mr (rd: reg) (a: addressing)    (**r load int32 *)
  | Pmov_mr_a (rd: reg) (a: addressing)  (**r load int32 as any32 *)
  | Pmovh_mr (rd: reg) (a: addressing)   (**r load int16 *)
  | Pmovsh_mr (rd: reg) (a: addressing)  (**r load signed int16 *)
  | Pmovb_mr (rd: reg) (a: addressing)   (**r load int8 *)
  | Pmovsb_mr (rd: reg) (a: addressing)  (**r load signed int8 *)
  | Pfmov_mr (rd: reg) (a: addressing)   (**r load float32 *)
  | Pfmov_mr_a (rd: reg) (a: addressing) (**r load float32 as any32 *)
  | Pmov_rm (a: addressing) (rd: reg)    (**r store int32 *)
  | Pmov_rm_a (a: addressing) (rd: reg)  (**r store int32 as any32 *)
  | Pmovh_rm (a: addressing) (rd: reg)   (**r store int16 *)
  | Pmovb_rm (a: addressing) (rd: reg)   (**r store int8 *)
  | Pfmov_rm (a: addressing) (rd: reg)   (**r store float32 *)
  | Pfmov_rm_a (a: addressing) (rd: reg) (**r store float32 as any32 *)
  (** Integer arithmetic *)
  | Padd (rd: reg) (r: reg)             (**r integer addiction *)
  | Paddi (rd: reg) (imm: int)           (**r add immediate *)
  | Psub (rd: reg) (r: reg)             (**r integer subtraction *)
  | Psubi (rd: reg) (imm: int)           (**r sub immediate *)
  | Pmul (rd: reg) (r: reg)             (**r integer multiplication *)
  | Pmul_u (rd: reg) (r: reg)           (**r unsigned integer mulitplication *)
  | Pmuli (rd: reg) (imm: int)           (**r mul immediate *)
  | Pmulh (rd: reg) (r: reg)            (**r integer multiply high signed *)
  | Pmulhu (rd: reg) (r: reg)           (**r integer multiply high unsigned *)
  | Pdiv (rd: reg) (r: reg)             (**r integer division *)
  | Pdivu (rd: reg) (r: reg)            (**r integer unsigned division *)
  | Prem (rd: reg) (r: reg)             (**r integer remainder *)
  | Premu (rd: reg) (r: reg)            (**r unsigned integer remainder *)
  | Psll (rd: reg) (r: reg)             (**r shift-left-logical *)
  | Pslil (rd: reg) (imm: int)           (**r shift-left-logical immediate *)
  | Psrl (rd: reg) (r: reg)             (**r shift-right-logical *)
  | Psril (rd: reg) (imm: int)           (**r shift-right-logical immediate *)
  | Psra (rd: reg) (r: reg)             (**r shift-right arithmetic *)
  | Psrai (rd: reg) (imm: int)           (**r shift-right arithmetic immediate *)
  | Prr (rd: reg) (r: reg)              (**r rotate right *)
  | Prri (rd: reg) (imm: int)            (**r rr immediate *)
  | Pand (rd: reg) (r: reg)             (**r bitwise and *)
  | Pandi (rd: reg) (imm: int)           (**r and immediate *)
  | Pnand (rd: reg) (r: reg)            (**r bitwise nand *)
  | Pnandi (rd: reg) (imm: int)          (**r nand immediate *)
  | Por (rd: reg) (r: reg)              (**r bitwise or *)
  | Pori (rd: reg) (imm: int)            (**r or immediate *)
  | Porui (rd: reg) (imm: int)           (**r unsigned or immediate *)
  | Pxor (rd: reg) (r: reg)             (**r bitwise xor *)
  | Pxori (rd: reg) (imm: int)           (**r xor immediate *)
  | Ptbi (rd: reg) (imm: int)            (**r test if bit is set immediate *)
  | Ptb (rd: reg) (r: reg)              (**r test if bit is set *)
  | Pcmp_eq (rd: reg) (r1 r2: reg)      (**r signed integer compare equal *)
  | Pcmpu_eq (rd: reg) (r1 r2: reg)     (**r unsigned integer compare equal *)
  | Pcmp_lt (rd: reg) (r1 r2: reg)      (**r signed integer less than *)
  | Pcmpu_lt (rd: reg) (r1 r2: reg)     (**r unsigned integer less than *)
  | Pmad (rd: reg) (r1 r2: reg)        (**r integer fused multiply and add *)
  | Pmsu (rd: reg) (r1 r2: reg)        (**r integer fused multiply and sub *)
  (** 32-bit (single-precision) floating point *)
  | Pfadds (rd :reg) (r: reg)           (**r addition *)
  | Pfsubs (rd: reg) (r: reg)           (**r subtraction *)
  | Pfmuls (rd: reg) (r: reg)           (**r multiplication *)
  | Pfdivs (rd: reg) (r: reg)           (**r division *)
  | Pfcmp (rd: reg) (r: reg)            (**r floating point comparison *)
  | Pfsqr (rd: reg) (r: reg)            (**r floating point square root *)
  | Pfabs (rd: reg)                      (**r floating point absolute value *)
  | Pfneg (rd: reg)                      (**r floating point negate *)
  | Pff2i (rd: reg) (r:reg)             (**r single to signed int32 conversion *)
  | Pff2iu (rd: reg) (r: reg)           (**r single to unsigned int32 conversion *)
  | Pfi2f (rd: reg) (r: reg)            (**r signed int32 to single conversion *)
  | Pfiu2f (rd: reg) (r:reg)            (**r unsigned int32 to single conversion *)
  | Pfmad (rd: reg) (rs1 rs2: reg)      (**r floating point fused multiply and addition *)
  | Pfmsu (rd: reg) (rs1 rs2: reg)      (**r floating point fused multiply and subtraction *)
  (** Branches *)
  | Pjmp_l (l: label)                     (**r unconditional jump to label *)
  | Pjmp (r: reg) (sg: signature)        (**r branch to register *)
  | Pjmp_s (id: ident) (sg: signature)    (**r branch to symbol *)
  | Pjmp_p (r: reg) (sg: signature)      (**r branch and link *)
  | Pjmp_sp (id: ident) (sg: signature)   (**r branch and link to symbol *)
  | Pbz (r: reg) (l: label)              (**r branch if zero *)
  | Pbnz (r: reg) (l: label)             (**r branch if not zero *)
  | Pbm (r: reg) (l: label)              (**r branch if less than zero aka msb is set *)
  | Pbmz (r: reg) (l: label)             (**r branch if less or equal zero aka msb is set or zero *)
  | Pbnm (r: reg) (l: label)             (**r brach if greater equal zero aka msb is not set *)
  | Pret                                  (**r return from procedure *)
  (** Pseudo-instructions *)
  | Pallocframe (sz: Z) (linkofs: ptrofs) (**r allocate new stack frame *)
  | Pfreeframe (sz: Z) (linkofs: ptrofs)  (**r deallocate stack frame and restore previous frame *)
  | Plabel (lbl: label)                   (**r define a code label *)
  | Ploadsymbol (rd: reg) (id: ident) (ofs: ptrofs) (**r load the address of [id] *)
  | Pnop                                             (**r no operation *)
  | Pcfi_adjust (ofs: int)                           (**r .cfi_adjust debug directive *)
  | Pcfi_rel_offset (ofs: int)                       (**r .cfi_rel_offset debug directive *)
  | Pbtbl (r1: reg) (tbl: list label)               (**r N-way branch through a jump table *)
  | Pbuiltin (ef: external_function)
             (args: list (builtin_arg preg)) (res: builtin_res preg)  (**r built-in function (pseudo) *)
  | Prvbi (rd: reg) (imm: int)                      (**r reverse [imm] of bits *)
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

(** Addressing modes that are possible *)

Definition eval_addressing (a: addressing) (rs: regset) : val :=
  match a with
  | ADimm base n => Val.add rs#base (Vint n)
  | ADreg base r => Val.add rs#base rs#r
  | ADregpostincr r => Vundef (* not modeled yet *)
  end.

(** Auxiliaries for memory accesses *)

Definition exec_load (chunk: memory_chunk) (rs: regset) (m: mem)
                     (r: preg) (a: addressing) :=
  match Mem.loadv chunk m (eval_addressing a rs) with
  | None => Stuck
  | Some v => Next (nextinstr (rs#r <- v)) m
  end.

Definition exec_store (chunk: memory_chunk) (rs: regset) (m: mem)
                      (a: addressing) (v: val) :=
  match Mem.storev chunk m (eval_addressing a rs) v with
  | None => Stuck
  | Some m' => Next (nextinstr rs) m'
  end.

(** Auxiliaries for compare *)

Definition cmpfs_float (v1 v2: val) :=
  match v1, v2 with
  | Vsingle f1, Vsingle f2 =>
    if Float32.cmp Ceq f1 f2
    then Vint (Int.shl Int.one (Int.repr 5))
    else if Float32.cmp Cgt f1 f2
    then Vint (Int.shl Int.one (Int.repr 6))
    else if Float32.cmp Clt f1 f2
    then Vint (Int.shl Int.one (Int.repr 7))
    else  Vint (Int.shl Int.one (Int.repr 9))
  | _, _  => Vundef
  end.

(** Evaluating a branch *)

Definition eval_branch (f: function) (l: label) (rs: regset) (m: mem) (res: option bool) : outcome :=
  match res with
    | Some true  => goto_label f l rs m
    | Some false => Next (nextinstr rs) m
    | None => Stuck
  end.

Definition exec_instr (f: function) (i: instruction) (rs: regset) (m: mem) : outcome :=
  match i with
  (** Moves *)
  | Pmov_rr rd r1 =>
    Next (nextinstr (rs#rd <- (rs r1))) m
  | Pmov_ri rd n =>
    Next (nextinstr (rs#rd <- (Vint n))) m
  | Pmovu_ri rd n =>
    Next (nextinstr (rs#rd <- (Vint n))) m
  | Pmov_rs rd f =>
    Next (nextinstr (rs#rd <- (Vsingle f))) m
  | Pmov_fcrp rd =>
    Next (nextinstr (rs#rd <- (rs#CRP))) m
  | Pmov_tcrp r =>
    Next (nextinstr (rs#CRP <- (rs#r))) m
  (** Load/Store variants of move *)
  | Pmov_mr rd a =>
    exec_load Mint32 rs m rd a
  | Pmov_mr_a rd a =>
    exec_load Many32 rs m rd a
  | Pmovh_mr rd a =>
    exec_load Mint16unsigned rs m rd a
  | Pmovsh_mr rd a =>
    exec_load Mint16signed rs m rd a
  | Pmovb_mr rd a =>
    exec_load Mint8unsigned rs m rd a
  | Pmovsb_mr rd a =>
    exec_load Mint8signed rs m rd a
  | Pfmov_mr rd a =>
    exec_load Mfloat32 rs m rd a
  | Pfmov_mr_a rd a =>
    exec_load Many32 rs m rd a
  | Pmov_rm a rd =>
    exec_store Mint32 rs m a rs#rd
  | Pmov_rm_a a rd =>
    exec_store Many32 rs m a rs#rd
  | Pmovh_rm a rd =>
    exec_store Mint16unsigned rs m a rs#rd
  | Pmovb_rm a rd =>
    exec_store Mint8unsigned rs m a rs#rd
  | Pfmov_rm a rd =>
    exec_store Mfloat32 rs m a rs#rd
  | Pfmov_rm_a a rd =>
    exec_store Many32 rs m a rs#rd
  (** Integer arithmetic *)
  | Padd rd r =>
    Next (nextinstr (rs#rd <- (Val.add rs#rd rs#r))) m
  | Paddi rd imm =>
    Next (nextinstr (rs#rd <- (Val.add rs#rd (Vint imm)))) m
  | Psub rd r =>
    Next (nextinstr (rs#rd <- (Val.sub rs#rd rs#r))) m
  | Psubi rd imm =>
    Next (nextinstr (rs#rd <- (Val.sub rs#rd (Vint imm)))) m
  | Pmul rd r =>
    Next (nextinstr (rs#rd <- (Val.mul rs#rd rs#r))) m
  | Pmuli rd imm =>
    Next (nextinstr (rs#rd <- (Val.mul rs#rd (Vint imm)))) m
  | Pmulh rd r =>
    Next (nextinstr (rs#rd <- (Val.mulhs rs#rd rs#r))) m
  | Pmulhu rd r =>
    Next (nextinstr (rs#rd <- (Val.mulhu rs#rd rs#r))) m
  | Pdiv rd r =>
    Next (nextinstr (rs#rd <- (Val.maketotal (Val.divs rs#rd rs#r)))) m
  | Pdivu rd r =>
    Next (nextinstr (rs#rd <- (Val.maketotal (Val.divu rs#rd rs#r)))) m
  | Prem rd r =>
    Next (nextinstr (rs#rd <- (Val.maketotal (Val.mods rs#rd rs#r)))) m
  | Premu rd r =>
    Next (nextinstr (rs#rd <- (Val.maketotal (Val.modu rs#rd rs#r)))) m
  | Psll rd r =>
    Next (nextinstr (rs#rd <- (Val.shl rs#rd rs#r))) m
  | Pslil rd imm =>
    Next (nextinstr (rs#rd <- (Val.shl rs#rd (Vint imm)))) m
  | Psrl rd r =>
    Next (nextinstr (rs#rd <- (Val.shru rs#rd rs#r))) m
  | Psril rd imm =>
    Next (nextinstr (rs#rd <- (Val.shru rs#rd (Vint imm)))) m
  | Psra rd r =>
    Next (nextinstr (rs#rd <- (Val.shr rs#rd rs#r))) m
  | Psrai rd imm =>
    Next (nextinstr (rs#rd <- (Val.shr rs#rd (Vint imm)))) m
  | Prr rd r =>
    Next (nextinstr (rs#rd <- (Val.ror rs#rd rs#r))) m
  | Prri rd imm =>
    Next (nextinstr (rs#rd <- (Val.ror rs#rd (Vint imm)))) m
  | Pand rd r =>
    Next (nextinstr (rs#rd <- (Val.and rs#rd rs#r))) m
  | Pandi rd imm =>
    Next (nextinstr (rs#rd <- (Val.and rs#rd (Vint imm)))) m
  | Pnand rd r =>
    Next (nextinstr (rs#rd <- (Val.notint (Val.and rs#rd rs#r)))) m
  | Pnandi rd imm =>
    Next (nextinstr (rs#rd <- (Val.notint (Val.and rs#rd (Vint imm))))) m
  | Por rd r =>
    Next (nextinstr (rs#rd <- (Val.or rs#rd rs#r))) m
  | Pori rd imm =>
    Next (nextinstr (rs#rd <- (Val.or rs#rd (Vint imm)))) m
  | Porui rd imm =>
    Next (nextinstr (rs#rd <- (Val.or rs#rd (Vint imm)))) m
  | Pxor rd r =>
    Next (nextinstr (rs#rd <- (Val.xor rs#rd rs#r))) m
  | Pxori rd imm =>
    Next (nextinstr (rs#rd <- (Val.xor rs#rd (Vint imm)))) m
  | Ptb rd r =>
    let res := Val.cmp Cne (Val.and rs#rd (Val.shl Vone rs#r)) Vzero in
    Next (nextinstr (rs#rd <- res)) m
  | Ptbi rd imm =>
    let res := Val.cmp Cne (Val.and rs#rd (Val.shl Vone (Vint imm))) Vzero in
    Next (nextinstr (rs#rd <- res)) m
  | Pcmp_eq rd r1 r2 =>
    Next (nextinstr (rs#rd <- (Val.cmp Ceq rs#r1 rs#r2))) m
  | Pcmpu_eq rd r1 r2 =>
    Next (nextinstr (rs#rd <- (Val.cmpu (Mem.valid_pointer m) Ceq rs#r1 rs#r2))) m
  | Pcmp_lt rd r1 r2 =>
    Next (nextinstr (rs#rd <- (Val.cmp Clt rs#r1 rs#r2))) m
  | Pcmpu_lt rd r1 r2 =>
    Next (nextinstr (rs#rd <- (Val.cmpu (Mem.valid_pointer m) Clt rs#r1 rs#r2))) m
  | Pmad rd r1 r2 =>
    Next (nextinstr (rs#rd <- (Val.add (Val.mul rs#rd rs#r1) rs#r2))) m
  | Pmsu rd r1 r2 =>
    Next (nextinstr (rs#rd <- (Val.sub (Val.mul rs#rd rs#r1) rs#r2))) m
  (** 32-bit (single-precision) floating point *)
  | Pfadds rd r =>
    Next (nextinstr (rs#rd <- (Val.addfs rs#rd rs#r))) m
  | Pfsubs rd r =>
    Next (nextinstr (rs#rd <- (Val.subfs rs#rd rs#r))) m
  | Pfmuls rd r =>
    Next (nextinstr (rs#rd <- (Val.mulfs rs#rd rs#r))) m
  | Pfdivs rd r =>
    Next (nextinstr (rs#rd <- (Val.divfs rs#rd rs#r))) m
  | Pfcmp rd r =>
    Next (nextinstr (rs#rd <- (cmpfs_float rs#rd rs#r))) m
  | Pfabs rd =>
    Next (nextinstr (rs#rd <- (Val.absfs rs#rd))) m
  | Pfneg rd =>
    Next (nextinstr (rs#rd <- (Val.negfs rs#rd))) m
  | Pff2i rd r =>
    Next (nextinstr (rs#rd <- (Val.maketotal (Val.intofsingle rs#r)))) m
  | Pff2iu rd r =>
    Next (nextinstr (rs#rd <- (Val.maketotal (Val.intuofsingle rs#r)))) m
  | Pfi2f rd r =>
    Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleofint rs#r)))) m
  | Pfiu2f rd r =>
    Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleofintu rs#r)))) m
  (** Branches *)
  | Pjmp_l l =>
    goto_label f l rs m
  | Pjmp r sg =>
    Next (rs#PC <- (rs#r)) m
  | Pjmp_s id sg =>
    Next (rs#PC <- (Genv.symbol_address ge id Ptrofs.zero)) m
  | Pjmp_p r sg =>
    Next (rs#CRP <- (Val.offset_ptr rs#PC Ptrofs.one) #PC <- (rs r)) m
  | Pjmp_sp id sg =>
    Next (rs#CRP <- (Val.offset_ptr rs#PC Ptrofs.one) #PC <- (Genv.symbol_address ge id Ptrofs.zero)) m
  | Pbz r lbl =>
    match Val.cmpu_bool (Mem.valid_pointer m) Ceq (rs # r) (Vint Int.zero) with
    | Some true => goto_label f lbl rs m
    | Some false => Next (nextinstr rs) m
    | None => Stuck
    end
  | Pbnz r lbl =>
    match Val.cmpu_bool (Mem.valid_pointer m) Ceq (rs # r) (Vint Int.zero) with
    | Some true => Next (nextinstr rs) m
    | Some false => goto_label f lbl rs m
    | None => Stuck
    end
  | Pbm r lbl =>
    match Val.cmp_bool Clt (rs # r) (Vint Int.zero) with
    | Some true => goto_label f lbl rs m
    | Some false => Next (nextinstr rs) m
    | None => Stuck
    end
  | Pbmz r lbl =>
    match Val.cmp_bool Cle (rs # r) (Vint Int.zero) with
    | Some true => goto_label f lbl rs m
    | Some false => Next (nextinstr rs) m
    | None => Stuck
    end
  | Pbnm r lbl =>
    match Val.cmp_bool Cge (rs # r) (Vint Int.zero) with
    | Some true => goto_label f lbl rs m
    | Some false => Next (nextinstr rs) m
    | None => Stuck
    end
  | Pret =>
    Next (rs#PC <- (rs#CRP)) m
  | Pallocframe sz pos =>
      let (m1, stk) := Mem.alloc m 0 sz in
      let sp := (Vptr stk Ptrofs.zero) in
      match Mem.storev Mint32 m1 (Val.offset_ptr sp pos) rs#SP with
      | None => Stuck
      | Some m2 => Next (nextinstr (rs# Reg2 <- (rs#SP)# SP <- sp # TMP <- Vundef)) m2
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
  | Ploadsymbol rd id ofs =>
    Next (nextinstr (rs#rd <- (Genv.symbol_address ge id ofs))) m
  | Pbtbl r tbl =>
    match rs#r with
    | Vint n =>
      match list_nth_z tbl (Int.unsigned n) with
      | None => Stuck
      | Some lbl => goto_label f lbl rs m
      end
    | _ => Stuck
    end
  | Pbuiltin ef args res => Stuck    (**r treated specially below *)
  (** The following instructions and directives are not generated directly by Asmgen,
      so we do not model them. *)
  | Pfsqr _ _
  | Pfmad _ _ _
  | Pfmsu _ _ _
  | Pmul_u _ _
  | Pnop
  | Pcfi_adjust _
  | Pcfi_rel_offset _
  | Prvbi _ _ =>
    Stuck
  end.


(** Translation of the LTL/Linear/Mach view of machine registers to
  the PEAKTOP view. *)

Definition preg_of (r: mreg) : preg :=
  match r with
  | R2 => Reg2   | R3 => Reg3   | R4 => Reg4   | R5 => Reg5
  | R6 => Reg6   | R7 => Reg7   | R8 => Reg8   | R9 => Reg9
  | R10 => Reg10 | R11 => Reg11 | R12 => Reg12 | R13 => Reg13
  | R14 => Reg14 | R15 => Reg15 | R16 => Reg16 | R17 => Reg17
  | R18 => Reg18 | R19 => Reg19 | R20 => Reg20 | R21 => Reg21
  | R22 => Reg22 | R23 => Reg23 | R24 => Reg24 | R25 => Reg25
  | R26 => Reg26 | R27 => Reg27 | R28 => Reg28 | R29 => Reg29
  | R30 => Reg30 | R31 => Reg31
  | Machregs.ErrorReg => ErrorReg
  end.

(** Undefine all registers except SP and callee-save registers *)

Definition undef_caller_save_regs (rs: regset) : regset :=
  fun r =>
    if preg_eq r SP
    || In_dec preg_eq r (List.map preg_of (List.filter is_callee_save all_mregs))
    then rs r
    else Vundef.

(** Extract the values of the arguments of an external call.
    We exploit the calling conventions from module [Conventions], except that
    we use PEAKTOP registers instead of locations. *)

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
      rs' = (set_pair (loc_external_result (ef_sig ef) ) res (undef_caller_save_regs rs))#PC <- (rs CRP) ->
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
        # CRP <- Vnullptr in
      Genv.init_mem p = Some m0 ->
      initial_state p (State rs0 m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs PC = Vnullptr ->
      rs Reg4 = Vint r ->
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
  | GPR Reg1 => false
  | GPR _   => true
  | CRP => false
  | PC     => false
  | ErrorReg => true
  end.
