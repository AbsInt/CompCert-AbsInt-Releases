(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Expanding built-ins and some pseudo-instructions by rewriting
   of the IA32 assembly code.  *)

open Asm
open Asmexpandaux
open AST
open Camlcoq
open Datatypes

(* Useful constants and helper functions *)

let stack_alignment () = _16

(* SP adjustment to allocate or free a stack frame. *)

let align n a =
  if n >= 0 then (n + a - 1) land (-a) else n land (-a)

let sp_adjustment_32 sz =
  (* Preserve proper alignment of the stack *)
  let sz = Coqlib.align sz (stack_alignment ()) in
  (* The top 4 bytes have already been allocated by the "call" instruction. *)
  Z.sub sz _4

let sp_adjustment_elf64 sz =
  if is_current_function_variadic() then begin
    (* If variadic, add room for register save area, which must be 16-aligned *)
    let ofs = Coqlib.align (Z.sub sz _8) _16 in
    let sz = Z.(add ofs (add _176 (* save area *) _8 (* return address *))) in
    (* Preserve proper alignment of the stack *)
    let sz = Coqlib.align sz _16 in
    (* The top 8 bytes have already been allocated by the "call" instruction. *)
    (Z.sub sz _8, ofs)
  end else begin
    (* Preserve proper alignment of the stack *)
    let sz = Coqlib.align sz _16 in
    (* The top 8 bytes have already been allocated by the "call" instruction. *)
    (Z.sub sz _8, _m1)
  end

let sp_adjustment_win64 sz =
  (* Preserve proper alignment of the stack *)
  let sz = Coqlib.align sz _16 in
  (* The top 8 bytes have already been allocated by the "call" instruction. *)
  Z.sub sz _8

(* Built-ins.  They come in two flavors:
   - annotation statements: take their arguments in registers or stack
   locations; generate no code;
   - inlined by the compiler: take their arguments in arbitrary
   registers; preserve all registers except ECX, EDX, XMM6 and XMM7. *)

(* Handling of annotations *)

let expand_annot_val kind txt targ args res =
  emit (Pbuiltin (EF_annot(kind,txt,[targ]), args, BR_none));
  match args, res with
  | [BA(IR src)], BR(IR dst) ->
     if dst <> src then emit (Pmov_rr (dst,src))
  | [BA(FR src)], BR(FR dst) ->
     if dst <> src then emit (Pmovsd_ff (dst,src))
  | _, _ ->
     raise (AsmexpandError "ill-formed __builtin_annot_intval")

(* Operations on addressing modes *)

let offset_addressing (Addrmode(base, ofs, cst)) delta =
  Addrmode(base, ofs,
           match cst with
           | Coq_inl n -> Coq_inl(Z.add n delta)
           | Coq_inr(id, n) -> Coq_inr(id, Ptrofs.(add n (repr delta))))

let linear_addr reg ofs = Addrmode(Some reg, None, Coq_inl ofs)
let global_addr id ofs = Addrmode(None, None, Coq_inr(id, ofs))

(* A "leaq" instruction that does not overflow *)

let emit_leaq r addr =
  match Asmgen.normalize_addrmode_64 addr with
  | (addr, None) ->
      emit (Pleaq (r, addr))
  | (addr, Some delta) ->
      emit (Pleaq (r, addr));
      emit (Paddq_ri (r, delta))

(* Pseudo "lea" instruction for 32/64 bit compatibility *)

let emit_lea r addr =
  if Archi.ptr64 then emit_leaq r addr else emit (Pleal (r, addr))

(* Translate a builtin argument into an addressing mode *)

let addressing_of_builtin_arg = function
  | BA (IR r) -> linear_addr r Z.zero
  | BA_addrstack ofs -> linear_addr RSP (Ptrofs.unsigned ofs)
  | BA_addrglobal(id, ofs) -> global_addr id ofs
  | BA_addptr(BA (IR r), BA_int n) -> linear_addr r (I32.signed n)
  | BA_addptr(BA (IR r), BA_long n) -> linear_addr r (I64.signed n)
  | _ -> assert false

(* Handling of memcpy *)

(* Unaligned memory accesses are quite fast on IA32, so use large
   memory accesses regardless of alignment. *)

let expand_builtin_memcpy_small sz al src dst =
  let rec copy src dst sz =
    if Ptrofs.cmpu Cge sz _8p && Archi.ptr64 then begin
      emit (Pmovq_rm (RCX, src));
      emit (Pmovq_mr (dst, RCX));
      copy (offset_addressing src _8) (offset_addressing dst _8) (Ptrofs.sub sz _8p)
    end else if Ptrofs.cmpu Cge sz _8p && !Clflags.option_ffpu then begin
      emit (Pmovsq_rm (XMM7, src));
      emit (Pmovsq_mr (dst, XMM7));
      copy (offset_addressing src _8) (offset_addressing dst _8) (Ptrofs.sub sz _8p)
    end else if Ptrofs.cmpu Cge sz _4p then begin
      emit (Pmovl_rm (RCX, src));
      emit (Pmovl_mr (dst, RCX));
      copy (offset_addressing src _4) (offset_addressing dst _4) (Ptrofs.sub sz _4p)
    end else if Ptrofs.cmpu Cge sz _2p then begin
      emit (Pmovw_rm (RCX, src));
      emit (Pmovw_mr (dst, RCX));
      copy (offset_addressing src _2) (offset_addressing dst _2) (Ptrofs.sub sz _2p)
    end else if Ptrofs.cmpu Cge sz _1p then begin
      emit (Pmovb_rm (RCX, src));
      emit (Pmovb_mr (dst, RCX));
      copy (offset_addressing src _1) (offset_addressing dst _1) (Ptrofs.sub sz _1p)
    end in
  copy (addressing_of_builtin_arg src) (addressing_of_builtin_arg dst) sz

let expand_builtin_memcpy_big sz al src dst =
  if src <> BA (IR RSI) then emit_lea RSI (addressing_of_builtin_arg src);
  if dst <> BA (IR RDI) then emit_lea RDI (addressing_of_builtin_arg dst);
  (* TODO: movsq? *)
  (* TODO: fix for 64 bit x86 larger and sz >= 4GB *)
  emit (Pmovl_ri (RCX,Ptrofs.(to_int (divu sz _4p))));
  emit Prep_movsl;
  if Ptrofs.(cmpu Cge (modu sz _4p) _2p) then emit Pmovsw;
  if Ptrofs.(cmpu Cge (modu sz _2p) _1p) then emit Pmovsb

let expand_builtin_memcpy sz al args =
  let (dst, src) = match args with [d; s] -> (d, s) | _ -> assert false in
  if Ptrofs.cmpu Cle sz _32p
  then expand_builtin_memcpy_small sz al src dst
  else expand_builtin_memcpy_big sz al src dst

(* Handling of volatile reads and writes *)

let expand_builtin_vload_common chunk addr res =
  match chunk, res with
  | (Mbool | Mint8unsigned), BR(IR res) ->
     emit (Pmovzb_rm (res,addr))
  | Mint8signed, BR(IR res) ->
     emit (Pmovsb_rm (res,addr))
  | Mint16unsigned, BR(IR res) ->
     emit (Pmovzw_rm (res,addr))
  | Mint16signed, BR(IR res) ->
     emit (Pmovsw_rm (res,addr))
  | Mint32, BR(IR res) ->
     emit (Pmovl_rm (res,addr))
  | Mint64, BR(IR res) ->
     emit (Pmovq_rm (res,addr))
  | Mint64, BR_splitlong(BR(IR res1), BR(IR res2)) ->
     let addr' = offset_addressing addr _4 in
     if not (Asmgen.addressing_mentions addr res2) then begin
	 emit (Pmovl_rm (res2,addr));
	 emit (Pmovl_rm (res1,addr'))
       end else begin
	 emit (Pmovl_rm (res1,addr'));
	 emit (Pmovl_rm (res2,addr))
       end
  | Mfloat32, BR(FR res) ->
     emit (Pmovss_fm (res,addr))
  | Mfloat64, BR(FR res) ->
     emit (Pmovsd_fm (res,addr))
  | _ ->
     assert false

let expand_builtin_vload chunk args res =
  match args with
  | [addr] ->
     expand_builtin_vload_common chunk (addressing_of_builtin_arg addr) res
  | _ ->
     assert false

let expand_builtin_vstore_common chunk addr src tmp =
  match chunk, src with
  | (Mbool | Mint8signed | Mint8unsigned), BA(IR src) ->
     if Archi.ptr64 || Asmgen.low_ireg src then
       emit (Pmovb_mr (addr,src))
     else begin
       emit (Pmov_rr (tmp,src));
       emit (Pmovb_mr (addr,tmp))
     end
  | (Mint16signed | Mint16unsigned), BA(IR src) ->
     emit (Pmovw_mr (addr,src))
  | Mint32, BA(IR src) ->
     emit (Pmovl_mr (addr,src))
  | Mint64, BA(IR src) ->
     emit (Pmovq_mr (addr,src))
  | Mint64, BA_splitlong(BA(IR src1), BA(IR src2)) ->
     let addr' = offset_addressing addr _4 in
     emit (Pmovl_mr (addr,src2));
     emit (Pmovl_mr (addr',src1))
  | Mfloat32, BA(FR src) ->
     emit (Pmovss_mf (addr,src))
  | Mfloat64, BA(FR src) ->
     emit (Pmovsd_mf (addr,src))
  | _ ->
     assert false

let expand_builtin_vstore chunk args =
  match args with
  | [addr; src] ->
     let addr = addressing_of_builtin_arg addr in
     expand_builtin_vstore_common chunk addr src
       (if Asmgen.addressing_mentions addr RAX then RCX else RAX)
  | _ -> assert false

(* Handling of varargs *)

let rec next_arg_locations ir fr ofs = function
  | [] ->
      (ir, fr, ofs)
  | (Tint | Tlong | Tany32 | Tany64) :: l ->
      if ir < 6
      then next_arg_locations (ir + 1) fr ofs l
      else next_arg_locations ir fr (Z.add ofs _8) l
  | (Tfloat | Tsingle) :: l ->
      if fr < 8
      then next_arg_locations ir (fr + 1) ofs l
      else next_arg_locations ir fr (Z.add ofs _8) l

let current_function_stacksize = ref _0

let expand_builtin_va_start_32 r =
  if not (is_current_function_variadic ()) then
    invalid_arg "Fatal error: va_start used in non-vararg function";
  let ofs =
    Z.(add (add !current_function_stacksize _4)
               (mul _4 (Conventions.size_arguments
                                      (get_current_function_sig ())))) in
  emit (Pleal (RAX, linear_addr RSP ofs));
  emit (Pmovl_mr (linear_addr r _0, RAX))

let expand_builtin_va_start_elf64 r =
  if not (is_current_function_variadic ()) then
    invalid_arg "Fatal error: va_start used in non-vararg function";
  let (ir, fr, ofs) =
    next_arg_locations 0 0 _0 (get_current_function_args ()) in
  (* [r] points to the following struct:
       struct {
         unsigned int gp_offset;
         unsigned int fp_offset;
         void *overflow_arg_area;
         void *reg_save_area;
       }
     gp_offset is initialized to ir * 8
     fp_offset is initialized to  6 * 8 + fr * 16
     overflow_arg_area is initialized to sp + current stacksize + ofs
     reg_save_area is initialized to
         sp + current stacksize - 16 - save area size (6 * 8 + 8 * 16) *)
  let gp_offset = Int32.of_int (ir * 8)
  and fp_offset = Int32.of_int (6 * 8 + fr * 16)
  and overflow_arg_area = Z.add !current_function_stacksize ofs
  and reg_save_area = Z.sub !current_function_stacksize _192 in
  assert (r <> RAX);
  emit (Pmovl_ri (RAX, coqint_of_camlint gp_offset));
  emit (Pmovl_mr (linear_addr r _0, RAX));
  emit (Pmovl_ri (RAX, coqint_of_camlint fp_offset));
  emit (Pmovl_mr (linear_addr r _4, RAX));
  emit_leaq RAX (linear_addr RSP overflow_arg_area);
  emit (Pmovq_mr (linear_addr r _8, RAX));
  emit_leaq RAX (linear_addr RSP reg_save_area);
  emit (Pmovq_mr (linear_addr r _16, RAX))

let expand_builtin_va_start_win64 r =
  if not (is_current_function_variadic ()) then
    invalid_arg "Fatal error: va_start used in non-vararg function";
  let num_args =
    List.length (get_current_function_args()) in
  let ofs =
    Z.(add !current_function_stacksize
               (mul _8 (of_uint num_args))) in
  emit_leaq RAX (linear_addr RSP ofs);
  emit (Pmovq_mr (linear_addr r _0, RAX))

(* FMA operations *)

(*   vfmadd<i><j><k> r1, r2, r3   performs r1 := ri * rj + rk
   hence
     vfmadd132 r1, r2, r3    performs  r1 := r1 * r3 + r2
     vfmadd213 r1, r2, r3    performs  r1 := r2 * r1 + r3
     vfmadd231 r1, r2, r3    performs  r1 := r2 * r3 + r1
*)

let expand_fma args res i132 i213 i231 =
  match args, res with
  | [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      if res = a1 then emit (i132 a1 a3 a2)       (* a1 * a2 + a3 *)
      else if res = a2 then emit (i213 a2 a1 a3)  (* a1 * a2 + a3 *)
      else if res = a3 then emit (i231 a3 a1 a2)  (* a1 * a2 + a3 *)
      else begin
        emit (Pmovsd_ff(res, a3));
        emit (i231 res a1 a2)                     (* a1 * a2 + res *)
      end
  | _ ->
     invalid_arg ("ill-formed fma builtin")

(* Handling of compiler-inlined builtins *)

let expand_builtin_inline name args res =
  match name, args, res with
  (* Integer arithmetic *)
  | ("__builtin_bswap"| "__builtin_bswap32"), [BA(IR a1)], BR(IR res) ->
     if a1 <> res then
       emit (Pmov_rr (res,a1));
     emit (Pbswap32 res)
  | "__builtin_bswap64", [BA(IR a1)], BR(IR res) ->
     if a1 <> res then
       emit (Pmov_rr (res,a1));
     emit (Pbswap64 res)
  | "__builtin_bswap16", [BA(IR a1)], BR(IR res) ->
     if a1 <> res then
       emit (Pmov_rr (res,a1));
     emit (Pbswap16 res)
  | "__builtin_clz", [BA(IR a1)], BR(IR res) ->
     emit (Pbsrl (res,a1));
     emit (Pxorl_ri(res, _31l))
  | "__builtin_clzl", [BA(IR a1)], BR(IR res) ->
     if not(Archi.ptr64) then begin
       emit (Pbsrl (res,a1));
       emit (Pxorl_ri(res, _31l))
     end else begin
       emit (Pbsrq (res,a1));
       emit (Pxorl_ri(res, _63l))
     end
  | "__builtin_clzll", [BA(IR a1)], BR(IR res) ->
     emit (Pbsrq (res,a1));
     emit (Pxorl_ri(res, _63l))
  | "__builtin_clzll", [BA_splitlong(BA (IR ah), BA (IR al))], BR(IR res) ->
     let lbl1 = new_label() in
     let lbl2 = new_label() in
     emit (Ptestl_rr(ah, ah));
     emit (Pjcc(Cond_e, lbl1));
     emit (Pbsrl(res, ah));
     emit (Pxorl_ri(res, _31l));
     emit (Pjmp_l lbl2);
     emit (Plabel lbl1);
     emit (Pbsrl(res, al));
     emit (Pxorl_ri(res, _63l));
     emit (Plabel lbl2)
  | "__builtin_ctz", [BA(IR a1)], BR(IR res) ->
     emit (Pbsfl (res,a1))
  | "__builtin_ctzl", [BA(IR a1)], BR(IR res) ->
     if not(Archi.ptr64) then
       emit (Pbsfl (res,a1))
     else
       emit (Pbsfq (res,a1))
  | "__builtin_ctzll", [BA(IR a1)], BR(IR res) ->
     emit (Pbsfq (res,a1))
  | "__builtin_ctzll", [BA_splitlong(BA (IR ah), BA (IR al))], BR(IR res) ->
     let lbl1 = new_label() in
     let lbl2 = new_label() in
     emit (Ptestl_rr(al, al));
     emit (Pjcc(Cond_e, lbl1));
     emit (Pbsfl(res, al));
     emit (Pjmp_l lbl2);
     emit (Plabel lbl1);
     emit (Pbsfl(res, ah));
     emit (Paddl_ri(res, _32l));
     emit (Plabel lbl2)
  (* Float arithmetic *)
  | ("__builtin_fsqrt" | "__builtin_sqrt"), [BA(FR a1)], BR(FR res) ->
     emit (Psqrtsd (res,a1))
  | "__builtin_fmadd",  _, _ ->
      expand_fma args res
        (fun r1 r2 r3 -> Pfmadd132(r1, r2, r3))
        (fun r1 r2 r3 -> Pfmadd213(r1, r2, r3))
        (fun r1 r2 r3 -> Pfmadd231(r1, r2, r3))
  | "__builtin_fmsub",  _, _ ->
      expand_fma args res
        (fun r1 r2 r3 -> Pfmsub132(r1, r2, r3))
        (fun r1 r2 r3 -> Pfmsub213(r1, r2, r3))
        (fun r1 r2 r3 -> Pfmsub231(r1, r2, r3))
  | "__builtin_fnmadd",  _, _ ->
      expand_fma args res
        (fun r1 r2 r3 -> Pfnmadd132(r1, r2, r3))
        (fun r1 r2 r3 -> Pfnmadd213(r1, r2, r3))
        (fun r1 r2 r3 -> Pfnmadd231(r1, r2, r3))
  | "__builtin_fnmsub",  _, _ ->
      expand_fma args res
        (fun r1 r2 r3 -> Pfnmsub132(r1, r2, r3))
        (fun r1 r2 r3 -> Pfnmsub213(r1, r2, r3))
        (fun r1 r2 r3 -> Pfnmsub231(r1, r2, r3))
  | "__builtin_dtob", [BA(FR a1)],
                          BR_splitlong(BR(IR rh), BR(IR rl)) ->
     assert (not Archi.ptr64);
     emit (Psubl_ri (RSP, _8l));
     emit (Pcfi_adjust _8p);
     emit (Pmovsd_mf ((linear_addr RSP _0), a1));
     emit (Pmovl_rm (rl, (linear_addr RSP _0)));
     emit (Pmovl_rm (rh, (linear_addr RSP _4)));
     emit (Paddl_ri (RSP, _8l));
     emit (Pcfi_adjust _m8p)
  | "__builtin_dtob", [BA(FR a1)],
                          BR(IR res) ->
     assert (Archi.ptr64);
     emit (Psubq_ri (RSP, _16L));
     emit (Pcfi_adjust _16p);
     emit (Pmovsd_mf ((linear_addr RSP _0), a1));
     emit (Pmovq_rm (res, (linear_addr RSP _0)));
     emit (Paddq_ri (RSP, _16L));
     emit (Pcfi_adjust _m16p);

  (* Memory accesses *)
  | "__builtin_read16_reversed", [BA(IR a1)], BR(IR res) ->
     emit (Pmovzw_rm (res, linear_addr a1 _0));
     emit (Pbswap16 res)
  | "__builtin_read32_reversed", [BA(IR a1)], BR(IR res) ->
     emit (Pmovl_rm (res, linear_addr a1 _0));
     emit (Pbswap32 res)
  | "__builtin_write16_reversed", [BA(IR a1); BA(IR a2)], _ ->
     let tmp = if a1 = RCX then RDX else RCX in
     if a2 <> tmp then
       emit (Pmov_rr (tmp,a2));
     emit (Pbswap16 tmp);
     emit (Pmovw_mr (linear_addr a1 _0, tmp))
  | "__builtin_write32_reversed", [BA(IR a1); BA(IR a2)], _ ->
     let tmp = if a1 = RCX then RDX else RCX in
     if a2 <> tmp then
       emit (Pmov_rr (tmp,a2));
     emit (Pbswap32 tmp);
     emit (Pmovl_mr (linear_addr a1 _0, tmp))
  (* Vararg stuff *)
  | "__builtin_va_start", [BA(IR a)], _ ->
     assert (a = RDX);
     if Archi.win64 then expand_builtin_va_start_win64 a
     else if Archi.ptr64 then expand_builtin_va_start_elf64 a
     else expand_builtin_va_start_32 a
  (* Synchronization *)
  | "__builtin_membar", [], _ ->
     ()
  (* No operation *)
  | "__builtin_nop", [], _ ->
     emit Pnop
  (* Optimization hint *)
  | "__builtin_unreachable", [], _ ->
     ()
  (* Catch-all *)
  | _ ->
     raise (AsmexpandError ("unrecognized builtin " ^ name))

(* Calls to variadic functions for x86-64 ELF: register AL must contain
   the number of XMM registers used for parameter passing.  To be on
   the safe side, do the same if the called function is
   unprototyped. *)

let fixup_funcall_elf64 sg =
  if sg.sig_cc.cc_vararg <> None || sg.sig_cc.cc_unproto then begin
    let (ir, fr, ofs) = next_arg_locations 0 0 _0 (proj_sig_args sg) in
    emit (Pmovl_ri (RAX, coqint_of_camlint (Int32.of_int fr)))
  end

(* Calls to variadic functions for x86-64 Windows:
   FP arguments passed in FP registers must also be passed in integer
   registers.
*)

let rec copy_fregs_to_iregs args fr ir =
  match (ir, fr, args) with
  | (i1 :: ir, f1 :: fr, (Tfloat | Tsingle) :: args) ->
      emit (Pmovq_rf (i1, f1));
      copy_fregs_to_iregs args fr ir
  | (i1 :: ir, f1 :: fr, _ :: args) ->
      copy_fregs_to_iregs args fr ir
  | _ ->
      ()

let fixup_funcall_win64 sg =
  if sg.sig_cc.cc_vararg <> None then
    copy_fregs_to_iregs (proj_sig_args sg) [XMM0; XMM1; XMM2; XMM3] [RCX; RDX; R8; R9]

let fixup_funcall sg =
  if Archi.ptr64
  then if Archi.win64
       then fixup_funcall_win64 sg
       else fixup_funcall_elf64 sg
  else ()

(* Expansion of instructions *)

let expand_instruction instr =
  match instr with
  | Pallocframe (sz, ofs_ra, ofs_link) ->
     if Archi.win64 then begin
       let sz = sp_adjustment_win64 sz in
       (* Check stack size + 16 for additional stack used by built-ins *)
       check_stack_size (Z.add sz _16);
       if is_current_function_variadic() then
         (* Save parameters passed in registers in reserved stack area *)
         emit (Pcall_s (intern_string "__compcert_va_saveregs",
                        {sig_args = []; sig_res = Xvoid; sig_cc = cc_default}));
       (* Allocate frame *)
       emit (Psubq_ri (RSP, I64.repr sz));
       emit (Pcfi_adjust (Ptrofs.repr sz));
       let sz = Z.add sz _8 in
       (* Stack chaining *)
       let addr1 = linear_addr RSP sz in
       let addr2 = linear_addr RSP (Ptrofs.unsigned ofs_link) in
       emit_leaq RAX addr1;
       emit (Pmovq_mr (addr2, RAX));
       current_function_stacksize := sz
     end else if Archi.ptr64 then begin
       let (sz, save_regs) = sp_adjustment_elf64 sz in
       (* Check stack size + 16 for additional stack used by built-ins *)
       check_stack_size (Z.add sz _16);
       (* Allocate frame *)
       emit (Psubq_ri (RSP, I64.repr sz));
       emit (Pcfi_adjust (Ptrofs.repr sz));
       if Z.ge save_regs _0 then begin
         (* Save the registers *)
         emit_leaq R10 (linear_addr RSP save_regs);
         emit (Pcall_s (intern_string "__compcert_va_saveregs",
                        {sig_args = []; sig_res = Xvoid; sig_cc = cc_default}))
       end;
       (* Stack chaining *)
       let fullsz = Z.add sz _8 in
       let addr1 = linear_addr RSP fullsz in
       let addr2 = linear_addr RSP (Ptrofs.unsigned ofs_link) in
       emit_leaq RAX addr1;
       emit (Pmovq_mr (addr2, RAX));
       current_function_stacksize := fullsz
     end else begin
       let sz = sp_adjustment_32 sz in
       (* Check stack size + 8 for additional stack used by built-ins *)
       check_stack_size (Z.add sz _8);
       (* Allocate frame *)
       emit (Psubl_ri (RSP, I32.repr sz));
       emit (Pcfi_adjust (Ptrofs.repr sz));
       (* Stack chaining *)
       let addr1 = linear_addr RSP (Z.add sz _4) in
       let addr2 = linear_addr RSP (Ptrofs.unsigned ofs_link) in
       emit (Pleal (RAX,addr1));
       emit (Pmovl_mr (addr2,RAX));
       current_function_stacksize := sz
     end
  | Pfreeframe(sz, ofs_ra, ofs_link) ->
     if Archi.win64 then begin
       let sz = sp_adjustment_win64 sz in
       emit (Paddq_ri (RSP, I64.repr sz))
     end else if Archi.ptr64 then begin
       let (sz, _) = sp_adjustment_elf64 sz in
       emit (Paddq_ri (RSP, I64.repr sz))
     end else begin
       let sz = sp_adjustment_32 sz in
       emit (Paddl_ri (RSP, I32.repr sz))
     end
  | Pjmp_s(_, sg) | Pjmp_r(_, sg) | Pcall_s(_, sg) | Pcall_r(_, sg) ->
     fixup_funcall sg;
     emit instr
  | Pbuiltin (ef,args, res) ->
     begin
       match ef with
       | EF_builtin(name, sg) ->
	  expand_builtin_inline name args res
       | EF_vload chunk ->
          expand_builtin_vload chunk args res
       | EF_vstore chunk ->
          expand_builtin_vstore chunk args
       | EF_memcpy(sz, al) ->
          expand_builtin_memcpy sz al args
       | EF_annot_val(kind,txt, targ) ->
          expand_annot_val kind txt targ args res
       | EF_annot _ | EF_debug _ | EF_inline_asm _ ->
          emit instr
       | _ ->
          assert false
     end
  | _ -> emit instr

let int_reg_to_dwarf_32 = function
  | RAX -> 0
  | RBX -> 3
  | RCX -> 1
  | RDX -> 2
  | RSI -> 6
  | RDI -> 7
  | RBP -> 5
  | RSP -> 4
  | _ -> assert false

let int_reg_to_dwarf_64 = function
  | RAX -> 0
  | RDX -> 1
  | RCX -> 2
  | RBX -> 3
  | RSI -> 4
  | RDI -> 5
  | RBP -> 6
  | RSP -> 7
  | R8 -> 8
  | R9 -> 9
  | R10 -> 10
  | R11 -> 11
  | R12 -> 12
  | R13 -> 13
  | R14 -> 14
  | R15 -> 15

let int_reg_to_dwarf =
  if Archi.ptr64 then int_reg_to_dwarf_64 else int_reg_to_dwarf_32

let float_reg_to_dwarf_32 = function
  | XMM0 -> 21
  | XMM1 -> 22
  | XMM2 -> 23
  | XMM3 -> 24
  | XMM4 -> 25
  | XMM5 -> 26
  | XMM6 -> 27
  | XMM7 -> 28
  | _ -> assert false

let float_reg_to_dwarf_64 = function
  | XMM0 -> 17
  | XMM1 -> 18
  | XMM2 -> 19
  | XMM3 -> 20
  | XMM4 -> 21
  | XMM5 -> 22
  | XMM6 -> 23
  | XMM7 -> 24
  | XMM8 -> 25
  | XMM9 -> 26
  | XMM10 -> 27
  | XMM11 -> 28
  | XMM12 -> 29
  | XMM13 -> 30
  | XMM14 -> 31
  | XMM15 -> 32

let float_reg_to_dwarf =
  if Archi.ptr64 then float_reg_to_dwarf_64 else float_reg_to_dwarf_32

let preg_to_dwarf = function
   | IR r -> int_reg_to_dwarf r, None
   | FR r -> float_reg_to_dwarf r, None
   | _ -> assert false


let expand_function id fn =
  try
    set_current_function fn;
    expand id (int_reg_to_dwarf RSP) preg_to_dwarf expand_instruction fn.fn_code;
    Errors.OK (get_current_function ())
  with AsmexpandError s ->
    Errors.Error (Errors.msg s)

let expand_fundef id = function
  | Internal f ->
      begin match expand_function id f with
      | Errors.OK tf -> Errors.OK (Internal tf)
      | Errors.Error msg -> Errors.Error msg
      end
  | External ef ->
      Errors.OK (External ef)

let expand_program (p: Asm.program) : Asm.program Errors.res =
  AST.transform_partial_program2 expand_fundef (fun id v -> Errors.OK v) p
