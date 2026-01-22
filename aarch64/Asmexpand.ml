(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*         Xavier Leroy, Collège de France and INRIA Paris             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Expanding built-ins and some pseudo-instructions by rewriting
   of the AArch64 assembly code. *)

open Asm
open Asmexpandaux
open AST
open Camlcoq


(* Emit instruction sequences that set or offset a register by a constant. *)

let expand_loadimm32 (dst: ireg) n =
  List.iter emit (Asmgen.loadimm32 dst n [])

let expand_loadimm64 (dst: ireg) n =
  List.iter emit (Asmgen.loadimm64 dst n [])

let expand_addimm64 (dst: iregsp) (src: iregsp) n =
  List.iter emit (Asmgen.addimm64 dst src n [])

(* Handling of varargs *)

(* Determine the number of int registers, FP registers, and stack locations
   used to pass the fixed parameters. *)

let typesize = function
  | Tint | Tany32 | Tsingle -> _4
  | Tlong | Tany64 | Tfloat -> _8

let reserve_stack stk ty =
  match Archi.abi with
  | Archi.AAPCS64 -> Z.add stk _8
  | Archi.Apple -> Z.add (Coqlib.align stk (typesize ty)) (typesize ty)

let rec next_arg_locations ir fr stk = function
  | [] ->
      (ir, fr, stk)
  | (Tint | Tlong | Tany32 | Tany64 as ty) :: l ->
      if ir < 8
      then next_arg_locations (ir + 1) fr stk l
      else next_arg_locations ir fr (reserve_stack stk ty) l
  | (Tfloat | Tsingle as ty) :: l ->
      if fr < 8
      then next_arg_locations ir (fr + 1) stk l
      else next_arg_locations ir fr (reserve_stack stk ty) l

(* Allocate memory on the stack and use it to save the registers
   used for parameter passing.  As an optimization, do not save
   the registers used to pass the fixed parameters. *)

let int_param_regs = [| X0; X1; X2; X3; X4; X5; X6; X7 |]
let float_param_regs = [| D0; D1; D2; D3; D4; D5; D6; D7 |]
let size_save_register_area = Z.of_uint (8*8 + 8*16)

let save_parameter_registers ir fr =
  emit (Psubimm(X, XSP, XSP, size_save_register_area));
  let i = ref ir in
  while !i < 8 do
    let pos = coqint_of_camlint64 (Int64.of_int (8*16 + !i*8)) in
    if !i land 1 = 0 then begin
      emit (Pstp(int_param_regs.(!i), int_param_regs.(!i + 1),
                 ADimm(XSP, pos)));
      i := !i + 2
    end else begin
      emit (Pstrx(int_param_regs.(!i), ADimm(XSP, pos)));
      i := !i + 1
    end
  done;
  for i = fr to 7 do
    let pos = coqint_of_camlint64 (Int64.of_int (i*16)) in
    emit (Pstrd(float_param_regs.(i), ADimm(XSP, pos)))
  done

let current_function_stacksize = ref _0L

(* Initialize a va_list as per va_start.
   Register r points to the following struct:

   typedef struct __va_list {
     void *__stack;             // next stack parameter
     void *__gr_top;            // top of the save area for int regs
     void *__vr_top;            // top of the save area for float regs
     int__gr_offs;              // offset from gr_top to next int reg
     int__vr_offs;              // offset from gr_top to next FP reg
   }
*)

(*- E_COMPCERT_CODE_Asmexpand_builtin_va_start_aapcs64_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_VA_START_001 *)
let expand_builtin_va_start_aapcs64 r =
  let (ir, fr, stk) =
    next_arg_locations 0 0 _0 (get_current_function_args ()) in
  let stack_ofs = I64.(add !current_function_stacksize (repr stk))
  and gr_top_ofs = !current_function_stacksize
  and vr_top_ofs = I64.sub !current_function_stacksize _64L
  and gr_offs = - ((8 - ir) * 8)
  and vr_offs = - ((8 - fr) * 16) in
  (* va->__stack = sp + stack_ofs *)
  expand_addimm64 (RR1 X16) XSP stack_ofs;
  emit (Pstrx(X16, ADimm(RR1 r, _0L)));
  (* va->__gr_top = sp + gr_top_ofs *)
  if gr_top_ofs <> stack_ofs then
    expand_addimm64 (RR1 X16) XSP gr_top_ofs;
  emit (Pstrx(X16, ADimm(RR1 r, _8L)));
  (* va->__vr_top = sp + vr_top_ofs *)
  expand_addimm64 (RR1 X16) XSP vr_top_ofs;
  emit (Pstrx(X16, ADimm(RR1 r, _16L)));
  (* va->__gr_offs = gr_offs *)
  expand_loadimm32 X16 (coqint_of_camlint (Int32.of_int gr_offs));
  emit (Pstrw(X16, ADimm(RR1 r, _24L)));
  (* va->__vr_offs = vr_offs *)
  expand_loadimm32 X16 (coqint_of_camlint (Int32.of_int vr_offs));
  emit (Pstrw(X16, ADimm(RR1 r, _28L)))
(*- #End *)

(* In macOS, va_list is just a pointer (char * ) and all variadic arguments
   are passed on the stack. *)

let expand_builtin_va_start_apple r =
  let (ir, fr, stk) =
    next_arg_locations 0 0 _0 (get_current_function_args ()) in
  let stk = Coqlib.align stk _8 in
  let stack_ofs = I64.(add !current_function_stacksize (repr stk)) in
  (* *va = sp + stack_ofs *)
  expand_addimm64 (RR1 X16) XSP stack_ofs;
  emit (Pstrx(X16, ADimm(RR1 r, _0L)))

(*- E_COMPCERT_CODE_Asmexpand_builtin_va_start_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_VA_START_001 *)
let expand_builtin_va_start r =
  (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_VA_START_001 *)
  if not (is_current_function_variadic ()) then
    invalid_arg "Fatal error: va_start used in non-vararg function";
  match Archi.abi with
  | Archi.AAPCS64 -> expand_builtin_va_start_aapcs64 r
  | Archi.Apple   -> expand_builtin_va_start_apple r
(*- #End *)

(* Handling of annotations *)

(*- E_COMPCERT_CODE_Asmexpand_annot_val_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_ANNOT_INT_001 *)
let expand_annot_val kind txt targ args res =
  emit (Pbuiltin (EF_annot(kind,txt,[targ]), args, BR_none));
  match args, res with
  | [BA(IR src)], BR(IR dst) ->
     if dst <> src then emit (Pmov (RR1 dst, RR1 src))
  | [BA(FR src)], BR(FR dst) ->
     if dst <> src then emit (Pfmov (dst, src))
  | _, _ ->
     (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_ANNOT_INTVAL_001 *)
     raise (AsmexpandError "ill-formed __builtin_annot_intval")
(*- #End *)

(* Handling of memcpy *)

(* We assume unaligned memory accesses are efficient.  Hence we use
   memory accesses as wide as we can, up to 16 bytes.
   Temporary registers used: x14 x15 x16 x17 x30. *)

let offset_in_range ofs =
  (* The 512 upper bound comes from ldp/stp.  Single-register load/store
     instructions support bigger offsets. *)
  Ptrofs.ltu ofs _512p

(*- E_COMPCERT_CODE_Asmexpand_memcpy_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_002 *)
let memcpy_small_arg sz arg tmp =
  match arg with
  | BA (IR r) ->
      (RR1 r, _0p)
  | BA_addrstack ofs ->
      if offset_in_range ofs
      && offset_in_range (Ptrofs.add ofs sz)
      && Ptrofs.(eq (modu ofs _8p) _0p)
      then (XSP, ofs)
      else begin expand_addimm64 (RR1 tmp) XSP (Ptrofs.to_int64 ofs); (RR1 tmp, _0p) end
  | _ ->
      assert false
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_memcpy_002 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_002 *)
let expand_builtin_memcpy_small sz al src dst =
  let tsrc = if dst <> BA (IR X17) then X17 else X15 in
  let tdst = if src <> BA (IR X15) then X15 else X17 in
  let (rsrc, osrc) = memcpy_small_arg sz src tsrc in
  let (rdst, odst) = memcpy_small_arg sz dst tdst in
  (* If the source and destination register are not equal the source and
     destination register after memcpy_small_arg should also be not equal,
     except for the case when both destination and source are on the stack *)
  assert (src = dst || rdst <> rsrc || (rsrc = XSP && rdst = XSP));
  let rec copy osrc odst sz =
    if Ptrofs.cmpu Cge sz _16p then begin
      emit (Pldp(X16, X30, ADimm(rsrc, osrc)));
      emit (Pstp(X16, X30, ADimm(rdst, odst)));
      copy (I64.add osrc _16L) (I64.add odst _16L) (Ptrofs.sub sz _16p)
    end
    else if Ptrofs.cmpu Cge sz _8p then begin
      emit (Pldrx(X16, ADimm(rsrc, osrc)));
      emit (Pstrx(X16, ADimm(rdst, odst)));
      copy (I64.add osrc _8L) (I64.add odst _8L) (Ptrofs.sub sz _8p)
    end
    else if Ptrofs.cmpu Cge sz _4p then begin
      emit (Pldrw(X16, ADimm(rsrc, osrc)));
      emit (Pstrw(X16, ADimm(rdst, odst)));
      copy (I64.add osrc _4L) (I64.add odst _4L) (Ptrofs.sub sz _4p)
    end
    else if Ptrofs.cmpu Cge sz _2p then begin
      emit (Pldrh(W, X16, ADimm(rsrc, osrc)));
      emit (Pstrh(X16, ADimm(rdst, odst)));
      copy (I64.add osrc _2L) (I64.add odst _2L) (Ptrofs.sub sz _2p)
    end
    else if Ptrofs.cmpu Cge sz _1p then begin
      emit (Pldrb(W, X16, ADimm(rsrc, osrc)));
      emit (Pstrb(X16, ADimm(rdst, odst)));
      copy (I64.add osrc _1L) (I64.add odst _1L) (Ptrofs.sub sz _1p)
    end
  in copy (Ptrofs.to_int64 osrc) (Ptrofs.to_int64 odst) sz
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_memcpy_003 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_003 *)
let memcpy_big_arg arg tmp =
  match arg with
  | BA (IR r) -> emit (Pmov(RR1 tmp, RR1 r))
  | BA_addrstack ofs -> expand_addimm64 (RR1 tmp) XSP (Ptrofs.to_int64 ofs)
  | _ -> assert false
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_memcpy_004 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_003 *)
let expand_builtin_memcpy_big sz al src dst =
  assert (Ptrofs.cmpu Cge sz _16p); (* sz >= 16 *)
  memcpy_big_arg src X30;
  memcpy_big_arg dst X14;
  let lbl = new_label () in
  expand_loadimm64 X15 (I64.divu (Ptrofs.to_int64 sz) _16L);
  emit (Plabel lbl);
  emit (Pldp(X16, X17, ADpostincr(RR1 X30, _16L)));
  emit (Pstp(X16, X17, ADpostincr(RR1 X14, _16L)));
  emit (Psubimm(X, RR1 X15, RR1 X15, _1));
  emit (Pcbnz(X, X15, lbl));
  if Ptrofs.cmpu Cge (Ptrofs.modu sz _16p) _8p then begin
    emit (Pldrx(X16, ADpostincr(RR1 X30, _8L)));
    emit (Pstrx(X16, ADpostincr(RR1 X14, _8L)))
  end;
  if Ptrofs.cmpu Cge (Ptrofs.modu sz _8p) _4p then begin
    emit (Pldrw(X16, ADpostincr(RR1 X30, _4L)));
    emit (Pstrw(X16, ADpostincr(RR1 X14, _4L)))
  end;
  if Ptrofs.cmpu Cge (Ptrofs.modu sz _4p) _2p then begin
    emit (Pldrh(W, X16, ADpostincr(RR1 X30, _2L)));
    emit (Pstrh(X16, ADpostincr(RR1 X14, _2L)))
  end;
  if Ptrofs.cmpu Cge (Ptrofs.modu sz _2p) _1p then begin
    emit (Pldrb(W, X16, ADpostincr(RR1 X30, _1L)));
    emit (Pstrb(X16, ADpostincr(RR1 X14, _1L)))
  end
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_memcpy_005 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_001 *)
let expand_builtin_memcpy  sz al args =
  let (dst, src) =
    match args with [d; s] -> (d, s) | _ -> assert false in
  if Ptrofs.ltu sz _64p
  then expand_builtin_memcpy_small sz al src dst
  else expand_builtin_memcpy_big sz al src dst
(*- #End *)

(* Handling of volatile reads and writes *)

(*- E_COMPCERT_CODE_Asmexpand_volatile_access_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_LOAD_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_ACCESS_001 *)
let expand_builtin_vload_common chunk base ofs res =
  let addr = ADimm(base, ofs) in
  match chunk, res with
  | (Mbool | Mint8unsigned), BR(IR res) ->
     emit (Pldrb(W, res, addr))
  | Mint8signed, BR(IR res) ->
     emit (Pldrsb(W, res, addr))
  | Mint16unsigned, BR(IR res) ->
     emit (Pldrh(W, res, addr))
  | Mint16signed, BR(IR res) ->
     emit (Pldrsh(W, res, addr))
  | Mint32, BR(IR res) ->
     emit (Pldrw(res, addr))
  | Mint64, BR(IR res) ->
     emit (Pldrx(res, addr))
  | Mfloat32, BR(FR res) ->
     emit (Pldrs(res, addr))
  | Mfloat64, BR(FR res) ->
     emit (Pldrd(res, addr))
  | _ ->
     assert false
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_volatile_access_002 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_LOAD_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_ACCESS_001 *)
let expand_builtin_vload chunk args res =
  let size_chunk = Memdata.size_chunk chunk in
  match args with
  | [BA(IR addr)] ->
      expand_builtin_vload_common chunk (RR1 addr) _0L res
  | [BA_addrstack ofs] ->
      let ofs = Ptrofs.to_int64 ofs in
      if Asmgen.offset_representable size_chunk ofs then
        expand_builtin_vload_common chunk XSP ofs res
      else begin
        expand_addimm64 (RR1 X16) XSP ofs; (* X16 <- SP + ofs *)
        expand_builtin_vload_common chunk (RR1 X16) _0L res
      end
  | [BA_addptr(BA(IR addr), BA_long ofs)] ->
      if Asmgen.offset_representable size_chunk ofs then
        expand_builtin_vload_common chunk (RR1 addr) ofs res
      else begin
        expand_addimm64 (RR1 X16) (RR1 addr) ofs; (* X16 <- addr + ofs *)
        expand_builtin_vload_common chunk (RR1 X16) _0L res
      end
  | _ ->
      assert false
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_volatile_access_003 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_STORE_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_ACCESS_001 *)
let expand_builtin_vstore_common chunk base ofs src =
  let addr = ADimm(base, ofs) in
  match chunk, src with
  | (Mbool | Mint8signed | Mint8unsigned), BA(IR src) ->
     emit (Pstrb(src, addr))
  | (Mint16signed | Mint16unsigned), BA(IR src) ->
     emit (Pstrh(src, addr))
  | Mint32, BA(IR src) ->
     emit (Pstrw(src, addr))
  | Mint64, BA(IR src) ->
     emit (Pstrx(src, addr))
  | Mfloat32, BA(FR src) ->
     emit (Pstrs(src, addr))
  | Mfloat64, BA(FR src) ->
     emit (Pstrd(src, addr))
  | _ ->
     assert false
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_volatile_access_004 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_STORE_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_ACCESS_001 *)
let expand_builtin_vstore chunk args =
  let size_chunk = Memdata.size_chunk chunk in
  match args with
  | [BA(IR addr); src] ->
      expand_builtin_vstore_common chunk (RR1 addr) _0L src
  | [BA_addrstack ofs; src] ->
      let ofs = Ptrofs.to_int64 ofs in
      if Asmgen.offset_representable size_chunk ofs then
        expand_builtin_vstore_common chunk XSP ofs src
      else begin
        expand_addimm64 (RR1 X16) XSP ofs; (* X16 <- SP + ofs *)
        expand_builtin_vstore_common chunk (RR1 X16) _0L src
      end
  | [BA_addptr(BA(IR addr), BA_long ofs); src] ->
      if Asmgen.offset_representable size_chunk ofs then
        expand_builtin_vstore_common chunk (RR1 addr) ofs src
      else begin
        expand_addimm64 (RR1 X16) (RR1 addr) ofs; (* X16 <- addr + ofs *)
        expand_builtin_vstore_common chunk (RR1 X16) _0L src
      end
  | _ ->
      assert false
(*- #End *)

(* Handling of compiler-inlined builtins *)

let expand_builtin_inline name args res =
  match name, args, res with
  (* Synchronization *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_001 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMBAR_001 *)
  | "__builtin_membar", [], _ ->
     ()
  (*- #End *)

  (* No operation *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_002 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_NOP_001 *)
  | "__builtin_nop", [], _ ->
     emit Pnop
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_003 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_UNREACHABLE_001 *)
  (* Optimization hint *)
  | "__builtin_unreachable", [], _ ->
     ()
  (*- #End *)

  (* Byte swap *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_004 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_BSWAP_001 *)
  | ("__builtin_bswap" | "__builtin_bswap32"), [BA(IR a1)], BR(IR res) ->
     emit (Prev(W, res, a1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_005 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_BSWAP64_001 *)
  | "__builtin_bswap64", [BA(IR a1)], BR(IR res) ->
     emit (Prev(X, res, a1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_006 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_BSWAP16_001 *)
  | "__builtin_bswap16", [BA(IR a1)], BR(IR res) ->
     emit (Prev16(W, res, a1));
     emit (Pandimm(W, res, RR0 res, Z.of_uint 0xFFFF))
  (*- #End *)

  (* Count leading zeros, leading sign bits, trailing zeros *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_007 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_CLZ_001 *)
  | "__builtin_clz",  [BA(IR a1)], BR(IR res) ->
     emit (Pclz(W, res, a1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_008 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_CLZLL_001 *)
  | ("__builtin_clzl" | "__builtin_clzll"),  [BA(IR a1)], BR(IR res) ->
     emit (Pclz(X, res, a1)) 
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_009 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_CLS_001 *)
  | "__builtin_cls",  [BA(IR a1)], BR(IR res) ->
     emit (Pcls(W, res, a1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_010 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_CLSLL_001 *)
  | ("__builtin_clsl" | "__builtin_clsll"),  [BA(IR a1)], BR(IR res) ->
     emit (Pcls(X, res, a1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_011 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_CTZ_001 *)
  | "__builtin_ctz",  [BA(IR a1)], BR(IR res) ->
     emit (Prbit(W, res, a1));
     emit (Pclz(W, res, res))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_012 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_CTZLL_001 *)
  | ("__builtin_ctzl" | "__builtin_ctzll"),  [BA(IR a1)], BR(IR res) ->
     emit (Prbit(X, res, a1));
     emit (Pclz(X, res, res))
  (*- #End *)

 (* Float arithmetic *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_013 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_FSQRT_001 *)
  | ("__builtin_fsqrt" | "__builtin_sqrt"),  [BA(FR a1)], BR(FR res) ->
     emit (Pfsqrt(D, res, a1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_014 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_FMADD_001 *)
  | "__builtin_fmadd", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfmadd(D, res, a1, a2, a3))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_015 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_FMSUB_001 *)
  | "__builtin_fmsub", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfmsub(D, res, a1, a2, a3))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_016 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_FNMADD_001 *)
  | "__builtin_fnmadd", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfnmadd(D, res, a1, a2, a3))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_017 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_FNMSUB_001 *)
  | "__builtin_fnmsub", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfnmsub(D, res, a1, a2, a3))
  (*- #End *)

  (*  We use the fmaxnm instruction instead of fmax since the behavior for
      NaN is compliant with the IEEE 754-2008 standards version of FP max. *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_018 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_FMAX_001 *)
  | "__builtin_fmax", [BA (FR a1); BA (FR a2)], BR (FR res) ->
      emit (Pfmaxnm (D, res, a1, a2))
  (*- #End *)

  (*  Similar to fmax, we also use the fminnm instruction instead of fmin since
      the behavior for NaN  arguments is compliant with the IEEE 754-2008
      standards version of FP min. *)
  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_019 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_FMIN_001 *)
  | "__builtin_fmin", [BA (FR a1); BA (FR a2)], BR (FR res) ->
      emit (Pfminnm (D, res, a1, a2))
  (*- #End *)

  (* Vararg *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_020 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_VA_START_001 *)
  | "__builtin_va_start", [BA(IR a)], _ ->
      expand_builtin_va_start a
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_021 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_DTOB_001 *)
  | "__builtin_dtob", [BA (FR a1)],
                          BR (IR res) ->
     emit (Pfmovd (res, a1))
  (*- #End *)

  (* Catch-all *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_022 *)
  (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_UNKNOWN_BUILTIN_001 *)
  | _ ->
     raise (AsmexpandError ("unrecognized builtin " ^ name))
  (*- #End *)

(* Expansion of instructions *)

let expand_instruction instr =
  match instr with
  (*- E_COMPCERT_CODE_Asmexpand_instruction_001 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_PALLOCFRAME_001 *)
  | Pallocframe sz ->
      emit (Pmov (RR1 X15, XSP));
      if is_current_function_variadic() && Archi.abi = Archi.AAPCS64 then begin
        let (ir, fr, _) =
          next_arg_locations 0 0 _0 (get_current_function_args ()) in
        save_parameter_registers ir fr;
        let full_sz = Z.add sz size_save_register_area in
        check_stack_size full_sz;
        current_function_stacksize := I64.repr full_sz
      end else begin
        check_stack_size sz;
        current_function_stacksize := I64.repr sz
      end;
      expand_addimm64 XSP XSP (I64.repr (Z.neg sz));
      emit (Pcfi_adjust (Ptrofs.repr sz))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_002 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_PFREEFRAME_001 *)
  | Pfreeframe (sz, ofs) ->
      expand_addimm64 XSP XSP !current_function_stacksize
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_003 *)
  (*- #Justify_Derived "case irrelevant" *)
  | Pcvtx2w rd ->
      (* no code generated, the upper 32 bits of rd will be ignored *)
      ()
  (*- #End *)

  | Pbuiltin (ef,args,res) ->
     begin match ef with
     (*- E_COMPCERT_CODE_Asmexpand_instruction_004 *)
     (*- #Justify_Derived "Call to expansion function for builtins" *)
     | EF_builtin (name,sg) ->
        expand_builtin_inline (camlstring_of_coqstring name) args res
     (*- #End *)

     (*- E_COMPCERT_CODE_Asmexpand_instruction_005 *)
     (*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_LOAD_001 *)
     | EF_vload chunk ->
        expand_builtin_vload chunk args res
     (*- #End *)

     (*- E_COMPCERT_CODE_Asmexpand_instruction_006 *)
     (*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_STORE_001 *)
     | EF_vstore chunk ->
        expand_builtin_vstore chunk args
     (*- #End *)

     (*- E_COMPCERT_CODE_Asmexpand_instruction_007 *)
     (*- #Link_to E_COMPCERT_TR_Function_EXPAND_ANNOT_INT_001 *)
     | EF_annot_val (kind,txt,targ) ->
        expand_annot_val kind txt targ args res
     (*- #End *)

     (*- E_COMPCERT_CODE_Asmexpand_instruction_008 *)
     (*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_001 *)
     | EF_memcpy(sz, al) ->
        expand_builtin_memcpy sz al args
      (*- #End *)

     (*- E_COMPCERT_CODE_Asmexpand_instruction_009 *)
     (*- #Justify_Derived "Default case" *)
     | EF_annot _ | EF_debug _ | EF_inline_asm _ ->
        emit instr
     (*- #End *)

     | _ ->
        assert false
     end
  | _ ->
     emit instr

let int_reg_to_dwarf = function
  | X0 -> 0 | X1 -> 1 | X2 -> 2 | X3 -> 3 | X4 -> 4
  | X5 -> 5 | X6 -> 6 | X7 -> 7 | X8 -> 8 | X9 -> 9
  | X10 -> 10 | X11 -> 11 | X12 -> 12 | X13 -> 13 | X14 -> 14
  | X15 -> 15 | X16 -> 16 | X17 -> 17 | X18 -> 18 | X19 -> 19
  | X20 -> 20 | X21 -> 21 | X22 -> 22 | X23 -> 23 | X24 -> 24
  | X25 -> 25 | X26 -> 26 | X27 -> 27 | X28 -> 28 | X29 -> 29
  | X30 -> 30

let float_reg_to_dwarf = function
  | D0 -> 64 | D1 -> 65 | D2 -> 66 | D3 -> 67 | D4 -> 68
  | D5 -> 69 | D6 -> 70 | D7 -> 71 | D8 -> 72 | D9 -> 73
  | D10 -> 74 | D11 -> 75 | D12 -> 76 | D13 -> 77 | D14 -> 78
  | D15 -> 79 | D16 -> 80 | D17 -> 81 | D18 -> 82 | D19 -> 83
  | D20 -> 84 | D21 -> 85 | D22 -> 86 | D23 -> 87 | D24 -> 88
  | D25 -> 89 | D26 -> 90 | D27 -> 91 | D28 -> 92 | D29 -> 93
  | D30 -> 94 | D31 -> 95

let preg_to_dwarf = function
   | IR r -> int_reg_to_dwarf r, None
   | FR r -> float_reg_to_dwarf r, None
   | SP -> 31, None
   | _ -> assert false

let expand_function id fn =
  try
    set_current_function fn;
    expand id (* sp= *) 31 preg_to_dwarf expand_instruction fn.fn_code;
    Errors.OK (get_current_function ())
  with AsmexpandError s ->
    Errors.Error (Errors.msg (coqstring_of_camlstring s))

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
