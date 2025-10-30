(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*           Prashanth Mundkur, SRI International                      *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(*  The contributions by Prashanth Mundkur are reused and adapted      *)
(*  under the terms of a Contributor License Agreement between         *)
(*  SRI International and INRIA.                                       *)
(*                                                                     *)
(* *********************************************************************)

(* Expanding built-ins and some pseudo-instructions by rewriting
   of the RISC-V assembly code. *)

open Asm
open Asmexpandaux
open AST
open Camlcoq
open Locations

(* BEGIN:untraced *)
(*- #Untraced E_COMPCERT_TR_Function_EXPAND_SEL_001 *)
(*- #Justify_Untraced "CompCert for RiscV currently has no specific assembly support for conditional selection." *)
(* END:untraced *)

(* Useful constants and helper functions *)

let wordsize = if Archi.ptr64 then 8 else 4

let align n a = (n + a - 1) land (-a)

(* Emit instruction sequences that set or offset a register by a constant. *)

let expand_loadimm32 dst n =
  List.iter emit (Asmgen.loadimm32 dst n [])
let expand_loadimm64 dst n =
  List.iter emit (Asmgen.loadimm64 dst n [])
let expand_loadptrofs dst n =
  if Archi.ptr64 then
    expand_loadimm64 dst (Ptrofs.to_int64 n)
  else
    expand_loadimm32 dst (Ptrofs.to_int n)
let expand_addptrofs dst src n =
  List.iter emit (Asmgen.addptrofs dst src n [])
let expand_storeind_ptr src base ofs =
  List.iter emit (Asmgen.storeind_ptr src base ofs [])

(* Fix-up code around function calls and function entry.
   Some floating-point arguments residing in FP registers need to be
   moved to integer registers or register pairs.
   Symmetrically, some floating-point parameter passed in integer
   registers or register pairs need to be moved to FP registers. *)

let int_param_regs = [| X10; X11; X12; X13; X14; X15; X16; X17 |]

let move_single_arg fr i =
  emit (Pfmvxs(int_param_regs.(i), fr))

let move_double_arg fr i =
  if Archi.ptr64 then begin
    emit (Pfmvxd(int_param_regs.(i), fr))
  end else begin
    emit (Paddiw(X2, X X2, _m16l));
    emit (Pfsd(fr, X2, Ofsimm _0p));
    emit (Plw(int_param_regs.(i), X2, Ofsimm _0p));
    if i < 7 then begin
      emit (Plw(int_param_regs.(i + 1), X2, Ofsimm _4p))
    end else begin
      emit (Plw(X31, X2, Ofsimm _4p));
      emit (Psw(X31, X2, Ofsimm _16p))
    end;
    emit (Paddiw(X2, X X2, _16l))
  end

let move_single_param fr i =
  emit (Pfmvsx(fr, int_param_regs.(i)))

let move_double_param fr i =
  if Archi.ptr64 then begin
    emit (Pfmvdx(fr, int_param_regs.(i)))
  end else begin
    emit (Paddiw(X2, X X2, _m16l));
    emit (Psw(int_param_regs.(i), X2, Ofsimm _0p));
    if i < 7 then begin
      emit (Psw(int_param_regs.(i + 1), X2, Ofsimm _4p))
    end else begin
      emit (Plw(X31, X2, Ofsimm _16p));
      emit (Psw(X31, X2, Ofsimm _4p))
    end;
    emit (Pfld(fr, X2, Ofsimm _0p));
    emit (Paddiw(X2, X X2, _16l))
  end

let float_extra_index = function
  | Machregs.F0 -> Some (F0, 0)
  | Machregs.F1 -> Some (F1, 1)
  | Machregs.F2 -> Some (F2, 2)
  | Machregs.F3 -> Some (F3, 3)
  | Machregs.F4 -> Some (F4, 4)
  | Machregs.F5 -> Some (F5, 5)
  | Machregs.F6 -> Some (F6, 6)
  | Machregs.F7 -> Some (F7, 7)
  | _  -> None

let fixup_gen single double sg =
  let fixup ty loc =
    match ty, loc with
    | Tsingle, One (R r) ->
        begin match float_extra_index r with
        | Some(r, i) -> single r i
        | None -> ()
        end
    | (Tfloat | Tany64), One (R r) ->
        begin match float_extra_index r with
        | Some(r, i) -> double r i
        | None -> ()
        end
    | _, _ -> ()
  in
    List.iter2 fixup (proj_sig_args sg) (Conventions1.loc_arguments sg)

let fixup_call sg =
  fixup_gen move_single_arg move_double_arg sg

let fixup_function_entry sg =
  fixup_gen move_single_param move_double_param sg

(* Built-ins.  They come in two flavors:
   - annotation statements: take their arguments in registers or stack
     locations; generate no code;
   - inlined by the compiler: take their arguments in arbitrary
     registers.
*)

(* Handling of annotations *)

(*- E_COMPCERT_CODE_Asmexpand_annot_val_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_ANNOT_INT_001 *)
let expand_annot_val kind txt targ args res =
  emit (Pbuiltin (EF_annot(kind,txt,[targ]), args, BR_none));
  match args, res with
  | [BA(IR src)], BR(IR dst) ->
     if dst <> src then emit (Pmv (dst, src))
  | [BA(FR src)], BR(FR dst) ->
     if dst <> src then emit (Pfmv (dst, src))
  | _, _ ->
     (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_ANNOT_INTVAL_001 *)
     raise (AsmexpandError "ill-formed __builtin_annot_intval")
(*- #End *)

(* Handling of memcpy *)

(* Unaligned accesses are slow on RISC-V, so don't use them *)

let offset_in_range ofs =
  Ptrofs.cmp Cle _m2048p ofs && Ptrofs.cmp Clt ofs _2048p

(*- E_COMPCERT_CODE_Asmexpand_memcpy_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_002 *)
let memcpy_small_arg sz arg tmp =
  match arg with
  | BA (IR r) ->
      (r, _0p)
  | BA_addrstack ofs ->
      if offset_in_range ofs
      && offset_in_range (Ptrofs.add ofs sz)
      then (X2, ofs)
      else begin expand_addptrofs tmp X2 ofs; (tmp, _0p) end
  | _ ->
      assert false
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_memcpy_002 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_002 *)
let expand_builtin_memcpy_small sz al src dst =
  let tsrc = if dst <> BA (IR X5) then X5 else X6 in
  let tdst = if src <> BA (IR X6) then X6 else X5 in
  let (rsrc, osrc) = memcpy_small_arg sz src tsrc in
  let (rdst, odst) = memcpy_small_arg sz dst tdst in
  (* If the source and destination register are not equal the source and
     destination register after memcpy_small_arg should also be not equal
     except for the case when both destination and source are on the stack *)
  assert (src = dst || rdst <> rsrc || (rsrc = X2 && rdst = X2));
  let rec copy osrc odst sz =
    if Archi.ptr64 && (Ptrofs.cmpu Cge sz _8p) && (Ptrofs.cmpu Cge al _8p) then
      begin
        emit (Pld (X31, rsrc, Ofsimm osrc));
        emit (Psd (X31, rdst, Ofsimm odst));
        copy (Ptrofs.add osrc _8p) (Ptrofs.add odst _8p) (Ptrofs.sub sz _8p)
      end
    else if !Clflags.option_ffpu && (Ptrofs.cmpu Cge sz _8p) && (Ptrofs.cmpu Cge al _8p) then
      begin
        emit (Pfld (F0, rsrc, Ofsimm osrc));
        emit (Pfsd (F0, rdst, Ofsimm odst));
        copy (Ptrofs.add osrc _8p) (Ptrofs.add odst _8p) (Ptrofs.sub sz _8p)
      end
    else if (Ptrofs.cmpu Cge sz _4p) && (Ptrofs.cmpu Cge al _4p) then
      begin
        emit (Plw (X31, rsrc, Ofsimm osrc));
        emit (Psw (X31, rdst, Ofsimm odst));
        copy (Ptrofs.add osrc _4p) (Ptrofs.add odst _4p) (Ptrofs.sub sz _4p)
      end
    else if (Ptrofs.cmpu Cge sz _2p) && (Ptrofs.cmpu Cge al _2p) then
      begin
        emit (Plh (X31, rsrc, Ofsimm osrc));
        emit (Psh (X31, rdst, Ofsimm odst));
        copy (Ptrofs.add osrc _2p) (Ptrofs.add odst _2p) (Ptrofs.sub sz _2p)
      end
    else if Ptrofs.cmpu Cge sz _1p then
      begin
        emit (Plb (X31, rsrc, Ofsimm osrc));
        emit (Psb (X31, rdst, Ofsimm odst));
        copy (Ptrofs.add osrc _1p) (Ptrofs.add odst _1p) (Ptrofs.sub sz _1p)
      end
  in copy osrc odst sz
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_memcpy_003 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_003 *)
let memcpy_big_arg sz arg tmp =
  match arg with
  | BA (IR r) -> if r <> tmp then emit (Pmv(tmp, r))
  | BA_addrstack ofs ->
      expand_addptrofs tmp X2 ofs
  | _ ->
      assert false
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_memcpy_004 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_003 *)
let expand_builtin_memcpy_big sz al src dst =
  assert (Ptrofs.cmpu Cge sz al);
  assert (Ptrofs.(eq (modu sz al) _0p));
  let (s, d) =
    if dst <> BA (IR X5) then (X5, X6) else (X6, X5) in
  memcpy_big_arg sz src s;
  memcpy_big_arg sz dst d;
  (* Use X7 as loop count, X31 and F0 as ld/st temporaries. *)
  let (load, store, chunksize) =
    if Archi.ptr64 && (Ptrofs.cmpu Cge al _8p) then
      (Pld (X31, s, Ofsimm _0p), Psd (X31, d, Ofsimm _0p), _8p)
    else if !Clflags.option_ffpu  && (Ptrofs.cmpu Cge al _8p) then
      (Pfld (F0, s, Ofsimm _0p), Pfsd (F0, d, Ofsimm _0p), _8p)
    else if  (Ptrofs.cmpu Cge al _4p) then
      (Plw (X31, s, Ofsimm _0p), Psw (X31, d, Ofsimm _0p), _4p)
    else if (Ptrofs.eq al _2p) then
      (Plh (X31, s, Ofsimm _0p), Psh (X31, d, Ofsimm _0p), _2p)
    else
      (Plb (X31, s, Ofsimm _0p), Psb (X31, d, Ofsimm _0p), _1p) in
  expand_loadptrofs X7 (Ptrofs.divu sz chunksize);
  let lbl = new_label () in
  emit (Plabel lbl);
  emit load;
  expand_addptrofs s s chunksize;
  expand_addptrofs X7 X7 _m1p;
  emit store;
  expand_addptrofs d d chunksize;
  if Archi.ptr64 then
    emit (Pbnel (X X7, X0, lbl))
  else
    emit (Pbnew (X X7, X0, lbl))
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_memcpy_005 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_001 *)
let expand_builtin_memcpy  sz al args =
  let (dst, src) =
    match args with [d; s] -> (d, s) | _ -> assert false in
  if Ptrofs.cmpu Cle sz _32p
  then expand_builtin_memcpy_small sz al src dst
  else expand_builtin_memcpy_big sz al src dst
(*- #End *)

(* Handling of volatile reads and writes *)

(*- E_COMPCERT_CODE_Asmexpand_volatile_access_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_LOAD_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_ACCESS_001 *)
let expand_builtin_vload_common chunk base ofs res =
  match chunk, res with
  | (Mbool | Mint8unsigned), BR(IR res) ->
     emit (Plbu (res, base, Ofsimm ofs))
  | Mint8signed, BR(IR res) ->
     emit (Plb  (res, base, Ofsimm ofs))
  | Mint16unsigned, BR(IR res) ->
     emit (Plhu (res, base, Ofsimm ofs))
  | Mint16signed, BR(IR res) ->
     emit (Plh  (res, base, Ofsimm ofs))
  | Mint32, BR(IR res) ->
     emit (Plw  (res, base, Ofsimm ofs))
  | Mint64, BR(IR res) ->
     emit (Pld  (res, base, Ofsimm ofs))
  | Mint64, BR_splitlong(BR(IR res1), BR(IR res2)) ->
     let ofs' = Ptrofs.add ofs _4p in
     if base <> res2 then begin
         emit (Plw (res2, base, Ofsimm ofs));
         emit (Plw (res1, base, Ofsimm ofs'))
       end else begin
         emit (Plw (res1, base, Ofsimm ofs'));
         emit (Plw (res2, base, Ofsimm ofs))
       end
  | Mfloat32, BR(FR res) ->
     emit (Pfls (res, base, Ofsimm ofs))
  | Mfloat64, BR(FR res) ->
     emit (Pfld (res, base, Ofsimm ofs))
  | _ ->
     assert false
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_volatile_access_002 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_LOAD_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_ACCESS_001 *)
let expand_builtin_vload chunk args res =
  let size_chunk = Ptrofs.repr (Memdata.size_chunk chunk) in
  match args with
  | [BA(IR addr)] ->
      expand_builtin_vload_common chunk addr _0p res
  | [BA_addrstack ofs] ->
      if offset_in_range (Ptrofs.add ofs size_chunk) then
        expand_builtin_vload_common chunk X2 ofs res
      else begin
        expand_addptrofs X31 X2 ofs; (* X31 <- sp + ofs *)
        expand_builtin_vload_common chunk X31 _0p res
      end
  | [BA_addptr(BA(IR addr), BA_int ofs)] ->
      let ofs = Ptrofs.of_int ofs in
      if offset_in_range (Ptrofs.add ofs size_chunk) then
        expand_builtin_vload_common chunk addr ofs res
      else begin
        expand_addptrofs X31 addr ofs; (* X31 <- addr + ofs *)
        expand_builtin_vload_common chunk X31 _0p res
      end
  | [BA_addptr(BA(IR addr), BA_long ofs)] ->
      let ofs = Ptrofs.of_int64 ofs in
      if offset_in_range (Ptrofs.add ofs size_chunk) then
        expand_builtin_vload_common chunk addr ofs res
      else begin
        expand_addptrofs X31 addr ofs; (* X31 <- addr + ofs *)
        expand_builtin_vload_common chunk X31 _0p res
      end
  | _ ->
      assert false
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_volatile_access_003 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_STORE_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_ACCESS_001 *)
let expand_builtin_vstore_common chunk base ofs src =
  match chunk, src with
  | (Mbool | Mint8signed | Mint8unsigned), BA(IR src) ->
     emit (Psb (src, base, Ofsimm ofs))
  | (Mint16signed | Mint16unsigned), BA(IR src) ->
     emit (Psh (src, base, Ofsimm ofs))
  | Mint32, BA(IR src) ->
     emit (Psw (src, base, Ofsimm ofs))
  | Mint64, BA(IR src) ->
     emit (Psd (src, base, Ofsimm ofs))
  | Mint64, BA_splitlong(BA(IR src1), BA(IR src2)) ->
     let ofs' = Ptrofs.add ofs _4p in
     emit (Psw (src2, base, Ofsimm ofs));
     emit (Psw (src1, base, Ofsimm ofs'))
  | Mfloat32, BA(FR src) ->
     emit (Pfss (src, base, Ofsimm ofs))
  | Mfloat64, BA(FR src) ->
     emit (Pfsd (src, base, Ofsimm ofs))
  | _ ->
     assert false
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_volatile_access_004 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_STORE_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_ACCESS_001 *)
let expand_builtin_vstore chunk args =
  let size_chunk = Ptrofs.repr (Memdata.size_chunk chunk) in
  match args with
  | [BA(IR addr); src] ->
      expand_builtin_vstore_common chunk addr _0p src
  | [BA_addrstack ofs; src] ->
      if offset_in_range (Ptrofs.add ofs size_chunk) then
        expand_builtin_vstore_common chunk X2 ofs src
      else begin
        expand_addptrofs X31 X2 ofs; (* X31 <- sp + ofs *)
        expand_builtin_vstore_common chunk X31 _0p src
      end
  | [BA_addptr(BA(IR addr), BA_int ofs); src] ->
      let ofs = Ptrofs.of_int ofs in
      if offset_in_range (Ptrofs.add ofs size_chunk) then
        expand_builtin_vstore_common chunk addr ofs src
      else begin
        expand_addptrofs X31 addr ofs; (* X31 <- addr + ofs *)
        expand_builtin_vstore_common chunk X31 _0p src
      end
  | [BA_addptr(BA(IR addr), BA_long ofs); src] ->
      let ofs = Ptrofs.of_int64 ofs in
      if offset_in_range (Ptrofs.add ofs size_chunk) then
        expand_builtin_vstore_common chunk addr ofs src
      else begin
        expand_addptrofs X31 addr ofs; (* X31 <- addr + ofs *)
        expand_builtin_vstore_common chunk X31 _0p src
      end
  | _ ->
      assert false
(*- #End *)

(* Handling of varargs *)

(* Number of integer registers, FP registers, and stack words
   used to pass the (fixed) arguments to a function. *)

let arg_int_size ri rf ofs k =
  if ri < 8
  then k (ri + 1) rf ofs
  else k ri rf (ofs + 1)

let arg_single_size ri rf ofs k =
  if rf < 8
  then k ri (rf + 1) ofs
  else arg_int_size ri rf ofs k

let arg_long_size ri rf ofs k =
  if Archi.ptr64 then
    if ri < 8
    then k (ri + 1) rf ofs
    else k ri rf (ofs + 1)
  else
    if ri < 7 then k (ri + 2) rf ofs
    else if ri = 7 then k (ri + 1) rf (ofs + 1)
    else k ri rf (align ofs 2 + 2)

let arg_double_size ri rf ofs k =
  if rf < 8
  then k ri (rf + 1) ofs
  else arg_long_size ri rf ofs k

let rec args_size l ri rf ofs =
  match l with
  | [] -> (ri, rf, ofs)
  | (Tint | Tany32) :: l ->
      arg_int_size ri rf ofs (args_size l)
  | Tsingle :: l ->
      arg_single_size ri rf ofs (args_size l)
  | Tlong :: l ->
      arg_long_size ri rf ofs (args_size l)
  | (Tfloat | Tany64) :: l ->
      arg_double_size ri rf ofs (args_size l)

(* Size in words of the arguments to a function.  This includes both
   arguments passed in integer registers and arguments passed on stack,
   but not arguments passed in FP registers. *)

let arguments_size sg =
  let (ri, _, ofs) = args_size (proj_sig_args sg) 0 0 0 in
  ri + ofs

let save_arguments first_reg base_ofs =
  for i = first_reg to 7 do
    expand_storeind_ptr
      int_param_regs.(i)
      X2
      (Ptrofs.repr (Z.add base_ofs (Z.of_uint ((i - first_reg) * wordsize))))
  done

let vararg_start_ofs : Ptrofs.int option ref = ref None

(*- E_COMPCERT_CODE_Asmexpand_builtin_va_start_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_VA_START_001 *)
let expand_builtin_va_start r =
  match !vararg_start_ofs with
  | None ->
      (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_VA_START_001 *)
      invalid_arg "Fatal error: va_start used in non-vararg function"
  | Some ofs ->
      expand_addptrofs X31 X2 ofs;
      expand_storeind_ptr X31 r _0p
(*- #End *)

(* Auxiliary for 64-bit integer arithmetic built-ins.  They expand to
   two instructions, one computing the low 32 bits of the result,
   followed by another computing the high 32 bits.  In cases where
   the first instruction would overwrite arguments to the second
   instruction, we must go through X31 to hold the low 32 bits of the result.
*)

let expand_int64_arith conflict rl fn =
  if conflict then (fn X31; emit (Pmv(rl, X31))) else fn rl

(* Byte swaps.  There are no specific instructions, so we use standard,
   not-very-efficient formulas. *)

(*- E_COMPCERT_CODE_Asmexpand_expand_bswap16_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_BSWAP16_001 *)
let expand_bswap16 d s =
  (* d = (s & 0xFF) << 8 | (s >> 8) & 0xFF *)
  emit (Pandiw(X31, X s, _255l));
  emit (Pslliw(X31, X X31, _8l));
  emit (Psrliw(d, X s, _8l));
  emit (Pandiw(d, X d, _255l));
  emit (Porw(d, X X31, X d))
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_expand_bswap32_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_BSWAP_001 *)
let expand_bswap32 d s =
  (* d = (s << 24)
       | (((s >> 8) & 0xFF) << 16)
       | (((s >> 16) & 0xFF) << 8)
       | (s >> 24)  *)
  emit (Pslliw(X1, X s, _24l));
  emit (Psrliw(X31, X s, _8l));
  emit (Pandiw(X31, X X31, _255l));
  emit (Pslliw(X31, X X31, _16l));
  emit (Porw(X1, X X1, X X31));
  emit (Psrliw(X31, X s, _16l));
  emit (Pandiw(X31, X X31, _255l));
  emit (Pslliw(X31, X X31, _8l));
  emit (Porw(X1, X X1, X X31));
  emit (Psrliw(X31, X s, _24l));
  emit (Porw(d, X X1, X X31))
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_expand_bswap64_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_BSWAP64_001 *)
let expand_bswap64 d s =
  (* d = s << 56
         | (((s >> 8) & 0xFF) << 48)
         | (((s >> 16) & 0xFF) << 40)
         | (((s >> 24) & 0xFF) << 32)
         | (((s >> 32) & 0xFF) << 24)
         | (((s >> 40) & 0xFF) << 16)
         | (((s >> 48) & 0xFF) << 8)
         | s >> 56 *)
  emit (Psllil(X1, X s, _56l));
  List.iter
    (fun (n1, n2) ->
      emit (Psrlil(X31, X s, n1));
      emit (Pandil(X31, X X31, _255L));
      emit (Psllil(X31, X X31, n2));
      emit (Porl(X1, X X1, X X31)))
    [(_8l,_48l); (_16l,_40l); (_24l,_32l); (_32l,_24l); (_40l,_16l); (_48l,_8l)];
  emit (Psrlil(X31, X s, _56l));
  emit (Porl(d, X X1, X X31))
(*- #End *)

(* Count leading zeros.  Algorithm 5-7 from Hacker's Delight,
   re-rolled as a loop to produce more compact code. *)

(*- E_COMPCERT_CODE_Asmexpand_expand_clz_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_CLZ_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_CLZLL_001 *)
let expand_clz ~sixtyfour ~splitlong =
  (* Input:  X in X5 or (X5, X6) if splitlong
     Result: N in X7
     Temporaries: S in X8, Y in X9 *)
  let lbl1 = new_label() in
  let lbl2 = new_label() in
  (* N := bitsize of X's type (32 or 64) *)
  expand_loadimm32 X7 (if sixtyfour || splitlong then _64l else _32l);
  (* S := initial shift amount (16 or 32) *)
  expand_loadimm32 X8 (if sixtyfour then _32l else _16l);
  if splitlong then begin
    (* if (Xhigh == 0) goto lbl1 *)
    emit (Pbeqw(X X6, X0, lbl1));
    (* N := 32 *)
    expand_loadimm32 X7 _32l;
    (* X := Xhigh *)
    emit (Pmv(X5, X6))
  end;
  (* lbl1: *)
  emit (Plabel lbl1);
  (* Y := X >> S *)
  emit (if sixtyfour then Psrll(X9, X X5, X X8) else Psrlw(X9, X X5, X X8));
  (* if (Y == 0) goto lbl2 *)
  emit (if sixtyfour then Pbeql(X X9, X0, lbl2) else Pbeqw(X X9, X0, lbl2));
  (* N := N - S *)
  emit (Psubw(X7, X X7, X X8));
  (* X := Y *)
  emit (Pmv(X5, X9));
  (* lbl2: *)
  emit (Plabel lbl2);
  (* S := S / 2 *)
  emit (Psrliw(X8, X X8, _1l));
  (* if (S != 0) goto lbl1; *)
  emit (Pbnew(X X8, X0, lbl1));
  (* N := N - X *)
  emit (Psubw(X7, X X7, X X5))
(*- #End *)

(* Count trailing zeros.  Algorithm 5-14 from Hacker's Delight,
   re-rolled as a loop to produce more compact code. *)

(*- E_COMPCERT_CODE_Asmexpand_expand_ctz_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_CTZ_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_CTZLL_001 *)
let expand_ctz ~sixtyfour ~splitlong =
  (* Input:  X in X6 or (X5, X6) if splitlong
     Result: N in X7
     Temporaries: S in X8, Y in X9 *)
  let lbl1 = new_label() in
  let lbl2 = new_label() in
  (* N := bitsize of X's type (32 or 64) *)
  expand_loadimm32 X7 (if sixtyfour || splitlong then _64l else _32l);
  (* S := initial shift amount (16 or 32) *)
  expand_loadimm32 X8 (if sixtyfour then _32l else _16l);
  if splitlong then begin
    (* if (Xlow == 0) goto lbl1 *)
    emit (Pbeqw(X X5, X0, lbl1));
    (* N := 32 *)
    expand_loadimm32 X7 _32l;
    (* X := Xlow *)
    emit (Pmv(X6, X5))
  end;
  (* lbl1: *)
  emit (Plabel lbl1);
  (* Y := X >> S *)
  emit (if sixtyfour then Pslll(X9, X X6, X X8) else Psllw(X9, X X6, X X8));
  (* if (Y == 0) goto lbl2 *)
  emit (if sixtyfour then Pbeql(X X9, X0, lbl2) else Pbeqw(X X9, X0, lbl2));
  (* N := N - S *)
  emit (Psubw(X7, X X7, X X8));
  (* X := Y *)
  emit (Pmv(X6, X9));
  (* lbl2: *)
  emit (Plabel lbl2);
  (* S := S / 2 *)
  emit (Psrliw(X8, X X8, _1l));
  (* if (S != 0) goto lbl1; *)
  emit (Pbnew(X X8, X0, lbl1));
  (* N := N - most significant bit of X *)
  emit (if sixtyfour then Psrlil(X6, X X6, _63l)
                     else Psrliw(X6, X X6, _31l));
  emit (Psubw(X7, X X7, X X6))
(*- #End *)

(* Full register width "and", "xor" *)

let _Pand (r, a1, a2) =
  if Archi.ptr64 then Pandl(r, a1, a2) else Pandw(r, a1, a2)
let _Pxor (r, a1, a2) =
  if Archi.ptr64 then Pxorl(r, a1, a2) else Pxorw(r, a1, a2)

(* Conditional move *)
(* res <- if cond then arg1 else arg2
   cond must be 0 or 1. *)

let expand_csel res cond arg1 arg2 =
  emit (Psubw(X31, X0, cond)); (* X31 = -1 if cond = 1, 0 if cond = 0 *)
  emit (_Pxor(X1, arg1, arg2));
  emit (_Pand(X1, X X1, X X31));
  emit (_Pxor(res, arg2, X X1))
     (* res = (arg1 ^ arg2) ^ arg2 = arg1  if cond = 1
        res = 0 ^ arg2 = arg2              if cond = 0 *)

(* Handling of compiler-inlined builtins *)

let expand_builtin_inline name args res =
  match name, args, res with
  (* Synchronization *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_001 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMBAR_001 *)
  | "__builtin_membar", [], _ ->
     ()
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_002 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_FENCE_001 *)
  | "__builtin_fence", [], _ ->
     emit Pfence
  (*- #End *)

  (* Vararg stuff *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_003 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_VA_START_001 *)
  | "__builtin_va_start", [BA(IR a)], _ ->
     expand_builtin_va_start a
  (*- #End *)

  (* Byte swaps *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_004 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_BSWAP16_001 *)
  | "__builtin_bswap16", [BA(IR a1)], BR(IR res) ->
     expand_bswap16 res a1
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_005 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_BSWAP_001 *)
  | ("__builtin_bswap"| "__builtin_bswap32"), [BA(IR a1)], BR(IR res) ->
     expand_bswap32 res a1
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_006 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_BSWAP64_001 *)
  | "__builtin_bswap64", [BA(IR a1)], BR(IR res) ->
     expand_bswap64 res a1
  (*- #End *)

  (* Count zeros *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_007 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_CLZ_001 *)
  | "__builtin_clz", [BA(IR a)], BR(IR res) ->
     assert (a = X5 && res = X7);
     expand_clz ~sixtyfour:false ~splitlong:false
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_008 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_CLZ_001 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_CLZLL_001 *)
  | "__builtin_clzl", [BA(IR a)], BR(IR res) ->
     assert (a = X5 && res = X7);
     expand_clz ~sixtyfour:Archi.ptr64 ~splitlong:false
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_009 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_CLZLL_001 *)
  | "__builtin_clzll", [BA(IR a)], BR(IR res) ->
     assert (a = X5 && res = X7);
     expand_clz ~sixtyfour:true ~splitlong:false

  | "__builtin_clzll", [BA_splitlong(BA(IR ah), BA(IR al))], BR(IR res) ->
     assert (al = X5 && ah = X6 && res = X7);
     expand_clz ~sixtyfour:false ~splitlong:true
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_010 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_CTZ_001 *)
  | "__builtin_ctz", [BA(IR a)], BR(IR res) ->
     assert (a = X6 && res = X7);
     expand_ctz ~sixtyfour:false ~splitlong:false
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_011 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_CTZ_001 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_CTZLL_001 *)
  | "__builtin_ctzl", [BA(IR a)], BR(IR res) ->
     assert (a = X6 && res = X7);
     expand_ctz ~sixtyfour:Archi.ptr64 ~splitlong:false
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_012 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_CTZLL_001 *)
  | "__builtin_ctzll", [BA(IR a)], BR(IR res) ->
     assert (a = X6 && res = X7);
     expand_ctz ~sixtyfour:true ~splitlong:false

  | "__builtin_ctzll", [BA_splitlong(BA(IR ah), BA(IR al))], BR(IR res) ->
     assert (al = X5 && ah = X6 && res = X7);
     expand_ctz ~sixtyfour:false ~splitlong:true
  (*- #End *)

  (* Float arithmetic *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_013 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_FSQRT_001 *)
  | ("__builtin_fsqrt" | "__builtin_sqrt"), [BA(FR a1)], BR(FR res) ->
     emit (Pfsqrtd(res, a1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_014 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_FMADD_001 *)
  | "__builtin_fmadd", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfmaddd(res, a1, a2, a3))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_015 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_FMSUB_001 *)
  | "__builtin_fmsub", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfmsubd(res, a1, a2, a3))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_016 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_FNMADD_001 *)
  | "__builtin_fnmadd", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfnmaddd(res, a1, a2, a3))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_017 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_FNMSUB_001 *)
  | "__builtin_fnmsub", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfnmsubd(res, a1, a2, a3))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_018 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_FMIN_001 *)
  | "__builtin_fmin", [BA(FR a1); BA(FR a2)], BR(FR res) ->
      emit (Pfmind(res, a1, a2))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_019 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_FMAX_001 *)
  | "__builtin_fmax", [BA(FR a1); BA(FR a2)], BR(FR res) ->
      emit (Pfmaxd(res, a1, a2))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_020 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_DTOB_001 *)
  | "__builtin_dtob", [BA(FR a1)],
                          BR_splitlong(BR(IR rh), BR(IR rl)) ->
     assert (not Archi.ptr64);
     emit (Paddiw(X2, X X2, _m16l));
     emit (Pcfi_adjust _16p);
     emit (Pfsd(a1, X2, Ofsimm _0p));
     emit (Plw(rl, X2, Ofsimm _0p));
     emit (Plw(rh, X2, Ofsimm _4p));
     emit (Paddiw(X2, X X2, _16l));
     emit (Pcfi_adjust _m16p);

  | "__builtin_dtob", [BA(FR a1)],
                          BR(IR res) ->
     assert (Archi.ptr64);
     emit (Pfmvxd(res, a1))
  (*- #End *)

  (* No operation *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_023 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_NOP_001 *)
  | "__builtin_nop", [], _ ->
     emit Pnop
  (*- #End *)

  (* Optimization hint *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_024 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_UNREACHABLE_001 *)
  | "__builtin_unreachable", [], _ ->
     ()
  (*- #End *)

  (* Catch-all *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_025 *)
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
      let sg = get_current_function_sig() in
      emit (Pmv (X30, X2));
      if (sg.sig_cc.cc_vararg <> None) then begin
        let n = arguments_size sg in
        let extra_sz = if n >= 8 then 0 else align ((8 - n) * wordsize) 16 in
        let full_sz = Z.add sz (Z.of_uint extra_sz) in
       (* Check stack size + 16 for additional stack used by built-ins *)
        check_stack_size (Z.add full_sz _16);
        expand_addptrofs X2 X2 (Ptrofs.repr (Z.neg full_sz));
        emit (Pcfi_adjust (Ptrofs.repr sz));
        let va_ofs =
          Z.add full_sz (Z.of_sint ((n - 8) * wordsize)) in
        vararg_start_ofs := Some (Ptrofs.repr va_ofs);
        save_arguments n va_ofs
      end else begin
        check_stack_size sz;
        expand_addptrofs X2 X2 (Ptrofs.repr (Z.neg sz));
        emit (Pcfi_adjust (Ptrofs.repr sz));
        vararg_start_ofs := None
      end
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_002 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_PFREEFRAME_001 *)
  | Pfreeframe (sz, ofs) ->
     let sg = get_current_function_sig() in
     let extra_sz =
      if (sg.sig_cc.cc_vararg <> None) then begin
        let n = arguments_size sg in
        if n >= 8 then 0 else align ((8 - n) * wordsize) 16
      end else 0 in
     expand_addptrofs X2 X2 (Ptrofs.repr (Z.add sz (Z.of_uint extra_sz)))
  (*- #End *)

  | Pcsel(rd, rcond, rs1, rs2) ->
      expand_csel rd (X rcond) (X rs1) (X rs2)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_003 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_PSEQW_001 *)
  | Pseqw(rd, rs1, rs2) ->
      (* emulate based on the fact that x == 0 iff x <u 1 (unsigned cmp) *)
      if rs2 = X0 then begin
        emit (Psltiuw(rd, rs1, _1l))
      end else begin
        emit (Pxorw(rd, rs1, rs2)); emit (Psltiuw(rd, X rd, _1l))
      end
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_004 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_PSNEW_001 *)
  | Psnew(rd, rs1, rs2) ->
      (* emulate based on the fact that x != 0 iff 0 <u x (unsigned cmp) *)
      if rs2 = X0 then begin
        emit (Psltuw(rd, X0, rs1))
      end else begin
        emit (Pxorw(rd, rs1, rs2)); emit (Psltuw(rd, X0, X rd))
      end
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_005 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_PSEQL_001 *)
  | Pseql(rd, rs1, rs2) ->
      (* emulate based on the fact that x == 0 iff x <u 1 (unsigned cmp) *)
      if rs2 = X0 then begin
        emit (Psltiul(rd, rs1, _1L))
      end else begin
        emit (Pxorl(rd, rs1, rs2)); emit (Psltiul(rd, X rd, _1L))
      end
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_006 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_PSNEL_001 *)
  | Psnel(rd, rs1, rs2) ->
      (* emulate based on the fact that x != 0 iff 0 <u x (unsigned cmp) *)
      if rs2 = X0 then begin
        emit (Psltul(rd, X0, rs1))
      end else begin
        emit (Pxorl(rd, rs1, rs2)); emit (Psltul(rd, X0, X rd))
      end
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_007 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_PCVTL2W_001 *)
  | Pcvtl2w(rd, rs) ->
      assert Archi.ptr64;
      emit (Paddiw(rd, rs, _0l))  (* 32-bit sign extension *)
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_008 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_PCVTW2L_001 *)
  | Pcvtw2l(r) ->
      assert Archi.ptr64
      (* no-operation because the 32-bit integer was kept sign extended already *)
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_009 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_PJAL_R_001 *)
  | Pjal_r(r, sg) ->
      fixup_call sg; emit instr
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_010 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_PJAL_S_001 *)
  | Pjal_s(symb, sg) ->
      fixup_call sg; emit instr
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_011 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_PJ_R_001 *)
  | Pj_r(r, sg) when r <> X1 ->
      fixup_call sg; emit instr
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_012 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_PJ_S_001 *)
  | Pj_s(symb, sg) ->
      fixup_call sg; emit instr
  (*- #End *)

  | Pbuiltin (ef,args,res) ->
     begin match ef with
     (*- E_COMPCERT_CODE_Asmexpand_instruction_013 *)
     (*- #Justify_Derived "Call to expansion function for builtins" *)
     | EF_builtin (name,sg) ->
        expand_builtin_inline (camlstring_of_coqstring name) args res
     (*- #End *)

     (*- E_COMPCERT_CODE_Asmexpand_instruction_014 *)
     (*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_LOAD_001 *)
     | EF_vload chunk ->
        expand_builtin_vload chunk args res
     (*- #End *)

     (*- E_COMPCERT_CODE_Asmexpand_instruction_015 *)
     (*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_STORE_001 *)
     | EF_vstore chunk ->
        expand_builtin_vstore chunk args
     (*- #End *)

     (*- E_COMPCERT_CODE_Asmexpand_instruction_016 *)
     (*- #Link_to E_COMPCERT_TR_Function_EXPAND_ANNOT_INT_001 *)
     | EF_annot_val (kind,txt,targ) ->
        expand_annot_val kind txt targ args res
     (*- #End *)

     (*- E_COMPCERT_CODE_Asmexpand_instruction_017 *)
     (*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_001 *)
     | EF_memcpy(sz, al) ->
        expand_builtin_memcpy sz al args
     (*- #End *)

     (*- E_COMPCERT_CODE_Asmexpand_instruction_018 *)
     (*- #Justify_Derived "Default case" *)
     | EF_annot _ | EF_debug _ | EF_inline_asm _ ->
        emit instr
     | _ ->
        assert false
     end
  | _ ->
     emit instr

(* NOTE: Dwarf register maps for RV32G are not yet specified
   officially.  This is just a placeholder.  *)
let int_reg_to_dwarf = function
               | X1  -> 1  | X2  -> 2  | X3  -> 3
   | X4  -> 4  | X5  -> 5  | X6  -> 6  | X7  -> 7
   | X8  -> 8  | X9  -> 9  | X10 -> 10 | X11 -> 11
   | X12 -> 12 | X13 -> 13 | X14 -> 14 | X15 -> 15
   | X16 -> 16 | X17 -> 17 | X18 -> 18 | X19 -> 19
   | X20 -> 20 | X21 -> 21 | X22 -> 22 | X23 -> 23
   | X24 -> 24 | X25 -> 25 | X26 -> 26 | X27 -> 27
   | X28 -> 28 | X29 -> 29 | X30 -> 30 | X31 -> 31

let float_reg_to_dwarf = function
   | F0  -> 32 | F1  -> 33 | F2  -> 34 | F3  -> 35
   | F4  -> 36 | F5  -> 37 | F6  -> 38 | F7  -> 39
   | F8  -> 40 | F9  -> 41 | F10 -> 42 | F11 -> 43
   | F12 -> 44 | F13 -> 45 | F14 -> 46 | F15 -> 47
   | F16 -> 48 | F17 -> 49 | F18 -> 50 | F19 -> 51
   | F20 -> 52 | F21 -> 53 | F22 -> 54 | F23 -> 55
   | F24 -> 56 | F25 -> 57 | F26 -> 58 | F27 -> 59
   | F28 -> 60 | F29 -> 61 | F30 -> 62 | F31 -> 63

let preg_to_dwarf = function
   | IR r -> int_reg_to_dwarf r, None
   | FR r -> float_reg_to_dwarf r, None
   | _ -> assert false

let expand_function id fn =
  try
    set_current_function fn;
    fixup_function_entry fn.fn_sig;
    expand id (* sp= *) 2 preg_to_dwarf expand_instruction fn.fn_code;
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
