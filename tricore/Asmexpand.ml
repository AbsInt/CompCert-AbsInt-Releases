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
(*  The contributions by Prashanth Mundkur are reused and adapted      *)
(*  under the terms of a Contributor License Agreement between         *)
(*  SRI International and INRIA.                                       *)
(*                                                                     *)
(* *********************************************************************)
open Asm
open Asmexpandaux
open AST
open Camlcoq

(* Useful constants and helper functions *)

(* Emit with check that indexed load stores only use A10  *)
let emit_checked instr =
  begin match instr with
  | Pldb (_, a, _) | Pldbu (_, a, _)  | Pldh (_, a, _) | Pldhu (_, a, _)
  | Pldw (_, a, _) | Pldw_a (_, a, _) | Plda (_, a, _) | Pfldw (_, a, _)
  | Pstb (_, a, _) | Psth (_, a, _)   | Pstw (_, a, _) | Pstw_a (_, a, _)
  | Psta (_, a, _) | Pfstw (_, a, _)  -> assert (a = A10);
  | _ -> ()
  end;
  emit instr

(* Emit_Checked instruction sequences that set or offset a register by a constant. *)

let expand_loadimm (dst: dreg) n =
  List.iter emit_checked (Asmgen.loadimm dst n [])

let expand_addimm_addr (dst: areg) (r: areg) n =
  List.iter emit_checked
    (Asmgen.addimm_addr dst r n [])


(* Handling of annotations *)

let expand_annot_val kind txt targ args res =
  emit_checked (Pbuiltin (EF_annot(kind,txt,[targ]), args, BR_none));
  match args, res with
  | [BA(DREG src)], BR(DREG dst) ->
     if dst <> src then emit_checked (Pmov (dst, src))
  | _, _ ->
     raise (AsmexpandError "ill-formed __builtin_annot_intval")

(* Handling of memcpy *)

(* Move the value of a builtin arg to the address register [tmp]. *)
let expand_memcpy_arg arg tmp =
  match arg with
  | BA (AREG r) ->
    if r <> tmp then
      emit_checked (Pmov_aa (tmp,r))
  | BA (DREG r) ->
    emit_checked (Pmov_a (tmp, r))
  | BA_addrstack ofs ->
    expand_addimm_addr tmp (INDREG A10) (Ptrofs.to_int ofs)
  | _ -> assert false

let expand_builtin_memcpy  sz args =
  let (dst, src) =
    match args with [d; s] -> (d, s) | _ -> assert false in
  if Ptrofs.ltu Ptrofs.zero sz then begin
    let sz = I32.sub (Ptrofs.to_int sz) _1l in
    let lbl = new_label () in
    (* We want to move [src] and [dst] to the registers [A12] and [A13] since they are
       both marked as destroyed. We move [src] first so we need to take care that it
       does no overwrite [dst]. For [dst] we just need to chose the register not used for
       [src] *)
    let src_tmp = if dst <> BA (AREG (INDREG A12)) then (INDREG A12) else A13 in
    let dst_tmp = if src_tmp <> A13 then A13 else (INDREG A12) in
    expand_memcpy_arg src src_tmp;
    expand_memcpy_arg dst dst_tmp;
    emit_checked (Pmovh_ao (A3, (Asmgen.high_s sz)));
    emit_checked (Plea_sc16 (A3, A3, (Asmgen.low_s sz)));
    emit_checked (Plabel lbl);
    emit_checked (Pldbu_prr (D0, src_tmp));
    emit_checked (Pstb_prr (D0, dst_tmp));
    emit_checked (Ploop (A3, lbl))
  end

(* Handling of volatile reads and writes *)

(* Since we don't use indexed addressing we need to add the offset before
   executing the memory access operations. For 64 bit memory accesses we
   move the base to A3 since we need to update the base for the load of the
   other half. *)
let expand_vmem_addr chunk base ofs =
  if not (I32.eq ofs _0l) then begin
    expand_addimm_addr A3 base ofs;
    A3
  end else if chunk = Mint64 then begin
    if base <> A3 then emit_checked (Pmov_aa (A3, base));
    A3
  end else
    base


let expand_builtin_vload_common chunk base ofs res =
  let b = expand_vmem_addr chunk base ofs in
  match chunk, res with
  | Mint8signed, BR (DREG dst) ->
    emit_checked (Pldb_rr (dst, b))
  | (Mbool | Mint8unsigned), BR (DREG dst) ->
    emit_checked (Pldbu_rr (dst, b))
  | Mint16signed, BR (DREG dst) ->
    emit_checked (Pldh_rr (dst, b))
  | Mint16unsigned, BR (DREG dst) ->
    emit_checked (Pldhu_rr (dst, b))
  | Mint32, BR (DREG dst) ->
    emit_checked (Pldw_rr (dst, b))
  | Mint64, BR_splitlong (BR (DREG dst1), BR (DREG dst2)) ->
    assert (b = A3);
    (* Use the increment variant to add 4 for the second half.
       We write first into dst2 because the second field of BR_splitlong 
       is the lower half of the value and TriCore is little-endian. *)
    emit_checked (Pldw_prr (dst2, b));
    emit_checked (Pldw_rr (dst1, b))
  | Mfloat32, BR (DREG dst) ->
    emit_checked (Pfldw_rr (dst, b))
  | _ ->
    assert false

let expand_builtin_vload chunk args dst =
  match args with
  | [BA (AREG addr)] ->
     expand_builtin_vload_common chunk addr _0l dst
  | [BA (DREG addr)] ->
    emit_checked (Pmov_a (A3, addr));
    expand_builtin_vload_common chunk A3 _0l dst
  | [BA_addrstack ofs] ->
    let ofs = Ptrofs.to_int ofs in
     expand_builtin_vload_common chunk (INDREG A10) ofs dst
  | [BA_addptr(BA(AREG addr), (BA_int ofs))] ->
    expand_builtin_vload_common chunk addr ofs dst
  | [BA_addptr(BA(DREG addr), (BA_int ofs))] ->
    emit_checked (Pmov_a (A3, addr));
    expand_builtin_vload_common chunk A3 ofs dst
  | _ ->
    assert false

let expand_builtin_vstore_common chunk base ofs src =
  let b = expand_vmem_addr chunk base ofs in
  match chunk, src with
  | (Mbool | Mint8signed | Mint8unsigned), BA (DREG src) ->
    emit_checked (Pstb_rr (src, b))
  | (Mint16signed | Mint16unsigned), BA (DREG src) ->
    emit_checked (Psth_rr (src, b))
  | Mint32, BA (DREG src) ->
    emit_checked (Pstw_rr (src, b))
  | Mint32, BA (AREG src) ->
    emit_checked (Psta_rr (src, b))
  | Mint64, BA_splitlong (BA (DREG src1), BA (DREG src2)) ->
    assert (b = A3);
    (* Use the increment variant to add 4 for the second half.
       We read first from dst2 because the second field of BR_splitlong 
       is the lower half of the value and TriCore is little-endian. *)
    emit_checked (Pstw_prr (src2, b));
    emit_checked (Pstw_rr (src1, b))
  | Mfloat32, BA (DREG src) ->
    emit_checked (Pfstw_rr (src, b))
  | _ ->
    assert false

let expand_builtin_vstore chunk args =
  match args with
  | [BA (AREG addr); src] ->
    expand_builtin_vstore_common chunk addr _0l src
  | [BA (DREG addr); src] ->
    emit_checked (Pmov_a (A3, addr));
    expand_builtin_vstore_common chunk A3 _0l src
  | [BA_addrstack ofs; src] ->
    let ofs = Ptrofs.to_int ofs in
     expand_builtin_vstore_common chunk (INDREG A10) ofs src
  | [BA_addptr(BA(AREG addr), (BA_int ofs)); src] ->
    expand_builtin_vstore_common chunk addr ofs src
  | [BA_addptr(BA(DREG addr), (BA_int ofs)); src] ->
    emit_checked (Pmov_a (A3, addr));
    expand_builtin_vstore_common chunk A3 ofs src
  | _ ->
    assert false

(* Handling of compiler-inlined builtins *)


(* The offset from the the current stack pointer to the first variable argument in the parent's stack frame. *)
let vararg_start_ofs : Z.t option ref = ref None

(* Place the address of the first variable argument into the memory location pointed to by the [r] register. *)
let expand_builtin_va_start r =
    match !vararg_start_ofs with
  | None ->
      invalid_arg "Fatal error: va_start used in non-vararg function"
  | Some ofs ->
     (* Move r to an address register. *)
     let r' = match r with
       | DREG r' -> emit_checked (Pmov_a (A3, r')); A3
       | AREG r' -> if r' = A13 then begin emit_checked (Pmov_aa (A3,r')); A3 end else r'
       | _ -> raise (AsmexpandError "Using builtin_va_start with wrong register")
     in
    (* Calculate the start address by adding the stored ofs to the stack pointer.
       We use A13 as temporary here since we might need the temporary register for
       holding the address from r. *)
    let ofs = I32.repr ofs in
    expand_addimm_addr A13 (INDREG A10) ofs;
    (* Store at r the start address. *)
    emit_checked (Psta_rr (A13, r'))

(* Auxiliary for 64-bit integer arithmetic built-ins.  They expand to
   two instructions, one computing the low 32 bits of the result,
   followed by another computing the high 32 bits.  In cases where
   the first instruction would overwrite arguments to the second
   instruction, we must go through D0 to hold the low 32 bits of the result.
*)

let expand_builtin_inline name args res =
  match name, args, res with
  (* Synchronization *)
  | "__builtin_membar", [], _ ->
    ()
  (* Byte swaps *)
  | "__builtin_bswap16", [BA(DREG a1)], BR(DREG res) ->
    (* a1  = aabbccdd *)
    emit_checked (Pextru (D0, a1, _8l, _8l));
    (* D0  = 000000cc *)
    emit_checked (Pinsert (res, D0, a1, _8l,_8l))
    (* res = 0000ddcc *)
  | ("__builtin_bswap"| "__builtin_bswap32"), [BA(DREG a1)], BR(DREG res) ->
    (* a1  = aabbccdd *)
    emit_checked (Psh_sc9 (D0, a1, _m16l));
    (* D0  = 0000aabb *)
    emit_checked (Pinsert (res, a1, a1,_16l, _8l));
    (* res = aaddccdd *)
    emit_checked (Pdextr (res, res, res, _8l));
    (* res = ddccddaa *)
    emit_checked (Pinsert (res, res, D0, _8l, _8l))
    (* res = ddccbbaa *)
  (* Count zeros *)
  | ("__builtin_clz" | "__builtin_clzl"), [BA(DREG a)], BR(DREG res) ->
    emit_checked (Pclz (res, a))
  | "__builtin_clzll", [BA_splitlong(BA(DREG ah), BA(DREG al))], BR (DREG res) ->
    (* We compute the leading zeros of the lower half and either add 32 to it (high half is zero)
       or just use the result of the clz for the higher half *)
    emit_checked (Pclz (D0, al));
    emit_checked (Pcsub (D0, ah, D0, D0)); (* D0 = ah == 0 ? D0 else 0 *)
    emit_checked (Pclz (res, ah));
    emit_checked (Padd (res, res, D0))
  | ("__builtin_ctz" | "__builtin_ctzl"), [BA(DREG a)], BR(DREG res) ->
    (* We calculate tmp = (a - 1) & !a. Then the trailing zeros are all one and the
       rest is zero. Then we can use clz and return the result subtracted from 32 *)
    emit_checked (Paddi (D0, a, _m1l));
    emit_checked (Pandn (D0, D0, a));
    emit_checked (Pclz (D0, D0));
    emit_checked (Prsub (res, D0, _32l));
  | "__builtin_ctzll",  [BA_splitlong(BA(DREG ah), BA(DREG al))], BR (DREG res) ->
    let lbl_zero = new_label () in
    let lbl_end = new_label () in
    (* Lower part is non zero so we just calculate the trailing bits of the low half *)
    emit_checked (Pjeq_sc4 (al, _0l, lbl_zero));
    emit_checked (Paddi (D0, al, _m1l));
    emit_checked (Pandn (D0, D0, al));
    emit_checked (Pclz (D0, D0));
    emit_checked (Prsub (res, D0, _32l));
    emit_checked (Pj_l lbl_end);
    (* Lower part is zero so we just add 32 to the trailing zeros of the high half *)
    emit_checked (Plabel lbl_zero);
    emit_checked (Paddi (D0, ah, _m1l));
    emit_checked (Pandn (D0, D0, ah));
    emit_checked (Pclz (D0, D0));
    emit_checked (Prsub (res, D0, _64l));
    emit_checked (Plabel lbl_end)
  (* Float arithmetic *)
  | ("__builtin_fsqrt" | "__builtin_sqrt"), [BA (DREG a1)], BR (DREG res) ->
    raise (AsmexpandError ("unsupported builtin " ^ name))
  (* va_start *)
  | "__builtin_va_start", [BA(r)], _ ->
    expand_builtin_va_start r
  (* No operation *)
  | "__builtin_nop", [], _ ->
     emit_checked Pnop

   (* Float arithmetic *)
  | "__builtin_fabs", [BA (DREG a1)], BR(DREG res) ->
      emit_checked (Pinsert_uc4 (res, a1, _0l, _31l, _1l));

   (* Optimization hint *)
  | "__builtin_unreachable", [], _ ->
     ()
  (* Catch-all *)
  | _ ->
     raise (AsmexpandError ("unrecognized builtin " ^ name))

let va_stack_offset sg =
  let fixed = Conventions1.fixed_arguments sg in
  let args = sg.sig_args @ [AST.Xint] in
  (* We calculate the offset by abusing the loc_arguments_rec function with the
     fixed arguments from the signature and one additional artificial argument that
     will be placed on the stack, then the offset of that argument is the start
     offset of the varargs *)
  let args = Conventions1.loc_arguments_rec args fixed false Z.Z0 Z.Z0 Z.Z0 in
  (* We know that the last argument must be on the stack and of integer type. *)
  match List.hd (List.rev args) with
  | Locations.(One S (Outgoing, ofs, Tint)) ->
    Z.mul ofs (Z.of_sint 4)
  | _ -> assert false

let expand_instruction instr =
  match instr with
  | Pallocframe sz ->
    emit_checked (Pmov_aa (INDREG A12, INDREG A10));
    check_stack_size sz;
    let sz' = I32.(neg (repr sz)) in
    expand_addimm_addr (INDREG A10) (INDREG A10) sz';
    let sg = get_current_function_sig() in
    if sg.sig_cc.cc_vararg <> None then begin
      let ofs = va_stack_offset sg in
      let va_ofs = Z.add sz ofs in
      vararg_start_ofs := Some va_ofs
    end else
      vararg_start_ofs := None
  | Pfreeframe (sz, ofs) ->
    expand_addimm_addr (INDREG A10) (INDREG A10) (I32.repr sz)
  | Pbuiltin (ef,args,res) ->
     begin match ef with
     | EF_builtin (name,sg) ->
        expand_builtin_inline name args res
     | EF_vload chunk ->
        expand_builtin_vload chunk args res
     | EF_vstore chunk ->
        expand_builtin_vstore chunk args
     | EF_annot_val (kind,txt,targ) ->
        expand_annot_val kind txt targ args res
     | EF_memcpy(sz, al) ->
        expand_builtin_memcpy sz args
     | EF_annot _ | EF_debug _ | EF_inline_asm _ ->
        emit_checked instr
     | _ ->
        assert false
     end
  | Pabsf (rd, r) ->
    (* There is no absf in older versions of the ISA.
       We implement this by inserting 0 into r at posistion
       31 and length 1 *)
    emit_checked (Pinsert_uc4 (rd,r,_0l,_31l,_1l))
  | Pnegf (rd, r) ->
    (* There is no negf in older versions of the ISA.
       We implement this by inserting the negated sign
       bit into r at position 31 *)
    emit_checked (Pinsn_t (rd,r,r,_31l,_31l))
  | Ploadsi (rd,c) ->
    expand_loadimm rd (Floats.Float32.to_bits c)
  | _ ->
    (* We use the version of emit_checked without check for unchanged intructions *)
    emit instr

let dreg_to_dwarf = function
  | D0  -> 0  | D1  -> 1  | D2  -> 2  | D3  -> 3
  | D4  -> 4  | D5  -> 5  | D6  -> 6  | D7  -> 7
  | D8  -> 8  | D9  -> 9  | D10 -> 10 | D11 -> 11
  | D12 -> 12 | D13 -> 13 | D14 -> 14 | D15 -> 15

let areg_to_dwarf = function
  | A0  -> 16 | A1  -> 17 | A2  -> 18 | A3  -> 19
  | A4  -> 20 | A5  -> 21 | A6  -> 22 | A7  -> 23
  | A8  -> 24 | A9  -> 25 | INDREG A10 -> 26
  | A11 -> 27 | INDREG A12 -> 28
  | A13 -> 29 | A14 -> 30 | A15 -> 31

let preg_to_dwarf = function
  | AREG r -> areg_to_dwarf r, None
  | DREG r -> dreg_to_dwarf r, None
  | _ -> assert false

let expand_function id fn =
  try
    set_current_function fn;
    let sp = areg_to_dwarf (INDREG A10) in
    expand id sp preg_to_dwarf expand_instruction fn.fn_code;
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
