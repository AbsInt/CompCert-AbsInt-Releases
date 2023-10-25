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

exception Error of string

(* Useful constants and helper functions *)

let _0 = Integers.Int.zero
let _1 = Integers.Int.one
let _4 = coqint_of_camlint 4l
let _8 = coqint_of_camlint 8l
let _16 = coqint_of_camlint 16l
let _27 = coqint_of_camlint 27l
let _31 = coqint_of_camlint 31l
let _32 = coqint_of_camlint 32l
let _64 = coqint_of_camlint 64l
let _255 = coqint_of_camlint 255l
let _283 = coqint_of_camlint 283l
let _m1 = Integers.Int.mone
let _m16 = coqint_of_camlint (-16l)

(* Emit instruction sequences that set or offset a register by a constant. *)

let expand_loadimm (dst: dreg) n =
  List.iter emit (Asmgen.loadimm dst n [])

let expand_addimm_a (dst: areg) (r: areg) n =
  List.iter emit
    (Asmgen.addimm_gen
       (fun rd r l -> Plea_sc16 (rd, r, l))
       (fun rd r h -> Paddih_a (rd, r, h)) dst r n [])

let expand_indexed_memory_access  mk1 mk2 base ofs =
  List.iter emit
    (Asmgen.indexed_memory_access mk1 mk2 base ofs [])


let expand_storeind_ptr (src: areg) (base: areg) ofs =
  List.iter emit (Asmgen.storeind_ptr src base ofs [])


(* Handling of annotations *)

let expand_annot_val kind txt targ args res =
  emit (Pbuiltin (EF_annot(kind,txt,[targ]), args, BR_none));
  match args, res with
  | [BA(DREG src)], BR(DREG dst) ->
     if dst <> src then emit (Pmov (dst, src))
  | _, _ ->
     raise (Error "ill-formed __builtin_annot_val")

(* Handling of memcpy *)

let expand_memcpy_arg arg tmp =
  match arg with
  | BA (DREG r) ->
    emit (Pmov_a (tmp, r))
  | BA_addrstack ofs ->
    expand_addimm_a tmp A10 ofs
  | _ -> assert false

let expand_builtin_memcpy  sz al args =
  let (dst, src) =
    match args with [d; s] -> (d, s) | _ -> assert false in
  if (Z.to_int sz) > 0 then begin
    let sz = Integers.Int.sub (Integers.Int.repr sz) _1 in
    let lbl = new_label () in
    let dst_tmp = A13
    and src_tmp = A12 in
    expand_memcpy_arg dst dst_tmp;
    expand_memcpy_arg src src_tmp;
    emit (Pmovh_ao (A14, (Asmgen.high_s sz)));
    emit (Plea_sc16 (A14, A14, (Asmgen.low_s sz)));
    emit (Plabel lbl);
    emit (Pldbu_prr (D0, src_tmp));
    emit (Pstb_prr (D0, dst_tmp));
    emit (Ploop (A14, lbl))
  end
(* Handling of volatile reads and writes *)

let expand_builtin_vload_common chunk base ofs res =
  match chunk, res with
  | Mint8signed, BR (DREG dst) ->
    expand_indexed_memory_access (fun b -> Pldb_rr (dst, b)) (fun b ofs -> Pldb (dst, b, ofs)) base ofs
  | Mint8unsigned, BR (DREG dst) ->
    expand_indexed_memory_access (fun b -> Pldbu_rr (dst, b)) (fun b ofs -> Pldbu (dst, b, ofs)) base ofs
  | Mint16signed, BR (DREG dst) ->
    expand_indexed_memory_access (fun b -> Pldh_rr (dst, b)) (fun b ofs -> Pldh (dst, b, ofs)) base ofs
  | Mint16unsigned, BR (DREG dst) ->
    expand_indexed_memory_access (fun b -> Pldhu_rr (dst, b)) (fun b ofs -> Pldhu (dst, b, ofs)) base ofs
  | Mint32, BR (DREG dst) ->
    expand_indexed_memory_access (fun b -> Pldw_rr (dst, b)) (fun b ofs -> Pldw (dst, b, ofs)) base ofs
  | Mint64, BR_splitlong (BR (DREG dst1), BR (DREG dst2)) ->
    let ofs_hi = Integers.Ptrofs.add ofs _4 in
    expand_indexed_memory_access (fun b -> Pldw_rr (dst1, b)) (fun b ofs -> Pldw (dst1, b, ofs)) base ofs_hi;
    expand_indexed_memory_access (fun b -> Pldw_rr (dst2, b)) (fun b ofs -> Pldw (dst2, b, ofs)) base ofs
  | Mfloat32, BR (DREG dst) ->
    expand_indexed_memory_access (fun b -> Pfldw_rr (dst, b)) (fun b ofs -> Pfldw (dst, b, ofs)) base ofs
  | _ ->
    assert false

let expand_builtin_vload chunk args dst =
  match args with
  | [BA (DREG addr)] ->
    emit (Pmov_a (A14, addr));
    expand_builtin_vload_common chunk A14 _0 dst
  | [BA_addrstack ofs] ->
    expand_builtin_vload_common chunk A10 ofs dst
  | [BA_addptr(BA(DREG addr), (BA_int ofs | BA_long ofs))] ->
    emit (Pmov_a (A14, addr));
    expand_builtin_vload_common chunk A14 ofs dst
  | _ ->
    assert false

let expand_builtin_vstore_common chunk base ofs src =
  match chunk, src with
  | Mint8signed, BA (DREG src)
  | Mint8unsigned, BA (DREG src) ->
    expand_indexed_memory_access (fun b -> Pstb_rr (src, b)) (fun b ofs -> Pstb (src, b, ofs)) base ofs
  | Mint16signed, BA (DREG src)
  | Mint16unsigned, BA (DREG src) ->
    expand_indexed_memory_access (fun b -> Psth_rr (src, b)) (fun b ofs -> Psth (src, b, ofs)) base ofs
  | Mint32, BA (DREG src) ->
    expand_indexed_memory_access (fun b -> Pstw_rr (src, b)) (fun b ofs -> Pstw (src, b, ofs)) base ofs
  | Mint64, BA_splitlong (BA (DREG src1), BA (DREG src2)) ->
    let ofs_hi = Integers.Ptrofs.add ofs _4 in
    expand_indexed_memory_access (fun b -> Pstw_rr (src2, b)) (fun b ofs -> Pstw (src2, b, ofs)) base ofs;
    expand_indexed_memory_access (fun b -> Pstw_rr (src1, b)) (fun b ofs -> Pstw (src1, b, ofs)) base ofs_hi
  | Mfloat32, BA (DREG src) ->
    expand_indexed_memory_access (fun b -> Pfstw_rr (src, b)) (fun b ofs -> Pfstw (src, b, ofs)) base ofs
  | _ ->
    assert false

let expand_builtin_vstore chunk args =
  match args with
  | [BA (DREG addr); src] ->
    emit (Pmov_a (A14, addr));
    expand_builtin_vstore_common chunk A14 _0 src
  | [BA_addrstack ofs; src] ->
    expand_builtin_vstore_common chunk A10 ofs src
  | [BA_addptr(BA(DREG addr), (BA_int ofs | BA_long ofs)); src] ->
    emit (Pmov_a (A14, addr));
    expand_builtin_vstore_common chunk A14 ofs src
  | _ ->
    assert false

(* Handling of compiler-inlined builtins *)


let vararg_start_ofs : Z.t option ref = ref None

let expand_builtin_va_start r =
    match !vararg_start_ofs with
  | None ->
      invalid_arg "Fatal error: va_start used in non-vararg function"
  | Some ofs ->
    (* Calculate the start offset by adding the stored ofs to the stack pointer.
       We use A13 as temporary here since we need the temporary register for
       holding the address from r *)
    expand_addimm_a A13 A10 ofs;
    (* Move r to the temporary register *)
    emit (Pmov_a (A14, r));
    (* Store at r the offset *)
    emit (Psta_rr (A13, A14))

(* Auxiliary for 64-bit integer arithmetic built-ins.  They expand to
   two instructions, one computing the low 32 bits of the result,
   followed by another computing the high 32 bits.  In cases where
   the first instruction would overwrite arguments to the second
   instruction, we must go through D0 to hold the low 32 bits of the result.
*)

let expand_int64_arith conflict rl fn =
  if conflict then (fn D0; emit (Pmov(rl, D0))) else fn rl

let expand_bswap32 res a1 =
  if Configuration.model <> "tc161" then begin
    (* Shuffle bytes using the shuffle instruction:
       A = byte_select(a1, 3);
       B = byte_select(a1, 2);
       C = byte_select(a1, 1);
       D = byte_select(a1, 0);
       res[7:0]   = A;
       res[15:8]  = B;
       res[23:16] = C;
       res[31:24] = D; *)
    emit (Pshuffle (res, a1, _27))
  end else begin
    emit (Psh_sc9 (D0, a1, _m16));
    emit (Pinsert (res, a1, a1,_16, _8));
    emit (Pdextr (res, res, res, _8));
    emit (Pinsert (res, res, D0, _8, _8))
  end

let expand_builtin_inline name args res =
  match name, args, res with
  (* Synchronization *)
  | "__builtin_membar", [], _ ->
    ()
  (* Byte swaps *)
  | "__builtin_bswap16", [BA(DREG a1)], BR(DREG res) ->
    if Configuration.model <> "tc161" then begin
      (* Shuffle bytes using the shuffle instruction:
         A = byte_select(a1, 1);
         B = byte_select(a1, 0);
         C = byte_select(a1, 2);
         D = byte_select(a1, 3);
         res[7:0]   = A;
         res[15:8]  = B;
         res[23:16] = C;
         res[31:24] = D; *)
      emit (Pshuffle (res, a1, _255))
    end else begin
      emit (Pextru (D0, a1, _8, _8));
      emit (Pinsert (res, D0, a1, _8,_8))
    end
  | ("__builtin_bswap"| "__builtin_bswap32"), [BA(DREG a1)], BR(DREG res) ->
    expand_bswap32 res a1
  | "__builtin_bswap64" , [BA_splitlong(BA(DREG ah), BA(DREG al))],
    BR_splitlong(BR(DREG rh), BR(DREG rl)) ->
    if Configuration.model <> "tc161" then begin
      (* Byte swap al and ah and write them into rh and rl *)
      expand_int64_arith (rl = al) rl (fun rl ->
          emit (Pshuffle (rl, ah, _27));
          emit (Pshuffle (rh, al, _27)));
    end else begin
      if rl = al then begin
        emit (Pmov (D0, al));
        emit (Pmov (rl, ah));
        emit (Pmov (rh, D0));
      end else begin
        emit (Pmov (rl, ah));
        emit (Pmov (rh, al));
      end;
      expand_bswap32 rl rl;
      expand_bswap32 rh rh
    end
  (* Count zeros *)
  | ("__builtin_clz" | "__builtin_clzl"), [BA(DREG a)], BR(DREG res) ->
    emit (Pclz (res, a))
  | "__builtin_clzll", [BA_splitlong(BA(DREG ah), BA(DREG al))], BR (DREG res) ->
    (* We compute the leading zeros of the lower half and either add 32 to it (high half is zero)
       or just use the result of the clz for the higher half *)
    emit (Pclz (D0, al));
    emit (Pcsub (D0, ah, D0, D0)); (* D0 = ah == 0 ? D0 else 0 *)
    emit (Pclz (res, ah));
    emit (Padd (res, res, D0))
  | ("__builtin_ctz" | "__builtin_ctzl"), [BA(DREG a)], BR(DREG res) ->
    if Configuration.model <> "tc161" then begin
      (* Shuffle bytes using the shuffle instruction:
         A = byte_select(a1, 3);
         B = byte_select(a1, 2);
         C = byte_select(a1, 1);
         D = byte_select(a1, 0);
         res[7:0]   = reverse(A);
         res[15:8]  = reverse(B);
         res[23:16] = reverse(C);
         res[31:24] = reverse(D); *)
      emit (Pshuffle (res, a, _283));
      (* Count the leading zeros of the reversed word *)
      emit (Pclz (res, res))
    end else begin
      (* We calculate tmp = (a - 1) & !a. Then the trailing zeros are all one and the
         rest is zero. Then we can use clz and return the result subtracted from 32 *)
      emit (Paddi (D0, a, _m1));
      emit (Pandn (D0, D0, a));
      emit (Pclz (D0, D0));
      emit (Prsub (res, D0, _32));
    end
  | "__builtin_ctzll",  [BA_splitlong(BA(DREG ah), BA(DREG al))], BR (DREG res) ->
    if Configuration.model <> "tc161" then begin
      (* Similar to the leading zeros version, just switch low and high and shuffle to get
         the leading zeros. *)
      emit (Pshuffle (D0, ah, _283));
      emit (Pclz (D0, D0));
      emit (Pcsub (D0, al, D0, D0));
      emit (Pshuffle (res, al, _283));
      emit (Pclz (res, res));
      emit (Padd (res, res, D0))
    end else begin
      let lbl_zero = new_label () in
      let lbl_end = new_label () in
      (* Lower part is non zero so we just calculate the trailing bits of the low half *)
      emit (Pjeq_sc4 (al, _0, lbl_zero));
      emit (Paddi (D0, al, _m1));
      emit (Pandn (D0, D0, al));
      emit (Pclz (D0, D0));
      emit (Prsub (res, D0, _32));
      emit (Pj_l lbl_end);
      (* Lower part is zero so we just add 32 to the trailing zeros of the high half *)
      emit (Plabel lbl_zero);
      emit (Paddi (D0, ah, _m1));
      emit (Pandn (D0, D0, ah));
      emit (Pclz (D0, D0));
      emit (Prsub (res, D0, _64));
      emit (Plabel lbl_end)
    end
  (* Float arithmetic *)
  | ("__builtin_fsqrt" | "__builtin_sqrt"), [BA (DREG a1)], BR (DREG res) ->
    raise (Error ("unsupported builtin " ^ name))
  (* 64-bit integer arithmetic *)
  | "__builtin_negl", [BA_splitlong(BA(DREG ah), BA(DREG al))],
                      BR_splitlong(BR(DREG rh), BR(DREG rl)) ->
      expand_int64_arith (rl = ah ) rl (fun rl ->
        emit (Prsub (rl, al, _0));
        emit (Prsub (rh, ah, _0));
        emit (Pcadd_sc9 (rh, rl, rh, _m1)))

  | "__builtin_addl", [BA_splitlong(BA(DREG ah), BA(DREG al));
                       BA_splitlong(BA(DREG bh), BA(DREG bl))],
                      BR_splitlong(BR(DREG rh), BR(DREG rl)) ->
     expand_int64_arith (rl = ah || rl = bh) rl
			(fun rl ->
			 emit (Paddx (rl,al, bl));
	        emit (Paddc (rh,ah, bh)))
  | "__builtin_subl", [BA_splitlong(BA(DREG ah), BA(DREG al));
                       BA_splitlong(BA(DREG bh), BA(DREG bl))],
                      BR_splitlong(BR(DREG rh), BR(DREG rl)) ->
     expand_int64_arith (rl = ah || rl = bh) rl
			(fun rl ->
			 emit (Psubx (rl,al, bl));
			 emit (Psubc (rh,ah, bh)))
  | "__builtin_mull", [BA(DREG a); BA(DREG b)],
    BR_splitlong(BR(DREG rh), BR(DREG rl)) ->
    assert (rh = D5 && rl = D4);
    emit (Pmulu (a,b))
  | "__builtin_va_start", [BA(DREG a)], _ ->
    expand_builtin_va_start a
  (* No operation *)
  | "__builtin_nop", [], _ ->
     emit Pnop

   (* Float arithmetic *)
  | "__builtin_fabs", [BA (DREG a1)], BR(DREG res) ->
      emit (Pinsert_uc4 (res, a1, _0, _31, _1));

   (* Optimization hint *)
  | "__builtin_unreachable", [], _ ->
     ()
  (* Catch-all *)
  | _ ->
     raise (Error ("unrecognized builtin " ^ name))

let va_stack_offset sg =
  let fixed = Conventions1.fixed_arguments sg in
  let args = sg.sig_args @ [AST.Targ AST.Tint] in
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
  | Pallocframe (sz, ofs) ->
    emit (Pmov_aa (A12, A10));
    expand_addimm_a A10 A10 (Integers.Int.neg sz);
    expand_storeind_ptr A12 A10 ofs;
    let sg = get_current_function_sig() in
    if sg.sig_cc.cc_vararg <> None then begin
      let ofs = va_stack_offset sg in
      let va_ofs = Z.add sz ofs in
      vararg_start_ofs := Some va_ofs
    end else
      vararg_start_ofs := None
  | Pfreeframe (sz, ofs) ->
    expand_addimm_a A10 A10 (Integers.Int.signed sz)
  | Pbuiltin (ef,args,res) ->
     begin match ef with
     | EF_builtin (name,sg) ->
        expand_builtin_inline (camlstring_of_coqstring name) args res
     | EF_vload chunk ->
        expand_builtin_vload chunk args res
     | EF_vstore chunk ->
        expand_builtin_vstore chunk args
     | EF_annot_val (kind,txt,targ) ->
        expand_annot_val kind txt targ args res
     | EF_memcpy(sz, al) ->
        expand_builtin_memcpy sz (Z.to_int al) args
     | EF_annot _ | EF_debug _ | EF_inline_asm _ ->
        emit instr
     | _ ->
        assert false
     end
  | Pabsf (rd, r) ->
    (* There is no absf in older versions of the ISA.
       We implement this by inserting 0 into r at posistion
       31 and length 1 *)
    emit (Pinsert_uc4 (rd,r,_0,_31,_1))
  | Pnegf (rd, r) ->
    (* There is no negf in older versions of the ISA.
       We implement this by inserting the negated sign
       bit into r at position 31 *)
    emit (Pinsn_t (rd,r,r,_31,_31))
  | Ploadsi (rd,c) ->
    expand_loadimm rd (Floats.Float32.to_bits c)
  | _ -> emit instr

let dreg_to_dwarf = function
  | D0  -> 0  | D1  -> 1  | D2  -> 2  | D3  -> 3
  | D4  -> 4  | D5  -> 5  | D6  -> 6  | D7  -> 7
  | D8  -> 8  | D9  -> 9  | D10 -> 10 | D11 -> 11
  | D12 -> 12 | D13 -> 13 | D14 -> 14 | D15 -> 15

let areg_to_dwarf = function
  | A0  -> 16 | A1  -> 17 | A2  -> 18 | A3  -> 19
  | A4  -> 20 | A5  -> 21 | A6  -> 22 | A7  -> 23
  | A8  -> 24 | A9  -> 25 | A10 -> 26 | A11 -> 27
  | A12 -> 28 | A13 -> 29 | A14 -> 30 | A15 -> 31

let preg_to_dwarf = function
  | AREG r -> areg_to_dwarf r
  | DREG r -> dreg_to_dwarf r
  | _ -> assert false

let expand_function id fn =
  try
    set_current_function fn;
    let sp = areg_to_dwarf A10 in
    expand id sp preg_to_dwarf expand_instruction fn.fn_code;
    Errors.OK (get_current_function ())
  with Error s ->
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
