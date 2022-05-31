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

open Asm
open Asmexpandaux
open AST
open Camlcoq

exception Error of string

let _0 = Integers.Int.zero
let _1 = Integers.Int.one
let _2 = coqint_of_camlint 2l
let _3 = coqint_of_camlint 3l
let _4 = coqint_of_camlint 4l
let _5 = coqint_of_camlint 5l
let _6 = coqint_of_camlint 6l
let _8 = coqint_of_camlint 8l
let _9 = coqint_of_camlint 9l
let _10 = coqint_of_camlint 10l
let _11 = coqint_of_camlint 11l
let _16 = coqint_of_camlint 16l
let _24 = coqint_of_camlint 24l
let _31 = coqint_of_camlint 31l
let _32 = coqint_of_camlint 32l
let _m1 = coqint_of_camlint (-1l)
let _m5 = coqint_of_camlint (-5l)
let _m6 = coqint_of_camlint (-6l)
let _m7 = coqint_of_camlint (-7l)
let _m8 = coqint_of_camlint (-8l)

let expand_addimm dst n =
  List.iter emit (Asmgen.addimm dst n [])

let expand_storeptr src base ofs =
  List.iter emit (Asmgen.storeptr src base ofs [])

let expand_loadptr base ofs dst =
  List.iter emit (Asmgen.loadptr base ofs dst [])

let expand_accessind instr base ofs =
  List.iter emit (Asmgen.accessind instr base ofs [])

let expand_loadimm dst n =
  List.iter emit (Asmgen.loadimm dst n [])

let expand_extsb reg =
  List.iter emit (Asmgen.extsb reg [])

let expand_extsh reg =
  List.iter emit (Asmgen.extsh reg [])

let expand_zero_ext reg size =
  emit (Pslil (reg, size));
  emit (Psril (reg,size))

let expand_move dst src =
  if dst <> src then
    emit (Pmov_rr (dst, src))

(* Handling of annotations *)

let expand_annot_val kind txt targ args res =
  emit (Pbuiltin (EF_annot(kind,txt,[targ]), args, BR_none));
  match args, res with
  | [BA GPR src], BR GPR dst ->
    expand_move dst src
  | _, _ ->
    raise (Error "ill-formed __builtin_annot_val")

 (* Memcopy *)

let offset_in_range ofs =
  Integers.Int.eq (Asmgen.high_s_20 ofs) _0

let memcpy_aux sz src osrc dst odst =
  match sz with
  | 1 ->
    emit (Pmovb_mr (Reg1, ADimm (src,osrc)));
    emit (Pmovb_rm (ADimm (dst, odst), Reg1))
  | 2 ->
    emit (Pmovh_mr (Reg1, ADimm (src,osrc)));
    emit (Pmovh_rm (ADimm (dst, odst), Reg1))
  | 3 ->
    let osrc' = Integers.Int.add osrc _2 in
    let odst' = Integers.Int.add odst _2 in
    emit (Pmovh_mr (Reg1, ADimm (src,osrc)));
    emit (Pmovh_rm (ADimm (dst, odst), Reg1));
    emit (Pmovb_mr (Reg1, ADimm (src, osrc')));
    emit (Pmovb_rm (ADimm (dst, odst'), Reg1))
  | sz when sz > 3 ->
    emit (Pmov_mr (Reg1, ADimm (src,osrc)));
    emit (Pmov_rm (ADimm (dst, odst), Reg1))
  | _ -> ()

let memcpy_small_arg sz arg tmp =
  match arg with
  | BA (GPR r) -> r, _0
  | BA_addrstack ofs ->
    let ofs' = Integers.Int.add ofs (Integers.Int.repr (Z.of_uint sz)) in
    if offset_in_range ofs && offset_in_range ofs' then
      (Reg0, ofs)
    else begin
      emit (Pmov_rr (tmp, Reg0));
      expand_addimm tmp ofs;
      tmp, _0
    end
  | _ -> assert false

(* For the small variant we unroll the loop 3 times.
   memcpy_aux does not generate code if the sz argument is
   smaller than 1. If the sz is between 1 and 4 the first
   call will generate the necessary code and the remaing two
   memcpy_aux calls will do nothing. If the sz is between
   5 and 8 the first memcpy_aux will generate a 32 bit load/store,
   the second call will generate load/store instruction for
   the rest and the last call will do nothing.
   Analogously for the case 9 to 12. *)
let expand_builtin_memcpy_small sz src dst =
  let tsrc = if dst <> BA (GPR Reg2) then Reg2 else Reg3 in
  let tdst = if src <> BA (GPR Reg3) then Reg3 else Reg2 in
  let rsrc, osrc = memcpy_small_arg sz src tsrc in
  let rdst, odst = memcpy_small_arg sz dst tdst in
  (* If the source and destination register are not equal the source and
     destination register after memcpy_small_arg should also be not equal
     except for the case when both destination and source are on the stack *)
  assert (src = dst || rdst <> rsrc || (rsrc = Reg0 && rdst = Reg0));
  memcpy_aux sz rsrc osrc rdst odst;
  memcpy_aux (sz - 4) rsrc (Integers.Int.add osrc _4) rdst (Integers.Int.add odst _4);
  memcpy_aux (sz - 8) rsrc (Integers.Int.add osrc _8) rdst (Integers.Int.add odst _8)

let memcpy_big_arg arg tmp =
  match arg with
  | BA (GPR r) ->
    expand_move tmp r
  | BA_addrstack ofs ->
    emit (Pmov_rr (tmp, Reg0));
    expand_addimm tmp ofs
  | _ ->
    assert false

let expand_builtin_memcpy_big sz src dst =
  let (rsrc, rdst) =
    if dst <> BA (GPR Reg2) then (Reg2, Reg3) else (Reg3, Reg2) in
  memcpy_big_arg src rsrc;
  memcpy_big_arg dst rdst;
  expand_loadimm Reg4 (Z.of_uint (sz / 4));
  let lbl = new_label () in
  emit (Plabel lbl);
  emit (Pmov_mr (Reg1, ADregpostincr rsrc));
  emit (Pmov_rm (ADregpostincr rdst, Reg1));
  expand_addimm Reg4 _m1;
  emit (Pbnz (Reg4,lbl));
  (* s and d lag behind by 4 bytes *)
  memcpy_aux (sz land 3) rsrc _0 rdst _0

let expand_builtin_memcpy sz args =
  let (dst, src) =
    match args with [d; s] -> (d, s) | _ -> assert false in
  if sz <= 12
  then expand_builtin_memcpy_small sz src dst
  else expand_builtin_memcpy_big sz src dst

let expand_builtin_vload_common chunk base ofs res =
  match chunk, res with
  | Mint8signed, BR (GPR dst) ->
    expand_accessind (fun a -> Pmovb_mr (dst,a)) base ofs;
    expand_extsb dst
  | Mint8unsigned, BR (GPR dst) ->
    expand_accessind (fun a -> Pmovb_mr (dst,a)) base ofs;
    expand_zero_ext dst _24
  | Mint16signed, BR (GPR dst) ->
    expand_accessind (fun a -> Pmovh_mr (dst,a)) base ofs;
    expand_extsh dst
  | Mint16unsigned, BR (GPR dst) ->
    expand_accessind (fun a -> Pmovh_mr (dst,a)) base ofs;
    expand_zero_ext dst _16
  | Mint32, BR (GPR dst) ->
    expand_accessind (fun a -> Pmov_mr (dst,a)) base ofs
  | Mint64, BR_splitlong (BR (GPR dst1), BR (GPR dst2)) ->
    let ofs_hi = Integers.Ptrofs.add ofs _4 in
    if base = dst2 then begin
      expand_accessind (fun a -> Pmov_mr (dst1,a)) base ofs_hi;
      expand_accessind (fun a -> Pmov_mr (dst2,a)) base ofs;
    end else begin
      expand_accessind (fun a -> Pmov_mr (dst2,a)) base ofs;
      expand_accessind (fun a -> Pmov_mr (dst1,a)) base ofs_hi;
    end
  | Mfloat32, BR (GPR dst) ->
    expand_accessind (fun a -> Pfmov_mr (dst,a)) base ofs
  | _ ->
    assert false

let expand_builtin_vload chunk args dst =
  match args with
  | [BA (GPR addr)] ->
    expand_builtin_vload_common chunk addr _0 dst
  | [BA_addrstack ofs] ->
    expand_builtin_vload_common chunk Reg0 ofs dst
  | [BA_addptr(BA(GPR addr), (BA_int ofs | BA_long ofs))] ->
    expand_builtin_vload_common chunk addr ofs dst
  | _ ->
    assert false

let vararg_start_ofs : Z.t option ref = ref None

let expand_builtin_va_start r =
  if not (is_current_function_variadic ()) then
    invalid_arg "Fatal error: va_start used in non-vararg function";
  match !vararg_start_ofs with
  | None -> assert false
  | Some ofs ->
    expand_loadimm Reg1 (Integers.Int.repr ofs);
    emit (Padd (Reg1,Reg0));
    emit (Pmov_rm (ADimm (r, _0), Reg1))

let expand_builtin_vstore_common chunk base ofs src =
  match chunk, src with
  | Mint8signed, BA (GPR src) ->
    expand_accessind (fun a -> Pmovb_rm (a, src)) base ofs
  | Mint8unsigned, BA (GPR src) ->
    expand_accessind (fun a -> Pmovb_rm (a, src)) base ofs
  | Mint16signed, BA (GPR src)
  | Mint16unsigned, BA (GPR src) ->
    expand_accessind (fun a -> Pmovh_rm (a, src)) base ofs
  | Mint32, BA (GPR src) ->
    expand_accessind (fun a -> Pmov_rm (a, src)) base ofs
  | Mint64, BA_splitlong (BA (GPR src1), BA (GPR src2)) ->
    let ofs_hi = Integers.Ptrofs.add ofs _4 in
    expand_accessind (fun a -> Pmov_rm (a, src2)) base ofs;
    expand_accessind (fun a -> Pmov_rm (a, src1)) base ofs_hi;
  | Mfloat32, BA (GPR src) ->
    expand_accessind (fun a -> Pfmov_rm (a, src)) base ofs
  | _ ->
    assert false

let expand_builtin_vstore chunk args =
  match args with
  | [BA (GPR addr); src] ->
    expand_builtin_vstore_common chunk addr _0 src
  | [BA_addrstack ofs; src] ->
    expand_builtin_vstore_common chunk Reg0 ofs src
  | [BA_addptr(BA(GPR addr), (BA_int ofs | BA_long ofs)); src] ->
    expand_builtin_vstore_common chunk addr ofs src
  | _ ->
    assert false

let expand_fmop args res op =
  match args, res with
  | [BA(GPR a1); BA(GPR a2); BA(GPR a3)], BR (GPR res) ->
    if res = a1 then
      op res a2 a3
    else if res = a2 then begin
      emit (Pmov_rr (Reg1, a2));
      emit (Pmov_rr (a2, a1));
      emit (Pmov_rr (a1, Reg1));
      op res a1 a3
    end else if res = a3 then begin
      emit (Pmov_rr (Reg1, a3));
      emit (Pmov_rr (a3, a1));
      emit (Pmov_rr (a1, Reg1));
      op res a2 a1
    end else begin
      emit (Pmov_rr (res, a1));
      op res a2 a3
    end
  | _ ->
    invalid_arg ("ill-formed fma builtin")

let expand_mop args res op =
  match args, res with
  | [BA(GPR a1); BA(GPR a2); BA(GPR a3)], BR (GPR res) ->
    if res = a1 then
      op res a2 a3
    else if res = a2 then begin
      emit (Pmov_rr (Reg1, a2));
      emit (Pmov_rr (a2, a1));
      emit (Pmov_rr (a1, Reg1));
      op res a1 a3
    end else if res = a3 then begin
      emit (Pmov_rr (Reg1, a3));
      emit (Pmov_rr (a3, a1));
      emit (Pmov_rr (a1, Reg1));
      op res a2 a1
    end else begin
      emit (Pmov_rr (res, a1));
      op res a2 a3
    end
  | _ ->
    invalid_arg ("ill-formed multiply and add/sub builtin")

let expand_ctz arg res =
  let lbl1 = new_label () in
  let lbl2 = new_label () in
  let lbl3 = new_label () in
  (* For all zero we return 32 *)
  emit (Pbz (arg,lbl2));
  emit (Pmov_ri (res, _0));
  emit (Plabel lbl1);
  emit (Pmov_rr (Reg1, arg));
  emit (Ptb (Reg1, res));
  emit (Pbnz (Reg1, lbl3));
  emit (Paddi (res,_1));
  emit (Pjmp_l lbl1);
  emit (Plabel lbl2);
  emit (Pmov_ri (res, _32));
  emit (Plabel lbl3)


(** Store the value in Reg1 in byte swapped order on the stack. *)
let expand_store_reg1_swapped () =
  emit (Pmovb_rm (ADimm (Reg0,_m5), Reg1));
  emit (Psril (Reg1, _8));
  emit (Pmovb_rm (ADimm (Reg0,_m6), Reg1));
  emit (Psril (Reg1, _8));
  emit (Pmovb_rm (ADimm (Reg0,_m7), Reg1));
  emit (Psril (Reg1, _8));
  emit (Pmovb_rm (ADimm (Reg0,_m8), Reg1))

(* 64 bit substraction *)
let expand_subl temp al ah bl bh =
  (* Compute carry bit *)
  emit (Pmov_rr (Reg1, al));
  emit (Pxor (Reg1, bl));
  emit (Pxori (Reg1, _m1));
  emit (Pmov_rr ((temp, al)));
  emit (Psub (temp, bl));
  emit (Pand (temp, Reg1));
  emit (Pmov_rr ((Reg1, al)));
  emit (Pxori (Reg1, _m1));
  emit (Pand (Reg1, bl));
  emit (Por (Reg1, temp));
  emit (Psril (Reg1, _31));
  (* Sub together the results with carry bit in TMP *)
  emit (Psub (al, bl));
  emit (Psub (ah, bh));
  emit (Psub (ah, Reg1))

(* Specialized version of subl using the fact that rl and rh are 0 *)
let expand_negl rl rh al ah =
  emit (Pmov_ri (rh, _0));
  emit (Pmov_rr (Reg1, al));
  emit (Pxori (Reg1, _m1));
  emit (Pmov_ri ((rl, _0)));
  emit (Psub (rl, al));
  emit (Pand (rl, Reg1));
  emit (Pmov_rr (Reg1, al));
  emit (Por (Reg1, rl));
  emit (Psril (Reg1, _31));
  emit (Pmov_ri (rl, _0));
  emit (Psub (rl, al));
  emit (Psub (rh, ah));
  emit (Psub (rh, Reg1))


let expand_builtin_inline name args res =
  match name, args, res with
  (* Synchronization *)
  | "__builtin_membar", [], _ ->
    ()
  (* Float arithmetic *)
  | ("__builtin_fsqrt" | "__builtin_sqrt"), [BA (GPR a1)], BR (GPR res) ->
    if (a1 <> res) then begin
      emit (Pmov_rr (res, a1));
      emit (Pfsqr (res));
    end else
      emit (Pfsqr res)
  | "__builtin_nop", [], _ ->
    (* This is what the ISA manual defines as nop instruction *)
    emit (Pmov_rr (Reg0, Reg0))
  (* 64-bit integer arithmetic *)
  | "__builtin_negl", [BA_splitlong(BA(GPR ah), BA(GPR al))],
    BR_splitlong(BR(GPR rh), BR(GPR rl)) ->
    assert (ah = Reg7 && al = Reg6 && rh = Reg5 && rl = Reg4);
    (* Compute negative value by subtracting from zero *)
    expand_negl rl rh al ah
  | "__builtin_addl",  [BA_splitlong(BA(GPR ah), BA(GPR al));
                        BA_splitlong(BA(GPR bh), BA(GPR bl))],
    BR_splitlong(BR(GPR rh), BR(GPR rl)) ->
    assert (ah = Reg5 && al = Reg4 && bh = Reg7 && bl = Reg6 && rh = Reg5 && rl = Reg4);
    (* Compute carry bit *)
    emit (Pmov_rr (Reg1, al));
    emit (Padd (Reg1, bl));
    emit (Pmov_rr (Reg8, al));
    emit (Por (Reg8, bl));
    emit (Pxori (Reg1, _m1));
    emit (Pand (Reg1, Reg8));
    emit (Pmov_rr (Reg8, al));
    emit (Pand (Reg8, bl));
    emit (Por (Reg1, Reg8));
    emit (Psril (Reg1, _31));
    (* Add together results with carry bit in TMP *)
    emit (Padd (ah, Reg1));
    emit (Padd (ah, bh));
    emit (Padd (al, bl))
  | "__builtin_subl",  [BA_splitlong(BA(GPR ah), BA(GPR al));
                        BA_splitlong(BA(GPR bh), BA(GPR bl))],
    BR_splitlong(BR(GPR rh), BR(GPR rl)) ->
    assert (ah = Reg5 && al = Reg4 && bh = Reg7 && bl = Reg6 && rh = Reg5 && rl = Reg4);
    expand_subl Reg8 al ah bl bh
  | "__builtin_mull", [BA(GPR a); BA(GPR b)],
    BR_splitlong(BR(GPR rh), BR(GPR rl)) ->
    assert (a = Reg5 && b = Reg4 && rh = Reg5 && rl = Reg4);
    emit (Pmul_u (Reg4,Reg5))
  | "__builtin_va_start", [BA(GPR a)], _ ->
    expand_builtin_va_start a
  | ("__builtin_bswap" | "__builtin_bswap32"), [BA (GPR a)], BR (GPR res) ->
    emit (Pmov_rr (Reg1, a));
    expand_store_reg1_swapped ();
    emit (Pmov_mr (res, ADimm (Reg0, _m8)))
  | "__builtin_bswap64", [BA_splitlong(BA(GPR ah), BA(GPR al))],
    BR_splitlong(BR(GPR rh), BR(GPR rl)) ->
    emit (Pmov_rr (Reg1, al));
    expand_store_reg1_swapped ();
    (* we must first move ah to the tmp register since ah can be the same
       register as rh *)
    emit (Pmov_rr (Reg1, ah));
    emit (Pmov_mr (rh, ADimm (Reg0, _m8)));
    expand_store_reg1_swapped ();
    emit (Pmov_mr (rl, ADimm (Reg0, _m8)))
  | ("__builtin_bswap16"), [BA (GPR a)], BR (GPR res) ->
    emit (Pmov_rr (Reg1, a));
    emit (Pmovb_rm (ADimm (Reg0,_m7), Reg1));
    emit (Psril (Reg1, _8));
    emit (Pmovb_rm (ADimm (Reg0,_m8), Reg1));
    emit (Pmovh_mr (res, ADimm (Reg0, _m8)));
    expand_zero_ext res _16
  | ("__builtin_ctz" | "__builtin_ctzl" ), [BA (GPR a)], BR (GPR res) ->
    assert (a == Reg3 && res == Reg4);
    expand_ctz a res
  | ("__builtin_clz" | "__builtin_clzl" ), [BA (GPR a)], BR (GPR res) ->
    assert (a == Reg3 && res == Reg4);
    emit (Prvbi (a,_31));
    expand_ctz a res
  | "__builtin_ctzll" , [BA_splitlong (BA (GPR ah), BA (GPR al))], BR (GPR res) ->
    assert (ah == Reg3 && al == Reg4 && res == Reg5);
    let lbl1 = new_label () in
    let lbl2 = new_label () in
    (* low word equal zero? *)
    emit (Pbnz (al, lbl1));
    (* low word is zero, count trailing zeros in high word and increment by 32 *)
    expand_ctz ah res;
    emit (Paddi (res, _32));
    emit (Pjmp_l lbl2);
    (* low word is non zero, count trailing zeros in low word *)
    emit (Plabel lbl1);
    expand_ctz al res;
    emit (Plabel lbl2)
  | "__builtin_clzll" , [BA_splitlong (BA (GPR ah), BA (GPR al))], BR (GPR res) ->
    assert (ah == Reg3 && al == Reg4 && res == Reg5);
    let lbl1 = new_label () in
    let lbl2 = new_label () in
    (* high word equal zero? *)
    emit (Pbnz (ah, lbl1));
    (* hight word is zero, count leading zeros in low word and increment by 32 *)
    emit (Prvbi (al,_31));
    expand_ctz al res;
    emit (Paddi (res, _32));
    emit (Pjmp_l lbl2);
    (* hight word is non-zero, count leading zeros in high word *)
    emit (Plabel lbl1);
    emit (Prvbi (ah,_31));
    expand_ctz ah res;
    emit (Plabel lbl2)
  | "__builtin_fmaddf",  _, _ ->
    expand_fmop args res (fun res a1 a2 -> emit (Pfmad (res, a1, a2)))
  | "__builtin_fmsubf",  _, _ ->
    expand_fmop args res (fun res a1 a2 -> emit (Pfmsu (res, a1, a2)))
  | "__builtin_madd", _, _ ->
    expand_mop args res (fun res a1 a2 -> emit (Pmad (res, a1, a2)));
  | "__builtin_msub", _, _ ->
    expand_mop args res (fun res a1 a2 -> emit (Pmsu (res, a1, a2)));
  (* Catch-all *)
  | _ ->
    raise (Error ("unrecognized builtin " ^ name))

let va_stack_offset sg =
  let (ofs, _) = List.fold_left (fun (ofs, r) ty ->
      match ty with
      | Tint | Tany32 | Tsingle ->
        if r < 8 then
          (ofs, r + 1)
        else
          (ofs + 1, r)
      | Tfloat | Tany64 ->
        (ofs + 2, r)
      | Tlong ->
        if r < 7 then
          (ofs, r + 2)
        else if r = 7 then
          (ofs + 1, r +1)
        else
          (ofs + 2, r)) (0, 0)  sg.sig_args in
  ofs * 4

let find_temp candidates args =
  match List.find_opt (fun c -> not (List.mem c args)) candidates with
  | Some t -> t
  | None -> assert false (* should always work *)

let find_temps2 candidates args =
  let temp1 = find_temp candidates args in
  let temp2 = find_temp candidates (temp1 :: args) in
  temp1, temp2

let expand_cmp_eq rd r1 r2 =
  let temp = find_temp [Reg1; Reg3; Reg4; Reg5; Reg6] [rd; r1; r2] in
  (* We assume that if rd is equal to one argument it should be
     r1, so we swap r1 and r2 in the other case *)
  let r1,r2 = if rd = r2 then r2,r1 else r1, r2 in
  (* We compute abs(r1 - r2) - 1 and test for the sign bit,
     since is is only set if r1 = r2. abs(x) is computed by
     (x ^ y) - y, were y is x >> 31 and x = r1 - r2 *)
  (* Calculate r1 - r2 in rd *)
  expand_move rd r1;
  emit (Psub (rd, r2));
  (* Calculate y = x >> 31 *)
  emit (Pmov_rr (temp, rd));
  emit (Psrai (temp, _31));
  (* Calculate (x ^ y) - y*)
  emit (Pxor (rd, temp));
  emit (Psub (rd, temp));
  (* Calcuate abs(x) - 1*)
  emit (Psubi (rd, _1));
  emit (Ptbi (rd,_31))

let expand_cmp_lt rd r1 r2 =
  let temp1, temp2 = find_temps2 [Reg1; Reg3; Reg4; Reg5; Reg6] [rd; r1; r2] in
  (* We compute (x - y) ^ ((x ^ y) & ((x -y) ^ x) and test for the sign bit *)
  (* Calculate temp1 = x ^ y *)
  emit (Pmov_rr ((temp1, r1)));
  emit (Pxor (temp1, r2));
  (* Calculate temp2 = (x - y) ^ x *)
  emit (Pmov_rr (temp2, r1));
  emit (Psub (temp2, r2));
  emit (Pxor (temp2, r1));
  (* Calculate temp1 = temp1 & temp2 *)
  emit (Pand (temp1, temp2));
  (* Calculate temp2 = x - y *)
  emit (Pmov_rr ((temp2, r1)));
  emit (Psub (temp2, r2));
  (* Calculate rd = temp2 ^ temp1 *)
  emit (Pxor (temp2, temp1));
  emit (Pmov_rr (rd, temp2));
  emit (Ptbi (rd, _31))

let expand_cmpu_lt rd r1 r2 =
  let temp1, temp2 = find_temps2 [Reg1; Reg3; Reg4; Reg5; Reg6] [rd; r1; r2] in
  (* We compute (!x & y) | ((!x | y) &(x - y)) and test for the sign bit *)
  (* Calculate temp1 = !x | y *)
  emit (Pmov_rr ((temp1, r1)));
  emit (Pxori (temp1, _m1));
  emit (Por (temp1, r2));
  (* Calculate temp2 = x - y *)
  emit (Pmov_rr ((temp2, r1)));
  emit (Psub (temp2, r2));
  (* Calculate temp1 = temp1 & temp2 *)
  emit (Pand (temp1, temp2));
  (* Calculate temp2 = !x & y *)
  emit (Pmov_rr ((temp2, r1)));
  emit (Pxori (temp2, _m1));
  emit (Pand (temp2, r2));
  (* Calculate rd = temp2 | temp1 *)
  emit (Por (temp2, temp1));
  emit (Pmov_rr (rd, temp2));
  emit (Ptbi (rd, _31))

(* We need to set the rounding mode to to_zero aka 1101 before the cast
   and then back after the cast. *)
let expand_float_cast tmp cast =
  emit (Pmov_fucr tmp);
  emit (Pmov_rr (Reg1, tmp));
  emit (Pori (Reg1, coqint_of_camlint 3328l));
  emit (Prb (Reg1, _9));
  emit (Pmov_tucr Reg1);
  cast ();
  emit (Pmov_tucr tmp)

let expand_instruction instr =
  match instr with
  | Pallocframe (sz, ofs) ->
    emit (Pmov_rr (Reg2,Reg0));
    expand_addimm Reg0 (Integers.Int.neg sz);
    expand_storeptr Reg2 Reg0 ofs;
    let sg = get_current_function_sig() in
    if sg.sig_cc.cc_vararg <> None then begin
      let ofs = va_stack_offset sg in
      let va_ofs = Z.add sz (Z.of_sint ofs) in
      vararg_start_ofs := Some va_ofs
    end else
      vararg_start_ofs := None
  | Pfreeframe (sz, ofs) ->
    let sz = (Integers.Int.signed sz) in
    if Integers.Int.eq (Asmgen.high_s_18 sz) Integers.Int.zero then
      emit (Paddi (Reg0,sz))
    else
      expand_loadptr Reg0 ofs Reg0
  | Pmovh_mr (rd, a) ->
    (* Load sets only the lower 16 bits of the target register *)
    emit (Pmovh_mr (rd, a));
    expand_zero_ext rd _16
  | Pmovsh_mr (rd, a) ->
    (* Load sets only the lower 16 bits of the target register *)
    emit (Pmovh_mr (rd, a));
    expand_extsh rd
  | Pmovb_mr (rd, a) ->
    (* Load sets only the lower 8 bits of the target register *)
    emit (Pmovb_mr (rd, a));
    expand_zero_ext rd _24
  | Pmovsb_mr (rd, a) ->
    (* Load sets only the lower 8 bits of the target register *)
    emit (Pmovb_mr (rd, a));
    expand_extsb rd
  | Pmov_rs (rd, c) ->
    expand_loadimm rd (Floats.Float32.to_bits c)
  | Pff2i rd ->
    let tmp = if rd = Reg3 then Reg4 else Reg3 in
    expand_float_cast tmp (fun () -> emit (Pff2i rd));
  | Pff2iu rd ->
    let tmp = if rd = Reg3 then Reg4 else Reg3 in
    expand_float_cast tmp (fun () -> emit (Pff2iu rd));
  | Pjmp (r, sg) ->
    emit (Psril (r, _2));
    emit (Pjmp (r, sg))
  | Pjmp_s (id, sg) ->
    emit (Ploadsymbol (Reg1, id, Integers.Ptrofs.zero));
    emit (Psril (Reg1, _2));
    emit (Pjmp (Reg1, sg))
  | Pjmp_p (r, sg) ->
    emit (Pmov_rr (Reg1, r));
    emit (Psril (Reg1, _2));
    emit (Pjmp_p (Reg1, sg))
  | Pjmp_sp (id, sg) ->
    emit (Ploadsymbol (Reg1, id, Integers.Ptrofs.zero));
    emit (Psril (Reg1, _2));
    emit (Pjmp_p (Reg1, sg))
  | Pcmp_eq (rd, r1, r2) ->
    expand_cmp_eq rd r1 r2
  | Pcmpu_eq (rd, r1, r2) ->
    expand_cmp_eq rd r1 r2
  | Pcmp_lt (rd, r1, r2) ->
    expand_cmp_lt rd r1 r2
  | Pcmpu_lt (rd, r1, r2) ->
    expand_cmpu_lt rd r1 r2
  | Pbuiltin (ef, args, res) ->
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
        expand_builtin_memcpy (Z.to_int sz) args
      | EF_annot _ | EF_debug _ | EF_inline_asm _ ->
        emit instr
      | _ ->
        assert false
    end
  | _ ->
    emit instr

let preg_to_dwarf = function
  | GPR Reg0 -> 0   | GPR Reg1 -> 1   | GPR Reg2 -> 2   | GPR Reg3 -> 3
  | GPR Reg4 -> 4   | GPR Reg5 -> 5   | GPR Reg6 -> 6   | GPR Reg7 -> 7
  | GPR Reg8 -> 8   | GPR Reg9 -> 9   | GPR Reg10 -> 10 | GPR Reg11 -> 11
  | GPR Reg12 -> 12 | GPR Reg13 -> 13 | GPR Reg14 -> 14 | GPR Reg15 -> 15
  | GPR Reg16 -> 16 | GPR Reg17 -> 17 | GPR Reg18 -> 18 | GPR Reg19 -> 19
  | GPR Reg20 -> 20 | GPR Reg21 -> 21 | GPR Reg22 -> 22 | GPR Reg23 -> 23
  | GPR Reg24 -> 24 | GPR Reg25 -> 25 | GPR Reg26 -> 26 | GPR Reg27 -> 27
  | GPR Reg28 -> 28 | GPR Reg29 -> 29 | GPR Reg30 -> 30 | GPR Reg31 -> 31
  | _ -> assert false

let expand_function id fn =
  try
    set_current_function fn;
    expand id (* sp= *) (preg_to_dwarf (GPR Reg0)) preg_to_dwarf expand_instruction fn.fn_code;
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
