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

(* Expanding built-ins and some pseudo-instructions by rewriting
   of the PPC assembly code. *)

open Camlcoq
open AST
open Asm
open Asmexpandaux

(* Useful constants and helper functions *)

(*- E_COMPCERT_CODE_emit_loadimm_001 *)
(*- #Justify_Derived "Utility function" *)
let emit_loadimm r n =
  List.iter emit (Asmgen.loadimm r n [])
(*- #End *)

(*- E_COMPCERT_CODE_emit_addimm_001 *)
(*- #Justify_Derived "Utility function" *)
let emit_addimm rd rs n =
  List.iter emit (Asmgen.addimm rd rs n [])
(*- #End *)

let emit_move_rr rd r =
  List.iter emit (Asmgen.move_rr rd r [])

let emit_aindexed mk r1 temp ofs =
  List.iter emit (Asmgen.aindexed mk r1 temp ofs [])

let emit_aindexed2 mk r1 r2 =
  List.iter emit (Asmgen.aindexed2 mk r1 r2 [])

let emit_aglobal mk1 mk2 temp symb ofs =
  List.iter emit (Asmgen.aglobal mk1 mk2 temp symb ofs [])

let emit_abased mk1 mk2 r1 temp symb ofs =
  List.iter emit (Asmgen.abased mk1 mk2 r1 temp symb ofs [])

let emit_ainstack mk1 mk2 ofs =
  List.iter emit (Asmgen.ainstack mk1 mk2 ofs [])

 (* Numbering of bits in the CR register *)
(*- E_COMPCERT_CODE_Asmexpand_num_crbit_001 *)
(*- #Justify_Derived "Utility function" *)
let num_crbit = function
  | CRbit_0 -> 0
  | CRbit_1 -> 1
  | CRbit_2 -> 2
  | CRbit_3 -> 3
  | CRbit_5 -> 5
  | CRbit_6 -> 6

(*- #End *)
(* Handling of annotations *)

(*- E_COMPCERT_CODE_Asmexpand_annot_intval_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_ANNOT_INT_001 *)
let expand_annot_val kind txt targ args res =
  emit (Pbuiltin(EF_annot(kind,txt, [targ]), args, BR_none));
  begin match args, res with
  | [BA(IR src)], BR(IR dst) ->
      if dst <> src then emit_move_rr dst src
  | _, _ ->
      raise (AsmexpandError "ill-formed __builtin_annot_intval")
  end
(*- #End *)


(* Handling of memcpy *)

(* On the PowerPC, unaligned accesses to 16- and 32-bit integers are
   fast, but unaligned accesses to 64-bit floats can be slow
   (not so much on G5, but clearly so on Power7).
   So, use 64-bit accesses only if alignment >= 4.
   Note that lfd and stfd cannot trap on ill-formed floats. *)

(*- E_COMPCERT_CODE_Asmexpand_offset_in_range_001 *)
(*- #Justify_Derived "Utility function" *)
let offset_in_range ofs =
  let ofs = Ptrofs.to_int ofs in
  I32.eq (Asmgen.high_s ofs) _0l
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_memcpy_small_arg_001 *)
(*- #Justify_Derived "Utility function" *)
let memcpy_small_arg sz arg tmp =
  match arg with
  | BA (IR r) ->
      (r, _0l)
  | BA_addrstack ofs ->
      if offset_in_range ofs
      && offset_in_range (Ptrofs.add ofs sz)
      then (Sreg GPR1, Ptrofs.to_int ofs)
      else begin emit_addimm tmp (Sreg GPR1) (Ptrofs.to_int ofs); (tmp, _0l) end
  | _ ->
      assert false
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_expand_builtin_memcpy_small_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_002 *)
let expand_builtin_memcpy_small sz al src dst =
  let tsrc = if dst <> BA (IR (Areg GPR11)) then Areg GPR11 else Areg GPR12 in
  let tdst = if src <> BA (IR (Areg GPR12)) then Areg GPR12 else Areg GPR11 in
  let (rsrc, osrc) = memcpy_small_arg sz src tsrc in
  let (rdst, odst) = memcpy_small_arg sz dst tdst in
  (* If the source and destination register are not equal the source and
     destination register after memcpy_small_arg should also be not equal
     except for the case when both destination and source are on the stack *)
  assert (src = dst || rdst <> rsrc || (rsrc = (Sreg GPR1) && rdst = (Sreg GPR1)));
  let rec copy osrc odst sz =
    if Ptrofs.cmpu Cge sz _4p then begin
      emit (Pe_lwz((Sreg GPR0), Cint osrc, rsrc));
      emit (Pe_stw((Sreg GPR0), Cint odst, rdst));
      copy (I32.add osrc _4l) (I32.add odst _4l) (Ptrofs.sub sz _4p)
    end else if Ptrofs.cmpu Cge sz _2p then begin
      emit (Pe_lhz((Sreg GPR0), Cint osrc, rsrc));
      emit (Pe_sth((Sreg GPR0), Cint odst, rdst));
      copy (I32.add osrc _2l) (I32.add odst _2l) (Ptrofs.sub sz _2p)
    end else if Ptrofs.cmpu Cge sz _1p then begin
      emit (Pe_lbz((Sreg GPR0), Cint osrc, rsrc));
      emit (Pe_stb((Sreg GPR0), Cint odst, rdst));
      copy (I32.add osrc _1l) (I32.add odst _1l) (Ptrofs.sub sz _1p)
    end in
  copy osrc odst sz
(*- #End *)


(*- E_COMPCERT_CODE_Asmexpand_memcpy_big_arg_001 *)
(*- #Justify_Derived "Utility function" *)
let memcpy_big_arg arg tmp =
  (* Set [tmp] to the value of [arg] minus 4 *)
  match arg with
  | BA (IR r) ->
      emit (Pe_add16i(tmp, r, Cint _m4l))
  | BA_addrstack ofs ->
      emit_addimm tmp (Sreg GPR1) (I32.add (Ptrofs.to_int ofs) _m4l)
  | _ ->
      assert false
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_expand_builtin_memcpy_big_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_003 *)
let expand_builtin_memcpy_big sz al src dst =
  assert (Ptrofs.cmpu Cge sz _4p);
  emit_loadimm (Sreg GPR0) (Ptrofs.(to_int (divu sz _4p)));
  emit (Pse_mtctr GPR0);
  let (s, d) =
    if dst <> BA (IR (Areg GPR11)) then ((Areg GPR11), (Areg GPR12)) else ((Areg GPR12), (Areg GPR11)) in
  memcpy_big_arg src s;
  memcpy_big_arg dst d;
  let lbl = new_label() in
  emit (Plabel lbl);
  emit (Pe_lwzu((Sreg GPR0), Cint _4l, s));
  emit (Pe_stwu((Sreg GPR0), Cint _4l, d));
  emit (Pbdnz lbl);
  (* s and d lag behind by 4 bytes *)
  let sz' = Ptrofs.modu sz _4p in
  if Ptrofs.eq sz' _1p then begin
    emit (Pe_lbz((Sreg GPR0), (Cint _4l), s));
    emit (Pe_stb((Sreg GPR0), (Cint _4l), d))
  end else if Ptrofs.eq sz' _2p then begin
    emit (Pe_lhz((Sreg GPR0), (Cint _4l), s));
    emit (Pe_sth((Sreg GPR0), (Cint _4l), d))
  end else if Ptrofs.eq sz' _3p then begin
    emit (Pe_lhz((Sreg GPR0), (Cint _4l), s));
    emit (Pe_sth((Sreg GPR0), (Cint _4l), d));
    emit (Pe_lbz((Sreg GPR0), (Cint _6l), s));
    emit (Pe_stb((Sreg GPR0), (Cint _6l), d))
  end
(*- #End *)


(*- E_COMPCERT_CODE_Asmexpand_memcpy_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_001 *)
let expand_builtin_memcpy sz al args =
  let (dst, src) =
    match args with [d; s] -> (d, s) | _ -> assert false in
  if Ptrofs.cmpu Cle sz (if !Clflags.option_Osize then _19p else _27p)
  then expand_builtin_memcpy_small sz al src dst
  else expand_builtin_memcpy_big sz al src dst
(*- #End *)


(* Handling of volatile reads and writes *)


(*- E_COMPCERT_CODE_Asmexpand_volatile_access_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_ACCESS_001 *)
let expand_volatile_access
       (mk1: constant -> ireg -> instruction list -> instruction list)
       (mk2: ireg -> ireg -> instruction list -> instruction list)
       addr temp =
  match addr with
  | BA(IR r) ->
      List.iter emit (mk1 (Cint _0l) r [])
  | BA_addrstack ofs ->
      emit_ainstack mk1 mk2 (Ptrofs.to_int ofs)
  | BA_addrglobal(id, ofs) ->
      emit_aglobal mk1 mk2 temp id ofs
  | BA_addptr(BA(IR r), BA_int n) ->
      emit_aindexed mk1 r temp n
  | BA_addptr(BA_addrglobal(id, ofs), BA(IR r)) ->
      emit_abased mk1 mk2 r temp id ofs
  | BA_addptr(BA(IR r1), BA(IR r2)) ->
      emit_aindexed2 mk2 r1 r2
  | _ ->
      assert false
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_offset_constant_001 *)
(*- #Justify_Derived "Utility function" *)
let offset_constant cst delta =
  match cst with
  | Cint n ->
      let n' = I32.add n delta in
      if offset_in_range (Ptrofs.of_int n') then Some (Cint n') else None
  | Csymbol_sda(id, ofs) ->
      Some (Csymbol_sda(id, Ptrofs.(add ofs (of_int delta))))
  | _ -> None
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_expand_load_int64_001 *)
(*- #Justify_Derived "Utility function" *)
let expand_load_int64 hi lo base ofs_hi ofs_lo k =
  if hi <> base then begin
    Pe_lwz(hi, ofs_hi, base) ::
    (Pe_lwz(lo, ofs_lo, base) :: k)
  end else begin
    Pe_lwz(lo, ofs_lo, base) ::
    (Pe_lwz(hi, ofs_hi, base) :: k)
  end
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_volatile_access_002 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_LOAD_001 *)
let expand_builtin_vload_1 chunk addr res =
  match chunk, res with
  | (Mbool | Mint8unsigned), BR(IR res) ->
      expand_volatile_access
        (fun c r k -> Pe_lbz(res, c, r) :: k)
        (fun r1 r2 k -> Plbzx(res, r1, r2) :: k)
        addr (Areg GPR11)
  | Mint8signed, BR(IR res) ->
      expand_volatile_access
        (fun c r k -> Pe_lbz(res, c, r) :: Pextsb(res, res) :: k)
        (fun r1 r2 k -> Plbzx(res, r1, r2) ::Pextsb(res, res) :: k)
        addr (Areg GPR11)
  | Mint16unsigned, BR(IR res) ->
      expand_volatile_access
        (fun c r k -> Pe_lhz(res, c, r) :: k)
        (fun r1 r2 k -> Plhzx(res, r1, r2) :: k)
        addr (Areg GPR11)
  | Mint16signed, BR(IR res) ->
      expand_volatile_access
        (fun c r k -> Pe_lha(res, c, r) :: k)
        (fun r1 r2 k ->  Plhax(res, r1, r2) :: k)
        addr (Areg GPR11)
  | (Mint32 | Many32), BR(IR res) ->
      expand_volatile_access
        (fun c r k -> Pe_lwz(res, c, r) :: k)
        (fun r1 r2 k -> Plwzx(res, r1, r2) :: k)
        addr (Areg GPR11)
  | Mfloat32, BR(IR res) ->
      expand_volatile_access
        (fun c r k -> Pfe_lwz(res, c, r) :: k)
        (fun r1 r2 k -> Pflwzx(res, r1, r2) :: k)
        addr (Areg GPR11)
  | Mint64, BR_splitlong(BR(IR hi), BR(IR lo)) ->
      expand_volatile_access
        (fun c r k ->
           match offset_constant c _4l with
           | Some c' -> expand_load_int64 hi lo r c c' k
           | None ->
               Pe_add16i ((Areg GPR11), r, c) ::
               (expand_load_int64 hi lo (Areg GPR11) (Cint _0l) (Cint _4l) k))
        (fun r1 r2 k ->
           Padd ((Areg GPR11), r1, r2) ::
           expand_load_int64 hi lo (Areg GPR11) (Cint _0l) (Cint _4l) k)
        addr (Areg GPR11)
  | _, _ ->
      assert false
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_volatile_access_003 *)
(*- #Justify_Derived "Utility function" *)
let expand_builtin_vload chunk args res =
  match args with
  | [addr] -> expand_builtin_vload_1 chunk addr res
  | _ -> assert false
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_temp_for_vstore_001 *)
(*- #Justify_Derived "Utility function" *)
let temp_for_vstore src =
  let rl = AST.params_of_builtin_arg src in
  if not (List.mem (IR (Areg GPR11)) rl) then (Areg GPR11)
  else if not (List.mem (IR (Areg GPR12)) rl) then (Areg GPR12)
  else (Areg GPR10)
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_expand_store_int64_001 *)
(*- #Justify_Derived "Utility function" *)
let expand_store_int64 hi lo base ofs_hi ofs_lo k =
  Pe_stw(hi, ofs_hi, base) :: (Pe_stw(lo, ofs_lo, base) :: k)
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_volatile_access_004 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_STORE_001 *)
let expand_builtin_vstore_1 chunk addr src =
  let temp = temp_for_vstore src in
  match chunk, src with
  | (Mbool | Mint8signed | Mint8unsigned), BA(IR src) ->
      expand_volatile_access
        (fun c r k -> Pe_stb(src, c, r) :: k)
        (fun r1 r2 k -> Pstbx(src, r1, r2) :: k)
        addr temp
  | (Mint16signed | Mint16unsigned), BA(IR src) ->
      expand_volatile_access
        (fun c r k -> Pe_sth(src, c, r) :: k)
        (fun r1 r2 k ->  Psthx(src, r1, r2) :: k)
        addr temp
  | (Mint32 | Many32), BA(IR src) ->
      expand_volatile_access
        (fun c r k -> Pe_stw(src, c, r) :: k)
        (fun r1 r2 k -> Pstwx(src, r1, r2) :: k)
        addr temp
  | Mfloat32, BA(IR src) ->
      expand_volatile_access
        (fun c r k -> Pfe_stw(src, c, r) :: k)
        (fun r1 r2 k -> Pfstwx(src, r1, r2) :: k)
        addr temp
  | Mint64, BA_splitlong(BA(IR hi), BA(IR lo)) ->
      expand_volatile_access
        (fun c r k ->
           match offset_constant c _4l with
           | Some c' -> expand_store_int64 hi lo r c c' k
           | None ->
               Pe_add16i(temp, r, c) ::
               expand_store_int64 hi lo temp (Cint _0l) (Cint _4l) k)
        (fun r1 r2 k ->
           Padd(temp, r1, r2) ::
           expand_store_int64 hi lo temp (Cint _0l) (Cint _4l) k)
        addr temp
  | _, _ ->
      assert false
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_volatile_access_005 *)
(*- #Justify_Derived "Utility function" *)
let expand_builtin_vstore chunk args =
  match args with
  | [addr; src] -> expand_builtin_vstore_1 chunk addr src
  | _ -> assert false
(*- #End *)

(* Handling of varargs *)

(*- E_COMPCERT_CODE_Asmexpand_stackframe_state_001 *)
(*- #Justify_Derived "Variable for local state" *)
let linkregister_offset = ref  _0l
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_stackframe_state_002 *)
(*- #Justify_Derived "Variable for local state" *)
let retaddr_offset = ref _0l
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_stackframe_state_003 *)
(*- #Justify_Derived "Variable for local state" *)
let current_function_stacksize = ref _0l
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_align_001 *)
(*- #Justify_Derived "Utility function" *)
let align n a = Int32.(logand (sub (add n a) 1l) (neg a))
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_next_arg_locations_001 *)
(*- #Justify_Derived "Utility function" *)
let rec next_arg_locations ir ofs = function
  | [] ->
      (ir, ofs)
  | (Tint | Tany32 | Tsingle) :: l ->
      if ir < 8l
      then next_arg_locations (Int32.add ir 1l) ofs l
      else next_arg_locations ir (Z.add ofs _4) l
  | (Tfloat | Tany64) :: l ->
      next_arg_locations ir (Z.add (Coqlib.align ofs _8) _8) l
  | Tlong :: l ->
      let ir = align ir 2l in
      if ir < 8l
      then next_arg_locations (Int32.add ir 2l) ofs l
      else next_arg_locations ir (Z.add (Coqlib.align ofs _8) _8) l
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_builtin_va_start_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_VA_START_001 *)
let expand_builtin_va_start r =
  if not (is_current_function_variadic ()) then
    invalid_arg "Fatal error: va_start used in non-vararg function";
  let (ir, ofs) =
    next_arg_locations 0l _0 (get_current_function_args ()) in
  emit_loadimm (Sreg GPR0) (coqint_of_camlint ir);
  emit (Pe_stb((Sreg GPR0), Cint _0l, r));
  emit_loadimm (Sreg GPR0)  _0l;
  emit (Pe_stb((Sreg GPR0), Cint _1l, r));
  emit_addimm (Sreg GPR0) (Sreg GPR1) (I32.(add (add !current_function_stacksize _8l)
                                      (repr ofs)));
  emit (Pe_stw((Sreg GPR0), Cint _4l, r));
  emit_addimm (Sreg GPR0) (Sreg GPR1) (I32.(sub !current_function_stacksize _96l));
  emit (Pe_stw((Sreg GPR0), Cint _8l, r))
(*- #End *)


(* Auxiliary for 64-bit integer arithmetic built-ins.  They expand to
   two instructions, one computing the low 32 bits of the result,
   followed by another computing the high 32 bits.  In cases where
   the first instruction would overwrite arguments to the second
   instruction, we must go through GPR0 to hold the low 32 bits of the result.
*)

(*- E_COMPCERT_CODE_Asmexpand_int64_arith_001 *)
(*- #Justify_Derived "Utility function" *)
let expand_int64_arith conflict rl fn =
  if conflict then (fn (Sreg GPR0); emit_move_rr rl (Sreg GPR0)) else fn rl
(*- #End *)

let expand_cmpi_small a1 n =
  match a1 with
  | Sreg a1 -> emit (Pse_cmpi (a1,n))
  | _ -> emit (Pe_cmp16i (a1, Cint n))

(* Convert integer constant into GPR with corresponding number *)
(*- E_COMPCERT_CODE_Asmexpand_int_to_int_reg_001 *)
(*- #Justify_Derived "Utility function" *)
let int_to_int_reg = function
   | 0l -> Some (Sreg GPR0)  | 1l -> Some (Sreg GPR1)  | 2l -> Some (Sreg GPR2)  | 3l -> Some (Sreg GPR3)
   | 4l -> Some (Sreg GPR4)  | 5l -> Some (Sreg GPR5)  | 6l -> Some (Sreg GPR6)  | 7l -> Some (Sreg GPR7)
   | 8l -> Some (Areg GPR8)  | 9l -> Some (Areg GPR9)  | 10l -> Some (Areg GPR10) | 11l -> Some (Areg GPR11)
   | 12l -> Some (Areg GPR12) | 13l -> Some (Areg GPR13) | 14l -> Some (Areg GPR14) | 15l -> Some (Areg GPR15)
   | 16l -> Some (Areg GPR16) | 17l -> Some (Areg GPR17) | 18l -> Some (Areg GPR18) | 19l -> Some (Areg GPR19)
   | 20l -> Some (Areg GPR20) | 21l -> Some (Areg GPR21) | 22l -> Some (Areg GPR22) | 23l -> Some (Areg GPR23)
   | 24l -> Some (Sreg GPR24) | 25l -> Some (Sreg GPR25) | 26l -> Some (Sreg GPR26) | 27l -> Some (Sreg GPR27)
   | 28l -> Some (Sreg GPR28) | 29l -> Some (Sreg GPR29) | 30l -> Some (Sreg GPR30) | 31l -> Some (Sreg GPR31)
   | _ -> None
(*- #End *)

(* Handling of compiler-inlined builtins *)

let expand_builtin_inline name args res =
  (* Can use as temporaries: GPR0, FPR13 *)
  match name, args, res with

  (* Integer arithmetic *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_005 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_CLZ_001 *)
  | ("__builtin_clz" | "__builtin_clzl"), [BA(IR a1)], BR(IR res) ->
      emit (Pcntlzw(res, a1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_006 *)
  | "__builtin_clzll", [BA_splitlong(BA(IR ah), BA(IR al))], BR(IR res) ->
      let lbl = new_label () in
      emit (Pcntlzw((Sreg GPR0), al));
      emit (Pcntlzw(res, ah));
      (* less than 32 bits zero? *)
      emit (Pe_cmp16i (res,Cint _32l));
      emit (Pbf (CRbit_2, lbl));
      (* high bits all zero, count bits in low word and increment by 32 *)
      emit (Padd(res, res, (Sreg GPR0)));
      emit (Plabel lbl)
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_007 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_CTZ_001 *)
  | ("__builtin_ctz" | "__builtin_ctzl"), [BA(IR a1)], BR(IR res) ->
      emit (Pe_add16i((Sreg GPR0), a1, Cint _m1l));   (* tmp := x-1 *)
      emit (Pandc(res, (Sreg GPR0), a1));        (* res := tmp & ~(x) *)
      emit (Pcntlzw(res, res));           (* res := #leading zeros *)
      emit (Pe_subfic(res, res, _32l))  (* res := 32 - #leading zeros *)
  (*- #End *)
  | "__builtin_ctzll", [BA_splitlong(BA(IR ah), BA(IR al))], BR(IR res) ->
      let lbl1 = new_label () in
      let lbl2 = new_label () in
      (* low word equal to zero? *)
      expand_cmpi_small al _0l;
      emit (Pbf (CRbit_2, lbl1));
      (* low word is zero, count trailing zeros in high word and increment by 32 *)
      emit (Pe_add16i((Sreg GPR0), ah, Cint _m1l));
      emit (Pandc(res, (Sreg GPR0), ah));
      emit (Pcntlzw(res, res));
      emit (Pe_subfic(res, res, _64l));
      emit (Pe_b lbl2);
      (* count trailing zeros in low word *)
      emit (Plabel lbl1);
      emit (Pe_add16i((Sreg GPR0), al, Cint _m1l));
      emit (Pandc(res, (Sreg GPR0), al));
      emit (Pcntlzw(res, res));
      emit (Pe_subfic(res, res, _32l));
      emit (Plabel lbl2)
  (*- #End *)


  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_010 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_BSWAP_001 *)
  | ("__builtin_bswap" | "__builtin_bswap32"), [BA(IR a1)], BR(IR res) ->
      emit (Pe_stwu(a1, Cint _m8l, Sreg GPR1));
      emit (Pcfi_adjust _8p);
      emit (Plwbrx(res, (Sreg GPR0), Sreg GPR1));
      emit (Pse_addi(GPR1, _8l));
      emit (Pcfi_adjust _m8p)
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_011 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_BSWAP16_001 *)
  | "__builtin_bswap16", [BA(IR a1)], BR(IR res) ->
      emit (Pe_rlwinm((Sreg GPR0), a1, _8l, _65280l));
      emit (Pe_rlwinm(res, a1, _24l, _255l));
      begin match res with
      | Sreg s -> emit (Pse_or (s,GPR0))
      | _ -> emit (Por(res, (Sreg GPR0), res))
      end
  (*- #End *)


  | "__builtin_fabs", [BA (IR a1)], BR(IR res) ->
      emit (Pefsabs (res, a1));

  (* Memory accesses *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_022 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_READ16_REVERSED_001 *)
  | "__builtin_read16_reversed", [BA(IR a1)], BR(IR res) ->
      emit (Plhbrx(res, (Sreg GPR0), a1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_023 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_READ32_REVERSED_001 *)
  | "__builtin_read32_reversed", [BA(IR a1)], BR(IR res) ->
      emit (Plwbrx(res, (Sreg GPR0), a1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_025 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_WRITE16_REVERSED_001 *)
  | "__builtin_write16_reversed", [BA(IR a1); BA(IR a2)], _ ->
      emit (Psthbrx(a2, (Sreg GPR0), a1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_026 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_WRITE32_REVERSED_001 *)
  | "__builtin_write32_reversed", [BA(IR a1); BA(IR a2)], _ ->
      emit (Pstwbrx(a2, (Sreg GPR0), a1))
  (*- #End *)

  (* Synchronization *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_028 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMBAR_001 *)
  | "__builtin_membar", [], _ ->
      ()
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_030 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_SYNC_001 *)
  | "__builtin_sync", [], _ ->
      emit (Psync)
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_031 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_ISYNC_001 *)
  | "__builtin_isync", [], _ ->
      emit (Pse_isync)
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_035 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_VA_START_001 *)
  (* Vararg stuff *)
  | "__builtin_va_start", [BA(IR a)], _ ->
      expand_builtin_va_start a
  (*- #End *)

  (* Cache control *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_036 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_DCBF_001 *)
  | "__builtin_dcbf", [BA(IR a1)],_ ->
      emit (Pdcbf ((Sreg GPR0),a1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_037 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_DCBI_001 *)
  | "__builtin_dcbi", [BA(IR a1)],_ ->
      emit (Pdcbi ((Sreg GPR0),a1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_038 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_ICBI_001 *)
  | "__builtin_icbi", [BA(IR a1)],_ ->
      emit (Picbi((Sreg GPR0),a1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_039 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_DCBTLS_001 *)
  | "__builtin_dcbtls", [BA (IR a1); BA_int loc],_ ->
      if not ((I32.eq loc _0l) || (I32.eq loc _2l)) then
        (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_CACHE_BLOCK_TLS_001 *)
        raise (AsmexpandError "the second argument of __builtin_dcbtls must be 0 or 2");
      emit (Pdcbtls (loc,(Sreg GPR0),a1))
  | "__builtin_dcbtls",_,_ ->
      (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_CACHE_BLOCK_TLS_002 *)
      raise (AsmexpandError "the second argument of __builtin_dcbtls must be a constant")
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_040 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_ICBTLS_001 *)
  | "__builtin_icbtls", [BA (IR a1); BA_int loc],_ ->
    if not ((I32.eq loc _0l) || (I32.eq loc _2l)) then
        (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_CACHE_BLOCK_TLS_001 *)
        raise (AsmexpandError "the second argument of __builtin_icbtls must be 0 or 2");
      emit (Picbtls (loc,(Sreg GPR0),a1))
  | "__builtin_icbtls",_,_ ->
      (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_CACHE_BLOCK_TLS_002 *)
      raise (AsmexpandError "the second argument of __builtin_icbtls must be a constant")
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_041 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_PREFETCH_001 *)
  | "__builtin_prefetch" , [BA (IR a1) ;BA_int rw; BA_int loc],_ ->
      if not (I32.ltu loc _4l) then
        (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_PREFETCH_001 *)
        raise (AsmexpandError "the last argument of __builtin_prefetch must be 0, 1 or 2");
      if I32.eq rw _0l then begin
        emit (Pdcbt (loc,(Sreg GPR0),a1));
      end else if I32.eq rw _1l then begin
        emit (Pdcbtst (loc,(Sreg GPR0),a1));
      end else
        (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_PREFETCH_002 *)
        raise (AsmexpandError "the second argument of __builtin_prefetch must be 0 or 1")
  | "__builtin_prefetch" ,_,_ ->
      (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_PREFETCH_003 *)
      raise (AsmexpandError "the second and third argument of __builtin_prefetch must be a constant")
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_042 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_DCBZ_001 *)
  | "__builtin_dcbz",[BA (IR a1)],_ ->
      emit (Pdcbz ((Sreg GPR0),a1))
  (*- #End *)

  (* Special registers *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_043 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_GET_SPR_001 *)
  | "__builtin_get_spr", [BA_int n], BR(IR res) ->
      emit (Pmfspr(res, n))
  | "__builtin_get_spr", _, _ ->
      (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_GET_SPR_001 *)
      raise (AsmexpandError "the argument of __builtin_get_spr must be a constant")
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_044 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_SET_SPR_001 *)
  | "__builtin_set_spr", [BA_int n; BA(IR a1)], _ ->
      emit (Pmtspr(n, a1))
  | "__builtin_set_spr", _, _ ->
      (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_SET_SPR_001 *)
      raise (AsmexpandError "the first argument of __builtin_set_spr must be a constant")
  (*- #End *)

  (* Move registers *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_047 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_MR_001 *)
  | "__builtin_mr", [BA_int dst; BA_int src], _ ->
      (match int_to_int_reg (camlint_of_coqint dst), int_to_int_reg (camlint_of_coqint src) with
       | Some dst, Some src -> emit_move_rr dst src
       (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_MR_001 *)
       | _, _ -> raise (AsmexpandError "the arguments of __builtin_mr must be in the range of 0..31"))
  | "__builtin_mr", _, _ ->
      (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_MR_002 *)
      raise (AsmexpandError "the arguments of __builtin_mr must be constants")
  (*- #End *)

  (* Frame and return address *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_048 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_CALL_FRAME_001 *)
  | "__builtin_call_frame", _,BR (IR res) ->
      let sz = !current_function_stacksize
      and ofs = !linkregister_offset in
      if I32.ltu sz _32768l  then
        emit (Pe_add16i(res, Sreg GPR1, Cint sz))
      else
        emit (Pe_lwz(res, Cint ofs, Sreg GPR1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_049 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_RETURN_ADDRESS_001 *)
  | "__builtin_return_address",_,BR (IR res) ->
      emit (Pe_lwz (res, Cint !retaddr_offset,Sreg GPR1))
  (*- #End *)

  (* no operation *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_051 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_NOP_001 *)
  | "__builtin_nop", [], _ ->
      emit (Pe_or2i ((Sreg GPR0),  Cint _0l))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_057 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_UNREACHABLE_001 *)
  (* Optimization hint *)
  | "__builtin_unreachable", [], _ ->
     ()
  (*- #End *)

  (* Catch-all *)
  | _ ->
      raise (AsmexpandError ("unrecognized builtin " ^ name))


(* Calls to variadic functions: condition bit 6 must be set
   if at least one argument is a float; clear otherwise.
   For compatibility with other compilers, do the same if the called
   function is unprototyped. *)

(*- E_COMPCERT_CODE_Asmexpand_set_cr6_001 *)
(*- #Justify_Derived "Utility function" *)
let set_cr6 sg =
  if (sg.sig_cc.cc_vararg <> None) || sg.sig_cc.cc_unproto then begin
    if List.exists (function Xfloat | Xsingle -> true | _ -> false) sg.sig_args
    then emit (Pe_creqv(CRbit_6, CRbit_6, CRbit_6))
    else emit (Pe_crxor(CRbit_6, CRbit_6, CRbit_6))
  end
(*- #End *)

(* Number of statements in a piece of inline assembly code.
   This gives an upper bound on the number of machine instructions.
   (Some statements can be labels or directives.) *)

(*- E_COMPCERT_CODE_Asmexpand_re_asm_comment_001 *)
(*- #Justify_Derived "Utility constant" *)
let re_asm_comment =
  if Configuration.system = "diab"
  then Str.regexp "[#;].*$"    (* comments start with # or ;  *)
  else Str.regexp "#.*$"       (* comments start with # *)
(*- #End *)
(*- E_COMPCERT_CODE_Asmexpand_re_blank_line_001 *)
(*- #Justify_Derived "Utility constant" *)
let re_blank_line = Str.regexp "^[ \t]*\n"
(*- #End *)
(*- E_COMPCERT_CODE_Asmexpand_re_asm_stmt_separator_001 *)
(*- #Justify_Derived "Utility constant" *)
let re_asm_stmt_separator = Str.regexp "[\n;]"    (* newline or ; *)
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_num_statements_inline_asm_001 *)
(*- #Justify_Derived "Utility function" *)
let num_statements_inline_asm txt =
  txt |> Str.global_replace re_asm_comment ""
      |> Str.global_replace re_blank_line ""
      |> Str.split re_asm_stmt_separator
      |> List.length
(*- #End *)

(* Branch relaxation *)

module BInfo: BRANCH_INFORMATION = struct

  (*- E_COMPCERT_CODE_Asmexpand_builtin_size_001 *)
  (*- #Justify_Derived "Utility function" *)
  let builtin_size = function
    | EF_annot _ -> 0
    | EF_debug _ -> 0
    | EF_inline_asm(txt, _, _) -> 4 * num_statements_inline_asm txt
    | _ -> assert false
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instr_size_001 *)
  (*- #Justify_Derived "Utility function" *)
  let instr_size = function
    | Pbtbl(r, tbl) -> 20
    | Plabel lbl -> 0
    | Pbuiltin(ef, _, _) -> builtin_size ef
    | Pcfi_adjust _ | Pcfi_rel_offset _ -> 0
    | _ -> 4
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_need_relaxation_001 *)
  (*- #Justify_Derived "Utility function" *)
  let need_relaxation ~map pc instr =
    match instr with
    | Pbf(_, lbl) | Pbt(_, lbl) ->
        let displ = map lbl - pc in
        displ < -0x8000 || displ >= 0x8000
    | _ ->
        false
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_relax_instruction_001 *)
  (*- #Justify_Derived "Utility function" *)
  let relax_instruction instr =
    match instr with
    | Pbf(bit, lbl) ->
        let lbl' = new_label() in
        [Pbt(bit, lbl'); Pe_b lbl; Plabel lbl']
    | Pbt(bit, lbl) ->
        let lbl' = new_label() in
        [Pbf(bit, lbl'); Pe_b lbl; Plabel lbl']
    | _ ->
        assert false
  (*- #End *)

end

(*- E_COMPCERT_CODE_Asmexpand_BRelax_001 *)
(*- #Justify_Derived "Type definition" *)
module BRelax = Branch_relaxation (BInfo)
(*- #End *)

(* Expand instructions *)

let expand_instruction instr =
  match instr with

  (*- E_COMPCERT_CODE_Asmexpand_instruction_001 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_PALLOCFRAME_001 *)
  | Pallocframe(sz, ofs,retofs) ->
      let variadic = is_current_function_variadic () in
      let sz = if variadic then Z.add sz _96 else sz in
       (* Check stack size + 8 for additional stack used by built-ins *)
      check_stack_size (Z.add sz _8);
      let sz = I32.repr sz in
      assert (ofs = _0p);
      let adj = I32.neg sz in
      if I32.cmp Cge adj _m128l && I32.cmp Clt adj _0l then
        emit (Pe_stwu(Sreg GPR1, Cint adj, Sreg GPR1))
      else begin
        emit_loadimm (Sreg GPR0) adj;
        emit (Pstwux(Sreg GPR1, Sreg GPR1, (Sreg GPR0)))
      end;
      emit (Pcfi_adjust (Ptrofs.of_int sz));
      if variadic then begin
        emit (Pse_mflr GPR0);
        emit (Pe_bl(intern_string "__compcert_va_saveregs",
                  {sig_args = []; sig_res = Xvoid; sig_cc = cc_default}));
        emit (Pse_mtlr GPR0)
      end;
      current_function_stacksize := sz;
      linkregister_offset := Ptrofs.to_int ofs;
      retaddr_offset := Ptrofs.to_int retofs
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_002 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_PBRANCH_001 *)
  | Pse_bctr sg | Pse_bctrl sg | Pe_bl(_, sg) | Pe_bs(_, sg) ->
      set_cr6 sg;
      emit instr
  (*- #End *)

  | Plfis (rd,c) ->
    emit_loadimm rd (Floats.Float32.to_bits c)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_004 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_PFREEFRAME_001 *)
  | Pfreeframe(sz, ofs) ->
      let variadic = is_current_function_variadic () in
      let sz = I32.repr sz in
      let sz = if variadic then I32.add sz _96l else sz in
      if I32.ltu sz _32768l then
        emit (Pe_add16i(Sreg GPR1, Sreg GPR1, Cint sz))
      else
        emit (Pe_lwz(Sreg GPR1, Cint (Ptrofs.to_int ofs), Sreg GPR1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_023 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_PISEL_001 *)
  | Pisel(rd, r1, r2, bit) ->
      emit (Pisel (rd, r1, r2, bit))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_016 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_PMFCRBIT_001 *)
  | Pmfcrbit(r1, bit) ->
      emit (Pmfcr r1);
      emit (Pe_rlwinm(r1, r1, coqint_of_camlint (Int32.of_int (1 + num_crbit bit)), _1l))
  (*- #End *)

  | Pbuiltin(ef, args, res) ->
      begin match ef with
      (*- E_COMPCERT_CODE_Asmexpand_instruction_017 *)
      (*- #Justify_Derived "Call to expansion function for builtins" *)
      | EF_builtin(name, sg) ->
          expand_builtin_inline name args res
      (*- #End *)

      (*- E_COMPCERT_CODE_Asmexpand_instruction_018 *)
      (*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_LOAD_001 *)
      | EF_vload chunk ->
          expand_builtin_vload chunk args res
      (*- #End *)

      (*- E_COMPCERT_CODE_Asmexpand_instruction_019 *)
      (*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_STORE_001 *)
      | EF_vstore chunk ->
          expand_builtin_vstore chunk args
      (*- #End *)

      (*- E_COMPCERT_CODE_Asmexpand_instruction_020 *)
      (*- #Link_to E_COMPCERT_TR_Function_EXPAND_ANNOT_INT_001 *)
      | EF_memcpy(sz, al) ->
          expand_builtin_memcpy sz al args
      (*- #End *)

      (*- E_COMPCERT_CODE_Asmexpand_instruction_021 *)
      (*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_001 *)
      | EF_annot_val(kind,txt, targ) ->
          expand_annot_val kind txt targ args res
      (*- #End *)

      (*- E_COMPCERT_CODE_Asmexpand_instruction_022 *)
      (*- #Justify_Derived "Default case" *)
      | EF_annot _ | EF_debug _ | EF_inline_asm _ ->
          emit instr
      (*- #End *)

      | _ ->
          assert false
      end
  | _ ->
      emit instr


(* Translate to the integer identifier of the register as
   the EABI specifies *)

let sreg_to_dwarf =  function
   | GPR0 -> 0  | GPR1 -> 1  | GPR2 -> 2  | GPR3 -> 3
   | GPR4 -> 4  | GPR5 -> 5  | GPR6 -> 6  | GPR7 -> 7
   | GPR24 -> 24 | GPR25 -> 25 | GPR26 -> 26 | GPR27 -> 27
   | GPR28 -> 28 | GPR29 -> 29 | GPR30 -> 30 | GPR31 -> 31

let areg_to_dwarf = function
   | GPR8 -> 8  | GPR9 -> 9  | GPR10 -> 10 | GPR11 -> 11
   | GPR12 -> 12 | GPR13 -> 13 | GPR14 -> 14 | GPR15 -> 15
   | GPR16 -> 16 | GPR17 -> 17 | GPR18 -> 18 | GPR19 -> 19
   | GPR20 -> 20 | GPR21 -> 21 | GPR22 -> 22 | GPR23 -> 23

(*- E_COMPCERT_CODE_Asmexpand_int_reg_to_dwarf_001 *)
(*- #Justify_Derived "Utility function" *)
let int_reg_to_dwarf = function
   | Sreg r -> sreg_to_dwarf r
   | Areg r -> areg_to_dwarf r
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_preg_to_dwarf_001 *)
(*- #Justify_Derived "Utility function" *)
let preg_to_dwarf = function
   | IR r -> int_reg_to_dwarf r, None
   | _ -> assert false
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_expand_function_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let expand_function id fn =
  try
    set_current_function fn;
    expand id 1 preg_to_dwarf expand_instruction fn.fn_code;
    let fn' = BRelax.relaxation (get_current_function ()) in
    Errors.OK fn'
  with AsmexpandError s ->
    Errors.Error (Errors.msg s)
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_expand_fundef_001 *)
(*- #Justify_Derived "Functional decomposition" *)
let expand_fundef id = function
  | Internal f ->
      begin match expand_function id f with
      | Errors.OK tf -> Errors.OK (Internal tf)
      | Errors.Error msg -> Errors.Error msg
      end
  | External ef ->
      Errors.OK (External ef)
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_expand_program_001 *)
(*- #Justify_Derived "Utility function" *)
let expand_program (p: Asm.program) : Asm.program Errors.res =
  AST.transform_partial_program2 expand_fundef (fun id v -> Errors.OK v) p
(*- #End *)
