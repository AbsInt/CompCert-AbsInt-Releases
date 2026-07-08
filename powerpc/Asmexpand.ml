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

(* FreeScale's EREF extensions *)

(*- E_COMPCERT_CODE_Asmexpand_eref_001 *)
(*- #Justify_Derived "Utility constant" *)
let eref =
  match Configuration.model with
  | "e5500" -> true
  | _ -> false
(*- #End *)

(* Useful constants and helper functions *)

(*- E_COMPCERT_CODE_Asmexpand_constants_001 *)
(*- #Justify_Derived "Utility constants" *)
let upper32 = coqint_of_camlint64 0xFFFF_FFFF_0000_0000L
let lower32 = coqint_of_camlint64 0x0000_0000_FFFF_FFFFL
(*- #End *)

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

(*- E_COMPCERT_CODE_emit_aindexed_001 *)
(*- #Justify_Derived "Utility function" *)
let emit_aindexed mk1 mk2 unaligned r1 temp ofs =
  List.iter emit (Asmgen.aindexed mk1 mk2 unaligned r1 temp ofs [])
(*- #End *)

(*- E_COMPCERT_CODE_emit_aindexed2_001 *)
(*- #Justify_Derived "Utility function" *)
let emit_aindexed2 mk r1 r2 =
  List.iter emit (Asmgen.aindexed2 mk r1 r2 [])
(*- #End *)

(*- E_COMPCERT_CODE_emit_aglobal_001 *)
(*- #Justify_Derived "Utility function" *)
let emit_aglobal mk1 mk2 unaligned temp symb ofs =
  List.iter emit (Asmgen.aglobal mk1 mk2 unaligned temp symb ofs [])
(*- #End *)

(*- E_COMPCERT_CODE_emit_adbased_001 *)
(*- #Justify_Derived "Utility function" *)
let emit_abased mk1 mk2 unaligned r1 temp symb ofs =
  List.iter emit (Asmgen.abased mk1 mk2 unaligned r1 temp symb ofs [])
(*- #End *)

(*- E_COMPCERT_CODE_emit_ainstack_001 *)
(*- #Justify_Derived "Utility function" *)
let emit_ainstack mk1 mk2 unaligned temp ofs =
  List.iter emit (Asmgen.ainstack mk1 mk2 unaligned temp ofs [])
(*- #End *)

 (* Numbering of bits in the CR register *)
(*- E_COMPCERT_CODE_Asmexpand_num_crbit_001 *)
(*- #Justify_Derived "Utility function" *)
let num_crbit = function
  | CRbit_0 -> 0
  | CRbit_1 -> 1
  | CRbit_2 -> 2
  | CRbit_3 -> 3
  | CRbit_6 -> 6
(*- #End *)

 (* Handling of annotations *)

(*- E_COMPCERT_CODE_Asmexpand_annot_intval_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_ANNOT_INT_001 *)
let expand_annot_val kind txt targ args res =
  emit (Pbuiltin(EF_annot(kind,txt, [targ]), args, BR_none));
  begin match args, res with
  | [BA(IR src)], BR(IR dst) ->
      if dst <> src then emit (Pmr(dst, src))
  | [BA(FR src)], BR(FR dst) ->
      if dst <> src then emit (Pfmr(dst, src))
  | _, _ ->
      (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_ANNOT_INTVAL_001 *)
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
      then (GPR1, Ptrofs.to_int ofs)
      else begin emit_addimm tmp GPR1 (Ptrofs.to_int ofs); (tmp, _0l) end
  | _ ->
      assert false
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_expand_builtin_memcpy_small_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_002 *)
let expand_builtin_memcpy_small sz al src dst =
  let tsrc = if dst <> BA (IR GPR11) then GPR11 else GPR12 in
  let tdst = if src <> BA (IR GPR12) then GPR12 else GPR11 in
  let (rsrc, osrc) = memcpy_small_arg sz src tsrc in
  let (rdst, odst) = memcpy_small_arg sz dst tdst in
  (* If the source and destination register are not equal the source and
     destination register after memcpy_small_arg should also be not equal
     except for the case when both destination and source are on the stack *)
  assert (src = dst || rdst <> rsrc || (rsrc = GPR1 && rdst = GPR1));
  let rec copy osrc odst sz =
    if Ptrofs.cmpu Cge sz _8p && Ptrofs.cmpu Cge al _4p && !Clflags.option_ffpu then begin
      emit (Plfd(FPR13, Cint osrc, rsrc));
      emit (Pstfd(FPR13, Cint odst, rdst));
      copy (I32.add osrc _8l) (I32.add odst _8l) (Ptrofs.sub sz _8p)
    end else if Ptrofs.cmpu Cge sz _4p then begin
      emit (Plwz(GPR0, Cint osrc, rsrc));
      emit (Pstw(GPR0, Cint odst, rdst));
      copy (I32.add osrc _4l) (I32.add odst _4l) (Ptrofs.sub sz _4p)
    end else if Ptrofs.cmpu Cge sz _2p then begin
      emit (Plhz(GPR0, Cint osrc, rsrc));
      emit (Psth(GPR0, Cint odst, rdst));
      copy (I32.add osrc _2l) (I32.add odst _2l) (Ptrofs.sub sz _2p)
    end else if Ptrofs.cmpu Cge sz _1p then begin
      emit (Plbz(GPR0, Cint osrc, rsrc));
      emit (Pstb(GPR0, Cint odst, rdst));
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
      emit (Paddi(tmp, r, Cint _m4l))
  | BA_addrstack ofs ->
      emit_addimm tmp GPR1 (I32.add (Ptrofs.to_int ofs) _m4l)
  | _ ->
      assert false
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_expand_builtin_memcpy_big_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_003 *)
let expand_builtin_memcpy_big sz al src dst =
  assert (Ptrofs.cmpu Cge sz _4p);
  emit_loadimm GPR0 (Ptrofs.(to_int (divu sz _4p)));
  emit (Pmtctr GPR0);
  let (s, d) =
    if dst <> BA (IR GPR11) then (GPR11, GPR12) else (GPR12, GPR11) in
  memcpy_big_arg src s;
  memcpy_big_arg dst d;
  let lbl = new_label() in
  emit (Plabel lbl);
  emit (Plwzu(GPR0, Cint _4l, s));
  emit (Pstwu(GPR0, Cint _4l, d));
  emit (Pbdnz lbl);
  (* s and d lag behind by 4 bytes *)
  let sz' = Ptrofs.modu sz _4p in
  if Ptrofs.eq sz' _1p then begin
    emit (Plbz(GPR0, Cint _4l, s));
    emit (Pstb(GPR0, Cint _4l, d))
  end else if Ptrofs.eq sz' _2p then begin
    emit (Plhz(GPR0, Cint _4l, s));
    emit (Psth(GPR0, Cint _4l, d))
  end else if Ptrofs.eq sz' _3p then begin
    emit (Plhz(GPR0, Cint _4l, s));
    emit (Psth(GPR0, Cint _4l, d));
    emit (Plbz(GPR0, Cint _6l, s));
    emit (Pstb(GPR0, Cint _6l, d))
  end
(*- #End *)


(*- E_COMPCERT_CODE_Asmexpand_memcpy_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_001 *)
let expand_builtin_memcpy sz al args =
  let (dst, src) =
    match args with [d; s] -> (d, s) | _ -> assert false in
  if Ptrofs.cmpu Cle sz (if !Clflags.option_ffpu && al >= _4p
            then if !Clflags.option_Osize then _35p else _51p
	    else if !Clflags.option_Osize then _19p else _27p)
  then expand_builtin_memcpy_small sz al src dst
  else expand_builtin_memcpy_big sz al src dst
(*- #End *)


(* Handling of volatile reads and writes *)

(* If you alter this, please adjust transl_memory_access in Asmgen.v, too *)

(*- E_COMPCERT_CODE_Asmexpand_volatile_access_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_ACCESS_001 *)
let expand_volatile_access
       (mk1: constant -> ireg -> instruction list -> instruction list)
       (mk2: ireg -> ireg -> instruction list -> instruction list)
       ?(ofs_unaligned = true)
       addr temp =
  match addr with
  | BA(IR r) ->
    List.iter emit (mk1 (Cint _0l) r [])
  | BA_addrstack ofs ->
    emit_ainstack mk1 mk2 ofs_unaligned temp (Ptrofs.to_int ofs)
  | BA_addrglobal(id, ofs) ->
    emit_aglobal mk1 mk2 ofs_unaligned temp id ofs
  | BA_addptr(BA(IR r), BA_int n) ->
    emit_aindexed mk1 mk2 ofs_unaligned r temp n
  | BA_addptr(BA_addrglobal(id, ofs), BA(IR r)) ->
    emit_abased mk1 mk2 ofs_unaligned r temp id ofs
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
    Plwz(hi, ofs_hi, base) ::
    Plwz(lo, ofs_lo, base) :: k
  end else begin
    Plwz(lo, ofs_lo, base) ::
    Plwz(hi, ofs_hi, base) :: k
  end
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_volatile_access_002 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_LOAD_001 *)
let expand_builtin_vload_1 chunk addr res =
  match chunk, res with
  | (Mbool | Mint8unsigned), BR(IR res) ->
      expand_volatile_access
        (fun c r k -> Plbz(res, c, r) :: k)
        (fun r1 r2 k -> Plbzx(res, r1, r2) :: k)
        addr GPR11
  | Mint8signed, BR(IR res) ->
      expand_volatile_access
        (fun c r k-> Plbz(res, c, r) :: Pextsb(res, res) :: k)
        (fun r1 r2 k -> Plbzx(res, r1, r2) :: Pextsb(res, res) :: k)
        addr GPR11
  | Mint16unsigned, BR(IR res) ->
      expand_volatile_access
        (fun c r k ->  Plhz(res, c, r) :: k)
        (fun r1 r2 k -> Plhzx(res, r1, r2) :: k)
        addr GPR11
  | Mint16signed, BR(IR res) ->
      expand_volatile_access
        (fun c r k-> Plha(res, c, r) :: k)
        (fun r1 r2 k -> Plhax(res, r1, r2) :: k)
        addr GPR11
  | (Mint32 | Many32), BR(IR res) ->
      expand_volatile_access
        (fun c r k-> Plwz(res, c, r) :: k)
        (fun r1 r2 k -> Plwzx(res, r1, r2) :: k)
        addr GPR11
  | Mfloat32, BR(FR res) ->
      expand_volatile_access
        (fun c r k-> Plfs(res, c, r) :: k)
        (fun r1 r2 k -> Plfsx(res, r1, r2) :: k)
        addr GPR11
  | (Mfloat64 | Many64), BR(FR res) ->
      expand_volatile_access
        (fun c r k-> Plfd(res, c, r) :: k)
        (fun r1 r2 k -> Plfdx(res, r1, r2) :: k)
        addr GPR11
  | (Mint64 | Many64), BR(IR res) ->
      expand_volatile_access
        (fun c r k-> Pld(res, c, r) :: k)
        (fun r1 r2 k -> Pldx(res, r1, r2) :: k)
        ~ofs_unaligned:false
        addr GPR11
  | Mint64, BR_splitlong(BR(IR hi), BR(IR lo)) ->
      expand_volatile_access
        (fun c r k->
           match offset_constant c _4l with
           | Some c' -> expand_load_int64 hi lo r c c' k
           | None ->
               Paddi(GPR11, r, c) ::
               expand_load_int64 hi lo GPR11 (Cint _0l) (Cint _4l) k)
        (fun r1 r2 k ->
           Padd(GPR11, r1, r2) ::
           expand_load_int64 hi lo GPR11 (Cint _0l) (Cint _4l) k)
        addr GPR11
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
  if not (List.mem (IR GPR11) rl) then GPR11
  else if not (List.mem (IR GPR12) rl) then GPR12
  else GPR10
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_expand_store_int64_001 *)
(*- #Justify_Derived "Utility function" *)
let expand_store_int64 hi lo base ofs_hi ofs_lo k =
  Pstw(hi, ofs_hi, base) ::
  Pstw(lo, ofs_lo, base) :: k
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_volatile_access_004 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_VOLATILE_STORE_001 *)
let expand_builtin_vstore_1 chunk addr src =
  let temp = temp_for_vstore src in
  match chunk, src with
  | (Mbool | Mint8signed | Mint8unsigned), BA(IR src) ->
      expand_volatile_access
        (fun c r k-> Pstb(src, c, r) :: k)
        (fun r1 r2 k -> Pstbx(src, r1, r2) :: k)
        addr temp
  | (Mint16signed | Mint16unsigned), BA(IR src) ->
      expand_volatile_access
        (fun c r k-> Psth(src, c, r) :: k)
        (fun r1 r2 k -> Psthx(src, r1, r2) :: k)
        addr temp
  | (Mint32 | Many32), BA(IR src) ->
      expand_volatile_access
        (fun c r k-> Pstw(src, c, r) :: k)
        (fun r1 r2 k -> Pstwx(src, r1, r2) :: k)
        addr temp
  | Mfloat32, BA(FR src) ->
      expand_volatile_access
        (fun c r k-> Pstfs(src, c, r) :: k)
        (fun r1 r2 k -> Pstfsx(src, r1, r2) :: k)
        addr temp
  | (Mfloat64 | Many64), BA(FR src) ->
      expand_volatile_access
        (fun c r k-> Pstfd(src, c, r) :: k)
        (fun r1 r2 k -> Pstfdx(src, r1, r2) :: k)
        addr temp
  | (Mint64 | Many64), BA(IR src) ->
      expand_volatile_access
        (fun c r k-> Pstd(src, c, r) :: k)
        (fun r1 r2 k -> Pstdx(src, r1, r2) :: k)
        ~ofs_unaligned:false
        addr temp
  | Mint64, BA_splitlong(BA(IR hi), BA(IR lo)) ->
      expand_volatile_access
        (fun c r k ->
           match offset_constant c _4l with
           | Some c' -> expand_store_int64 hi lo r c c' k
           | None ->
               Paddi(temp, r, c) ::
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
let rec next_arg_locations ir fr ofs = function
  | [] ->
      (ir, fr, ofs)
  | (Tint | Tany32) :: l ->
      if ir < 8l
      then next_arg_locations (Int32.add ir 1l) fr ofs l
      else next_arg_locations ir fr (Z.add ofs _4) l
  | (Tfloat | Tsingle | Tany64) :: l ->
      if fr < 8l
      then next_arg_locations ir (Int32.add fr 1l) ofs l
      else next_arg_locations ir fr (Z.add (Coqlib.align ofs _8) _8) l
  | Tlong :: l ->
      let ir = align ir 2l in
      if ir < 8l
      then next_arg_locations (Int32.add ir 2l) fr ofs l
      else next_arg_locations ir fr (Z.add (Coqlib.align ofs _8) _8) l
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_builtin_va_start_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_VA_START_001 *)
let expand_builtin_va_start r =
  (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_VA_START_001 *)
  if not (is_current_function_variadic ()) then
    invalid_arg "Fatal error: va_start used in non-vararg function";
  let (ir, fr, ofs) =
    next_arg_locations 0l 0l _0 (get_current_function_args ()) in
  emit_loadimm GPR0 (coqint_of_camlint ir);
  emit (Pstb(GPR0, Cint _0l, r));
  emit_loadimm GPR0 (coqint_of_camlint fr);
  emit (Pstb(GPR0, Cint _1l, r));
  emit_addimm GPR0 GPR1 (I32.(add (add !current_function_stacksize _8l)
                                      (repr ofs)));
  emit (Pstw(GPR0, Cint _4l, r));
  emit_addimm GPR0 GPR1 (I32.(sub !current_function_stacksize _96l));
  emit (Pstw(GPR0, Cint _8l, r))
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
  if conflict then (fn GPR0; emit (Pmr(rl, GPR0))) else fn rl
(*- #End *)

(* Expansion of integer conditional moves (__builtin_*sel and Pisel) *)
(* The generated code works equally well with 32-bit integer registers
   and with 64-bit integer registers. *)

(*- E_COMPCERT_CODE_Asmexpand_expand_integer_cond_move_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_SEL_001 *)
let expand_integer_cond_move a2 a3 res =
  (* GPR0 is -1 (all ones) if condition is true, 0 if it is false *)
  if res <> a3 then begin
    emit (Pand_ (res, a2, GPR0));
    emit (Pandc (GPR0, a3, GPR0))
  end else begin
    emit (Pandc (res, a3, GPR0));
    emit (Pand_ (GPR0, a2, GPR0))
  end;
  emit (Por (res, res, GPR0))
(*- #End *)

(* Expansion of floating point conditional moves (Pfcmove) *)

(*- E_COMPCERT_CODE_Asmexpand_expand_float_cond_move_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_SEL_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_PFSEL_GEN_001 *)
let expand_float_cond_move bit a2 a3 res =
  emit (Pmfcr GPR0);
  emit (Prlwinm(GPR0, GPR0, I32.repr (Z.of_uint (4 + num_crbit bit)), _8l));
  emit (Pstfdu (a3, Cint (_m16l), GPR1));
  emit (Pcfi_adjust (Ptrofs.of_int _16l));
  emit (Pstfd (a2, (Cint _8l), GPR1));
  emit (Plfdx (res, GPR1, GPR0));
  emit (Paddi (GPR1, GPR1, (Cint _16l)));
  emit (Pcfi_adjust (Ptrofs.of_int _m16l))
(*- #End *)

(* Symmetrically, we emulate the "isel" instruction on PPC processors
   that do not have it. *)

(*- E_COMPCERT_CODE_Asmexpand_expand_isel_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_SEL_001 *)
(*- #Link_to E_COMPCERT_TR_Function_EXPAND_PISEL_001 *)
let expand_isel bit a2 a3 res =
  assert (a2 <> a3);
  if eref then
    emit (Pisel (res, a2, a3, bit))
  else begin
    emit (Pmfcr GPR0);
    emit (Prlwinm(GPR0, GPR0, I32.repr (Z.of_uint (1 + num_crbit bit)), _1l));
    emit (Psubfic (GPR0, GPR0, Cint _0l));
    expand_integer_cond_move a2 a3 res
  end
(*- #End *)


(* Convert integer constant into GPR with corresponding number *)
(*- E_COMPCERT_CODE_Asmexpand_int_to_int_reg_001 *)
(*- #Justify_Derived "Utility function" *)
let int_to_int_reg = function
   | 0l -> Some GPR0  | 1l -> Some GPR1  | 2l -> Some GPR2  | 3l -> Some GPR3
   | 4l -> Some GPR4  | 5l -> Some GPR5  | 6l -> Some GPR6  | 7l -> Some GPR7
   | 8l -> Some GPR8  | 9l -> Some GPR9  | 10l -> Some GPR10 | 11l -> Some GPR11
   | 12l -> Some GPR12 | 13l -> Some GPR13 | 14l -> Some GPR14 | 15l -> Some GPR15
   | 16l -> Some GPR16 | 17l -> Some GPR17 | 18l -> Some GPR18 | 19l -> Some GPR19
   | 20l -> Some GPR20 | 21l -> Some GPR21 | 22l -> Some GPR22 | 23l -> Some GPR23
   | 24l -> Some GPR24 | 25l -> Some GPR25 | 26l -> Some GPR26 | 27l -> Some GPR27
   | 28l -> Some GPR28 | 29l -> Some GPR29 | 30l -> Some GPR30 | 31l -> Some GPR31
   | _ -> None
(*- #End *)

(* Handling of compiler-inlined builtins *)

let expand_builtin_inline name args res =
  (* Can use as temporaries: GPR0 *)
  match name, args, res with

  (* Integer arithmetic *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_005 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_CLZ_001 *)
  | ("__builtin_clz" | "__builtin_clzl"), [BA(IR a1)], BR(IR res) ->
      emit (Pcntlzw(res, a1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_006 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_CLZLL_001 *)
  | "__builtin_clzll", [BA(IR a1)], BR(IR res) ->
      emit (Pcntlzd(res, a1))
  | "__builtin_clzll", [BA_splitlong(BA(IR ah), BA(IR al))], BR(IR res) ->
      let lbl = new_label () in
      emit (Pcntlzw(GPR0, al));
      emit (Pcntlzw(res, ah));
      (* less than 32 bits zero? *)
      emit (Pcmpwi (res, Cint _32l));
      emit (Pbf (CRbit_2, lbl));
      (* high bits all zero, count bits in low word and increment by 32 *)
      emit (Padd(res, res, GPR0));
      emit (Plabel lbl)
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_007 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_CTZ_001 *)
  | ("__builtin_ctz" | "__builtin_ctzl"), [BA(IR a1)], BR(IR res) ->
      emit (Paddi(GPR0, a1, Cint _m1l));   (* tmp := x-1 *)
      emit (Pandc(res, GPR0, a1));        (* res := tmp & ~(x) *)
      emit (Pcntlzw(res, res));           (* res := #leading zeros *)
      emit (Psubfic(res, res, Cint _32l))  (* res := 32 - #leading zeros *)
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_008 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_CTZLL_001 *)
  | "__builtin_ctzll", [BA(IR a1)], BR(IR res) ->
      emit (Paddi64(GPR0, a1, _m1L));     (* tmp := x-1 *)
      emit (Pandc(res, GPR0, a1));        (* res := tmp & ~(x) *)
      emit (Pcntlzd(res, res));           (* res := #leading zeros *)
      emit (Psubfic64(res, res, _64L))    (* res := 64 - #leading zeros *)
  | "__builtin_ctzll", [BA_splitlong(BA(IR ah), BA(IR al))], BR(IR res) ->
      let lbl1 = new_label () in
      let lbl2 = new_label () in
      (* low word equal to zero? *)
      emit (Pcmpwi (al, Cint _0l));
      emit (Pbf (CRbit_2, lbl1));
      (* low word is zero, count trailing zeros in high word and increment by 32 *)
      emit (Paddi(GPR0, ah, Cint _m1l));
      emit (Pandc(res, GPR0, ah));
      emit (Pcntlzw(res, res));
      emit (Psubfic(res, res, Cint _64l));
      emit (Pb lbl2);
      (* count trailing zeros in low word *)
      emit (Plabel lbl1);
      emit (Paddi(GPR0, al, Cint _m1l));
      emit (Pandc(res, GPR0, al));
      emit (Pcntlzw(res, res));
      emit (Psubfic(res, res, Cint _32l));
      emit (Plabel lbl2)
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_009 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_CMPB_001 *)
  | "__builtin_cmpb",  [BA(IR a1); BA(IR a2)], BR(IR res) ->
      emit (Pcmpb (res,a1,a2))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_056 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_BSWAP64_001 *)
  |  "__builtin_bswap64", [BA(IR a1)], BR(IR res) ->
      assert (Archi.ppc64);
      emit (Pstdu(a1, Cint _m8l, GPR1));
      emit (Pcfi_adjust _8p);
      emit (Pldbrx(res, GPR0, GPR1));
      emit (Paddi(GPR1, GPR1, Cint _8l));
      emit (Pcfi_adjust _m8p)
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_010 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_BSWAP_001 *)
  | ("__builtin_bswap" | "__builtin_bswap32"), [BA(IR a1)], BR(IR res) ->
      emit (Pstwu(a1, Cint _m8l, GPR1));
      emit (Pcfi_adjust  _8p);
      emit (Plwbrx(res, GPR0, GPR1));
      emit (Paddi(GPR1, GPR1, Cint _8l));
      emit (Pcfi_adjust _m8p)
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_011 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_BSWAP16_001 *)
  | "__builtin_bswap16", [BA(IR a1)], BR(IR res) ->
      emit (Prlwinm(GPR0, a1, _8l, _65280l));
      emit (Prlwinm(res, a1, _24l, _255l));
      emit (Por(res, GPR0, res))
  (*- #End *)

  (* Float arithmetic *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_012 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_FMADD_001 *)
  | "__builtin_fmadd", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfmadd(res, a1, a2, a3))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_013 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_FMSUB_001 *)
  | "__builtin_fmsub", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfmsub(res, a1, a2, a3))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_014 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_FNMADD_001 *)
  | "__builtin_fnmadd", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfnmadd(res, a1, a2, a3))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_015 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_FNMSUB_001 *)
  | "__builtin_fnmsub", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfnmsub(res, a1, a2, a3))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_017 *)
  (*- #Justify_Derived "Not available on e5500" *)
  | ("__builtin_fsqrt" | "__builtin_sqrt"), [BA(FR a1)], BR(FR res) ->
      emit (Pfsqrt(res, a1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_018 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_FRSQRTE_001 *)
  | "__builtin_frsqrte", [BA(FR a1)], BR(FR res) ->
      emit (Pfrsqrte(res, a1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_019 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_FRES_001 *)
  | "__builtin_fres", [BA(FR a1)], BR(FR res) ->
      emit (Pfres(res, a1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_021 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_FCTI_001 *)
  | "__builtin_fcti", [BA(FR a1)], BR(IR res) ->
      emit (Pfctiw(FPR13, a1));
      emit (Pstfdu(FPR13, Cint _m8l, GPR1));
      emit (Pcfi_adjust _8p);
      emit (Plwz(res, Cint _4l, GPR1));
      emit (Paddi(GPR1, GPR1, Cint _8l));
      emit (Pcfi_adjust _m8p)
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_059 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_DTOB_001 *)
  | "__builtin_dtob", [BA(FR a1)], BR(IR res) ->
      assert (Archi.ppc64);
      emit (Pstfdu(a1, Cint _m8l, GPR1));
      emit (Pcfi_adjust _8p);
      emit (Pld(res, Cint _0l, GPR1));
      emit (Paddi(GPR1, GPR1, Cint _8l));
      emit (Pcfi_adjust _m8p)

  | "__builtin_dtob", [BA(FR a1)],
                          BR_splitlong(BR(IR rh), BR(IR rl)) ->
      assert (not Archi.ppc64);
      emit (Pstfdu(a1, Cint _m8l, GPR1));
      emit (Pcfi_adjust _8p);
      emit (Plwz(rh, Cint _0l, GPR1));
      emit (Plwz(rl, Cint _4l, GPR1));
      emit (Paddi(GPR1, GPR1, Cint _8l));
      emit (Pcfi_adjust _m8p)
  (*- #End *)

  (* Memory accesses *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_022 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_READ16_REVERSED_001 *)
  | "__builtin_read16_reversed", [BA(IR a1)], BR(IR res) ->
      emit (Plhbrx(res, GPR0, a1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_023 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_READ32_REVERSED_001 *)
  | "__builtin_read32_reversed", [BA(IR a1)], BR(IR res) ->
      emit (Plwbrx(res, GPR0, a1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_024 *)
  (*- - *)
  | "__builtin_read64_reversed", [BA(IR a1)], BR(IR res) ->
      if Archi.ppc64 then
        emit (Pldbrx(res, GPR0, a1))
      else
        (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_INVALID_BUILTIN_001 *)
        raise (AsmexpandError "__builtin_read64_reversed is only supported for PPC64 targets")
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_025 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_WRITE16_REVERSED_001 *)
  | "__builtin_write16_reversed", [BA(IR a1); BA(IR a2)], _ ->
      emit (Psthbrx(a2, GPR0, a1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_026 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_WRITE32_REVERSED_001 *)
  | "__builtin_write32_reversed", [BA(IR a1); BA(IR a2)], _ ->
      emit (Pstwbrx(a2, GPR0, a1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_027 *)
  (*- - *)
  | "__builtin_write64_reversed", [BA(IR a1); BA(IR a2)], _ ->
      if Archi.ppc64 then
        emit (Pstdbrx(a2, GPR0, a1))
      else
        (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_INVALID_BUILTIN_001 *)
        raise (AsmexpandError "__builtin_write64_reversed is only supported for PPC64 targets")
  (*- #End *)

  (* Synchronization *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_028 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMBAR_001 *)
  | "__builtin_membar", [], _ ->
      ()
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_029 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_EIEIO_001 *)
  | "__builtin_eieio", [], _ ->
      emit (Peieio)
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_030 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_SYNC_001 *)
  | "__builtin_sync", [], _ ->
      emit (Psync)
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_031 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_ISYNC_001 *)
  | "__builtin_isync", [], _ ->
      emit (Pisync)
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_032 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_LWSYNC_001 *)
  | "__builtin_lwsync", [], _ ->
      emit (Plwsync)
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_033 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_MBAR_001 *)
  | "__builtin_mbar", [BA_int mo], _ ->
      if not (I32.eq mo _0l || I32.eq mo _1l) then
        (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_MBAR_001 *)
        raise (AsmexpandError "the argument of __builtin_mbar must be 0 or 1");
      emit (Pmbar mo)
  | "__builtin_mbar", _, _ ->
      (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_MBAR_002 *)
      raise (AsmexpandError "the argument of __builtin_mbar must be a constant");
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_034 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_TRAP_001 *)
  | "__builtin_trap", [], _ ->
      emit (Ptrap)
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
      emit (Pdcbf (GPR0,a1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_037 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_DCBI_001 *)
  | "__builtin_dcbi", [BA(IR a1)],_ ->
      emit (Pdcbi (GPR0,a1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_038 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_ICBI_001 *)
  | "__builtin_icbi", [BA(IR a1)],_ ->
      emit (Picbi(GPR0,a1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_039 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_DCBTLS_001 *)
  | "__builtin_dcbtls", [BA (IR a1); BA_int loc],_ ->
      if not ((I32.eq loc _0l) || (I32.eq loc _2l)) then
        (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_CACHE_BLOCK_TLS_001 *)
        raise (AsmexpandError "the second argument of __builtin_dcbtls must be 0 or 2");
      emit (Pdcbtls (loc,GPR0,a1))
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
      emit (Picbtls (loc,GPR0,a1))
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
        emit (Pdcbt (loc,GPR0,a1));
      end else if I32.eq rw _1l then begin
        emit (Pdcbtst (loc,GPR0,a1));
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
      emit (Pdcbz (GPR0,a1))
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

  (* Special registers in 32bit hybrid mode *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_045 *)
  (*- - *)
  | "__builtin_get_spr64", [BA_int n], BR(IR r) ->
      if Archi.ppc64 then
        emit (Pmfspr(r, n))
      else
        (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_INVALID_BUILTIN_001 *)
        raise (AsmexpandError "__builtin_get_spr64 is only supported for PPC64 targets")
  | "__builtin_get_spr64", _, _ ->
      if Archi.ppc64 then
        (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_GET_SPR_001 *)
        raise (AsmexpandError "the argument of __builtin_get_spr64 must be a constant")
      else
        (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_INVALID_BUILTIN_001 *)
        raise (AsmexpandError "__builtin_get_spr64 is only supported for PPC64 targets")
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_046 *)
  (*- - *)
  | "__builtin_set_spr64", [BA_int n; BA(IR a)], _ ->
      if Archi.ppc64 then
        emit (Pmtspr(n, a))
      else
        (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_INVALID_BUILTIN_001 *)
        raise (AsmexpandError "__builtin_set_spr64 is only supported for PPC64 targets")
  | "__builtin_set_spr64", _, _ ->
      if Archi.ppc64 then
        (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_SET_SPR_001 *)
        raise (AsmexpandError "the first argument of __builtin_set_spr64 must be a constant")
      else
        (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_INVALID_BUILTIN_001 *)
        raise (AsmexpandError "__builtin_set_spr64 is only supported for PPC64 targets")
  (*- #End *)

  (* Move registers *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_047 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_MR_001 *)
  | "__builtin_mr", [BA_int dst; BA_int src], _ ->
      (match int_to_int_reg (camlint_of_coqint dst), int_to_int_reg (camlint_of_coqint src) with
       | Some dst, Some src -> emit (Pori (dst, src, Cint _0l))
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
      if I32.ltu sz _32768l then
        emit (Paddi(res, GPR1, Cint sz))
      else
        emit (Plwz(res, Cint ofs, GPR1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_049 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_RETURN_ADDRESS_001 *)
  | "__builtin_return_address",_,BR (IR res) ->
      emit (Plwz (res, Cint! retaddr_offset,GPR1))
  (*- #End *)

  (* no operation *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_051 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_NOP_001 *)
  | "__builtin_nop", [], _ ->
      emit (Pori (GPR0, GPR0, Cint _0l))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_057 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_UNREACHABLE_001 *)
  (* Optimization hint *)
  | "__builtin_unreachable", [], _ ->
     ()
  (*- #End *)

  (* atomic operations *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_052 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_ATOMIC_EXCHANGE_001 *)
  | "__builtin_atomic_exchange", [BA (IR a1); BA (IR a2); BA (IR a3)],_ ->
      (* Register constraints imposed by Machregs.v *)
      assert(a1 = GPR3 && a2 = GPR4 && a3 = GPR5);
      emit (Plwz (GPR10,Cint _0l,a2));
      emit (Psync);
      let lbl = new_label() in
      emit (Plabel lbl);
      emit (Plwarx (GPR0,GPR0,a1));
      emit (Pstwcx_ (GPR10,GPR0,a1));
      emit (Pbf (CRbit_2,lbl));
      emit (Pisync);
      emit (Pstw (GPR0,Cint _0l,a3))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_053 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_ATOMIC_LOAD_001 *)
  | "__builtin_atomic_load", [BA (IR a1); BA (IR a2)],_ ->
      let lbl = new_label () in
      emit (Psync);
      emit (Plwz (GPR0,Cint _0l,a1));
      emit (Pcmpw (GPR0,GPR0));
      emit (Pbf (CRbit_2,lbl));
      emit (Plabel lbl);
      emit (Pisync);
      emit (Pstw (GPR0,Cint _0l, a2))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_054 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_SYNC_FETCH_AND_ADD_001 *)
  | "__builtin_sync_fetch_and_add", [BA (IR a1); BA(IR a2)], BR (IR res) ->
      (* Register constraints imposed by Machregs.v *)
      assert (a1 = GPR4 && a2 = GPR5 && res = GPR3);
      let lbl = new_label() in
      emit (Psync);
      emit (Plabel lbl);
      emit (Plwarx (res,GPR0,a1));
      emit (Padd (GPR0,res,a2));
      emit (Pstwcx_ (GPR0,GPR0,a1));
      emit (Pbf (CRbit_2, lbl));
      emit (Pisync);
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_055 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_ATOMIC_COMPARE_EXCHANGE_001 *)
  | "__builtin_atomic_compare_exchange", [BA (IR dst); BA(IR exp); BA (IR des)],  BR (IR res) ->
      (* Register constraints imposed by Machregs.v *)
      assert (dst = GPR4 && exp = GPR5 && des = GPR6 && res = GPR3);
      let lbls = new_label ()
      and lblneq = new_label ()
      and lblsucc = new_label () in
      emit (Plwz (GPR10,Cint _0l,exp));
      emit (Plwz (GPR11,Cint _0l,des));
      emit (Psync);
      emit (Plabel lbls);
      emit (Plwarx (GPR0,GPR0,dst));
      emit (Pcmpw (GPR0,GPR10));
      emit (Pbf (CRbit_2,lblneq));
      emit (Pstwcx_ (GPR11,GPR0,dst));
      emit (Pbf (CRbit_2,lbls));
      emit (Plabel lblneq);
      (* Here, CR2 is true if the exchange succeeded, false if it failed *)
      emit (Pisync);
      emit (Pmfcr GPR10);
      emit (Prlwinm (res,GPR10, _3l,_1l));
      (* Update exp with the current value of dst if the exchange failed *)
      emit (Pbt (CRbit_2,lblsucc));
      emit (Pstw (GPR0,Cint _0l,exp));
      emit (Plabel lblsucc)
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_builtin_inline_058 *)
  (* Catch-all *)
  | _ ->
      (*- #Link_to E_COMPCERT_TR_Robustness_DIAG_UNKNOWN_BUILTIN_001 *)
      raise (AsmexpandError ("unrecognized builtin " ^ name))
  (*- #End *)

(* Calls to variadic functions: condition bit 6 must be set
   if at least one argument is a float; clear otherwise.
   For compatibility with other compilers, do the same if the called
   function is unprototyped. *)

(*- E_COMPCERT_CODE_Asmexpand_set_cr6_001 *)
(*- #Justify_Derived "Utility function" *)
let set_cr6 sg =
  if (sg.sig_cc.cc_vararg <> None) || sg.sig_cc.cc_unproto then begin
    if List.exists (function Xfloat | Xsingle -> true | _ -> false) sg.sig_args
    then emit (Pcreqv(CRbit_6, CRbit_6, CRbit_6))
    else emit (Pcrxor(CRbit_6, CRbit_6, CRbit_6))
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
    | Pldi (r1,c) -> 8
    | Plfi(r1, c) -> 8
    | Plfis(r1, c) -> 8
    | Plabel lbl -> 0
    | Pbuiltin(ef, _, _) -> builtin_size ef
    | Pcfi_adjust _ | Pcfi_rel_offset _ -> 0
    | _ -> 4
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_need_relaxation_001 *)
  let need_relaxation ~map pc instr =
    match instr with
    (*- #Link_to E_COMPCERT_TR_Function_PRINT_PBF_001 *)
    (*- #Link_to E_COMPCERT_TR_Function_PRINT_PBT_001 *)
    | Pbf(_, lbl) | Pbt(_, lbl) ->
        let displ = map lbl - pc in
        displ < -0x8000 || displ >= 0x8000
    | _ ->
        false
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_relax_instruction_001 *)
  let relax_instruction instr =
    match instr with
    (*- #Link_to E_COMPCERT_TR_Function_PRINT_PBF_001 *)
    | Pbf(bit, lbl) ->
        let lbl' = new_label() in
        [Pbt(bit, lbl'); Pb lbl; Plabel lbl']
    (*- #Link_to E_COMPCERT_TR_Function_PRINT_PBT_001 *)
    | Pbt(bit, lbl) ->
        let lbl' = new_label() in
        [Pbf(bit, lbl'); Pb lbl; Plabel lbl']
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
      (* Check stack size + 16 for additional stack used by built-ins *)
      check_stack_size (Z.add sz _16);
      let sz = I32.repr sz in
      assert (ofs = _0p);
      let adj = I32.neg sz in
      if I32.cmp Cge adj _m32768l && I32.cmp Clt adj _0l then
        emit (Pstwu(GPR1, Cint adj, GPR1))
      else begin
        emit_loadimm GPR0 adj;
        emit (Pstwux(GPR1, GPR1, GPR0))
      end;
      emit (Pcfi_adjust (Ptrofs.of_int sz));
      if variadic then begin
        emit (Pmflr GPR0);
        emit (Pbl(intern_string "__compcert_va_saveregs",
                  {sig_args = []; sig_res = Xvoid; sig_cc = cc_default}));
        emit (Pmtlr GPR0)
      end;
      current_function_stacksize := sz;
      linkregister_offset := (Ptrofs.to_int ofs);
      retaddr_offset := (Ptrofs.to_int retofs)
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_002 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_PBRANCH_001 *)
  | Pbctr sg | Pbctrl sg | Pbl(_, sg) | Pbs(_, sg) ->
      set_cr6 sg;
      emit instr
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_003 *)
  (*- - *)
  | Pextzw(r1, r2) ->
      emit (Prldinm(r1, r2, _0l, lower32))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_004 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_PFREEFRAME_001 *)
  | Pfreeframe(sz, ofs) ->
      let variadic = is_current_function_variadic () in
      let sz = I32.repr sz in
      let sz = if variadic then I32.add sz _96l else sz in
      if I32.ltu sz _32768l then
        emit (Paddi(GPR1, GPR1, Cint sz))
      else
        emit (Plwz(GPR1, Cint (Ptrofs.to_int ofs), GPR1))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_006 *)
  (*- - *)
  | Pfcfl(r1, r2) ->
      assert (Archi.ppc64);
      emit (Pstdu(r2, Cint _m8l, GPR1));
      emit (Pcfi_adjust _8p);
      emit (Plfd(r1, Cint _0l, GPR1));
      emit (Pfcfid(r1, r1));
      emit (Paddi(GPR1, GPR1, Cint _8l));
      emit (Pcfi_adjust _m8p)
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_008 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_PFCTI_001 *)
  | Pfcti(r1, r2) ->
      emit (Pfctiwz(FPR13, r2));
      emit (Pstfdu(FPR13, Cint _m8l, GPR1));
      emit (Pcfi_adjust  _8p);
      emit (Plwz(r1, Cint _4l, GPR1));
      emit (Paddi(GPR1, GPR1, Cint _8l));
      emit (Pcfi_adjust _m8p)
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_010 *)
  (*- - *)
  | Pfctid(r1, r2) ->
      assert (Archi.ppc64);
      emit (Pfctidz(FPR13, r2));
      emit (Pstfdu(FPR13, Cint _m8l, GPR1));
      emit (Pcfi_adjust _8p);
      emit (Pld(r1, Cint _0l, GPR1));
      emit (Paddi(GPR1, GPR1, Cint _8l));
      emit (Pcfi_adjust _m8p)
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_011 *)
  (*- #Justify_Derived "Case relevant only for 32-bit PowerPC" *)
  | Pfmake(rd, r1, r2) ->
      emit (Pstwu(r1, Cint _m8l, GPR1));
      emit (Pcfi_adjust _8p);
      emit (Pstw(r2, Cint _4l, GPR1));
      emit (Plfd(rd, Cint _0l, GPR1));
      emit (Paddi(GPR1, GPR1, Cint _8l));
      emit (Pcfi_adjust _m8p)
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_012 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_PFXDP_001 *)
  | Pfxdp(r1, r2) ->
      if r1 <> r2 then emit(Pfmr(r1, r2))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_023 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_PISEL_001 *)
  | Pisel(rd, r1, r2, bit) ->
      expand_isel bit r1 r2 rd
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_024 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_PFSEL_GEN_001 *)
  | Pfsel_gen (rd, r1, r2, bit) ->
      expand_float_cond_move bit r1 r2 rd
  (*- #End *)
  (*- E_COMPCERT_CODE_Asmexpand_instruction_013 *)
  (*- - *)
  | Plmake(r1, rhi, rlo) ->
      if r1 = rlo then
        emit (Prldimi(r1, rhi, _32l, upper32))
      else if r1 = rhi then begin
        emit (Prldinm(r1, rhi, _32l, upper32));
        emit (Prldimi(r1, rlo, _0l, lower32))
      end else begin
        emit (Pmr(r1, rlo));
        emit (Prldimi(r1, rhi, _32l, upper32))
      end
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_014 *)
  (*- - *)
  | Pllo r1 ->
      ()   (* no computational content *)
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_015 *)
  (*- - *)
  | Plhi(r1, r2) ->
      emit (Prldinm(r1, r2, _32l, lower32))
  (*- #End *)

  (*- E_COMPCERT_CODE_Asmexpand_instruction_016 *)
  (*- #Link_to E_COMPCERT_TR_Function_EXPAND_PMFCRBIT_001 *)
  | Pmfcrbit(r1, bit) ->
      emit (Pmfcr r1);
      emit (Prlwinm(r1, r1, I32.repr (Z.of_uint (1 + num_crbit bit)), _1l))
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
      (*- #Link_to E_COMPCERT_TR_Function_EXPAND_MEMCPY_ALIGNED_001 *)
      | EF_memcpy(sz, al) ->
          expand_builtin_memcpy sz al args
      (*- #End *)

      (*- E_COMPCERT_CODE_Asmexpand_instruction_021 *)
      (*- #Link_to E_COMPCERT_TR_Function_EXPAND_ANNOT_INT_001 *)
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

(*- E_COMPCERT_CODE_Asmexpand_int_reg_to_dwarf_001 *)
(*- #Justify_Derived "Utility function" *)
let int_reg_to_dwarf = function
   | GPR0 -> 0  | GPR1 -> 1  | GPR2 -> 2  | GPR3 -> 3
   | GPR4 -> 4  | GPR5 -> 5  | GPR6 -> 6  | GPR7 -> 7
   | GPR8 -> 8  | GPR9 -> 9  | GPR10 -> 10 | GPR11 -> 11
   | GPR12 -> 12 | GPR13 -> 13 | GPR14 -> 14 | GPR15 -> 15
   | GPR16 -> 16 | GPR17 -> 17 | GPR18 -> 18 | GPR19 -> 19
   | GPR20 -> 20 | GPR21 -> 21 | GPR22 -> 22 | GPR23 -> 23
   | GPR24 -> 24 | GPR25 -> 25 | GPR26 -> 26 | GPR27 -> 27
   | GPR28 -> 28 | GPR29 -> 29 | GPR30 -> 30 | GPR31 -> 31
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_float_reg_to_dwarf_001 *)
(*- #Justify_Derived "Utility function" *)
let float_reg_to_dwarf = function
   | FPR0 -> 32  | FPR1 -> 33  | FPR2 -> 34  | FPR3 -> 35
   | FPR4 -> 36  | FPR5 -> 37  | FPR6 -> 38  | FPR7 -> 39
   | FPR8 -> 40  | FPR9 -> 41  | FPR10 -> 42 | FPR11 -> 43
   | FPR12 -> 44 | FPR13 -> 45 | FPR14 -> 46 | FPR15 -> 47
   | FPR16 -> 48 | FPR17 -> 49 | FPR18 -> 50 | FPR19 -> 51
   | FPR20 -> 52 | FPR21 -> 53 | FPR22 -> 54| FPR23 -> 55
   | FPR24 -> 56 | FPR25 -> 57 | FPR26 -> 58 | FPR27 -> 59
   | FPR28 -> 60 | FPR29 -> 61 | FPR30 -> 62 | FPR31 -> 63
(*- #End *)

(*- E_COMPCERT_CODE_Asmexpand_preg_to_dwarf_001 *)
(*- #Justify_Derived "Utility function" *)
let preg_to_dwarf = function
   | IR r -> int_reg_to_dwarf r, None
   | FR r -> float_reg_to_dwarf r, None
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
