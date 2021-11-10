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

(* Simple functions to serialize powerpc Asm to JSON *)

open Asm
open AST
open BinNums
open Camlcoq
open Json
open JsonAST

(*- E_COMPCERT_CODE_AsmToJson_pp_reg_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_reg pp t n =
  pp_jsingle_object pp "Register" pp_jstring (t ^ n)
(*- #End *)

(*- E_COMPCERT_CODE_AsmToJson_pp_ireg_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_ireg pp reg =
  pp_reg pp "r" (TargetPrinter.int_reg_name reg)
(*- #End *)

(*- E_COMPCERT_CODE_AsmToJson_preg_annot_001 *)
(*- #Justify_Derived "Utility function" *)
let preg_annot = function
  | IR r -> "r" ^ (TargetPrinter.int_reg_name r)
  | _    -> assert false
(*- #End *)

(*- E_COMPCERT_CODE_AsmToJson_pp_constant_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_constant pp c =
  let pp_symbol pp (i,c) =
    pp_jobject_start pp;
    pp_jmember ~first:true pp "Name" pp_atom i;
    pp_jmember  pp "Offset" pp_int c;
    pp_jobject_end pp in
  match c with
  | Cint i ->  pp_int_constant pp i
  | Csymbol_low (i,c) ->
      pp_jsingle_object pp "Symbol_low" pp_symbol (i,c)
  | Csymbol_high (i,c) ->
      pp_jsingle_object pp "Symbol_high" pp_symbol (i,c)
  | Csymbol_sda (i,c) ->
      pp_jsingle_object pp "Symbol_sda" pp_symbol (i,c)
  | Csymbol_rel_low (i,c) ->
      pp_jsingle_object pp "Symbol_rel_low" pp_symbol (i,c)
  | Csymbol_rel_high (i,c) ->
      pp_jsingle_object pp "Symbol_rel_high" pp_symbol (i,c)
(*- #End *)

(*- E_COMPCERT_CODE_AsmToJson_pp_crbit_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_crbit pp c =
  pp_jsingle_object pp "CRbit" pp_jint (TargetPrinter.num_crbit c)
(*- #End *)

let pp_CondReg pp c =
  pp_jsingle_object pp "CondReg" pp_jint c

(*- E_COMPCERT_CODE_AsmToJson_pp_label_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_label pp l =
  pp_jsingle_object pp "Label" pp_jint32 (P.to_int32 l)
(*- #End *)

(*- E_COMPCERT_CODE_AsmToJson_instruction_arg_001 *)
(*- #Justify_Derived "Type definition" *)
type instruction_arg =
  | Ireg of ireg
  | Constant of constant
  | Id
  | Crbit of crbit
  | ALabel of positive
  | Atom of positive
  | String of string
  | CondReg of int
(*- #End *)

(*- E_COMPCERT_CODE_AsmToJson_pp_arg_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_arg pp = function
  | Ireg ir -> pp_ireg pp ir
  | Constant c -> pp_constant pp c
  | Id -> pp_id_const pp ()
  | Crbit cr -> pp_crbit pp cr
  | ALabel lbl -> pp_label pp lbl
  | Atom a -> pp_atom_constant pp a
  | String s -> pp_jsingle_object pp "String" pp_jstring s
  | CondReg c -> pp_CondReg pp c
(*- #End *)

module StringSet = Set.Make(String)

(*- E_COMPCERT_CODE_AsmToJson_mnemonic_names_001 *)
(*- #Justify_Derived "Utility constant" *)
let mnemonic_names = StringSet.of_list
    (* pseudo instructions *)
    [ "Pannot"
    ; "Pbf"
    ; "Pbt"
    ; "Pbtbl"
    ; "Pinlineasm"
    ; "Plabel"
    (* normal *)
    ; "Padd"; "Paddc"; "Padde"; "Paddze"; "Pand_"; "Pandc"
    ; "Pbdnz"
    ; "Pcmplw"; "Pcmpw"; "Pcntlzw"
    ; "Pdcbf"; "Pdcbi"; "Pdcbt"; "Pdcbtls"; "Pdcbtst"; "Pdcbz"; "Pdivw"; "Pdivwu"
    ; "Peqv"; "Pextsb"; "Pextsh"
    ; "Picbi"; "Picbtls"; "Pisel"
    ; "Plbzx"; "Plhax"; "Plhbrx"; "Plhzx"; "Plwbrx"; "Plwzx"
    ; "Pmfcr"; "Pmfspr"; "Pmr"; "Pmtspr"; "Pmulhw"; "Pmulhwu"; "Pmullw"
    ; "Pnand"; "Pnor"
    ; "Por"; "Porc"
    ; "Pslw"; "Psraw"; "Psrawi"; "Psrw"; "Pstbx"; "Psthbrx"; "Psthx"; "Pstwbrx"; "Pstwux"; "Pstwx"; "Psubfc"; "Psubfe"; "Psubfze"; "Psync"
    ; "Pxor"
    (* e encoding *)
    ; "Pe_add16i"; "Pe_add2is"; "Pe_addic"; "Pe_and2i_"; "Pe_and2is_"
    ; "Pe_b"; "Pe_bl"; "Pe_bs"
    ; "Pe_cmp16i"; "Pe_cmpl16i"; "Pe_creqv"; "Pe_cror"; "Pe_crxor"
    ; "Pe_lbz"; "Pe_lha"; "Pe_lhz"; "Pe_li"; "Pe_lis"; "Pe_lwz"; "Pe_lwzu"
    ; "Pe_or2i"; "Pe_or2is"
    ; "Pe_rlwimi"; "Pe_rlwinm"
    ; "Pe_stb"; "Pe_sth"; "Pe_stw"; "Pe_stwu"; "Pe_subfic"
    ; "Pe_xori"
    (* se encoding *)
    ; "Pse_addi"; "Pse_add"; "Pse_and_"; "Pse_andc"
    ; "Pse_bctr"; "Pse_bctrl"; "Pse_bgeni"; "Pse_blr"
    ; "Pse_cmp"; "Pse_cmpi"; "Pse_cmpl"
    ; "Pse_extsb"; "Pse_extsh"
    ; "Pse_isync"
    ; "Pse_lbz"; "Pse_lhz"; "Pse_li"; "Pse_lwz"
    ; "Pse_mfar"; "Pse_mflr"; "Pse_mr"; "Pse_mtar"; "Pse_mtctr"; "Pse_mtlr"; "Pse_mullw"
    ; "Pse_or"
    ; "Pse_slw"; "Pse_sraw"; "Pse_srawi"; "Pse_srw"; "Pse_stb"; "Pse_sth"; "Pse_stw"; "Pse_sub"; "Pse_subf"; "Pse_subi"
      (* SPE *)
    ; "Pefsabs"; "Pefsadd"; "Pefsdiv"; "Pefsmul"; "Pefsneg"; "Pefssub"; "Pefscfsi"; "Pefscfui"; "Pefsctsi"; "Pefsctui"
    ; "Pefscmpeq"; "Pefscmpgt"; "Pefscmplt"
    ]
(*- #End *)

(*- E_COMPCERT_CODE_AsmToJson_pp_instructions_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_instructions pp ic =
  let ic = List.filter (fun s -> match s with
      | Pbuiltin (ef,args,_) ->
        begin match ef with
          | EF_inline_asm _ -> true
          | EF_annot (kind,txt,targs) ->
            begin match  P.to_int kind with
              | 1 -> false
              | 2 ->  AisAnnot.json_ais_annot preg_annot "r1" (camlstring_of_coqstring txt) args <> []
              | _ -> false
            end
          | _ -> false
        end
      | Pcfi_adjust _  (* Only debug relevant *)
      | Pcfi_rel_offset _ -> false
      | _ -> true) ic in
  let instruction pp n args =
    assert (StringSet.mem n mnemonic_names);
    pp_jobject_start pp;
    pp_jmember ~first:true pp "Instruction Name" pp_jstring n;
    pp_jmember pp "Args" (pp_jarray pp_arg) args;
    pp_jobject_end pp in
  let [@ocaml.warning "+4"] instruction pp = function
  | Padd (ir1,ir2,ir3) -> instruction pp "Padd" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pse_add (ir1,ir2) -> instruction pp "Pse_add" [Ireg (Sreg ir1); Ireg (Sreg ir1); Ireg (Sreg ir2)] (* converted to explicit 3-address form for exec2crl compatibility *)
  | Paddc (ir1,ir2,ir3) -> instruction pp "Paddc" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Padde (ir1,ir2,ir3) -> instruction pp "Padde" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Paddze (ir1,ir2) -> instruction pp "Paddze" [Ireg ir1; Ireg ir2]
  | Pallocframe _ -> assert false (* Should not occur *)
  | Pand_ (ir1,ir2,ir3) -> instruction pp "Pand_" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pse_and_ (ir1,ir2) -> instruction pp "Pse_and_" [Ireg (Sreg ir1); Ireg (Sreg ir1); Ireg (Sreg ir2)] (* converted to explicit 3-address form for exec2crl compatibility *)
  | Pse_andc (ir1,ir2) -> instruction pp "Pse_andc" [Ireg (Sreg ir1); Ireg (Sreg ir1); Ireg (Sreg ir2)] (* converted to explicit 3-address form for exec2crl compatibility *)
  | Pandc (ir1,ir2,ir3) -> instruction pp "Pandc" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pbdnz l -> instruction pp "Pbdnz" [ALabel l]
  | Pbf (cr,l) -> instruction pp "Pbf" [Crbit cr; ALabel l]
  | Pbt (cr,l) ->  instruction pp "Pbt" [Crbit cr; ALabel l]
  | Pbtbl (i,lb) -> instruction pp "Pbtbl" ((Ireg i)::(List.map (fun a -> ALabel a) lb))
  | Pcmplw (ir1,ir2) -> instruction pp "Pcmplw" [Ireg ir1; Ireg ir2]
  | Pcmpw (ir1,ir2) -> instruction pp "Pcmpw" [Ireg ir1; Ireg ir2]
  | Pcntlzw (ir1,ir2) -> instruction pp "Pcntlzw" [Ireg ir1; Ireg ir2]
  | Pe_creqv (cr1,cr2,cr3) -> instruction pp "Pe_creqv" [Crbit cr1; Crbit cr2; Crbit cr3]
  | Pe_cror (cr1,cr2,cr3) -> instruction pp "Pe_cror" [Crbit cr1; Crbit cr2; Crbit cr3]
  | Pe_crxor (cr1,cr2,cr3) -> instruction pp "Pe_crxor" [Crbit cr1; Crbit cr2; Crbit cr3]
  | Pdcbf (ir1,ir2) -> instruction pp "Pdcbf" [Ireg ir1; Ireg ir2]
  | Pdcbi (ir1,ir2) -> instruction pp "Pdcbi" [Ireg ir1; Ireg ir2]
  | Pdcbt (n,ir1,ir2) -> instruction pp "Pdcbt" [Constant (Cint n); Ireg ir1; Ireg ir2]
  | Pdcbtst (n,ir1,ir2) -> instruction pp "Pdcbtst" [Constant (Cint n); Ireg ir1; Ireg ir2]
  | Pdcbtls (n,ir1,ir2) ->  instruction pp "Pdcbtls" [Constant (Cint n); Ireg ir1; Ireg ir2]
  | Pdcbz (ir1,ir2) -> instruction pp "Pdcbz" [Ireg ir1; Ireg ir2]
  | Pdivw (ir1,ir2,ir3) -> instruction pp "Pdivw" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pdivwu (ir1,ir2,ir3) -> instruction pp "Pdivwu" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Peqv (ir1,ir2,ir3) -> instruction pp "Peqv" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pextsb (ir1,ir2) -> instruction pp "Pextsb" [Ireg ir1; Ireg ir2]
  | Pextsh (ir1,ir2) -> instruction pp "Pextsh" [Ireg ir1; Ireg ir2]
  | Pfreeframe (c,i) -> assert false (* Should not occur *)
  | Pisel (ir1,ir2,ir3,cr) ->  instruction pp "Pisel" [Ireg ir1; Ireg ir2; Ireg ir3; Crbit cr]
  | Picbi (ir1,ir2) -> instruction pp "Picbi" [Ireg ir1; Ireg ir2]
  | Picbtls (n,ir1,ir2) -> instruction pp "Picbtls" [Constant (Cint n);Ireg ir1; Ireg ir2]
  | Pse_isync -> instruction pp "Pse_isync" []
  | Plbzx (ir1,ir2,ir3) -> instruction pp "Plbzx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Plhax (ir1,ir2,ir3) -> instruction pp "Plhax" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Plhbrx (ir1,ir2,ir3) -> instruction pp "Plhbrx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Plhzx (ir1,ir2,ir3) -> instruction pp "Plhzx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Plwzx (ir1,ir2,ir3)
  | Pflwzx (ir1,ir2,ir3)
  | Plwzx_a (ir1,ir2,ir3) -> instruction pp "Plwzx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Plwbrx (ir1,ir2,ir3) -> instruction pp "Plwbrx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pmfcr ir -> instruction pp "Pmfcr" [Ireg ir]
  | Pmfcrbit (ir,crb) -> assert false (* Should not occur *)
  | Pse_mflr ir -> instruction pp "Pse_mflr" [Ireg (Sreg ir)]
  | Pmfspr(ir, n) -> instruction pp "Pmfspr" [Ireg ir; Constant (Cint n)]
  | Pmtspr(n, ir) -> instruction pp "Pmtspr" [Constant (Cint n); Ireg ir]
  | Pmr (rd, r) -> instruction pp "Pmr" [Ireg rd; Ireg r]
  | Pmullw (ir1,ir2,ir3) -> instruction pp "Pmullw" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pse_mullw (ir1,ir2) -> instruction pp "Pse_mullw" [Ireg (Sreg ir1); Ireg (Sreg ir1); Ireg (Sreg ir2)] (* converted to explicit 3-address form for exec2crl compatibility *)
  | Pmulhw (ir1,ir2,ir3) -> instruction pp "Pmulhw" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pmulhwu (ir1,ir2,ir3) -> instruction pp "Pmulhwu" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pnand (ir1,ir2,ir3) -> instruction pp "Pnand" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pnor (ir1,ir2,ir3)  -> instruction pp "Pnor" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Por (ir1,ir2,ir3) -> instruction pp "Por" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Porc (ir1,ir2,ir3) -> instruction pp "Porc" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pse_or (ir1,ir2) -> instruction pp "Pse_or" [Ireg (Sreg ir1); Ireg (Sreg ir1); Ireg (Sreg ir2)] (* converted to explicit 3-address form for exec2crl compatibility *)
  | Pslw (ir1,ir2,ir3) -> instruction pp "Pslw" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pse_slw (ir1,ir2) -> instruction pp "Pse_slw" [Ireg (Sreg ir1); Ireg (Sreg ir1); Ireg (Sreg ir2)] (* converted to explicit 3-address form for exec2crl compatibility *)
  | Psraw (ir1,ir2,ir3) -> instruction pp "Psraw" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pse_sraw (ir1,ir2) -> instruction pp "Pse_sraw" [Ireg (Sreg ir1); Ireg (Sreg ir1); Ireg (Sreg ir2)] (* converted to explicit 3-address form for exec2crl compatibility *)
  | Psrawi (ir1,ir2,n) -> instruction pp "Psrawi" [Ireg ir1; Ireg ir2; Constant (Cint n)]
  | Psrw (ir1,ir2,ir3) -> instruction pp "Psrw" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pse_srw (ir1,ir2) -> instruction pp "Pse_srw" [Ireg (Sreg ir1); Ireg (Sreg ir1); Ireg (Sreg ir2)] (* converted to explicit 3-address form for exec2crl compatibility *)
  | Pstbx (ir1,ir2,ir3) -> instruction pp "Pstbx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Psthx (ir1,ir2,ir3) -> instruction pp "Psthx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Psthbrx (ir1,ir2,ir3) -> instruction pp "Psthbrx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pstwx (ir1,ir2,ir3)
  | Pfstwx (ir1,ir2,ir3)
  | Pstwx_a (ir1,ir2,ir3) -> instruction pp "Pstwx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pstwux (ir1,ir2,ir3) -> instruction pp "Pstwux" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pstwbrx (ir1,ir2,ir3) -> instruction pp "Pstwbrx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pse_subf (ir1,ir2) -> instruction pp "Pse_subf" [Ireg (Sreg ir1); Ireg (Sreg ir1); Ireg (Sreg ir2)]  (* converted to explicit 3-address form for exec2crl compatibility *)
  | Pse_sub (ir1,ir2) -> instruction pp "Pse_sub" [Ireg (Sreg ir1); Ireg (Sreg ir1); Ireg (Sreg ir2)] (* converted to explicit 3-address form for exec2crl compatibility *)
  | Psubfc (ir1,ir2,ir3) -> instruction pp "Psubfc" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Psubfe (ir1,ir2,ir3) -> instruction pp "Psubfe" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Psubfze (ir1,ir2) -> instruction pp "Psubfze" [Ireg ir1; Ireg ir2]
  | Psync -> instruction pp "Psync" []
  | Pxor (ir1,ir2,ir3) -> instruction pp "Pxor" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Plabel l -> instruction pp "Plabel" [ALabel l]
  | Pbuiltin (ef,args,_) ->
    begin match ef with
      | EF_inline_asm _ ->
        instruction pp "Pinlineasm" [Id];
        Diagnostics.(warning no_loc Inline_asm_sdump "inline assembler is not supported in sdump")
      | EF_annot (kind,txt,targs) ->
        begin match P.to_int kind with
          | 2 ->
            let annots = AisAnnot.json_ais_annot preg_annot "r1" (camlstring_of_coqstring txt) args in
            let annots = List.map (function
                | AisAnnot.String s -> String s
                | AisAnnot.Symbol s -> Atom s
                | AisAnnot.Label _ -> assert false (* should never happen *)
              ) annots in
            instruction pp "Pannot" annots
          | _ -> assert false
        end
      | EF_annot_val _
      | EF_builtin _
      | EF_debug _
      | EF_external _
      | EF_free
      | EF_malloc
      | EF_memcpy _
      | EF_runtime _
      | EF_vload _
      | EF_vstore _ -> assert false
    end
  | Pcfi_adjust _  (* Only debug relevant *)
  | Pcfi_rel_offset _ -> assert false
  (* VLE instructions *)
  | Pse_mr (rd,r1) -> instruction pp "Pse_mr" [Ireg (Sreg rd); Ireg (Sreg r1)]
  | Pse_mtar (rd,r1) -> instruction pp "Pse_mtar" [Ireg (Areg rd); Ireg (Sreg r1)]
  | Pse_mfar (rd,r1) -> instruction pp "Pse_mfar" [Ireg (Sreg rd); Ireg (Areg r1)]
  | Pe_and2i_ (rd,c) -> instruction pp "Pe_and2i_" [Ireg rd; Ireg rd; Constant c] (* converted to explicit 3-address form for exec2crl compatibility *)
  | Pe_and2is_ (rd,c) -> instruction pp "Pe_and2is_" [Ireg rd; Ireg rd; Constant c] (* converted to explicit 3-address form for exec2crl compatibility *)
  | Pe_add16i (ir1,ir2,c) -> instruction pp "Pe_add16i" [Ireg ir1; Ireg ir2; Constant c]
  | Pe_add2is (rd,c) -> instruction pp "Pe_add2is" [Ireg rd; Ireg rd; Constant c] (* converted to explicit 3-address form for exec2crl compatibility *)
  | Pse_addi (rd,c) -> instruction pp "Pse_addi" [Ireg (Sreg rd); Ireg (Sreg rd); Constant (Cint c)] (* converted to explicit 3-address form for exec2crl compatibility *)
  | Pe_addic  (ir1,ir2,c) -> instruction pp "Pe_addic" [Ireg ir1; Ireg ir2; Constant (Cint c)]
  | Pe_b lbl -> instruction pp "Pe_b" [ALabel lbl]
  | Pe_bl (i, sg) -> instruction pp "Pe_bl" [Atom i]
  | Pse_blr -> instruction pp "Pse_blr" []
  | Pse_bctr sg -> instruction pp "Pse_bctr" []
  | Pse_bctrl sg -> instruction pp "Pse_bctrl" []
  | Pe_bs (i,s) -> instruction pp "Pe_bs" [Atom i]
  | Pse_cmp (rd,r1) -> instruction pp "Pse_cmp" [Ireg (Sreg rd); Ireg (Sreg r1)]
  | Pe_cmp16i (rd,c) -> instruction pp "Pe_cmp16i" [Ireg rd; Constant c]
  | Pse_cmpi (rd,c) -> instruction pp "Pse_cmpi" [Ireg (Sreg rd); Constant (Cint c)]
  | Pse_cmpl (rd,r1) -> instruction pp "Pse_cmpl" [Ireg (Sreg rd); Ireg (Sreg r1)]
  | Pe_cmpl16i (rd,c) -> instruction pp "Pe_cmpl16i" [Ireg rd; Constant c]
  | Pse_extsb rd -> instruction pp "Pse_extsb" [Ireg (Sreg rd); Ireg (Sreg rd)] (* converted to explicit 2-address form for exec2crl compatibility *)
  | Pse_extsh rd -> instruction pp "Pse_extsh" [Ireg (Sreg rd); Ireg (Sreg rd)] (* converted to explicit 2-address form for exec2crl compatibility *)
  | Pse_bgeni (rd,c) -> instruction pp "Pse_bgeni" [Ireg (Sreg rd); Constant (Cint c)]
  | Pse_li (rd,c) -> instruction pp "Pse_li" [Ireg (Sreg rd); Constant (Cint c)]
  | Pe_li (rd,c) -> instruction pp "Pe_li" [Ireg rd; Constant c]
  | Pe_lis (rd,c) -> instruction pp "Pe_lis" [Ireg rd; Constant c]
  | Pe_lbz (ir1,c,ir2) -> instruction pp "Pe_lbz" [Ireg ir1;Constant c; Ireg ir2]
  | Pse_lbz (ir1,c,ir2) -> instruction pp "Pse_lbz" [Ireg (Sreg ir1);Constant (Cint c); Ireg (Sreg ir2)]
  | Pe_lha (ir1,c,ir2) -> instruction pp "Pe_lha" [Ireg ir1;Constant c; Ireg ir2]
  | Pe_lhz (ir1,c,ir2) -> instruction pp "Pe_lhz" [Ireg ir1;Constant c; Ireg ir2]
  | Pse_lhz (ir1,c,ir2) -> instruction pp "Pse_lhz" [Ireg (Sreg ir1);Constant (Cint c); Ireg (Sreg ir2)]
  | Pe_lwz (ir1,c,ir2)
  | Pfe_lwz (ir1,c,ir2)
  | Pe_lwz_a (ir1,c,ir2) -> instruction pp "Pe_lwz" [Ireg ir1;Constant c; Ireg ir2]
  | Pe_lwzu (ir1,c,ir2) -> instruction pp "Pe_lwzu" [Ireg ir1;Constant c; Ireg ir2]
  | Pse_lwz (ir1,c,ir2)
  | Pfse_lwz (ir1,c,ir2)
  | Pse_lwz_a (ir1,c,ir2) -> instruction pp "Pse_lwz" [Ireg (Sreg ir1);Constant (Cint c); Ireg (Sreg ir2)]
  | Pse_mtctr ir -> instruction pp "Pse_mtctr" [Ireg (Sreg ir)]
  | Pse_mtlr ir -> instruction pp "Pse_mtlr" [Ireg (Sreg ir)]
  | Pe_or2i (rd,c) -> instruction pp "Pe_or2i" [Ireg rd; Ireg rd; Constant c] (* converted to explicit 3-address form for exec2crl compatibility *)
  | Pe_or2is (rd,c) -> instruction pp "Pe_or2is" [Ireg rd; Ireg rd; Constant c] (* converted to explicit 3-address form for exec2crl compatibility *)
  | Pe_rlwinm (ir1,ir2,ic1,ic2) -> instruction pp "Pe_rlwinm" [Ireg ir1; Ireg ir2; Constant (Cint ic1); Constant (Cint ic2)]
  | Pe_rlwimi  (ir1,ir2,ic1,ic2) ->instruction pp "Pe_rlwimi" [Ireg ir1; Ireg ir2; Constant (Cint ic1); Constant (Cint ic2)]
  | Pse_srawi (rd,ic) -> instruction pp "Pse_srawi" [Ireg (Sreg rd); Ireg (Sreg rd); Constant (Cint ic)] (* converted to explicit 3-address form for exec2crl compatibility *)
  | Pe_stb (ir1,c,ir2) -> instruction pp "Pe_stb" [Ireg ir1;Constant c; Ireg ir2]
  | Pse_stb (ir1,c,ir2) -> instruction pp "Pse_stb" [Ireg (Sreg ir1);Constant (Cint c); Ireg (Sreg ir2)]
  | Pe_sth (ir1,c,ir2) -> instruction pp "Pe_sth" [Ireg ir1;Constant c; Ireg ir2]
  | Pse_sth (ir1,c,ir2) -> instruction pp "Pse_sth" [Ireg (Sreg ir1);Constant (Cint c); Ireg (Sreg ir2)]
  | Pe_stw (ir1,c,ir2)
  | Pfe_stw (ir1,c,ir2)
  | Pe_stw_a (ir1,c,ir2) -> instruction pp "Pe_stw" [Ireg ir1;Constant c; Ireg ir2]
  | Pe_stwu (ir1,c,ir2) -> instruction pp "Pe_stwu" [Ireg ir1;Constant c; Ireg ir2]
  | Pse_stw (ir1,c,ir2)
  | Pfse_stw (ir1,c,ir2)
  | Pse_stw_a (ir1,c,ir2) -> instruction pp "Pse_stw" [Ireg (Sreg ir1);Constant (Cint c); Ireg (Sreg ir2)]
  | Pe_subfic (ir1,ir2,c) -> instruction pp "Pe_subfic" [Ireg ir1; Ireg ir2; Constant (Cint c)]
  | Pse_subi (rd,c) -> instruction pp "Pse_subi" [Ireg (Sreg rd); Ireg (Sreg rd); Constant (Cint c)] (* converted to explicit 3-address form for exec2crl compatibility *)
  | Pe_xori (ir1,ir2,c) -> instruction pp "Pe_xori" [Ireg ir1; Ireg ir2; Constant (Cint c)]
  | Pefsabs (ir1, ir2) -> instruction pp "Pefsabs" [Ireg ir1; Ireg ir2]
  | Pefsadd (ir1, ir2, ir3) -> instruction pp "Pefsadd" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pefsdiv (ir1, ir2, ir3) -> instruction pp "Pefsdiv" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pefsmul (ir1, ir2, ir3) -> instruction pp "Pefsmul" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pefsneg (ir1, ir2) -> instruction pp "Pefsneg" [Ireg ir1; Ireg ir2]
  | Pefssub (ir1, ir2, ir3) -> instruction pp "Pefssub" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Plfis _ -> assert false (* Removed in Asmexpand *)
  | Pefscfsi (ir1, ir2) -> instruction pp "Pefscfsi" [Ireg ir1; Ireg ir2]
  | Pefscfui (ir1, ir2) -> instruction pp "Pefscfui" [Ireg ir1; Ireg ir2]
  | Pefsctsi (ir1, ir2) -> instruction pp "Pefsctsi" [Ireg ir1; Ireg ir2]
  | Pefsctui (ir1, ir2) -> instruction pp "Pefsctui" [Ireg ir1; Ireg ir2]
  | Pefscmpeq (ir1, ir2) -> instruction pp "Pefscmpeq" [CondReg 0; Ireg ir1; Ireg ir2]
  | Pefscmpgt (ir1, ir2) -> instruction pp "Pefscmpgt" [CondReg 1; Ireg ir1; Ireg ir2]
  | Pefscmplt (ir1, ir2) -> instruction pp "Pefscmplt" [CondReg 1; Ireg ir1; Ireg ir2]
  in (* Only debug relevant *)
  pp_jarray instruction pp ic
(*- #End *)

(*- E_COMPCERT_CODE_AsmToJson_destination_001 *)
(*- #Justify_Derived "Variable for global state" *)
let destination : string option ref = ref None
(*- #End *)

(*- E_COMPCERT_CODE_AsmToJson_sdump_folder_001 *)
(*- #Justify_Derived "Variable for global state" *)
let sdump_folder : string ref = ref ""
(*- #End *)

(*- E_COMPCERT_CODE_AsmToJson_print_if_001 *)
(*- #Link_to E_COMPCERT_TR_Function_DRIVER_001 *)
let print_if prog sourcename =
  match !destination with
  | None -> ()
  | Some f ->
    let f = Filename.concat !sdump_folder f in
    let oc = open_out_bin f in
    pp_ast oc pp_instructions prog sourcename;
    close_out oc
(*- #End *)

(*- E_COMPCERT_CODE_AsmToJson_pp_mnemonics_001 *)
(*- #Justify_Derived "Utility function" *)
let pp_mnemonics pp =
  pp_mnemonics pp (StringSet.elements mnemonic_names)
(*- #End *)
