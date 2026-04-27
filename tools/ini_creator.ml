(*- E_COMPCERT_DEACTIVATED_CODE_ini_creator_001 *)
(*- #Condition "Code is not compiled into CompCert." *)
(*- #Justification "Code is not part of CompCert" *)

(*- E_COMPCERT_CODE_ini_creator_001 *)
(*- #Justify_Derived "Module ini_creator.ml is an external helper tool. It is part of the build system and is not part of CompCert." *)

open Printf

(* Module to create compcert.ini module from given Makefile.config file. *)

let usage_msg = 
  "Usage: dune exec tools/ini_creator.exe Makefile.config"

let input = ref None

let anon_fun filename = if Option.is_none !input
  then input := Some filename else raise (Arg.Bad ("Unexpected positional argument: "^filename))

let _ = 
  Arg.parse [] anon_fun usage_msg;
  if Option.is_none !input then invalid_arg "Need path to Makefile.config as argument."

let _ =
  let config = Kv_parser.parse_file (Option.get !input) in
  printf "stdlib_path=%s\n" (Kv_parser.get "RELLIBDIR" config);
  printf "prepro=%s\n" (Kv_parser.get "CPREPRO" config);
  printf "linker=%s\n" (Kv_parser.get "CLINKER" config);
  printf "asm=%s\n" (Kv_parser.get "CASM" config);
  printf "prepro_options=%s\n" (Kv_parser.get "CPREPRO_OPTIONS" config);
  printf "asm_options=%s\n" (Kv_parser.get "CASM_OPTIONS" config);
  printf "linker_options=%s\n" (Kv_parser.get "CLINKER_OPTIONS" config);
  printf "arch=%s\n" (Kv_parser.get "ARCH" config);
  printf "model=%s\n" (Kv_parser.get "MODEL" config);
  printf "abi=%s\n" (Kv_parser.get "ABI" config);
  printf "endianness=%s\n" (Kv_parser.get "ENDIANNESS" config);
  printf "system=%s\n" (Kv_parser.get "SYSTEM" config);
  printf "has_runtime_lib=%s\n" (Kv_parser.get "HAS_RUNTIME_LIB" config);
  printf "has_standard_headers=%s\n" (Kv_parser.get "HAS_STANDARD_HEADERS" config);
  printf "has_double=%s\n" (Kv_parser.get "HAS_DOUBLE" config);
  printf "asm_supports_cfi=%s\n" (Kv_parser.get "ASM_SUPPORTS_CFI" config);
  printf "response_file_style=%s\n" (Kv_parser.get "RESPONSEFILE" config);
  printf "pic_supported=%s\n" (Kv_parser.get "PIC_SUPPORTED" config)

(*- #End *)

(*- #End_DEACTIVATED_CODE *)
