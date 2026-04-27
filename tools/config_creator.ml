(*- E_COMPCERT_DEACTIVATED_CODE_config_creator_001 *)
(*- #Condition "Code is not compiled into CompCert." *)
(*- #Justification "Code is not part of CompCert" *)

(*- E_COMPCERT_CODE_config_creator_001 *)
(*- #Justify_Derived "Module config_creator.ml is an external helper tool. It is part of the build system and is not part of CompCert." *)

open Printf

(* Module to create compcert.config module from Makefile.config & VERSION files. *)

let _ =
  let config = Kv_parser.parse_file "Makefile.config" in
  let version_config = Kv_parser.parse_file "VERSION" in
  printf "# CompCert configuration parameters\n";
  printf "COMPCERT_ARCH=%s\n" (Kv_parser.get "ARCH" config);
  printf "COMPCERT_MODEL=%s\n" (Kv_parser.get "MODEL" config);
  printf "COMPCERT_ABI=%s\n" (Kv_parser.get "ABI" config);
  printf "COMPCERT_ENDIANNESS=%s\n" (Kv_parser.get "ENDIANNESS" config);
  printf "COMPCERT_BITSIZE=%s\n" (Kv_parser.get "BITSIZE" config);
  printf "COMPCERT_SYSTEM=%s\n" (Kv_parser.get "SYSTEM" config);
  printf "COMPCERT_VERSION=%s\n" (Kv_parser.get "version" version_config);
  printf "COMPCERT_BUILDNR=%s\n" (Kv_parser.get "buildnr" version_config);
  printf "COMPCERT_TAG=%s\n" (Kv_parser.get "tag" version_config);
  printf "COMPCERT_BRANCH=%s\n" (Kv_parser.get "branch" version_config)

(*- #End *)

(*- #End_DEACTIVATED_CODE *)
