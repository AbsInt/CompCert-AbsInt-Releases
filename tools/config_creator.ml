(*- E_COMPCERT_DEACTIVATED_CODE_config_creator_001 *)
(*- #Condition "Code is not compiled into CompCert." *)
(*- #Justification "Code is not part of CompCert" *)

(*- E_COMPCERT_CODE_config_creator_001 *)
(*- #Justify_Derived "Module config_creator.ml is an external helper tool. It is part of the build system and is not part of CompCert." *)

open Printf
open MakefileConfig
open Version

let _ = printf "# CompCert configuration parameters\n";
        printf "COMPCERT_ARCH=%s\n" arch;
        printf "COMPCERT_MODEL=%s\n" model;
        printf "COMPCERT_ABI=%s\n" abi;
        printf "COMPCERT_ENDIANNESS=%s\n" endianness;
        printf "COMPCERT_BITSIZE=%s\n" bitsize;
        printf "COMPCERT_SYSTEM=%s\n" system;
        printf "COMPCERT_VERSION=%s\n" version;
        printf "COMPCERT_BUILDNR=%s\n" buildnr;
        printf "COMPCERT_TAG=%s\n" tag;
        printf "COMPCERT_BRANCH=%s\n" branch;

(*- #End *)

(*- #End_DEACTIVATED_CODE *)
