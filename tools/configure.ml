(*- E_COMPCERT_DEACTIVATED_CODE_configure_001 *)
(*- #Condition "Code is not compiled into CompCert." *)
(*- #Justification "Code is not part of CompCert" *)

(*- E_COMPCERT_CODE_configure_001 *)
(*- #Justify_Derived "Module configure.ml is an external helper tool. It is part of the build system and is not part of CompCert." *)

open Printf
open Util

let prefix = ref (if Sys.unix
                  then Filename.(concat "usr" "local")
                  else Filename.current_dir_name)
let bindir = ref Filename.(concat !prefix "bin")
let libdir = ref Filename.(concat !prefix (concat "lib" "compcert"))
let mandir = ref Filename.(concat !prefix (concat "share" "man"))
let sharedir = ref "" (* determined later based on !bindir and -sharedir option *)
let coqdevdir = ref Filename.(concat !prefix (concat "lib" (concat "compcert" "coq")))
let toolprefix = ref ""
let target = ref ""
let has_runtime_lib = ref true
let has_standard_headers = ref true
let has_double = ref true
let install_coqdev = ref false
let ignore_coq_version = ref false
let ignore_ocaml_version = ref false

(* Generate placeholder values for later use by the compcert-configedit program. *)
let configedit_defaults = ref false
let output = ref "Makefile.config"
let print_help = ref false


let usage_msg = {|
Usage: dune exec tools/configure.exe -- [options] target
For help on options and targets, do: dune exec tools/configure.exe -- -help
|}

let help_msg = {|Usage: dune exec tools/configure.exe -- [options] target

Supported targets:
  ppc-eabi             (PowerPC, EABI with GNU/Unix tools)
  ppc-eabi-diab        (PowerPC, EABI with Diab tools)
  ppc-linux            (PowerPC, Linux)
  ppcvle-eabi          (PowerPC, EABI with GNU/Unix tools and vle instructions)
  arm-eabi             (ARM, EABI, little endian)
  arm-eabihf           (ARM, EABI using hardware FP registers, little endian)
  arm-linux            (ARM, EABI using hardware FP registers, little endian)
  armeb-eabi           (ARM, EABI, big endian)
  armeb-eabihf         (ARM, EABI using hardware FP registers, big endian)
  armeb-linux          (ARM, EABI using hardware FP registers, big endian)
  x86_32-linux         (x86 32 bits, Linux)
  x86_32-bsd           (x86 32 bits, BSD)
  x86_64-linux         (x86 64 bits, Linux)
  x86_64-bsd           (x86 64 bits, BSD)
  x86_64-macos         (x86 64 bits, MacOS X)
  x86_64-cygwin        (x86 64 bits, Cygwin environment under Windows)
  rv32-linux           (RISC-V 32 bits, Linux)
  rv64-linux           (RISC-V 64 bits, Linux)
  aarch64-linux        (AArch64, i.e. ARMv8 in 64-bit mode, Linux)
  aarch64-macos        (AArch64, i.e. Apple silicon, MacOS)
  peaktop              (Peaktop 32 bits)
  tricore-eabi         (TriCore 32 bits)
  tricore-eabi-llvm    (TriCore 32 bits with llvm based toolchain)
  manual               (edit configuration file by hand)

For x86 targets, the "x86_32-" prefix can also be written "ia32-" or "i386-".
For x86 targets, the "x86_64-" prefix can also be written "amd64-".
For AArch64 targets, the "aarch64-" prefix can also be written "arm64-".
For RISC-V targets, the "rv32-" or "rv64-" prefix can also be written "riscv32-" or "riscv64-".

For PowerPC targets, the "ppc-" prefix can be refined into:
  ppc64-               PowerPC 64 bits
  e5500-               Freescale e5500 core (PowerPC 64 bit, EREF extensions)

For ARM targets, the "arm-" or "armeb-" prefix can be refined into:
  armv6-               ARMv6   + VFPv2       (Thumb mode not supported)
  armv6t2-             ARMv6T2 + VFPv2
  armv7a-              ARMv7-A + VFPv3-d16   (default for arm-)
  armv7r-              ARMv7-R + VFPv3-d16
  armv7m-              ARMv7-M + VFPv3-d16

  armebv6-             ARMv6   + VFPv2       (Thumb mode not supported)
  armebv6t2-           ARMv6T2 + VFPv2
  armebv7a-            ARMv7-A + VFPv3-d16   (default for armeb-)
  armebv7r-            ARMv7-R + VFPv3-d16
  armebv7m-            ARMv7-M + VFPv3-d16

Options:
  -prefix <dir>        Install in <dir>/bin and <dir>/lib/compcert
  -bindir <dir>        Install binaries in <dir>
  -libdir <dir>        Install libraries in <dir>
  -sharedir <dir>      Install configuration file in <dir>
  -mandir <dir>        Install man pages in <dir>
  -coqdevdir <dir>     Install Coq development (.vo files) in <dir>
  -toolprefix <pref>   Prefix names of tools ("gcc", etc) with <pref>
  -no-runtime-lib      Do not compile nor install the runtime support library
  -no-standard-headers Do not install nor use the standard .h headers
  -install-coqdev      Also install the Coq development
  -ignore-coq-version  Accept to use experimental or unsupported versions of Coq
  -ignore-ocaml-version Accept to use experimental or unsupported versions of OCaml
|}

(* Parse Command-Line Arguments *)

let anon_fun input = if !target = "" then
    target := input else raise (Arg.Bad "Specify only one target.")

let speclist = [
  ("-o", Arg.Set_string output, "Output configuration to <file>. Default: "^(!output));
  ("-prefix", Arg.Set_string prefix, "Install in <dir>/bin and <dir>/lib/compcert");
  ("-bindir", Arg.Set_string bindir, "Install binaries in <dir>");
  ("-libdir", Arg.Set_string libdir, "Install libraries in <dir>");
  ("-mandir", Arg.Set_string mandir, "Install man pages in <dir>");
  ("-sharedir", Arg.Set_string sharedir, "Install configuration file in <dir>");
  ("-coqdevdir", Arg.Tuple [
      Arg.Set_string coqdevdir;
      Arg.Set install_coqdev
    ], "Install Coq development (.vo files) in <dir>");
  ("-toolprefix", Arg.Set_string toolprefix, "Prefix names of tools (\"gcc\", etc) with <pref>");
  ("-no-runtime-lib", Arg.Clear has_runtime_lib, "Do not compile nor install the runtime support library");
  ("-no-standard-headers", Arg.Clear has_standard_headers, "Do not install nor use the standard .h headers");
  ("-ignore-coq-version", Arg.Set ignore_coq_version, "Accept to use experimental or unsupported versions of Coq");
  ("-ignore-ocaml-version", Arg.Set ignore_ocaml_version, "Accept to use experimental or unsupported versions of OCaml");
  ("-install-coqdev", Arg.Set install_coqdev, "Also install the Coq development");
  ("-install-coq-dev", Arg.Set install_coqdev, "Also install the Coq development");
  ("-set-configedit-defaults", Arg.Set configedit_defaults, "Set tool prefix to '%TOOLPATH%' and library dir to '%LIBPATH%'. The arguments -toolprefix and -libdir are ignored.");
  ("-help", Arg.Set print_help, "Display this list of options");
]

let _ =
  (* Remove Leftover Makefile.config (if any)  (GPR#244) *)
  file_delete "Makefile.config";
  Arg.parse speclist anon_fun usage_msg;
  if !print_help then begin
    print_string help_msg;
    exit 0
  end

(* Quits configure process *)
let invalid_input reason =
  eprintf "Error: %s\n" reason;
  eprintf "%s" usage_msg;
  exit 2

let rec target_starts_with choices = match choices with
  | [] -> false
  | prefix::choices -> (String.starts_with ~prefix !target) || (target_starts_with choices)

(* Extract Architecture, Model and Default Endianness *)
let (arch, model, endianess, bitsize) =
  if target_starts_with [ "arm-" ; "armv7a-" ] then
    "arm", "armv7a", "little", 32
  else if target_starts_with [ "armv6-" ] then
    "arm", "armv6", "little", 32
  else if target_starts_with [ "armv6t2-" ] then
    "arm", "armv6t2", "little", 32
  else if target_starts_with [ "armv7r-" ] then
    "arm", "armv7r", "little", 32
  else if target_starts_with [ "armv7m-" ] then
    "arm", "armv7m", "little", 32
  else if target_starts_with [ "armv7m+nofp.dp-" ] then
    (has_double := false; "arm", "armv7m", "little", 32)
  else if target_starts_with [ "armeb-" ; "armebv7a" ] then
    "arm", "armv7a", "big", 32
  else if target_starts_with [ "armebv6-" ] then
    "arm", "armv6", "big", 32
  else if target_starts_with [ "armebv6t2-" ] then
    "arm", "armv6t2", "big", 32
  else if target_starts_with [ "armebv7r-" ] then
    "arm", "armv7r", "big", 32
  else if target_starts_with [ "armebv7m-" ] then
    "arm", "armv7m", "big", 32
  else if target_starts_with [ "x86_32-" ; "ia32-" ; "i386-" ] then
    "x86", "32sse2", "little", 32
  else if target_starts_with [ "x86_64-" ; "amd64-" ] then
    "x86", "64", "little", 64
  else if target_starts_with [ "powerpc-" ; "ppc-" ] then
    "powerpc", "ppc32", "big", 32
  else if target_starts_with [ "powerpc64-" ; "ppc64-" ] then
    "powerpc", "ppc64", "big", 32
  else if target_starts_with [ "e5500-" ] then
    "powerpc", "e5500", "big", 32
  else if target_starts_with [ "powerpcvle-" ; "ppcvle-" ] then
    (has_double := false; "powerpc_vle", "ppc32", "big", 32)
  else if target_starts_with [ "riscv32-" ; "rv32-" ] then
    "riscV", "32", "little", 32
  else if target_starts_with [ "riscv64-" ; "rv64-" ] then
    "riscV", "64", "little", 64
  else if target_starts_with [ "aarch64-" ; "arm64-" ] then
    "aarch64", "default", "little", 64
  else if target_starts_with [ "tricore-" ]  then
    (has_double := false; "tricore", "tc161", "little", 32)
  else if !target = "manual" then
    ("", "", "", 0)
  else if !target = "" then
    invalid_input "no target architecture specified"
  else
    invalid_input "unkown target architecture."

(* Take everything after the first dash. *)
let target_suffix =
  let sep = '-' in
  let components = String.split_on_char sep !target in
  String.concat (String.make 1 sep) (List.tl components)

(* Default configuration for compcert-configedit. *)
let _ = if !configedit_defaults then begin
  toolprefix := "%TOOLPATH%";
  libdir := "%LIBPATH%";
end

(* Per-target configuration
   We start with reasonable defaults,
   then redefine the required parameters for each target,
   then check for missing parameters and derive values for them. *)
let asm_supports_cfi = ref None
let cc = ref (!toolprefix ^ "gcc")
let cc_options = ref ""
let casm = ref (!toolprefix ^ "gcc")
let casm_options = ref "-c"
let casmruntime = ref ""
let clinker = ref (!toolprefix ^ "gcc")
let clinker_options = ref ""
let clinker_needs_no_pie = ref true
let clinker_needs_nobtcfi = ref false
let cprepro = ref (!toolprefix ^ "gcc")
let cprepro_options = ref "-E"
let archiver = ref (!toolprefix ^ "ar rcs")
let libmath = ref "-lm"
let responsefile = ref "gnu"
let pic_supported = ref false
let system = ref None
let abi = ref None

let _ = match arch with

  (* ARM Target Configuration *)
  | "arm" -> begin
      begin match target_suffix with
      | "eabi" ->
          abi := Some "eabi";
      | "eabihf" | "linux" | "hf" | "hardfloat" ->
          abi := Some "hardfloat";
      | _ ->
          invalid_input (sprintf "invalid eabi/system '%s' for architecture ARM." target_suffix);
      end;

      cprepro_options := "-U__GNUC__ '-D__REDIRECT(name,proto,alias)=name proto' '-D__REDIRECT_NTH(name,proto,alias)=name proto' -E";
      system := Some "linux";
  end

  (* PowerPC Target Configuration *)
  | "powerpc" -> begin
      begin match target_suffix with
      | "linux" ->
          abi := Some "linux";
      | "eabi" | "eabi-diab" ->
          abi := Some "eabi";
      | _ ->
          invalid_input (sprintf "invalid eabi/system '%s' for architecture PowerPC." target_suffix);
      end;

      begin match target_suffix with
      | "eabi-diab" -> begin
          asm_supports_cfi := Some false;
          casm := !toolprefix ^ "das";
          casm_options := "-Xalign-value";
          cc := !toolprefix ^ "dcc";
          clinker_needs_no_pie := false;
          clinker := !toolprefix ^ "dcc";
          cprepro := !toolprefix ^ "dcc";
          cprepro_options := "-E -D__GNUC__ -D__CHAR_UNSIGNED__";
          archiver := !toolprefix ^ "dar -q";
          libmath := "-lm";
          system := Some "diab";
          responsefile := "diab";
      end
      | _ ->
          casmruntime := !toolprefix ^ "gcc -c -Wa,-mregnames";
          cprepro_options := "-U__GNUC__ -E";
          system := Some "linux";
      end
  end

  (* PowerPC VLE Target Configuration *)
  | "powerpc_vle" -> begin
      begin match target_suffix with
      | "linux" ->
          abi := Some "linux";
      | "eabi" | "eabi-diab" ->
          abi := Some "eabi";
      | _ ->
          invalid_input (sprintf "invalid eabi/system '%s' for architecture PowerPC VLE." target_suffix);
      end;

      begin match target_suffix with
      | "eabi-diab" -> begin
          asm_supports_cfi := Some false;
          casm := !toolprefix ^ "das";
          casm_options := "-Xalign-value";
          cc := !toolprefix ^ "dcc";
          clinker_needs_no_pie := false;
          clinker := !toolprefix ^ "dcc";
          cprepro := !toolprefix ^ "dcc";
          cprepro_options := "-E -D__GNUC__ -D__CHAR_UNSIGNED__";
          archiver := !toolprefix ^ "dar -q";
          libmath := "-lm";
          system := Some "diab";
          responsefile := "diab";
      end
      | _ ->
          casmruntime := !toolprefix ^ "gcc -c -Wa,-mregnames";
          cprepro_options := "-U__GNUC__ -E";
          system := Some "linux";
      end
  end

  (* x86 (32 bits) Target Configuration *)
  | "x86" when bitsize = 32 -> begin
      match target_suffix with
      | "bsd" -> begin
          abi := Some "standard";
          cc := !toolprefix ^ "cc";
          cc_options := "-m32";
          casm := !toolprefix ^ "cc";
          casm_options := "-m32 -c";
          clinker := !toolprefix ^ "cc";
          clinker_options := "-m32";
          cprepro := !toolprefix ^ "cc";
          cprepro_options := "-m32 -U__GNUC__ -E";
          system := Some "bsd";
      end
      | "linux" -> begin
          abi := Some "standard";
          cc_options := "-m32";
          casm_options := "-m32 -c";
          clinker_options := "-m32";
          cprepro_options := "-m32 -U__GNUC__ -E";
          system := Some "linux";
      end
      | _ ->
          invalid_input (sprintf "invalid eabi/system '%s' for architecture IA32/X86_32." target_suffix);
  end

  (* x86 (64 bits) Target Configuration *)
  | "x86" when bitsize = 64 -> begin
      match target_suffix with
      | "bsd" -> begin
          abi := Some "standard";
          cc := !toolprefix ^ "cc";
          cc_options := "-m64";
          casm := !toolprefix ^ "cc";
          casm_options := "-m64 -c";
          clinker := !toolprefix ^ "cc";
          clinker_options := "-m64";
          clinker_needs_no_pie := false;
          cprepro := !toolprefix ^ "cc";
          cprepro_options := "-m64 -U__GNUC__ -U__SIZEOF_INT128__ -E";
          system := Some "bsd";
          pic_supported := true;
          clinker_needs_nobtcfi := true;
      end
      | "linux" -> begin
          abi := Some "standard";
          cc_options := "-m64";
          casm_options := "-m64 -c";
          clinker_options := "-m64";
          clinker_needs_no_pie := false;
          cprepro_options := "-m64 -U__GNUC__ -U__SIZEOF_INT128__ -E";
          system := Some "linux";
          pic_supported := true;
      end
      | "macos" | "macosx" -> begin
          abi := Some "macos";
          cc_options := "-arch x86_64";
          casm_options := "-arch x86_64 -c";
          clinker_options := "-arch x86_64";
          clinker_needs_no_pie := false;
          (* a.d. TODO check if the double backslash is correct like this. *)
          cprepro_options := "-arch x86_64 -U__GNUC__ -U__SIZEOF_INT128__ -U__clang__ -U__BLOCKS__ '-D__attribute__(x)=' '-D__asm(x)=' '-D_Nullable=' '-D_Nonnull=' '-D__DARWIN_OS_INLINE=static inline' -Wno-\\#warnings -E";
          libmath := "";
          system := Some "macos";
          pic_supported := true;
      end
      | "cygwin" -> begin
          abi := Some "standard";
          cc_options := "-m64";
          casm_options := "-m64 -c";
          clinker_options := "-m64";
          cprepro_options := "-m64 -U__GNUC__ -U__SIZEOF_INT128__ '-D__attribute__(x)=' -E";
          system := Some "cygwin";
      end
      | _ ->
          invalid_input (sprintf "invalid eabi/system '%s' for architecture X86_64." target_suffix);
  end

  (* RISC-V Target Configuration *)
  | "riscV" -> begin
      let model_options =
        if model = "64" then
          "-mabi=lp64d"
        else
          "-mabi=ilp32d"
      in
      abi := Some "standard";
      cc_options := model_options;
      casm_options := model_options ^ " -c";
      clinker_options := model_options;
      clinker_needs_no_pie := false;
      cprepro_options := model_options ^ " -U__GNUC__ -E";
      system := Some "linux";
      pic_supported := true;
  end

  (* AArch64 (ARMv8 64 bits) Target Configuration *)
  | "aarch64" -> begin
      match target_suffix with
      | "linux" -> begin
          abi := Some "standard";
          cprepro_options := "-U__GNUC__ -E";
          system := Some "linux";
          pic_supported := true;
      end
      | "macos" | "macosx" -> begin
          abi := Some "apple";
          casm := !toolprefix ^ "cc";
          casm_options := "-c -arch arm64";
          cc := !toolprefix ^ "cc -arch arm64";
          clinker := !toolprefix ^ "cc";
          clinker_needs_no_pie := false;
          cprepro := !toolprefix ^ "cc";
          cprepro_options := "-arch arm64 -U__GNUC__ -U__clang__ -U__BLOCKS__ '-D__attribute__(x)=' '-D__asm(x)=' '-D_Nullable=' '-D_Nonnull=' '-D__DARWIN_OS_INLINE=static inline' -Wno-\\#warnings -Wno-builtin-macro-redefined -E";
          libmath := "";
          system := Some "macos";
          pic_supported := true;
      end
      | _ ->
          invalid_input (sprintf "invalid eabi/system '%s' for architecture AArch64." target_suffix);
  end

  (* TriCore Target Configuration *)
  | "tricore" -> begin
      begin match target_suffix with
      | "eabi-llvm" -> begin
          cc := !toolprefix ^ "clang";
          casm := !toolprefix ^ "clang";
          casm_options := "-march=tc162 -c";
          clinker := !toolprefix ^ "clang";
          clinker_options := "-march=tc162";
          cprepro := !toolprefix ^ "clang";
          cprepro_options := "-march=tc162 -E -U__GNUC__";
          archiver := !toolprefix ^ "llvm-ar rcs";
      end
      | "eabi" -> begin
          cc := !toolprefix ^ "gcc";
          casm := !toolprefix ^ "gcc";
          casm_options := "-mtc161 -c";
          clinker := !toolprefix ^ "gcc";
          clinker_options := "-mtc161";
          cprepro := !toolprefix ^ "gcc";
          cprepro_options := "-mtc161 -E -U__GNUC__";
      end
      | _ ->
          invalid_input (sprintf "invalid eabi/system '%s' for architecture TriCore." target_suffix);
      end;

      abi := Some "eabi";
      asm_supports_cfi := Some false;
      system := Some "tricore";
  end
  | "" when !target = "manual" -> begin end
  | _ -> begin
      invalid_input (sprintf "somehow got invalid system with architecture %s." arch);
  end

(* Finalize Target Configuration *)
let _ = if !casmruntime = "" then casmruntime := !casm ^ " " ^ !casm_options

(* Invoke a C compiler, e.g. to check for availability of command-line options *)
let testcompiler cc_cmd extra_args =
  let tmpsrc =
    let (tmpsrc,oc) = open_tmp_file "compcert-configure-" ".c" in
    let content = "
int main (void) {
  return 0;
}" in
    output_string oc content;
    close_out oc;
    tmpsrc in
  let res = run_command cc_cmd ((String.split_on_char ' ' extra_args) @ ["-o"; Filename.null; tmpsrc]) in
  let re_error = {|\(unknown\|unsupported\|unrecognized\|ignored\)|} in
  let has_error = grepi re_error res.stderr in
  (* OK and no error was logged *)
  res.exit_code = 0 && not has_error

(* Test Assembler Support for CFI Directives *)
(* If the option has not been defined above and we are in manual mode or setting default values for compcert-configedit,
     the assembler is not determined yet so we set it to false by default.
   Otherwise try to deduce it from the configured assembler. *)
let _ = if !asm_supports_cfi = None then begin
  if (!target = "manual") || !configedit_defaults then begin
    asm_supports_cfi := Some false
  end else begin
    printf "Testing assembler support for CFI directives... ";
    let tmpsrc =
      let (asm_file, oc) = open_tmp_file "compcert-configure-" ".s" in
      let content = {|testfun:
    .file 1 "testfun.c"
    .loc 1 1
    .cfi_startproc
    .cfi_adjust_cfa_offset 16
    .cfi_endproc
|} in
      output_string oc content;
      close_out oc;
      asm_file in
    let res = run_command !casm ((String.split_on_char ' ' !casm_options) @ ["-o"; Filename.null; tmpsrc]) in
    if res.exit_code = 0 then begin
      asm_supports_cfi := Some true;
      printf "yes\n";
    end else begin
      asm_supports_cfi := Some false;
      printf "no\n";
    end
  end
end

(* Test Availability of Option '-no-pie' or '-nopie' *)
(* Skip if we set configedit defaults because the C compiler is not determined yet. *)
let _ = if (!clinker_needs_no_pie && not !configedit_defaults) then begin
  printf "Testing linker support for '-no-pie' / '-nopie' option... ";
  if testcompiler !cc "-no-pie" then begin
    printf "yes, '-no-pie'\n";
    clinker_options := !clinker_options ^ " -no-pie";
  end else if testcompiler !cc "-nopie" then begin
    printf "yes, '-nopie'\n";
    clinker_options := !clinker_options ^ " -nopie";
  end else begin
    printf "no\n";
    clinker_needs_no_pie := false;
  end
end

(* Test Availability of Option '-z nobtcfi' or '-Wl,-z,nobtcfi'*)
(* Skip if we set configedit defaults because the C compiler is not determined yet. *)
let _ = if (!clinker_needs_nobtcfi && not !configedit_defaults) then begin
  printf "Testing linker support for 'nobtcfi' option... ";
  if testcompiler !cc "-z nobtcfi" then begin
    printf "yes, '-z nobtcfi'\n";
    clinker_options := !clinker_options ^ "-z nobtcfi";
  end else if testcompiler !cc "-Wl,-z,nobtcfi" then begin
    printf "yes, '-Wl,-z,nobtcfi'\n";
    clinker_options := !clinker_options ^ "-Wl,-z,nobtcfi";
  end else
    printf "no\n"
end

(* Availability of Required Tools: only check tool versions *)
let missingtools = ref false

let _ =
  printf "Testing Coq... ";
  let res = run_command "coqc" ["--print-version"] in
  let coq_ver = String.trim (List.hd (String.split_on_char ' ' res.stdout)) in
  let coq_ver_good =
    Str.regexp {|8\.15\.0\|8\.15\.1\|8\.15\.2\|8\.16\.0\|8\.16\.1\|8\.17\.0\|8\.17\.1\|8\.18\.0\|8\.19\.0\|8\.19\.1\|8\.19\.2\|8\.20\.0\|8\.20\.1\|9\.0\.0\|9\.1\.0|}
  in
  if Str.string_match coq_ver_good coq_ver 0 then
    printf "version %s -- good!\n" coq_ver
  else match coq_ver with
  | "" -> begin
      printf "NOT FOUND\n";
      let res = run_command "rocq" ["--print-version"] in
      let rocq_ver = List.hd (String.split_on_char ' ' res.stdout) in
      begin match rocq_ver with
      | "" ->
          printf "Error: make sure Coq is installed.\n"
      | _ ->
          printf "Rocq prover version %s found.\n\
                  Please install the Coq wrapper for this version of Rocq.\n"
                 rocq_ver;
      end;
      missingtools := true
  end
  | _ -> begin
      printf "version %s -- UNSUPPORTED\n" coq_ver;
      if !ignore_coq_version then
        printf "Warning: this version of Coq is unsupported, proceed at your own risks.\n"
      else begin
        printf "Error: CompCert requires a version of Coq between 8.15 and 9.1\n";
        missingtools := true
      end
  end

let _ =
  printf "Testing OCaml... ";
  let res = run_command "ocamlc" ["-version"] in
  let ocaml_ver = String.trim res.stdout in
  let re_ocaml_ver_good = Str.regexp {|4\.0[5-9]\..*\|4\.1.\..*\|5\.3\..*|} in
  let re_ocaml_ver_bad = Str.regexp {|.\..*|} in
  if Str.string_match re_ocaml_ver_good ocaml_ver 0 then
    printf "version %s -- good!\n" ocaml_ver
  else if Str.string_match re_ocaml_ver_bad ocaml_ver 0 then begin
    printf "version %s -- UNSUPPORTED\n" ocaml_ver;
    if !ignore_ocaml_version then
      printf "Warning: this version of OCaml is unsupported, proceed at your own risks.\n"
    else begin
      printf "Error: make sure OCaml version 4.05 to 5.3 is installed.\n";
      missingtools := true
    end
  end else begin
    printf "NOT FOUND\n";
    missingtools := true
  end

let _ =
  let menhir_required = 20200624 in
  printf "Testing Menhir... ";
  let res = run_command "menhir" ["--version"] in
  let re_menhir_ver = Str.regexp {|^.*version \([0-9]*\).*$|} in
  let re_menhir_ver_good = Str.regexp {|20[0-9][0-9][0-9][0-9][0-9][0-9]|} in
  let menhir_ver =
    (* Need to call string_match before you can extract matched group. *)
    let _ = Str.string_match re_menhir_ver (String.trim res.stdout) 0 in
    Str.matched_group 1 res.stdout in
  if Str.string_match re_menhir_ver_good menhir_ver 0 then
    if int_of_string menhir_ver >= menhir_required then
      printf "version %s -- good!\n" menhir_ver
      (* Menhir directory location is managed by dune. *)
    else begin
      printf "version %s -- UNSUPPORTED\n" menhir_ver;
      printf "Error: CompCert requires a version greater or equal to %d.\n" menhir_required;
      missingtools := true
    end
  else begin
    printf "NOT FOUND\n";
    printf "Error: make sure Menhir version %d or later is installed.\n" menhir_required;
    missingtools := true
  end

let _ =
  if !missingtools then begin
    print_endline "One or several required tools are missing or too old.  Aborting.";
    exit 2
  end

(* Determine !sharedir or check that user-provided !sharedir is valid *)
let _ =
  if !sharedir = "" then
    sharedir := Filename.(concat (dirname !bindir) "share")
  else begin
    (* The paths are always expanded. *)
    let bindirshare = Filename.(concat (dirname !bindir) "share") in
    if !sharedir = Filename.concat bindirshare  "compcert"
    || !sharedir = bindirshare
    || !sharedir = !bindir
    then () (* ok! *)
    else
      let msg =
        sprintf "Wrong -sharedir option. The share directory must be one of\
                \n  %s\
                \n  %s\
                \n  %s"
                (Filename.concat bindirshare "compcert")
                bindirshare
                !bindir in
      invalid_input msg
  end

(* See if !libdir can be accessed with a relative path from !sharedir *)
let rellibdir =
  let parentdir = Filename.dirname !sharedir in
  if !libdir = Filename.(concat parentdir (concat "lib" "compcert")) then
    Filename.(concat parent_dir_name (concat "lib" "compcert"))
  else
    !libdir

(* Generate Makefile.config *)
let _ =
  let config_base = sprintf "\
PREFIX=%s
BINDIR=%s
LIBDIR=%s
RELLIBDIR=%s
MANDIR=%s
SHAREDIR=%s
COQDEVDIR=%s
COMPFLAGS=-bin-annot
" !prefix !bindir !libdir rellibdir !mandir !sharedir !coqdevdir
  in
  let config_extension =
    if !target != "manual" then
      sprintf "\
ABI=%s
ARCH=%s
ASM_SUPPORTS_CFI=%B
BITSIZE=%d
CASM=%s
CASM_OPTIONS=%s
CASMRUNTIME=%s
CC=%s %s
CLINKER=%s
CLINKER_OPTIONS=%s
CPREPRO=%s
CPREPRO_OPTIONS=%s
ARCHIVER=%s
ENDIANNESS=%s
HAS_RUNTIME_LIB=%B
HAS_STANDARD_HEADERS=%B
HAS_DOUBLE=%B
INSTALL_COQDEV=%B
LIBMATH=%s
MODEL=%s
PIC_SUPPORTED=%B
SYSTEM=%s
RESPONSEFILE=%s
" (Option.get !abi) arch (Option.get !asm_supports_cfi) bitsize !casm !casm_options
  !casmruntime !cc !cc_options !clinker !clinker_options !cprepro !cprepro_options
  !archiver endianess !has_runtime_lib !has_standard_headers !has_double !install_coqdev !libmath
  model !pic_supported (Option.get !system) !responsefile
    else "

# Target architecture
# ARCH=powerpc
# ARCH=powerpc_vle
# ARCH=arm
# ARCH=x86
# ARCH=riscV
# ARCH=aarch6
# ARCH=peaktop
# ARCH=tricore
ARCH=

# Hardware variant
# MODEL=ppc32       # for plain PowerPC
# MODEL=ppc64       # for PowerPC with 64-bit instructions
# MODEL=e5500       # for Freescale e5500 PowerPC variant
# MODEL=armv6       # for ARM
# MODEL=armv6t2     # for ARM
# MODEL=armv7a      # for ARM
# MODEL=armv7r      # for ARM
# MODEL=armv7m      # for ARM
# MODEL=32sse2      # for x86 in 32-bit mode
# MODEL=64          # for x86 in 64-bit mode
# MODEL=default     # for others
MODEL=

# Target ABI
# ABI=eabi          # for PowerPC / Linux and other SVR4 or EABI platforms
# ABI=eabi          # for ARM
# ABI=hardfloat     # for ARM
# ABI=standard      # for others
ABI=

# Target bit width
# BITSIZE=64        # for x86 in 64-bit mode, RiscV in 64-bit mode, AArch64
# BITSIZE=32        # otherwise
BITSIZE=

# Target endianness
# ENDIANNESS=big     # for ARM or PowerPC
# ENDIANNESS=little  # for ARM or x86 or RiscV or AArch64
ENDIANNESS=

# Target operating system and development environment
#
# Possible choices for PowerPC:
# SYSTEM=linux
# SYSTEM=diab
#
# Possible choices for ARM, AArch64, RiscV:
# SYSTEM=linux
#
# Possible choices for x86:
# SYSTEM=linux
# SYSTEM=bsd
# SYSTEM=macos
# SYSTEM=cygwin
SYSTEM=

# Are we able to produce position-independent code (with the `-fpic` option)?
#PIC_SUPPORTED=true
PIC_SUPPORTED=false

# C compiler (for testing only)
CC=cc

# Assembler for assembling compiled files
CASM=cc
CASM_OPTIONS=-c

# Assembler for assembling runtime library files
CASMRUNTIME=$(CASM) $(CASM_OPTIONS)

# Linker
CLINKER=cc
CLINKER_OPTIONS=-no-pie

# Preprocessor for .c files
CPREPRO=cc
CPREPRO_OPTIONS=-U__GNUC__ -E

# Archiver to build .a libraries
ARCHIVER=ar rcs

# Math library. Set to empty under macOS
LIBMATH=-lm

# Turn on/off the installation and use of the runtime support library
HAS_RUNTIME_LIB=true

# Turn on/off the installation and use of the standard header files
HAS_STANDARD_HEADERS=true

# Turn on/off support for double precision floating point only for selected architectures
HAS_DOUBLE=true

# Whether the assembler $(CASM) supports .cfi debug directives
ASM_SUPPORTS_CFI=false
#ASM_SUPPORTS_CFI=true

# Whether the other tools support responsefiles in GNU syntax or Diab syntax
RESPONSEFILE=gnu  # diab
" in
  let config_oc = open_out !output in
  output_string config_oc (config_base ^ config_extension);
  close_out config_oc

(* Summarize Configuration *)
let _ =
  if !target = "manual" then
    printf "

Please finish the configuration by editing file ./Makefile.config.

" else begin
    printf "
CompCert configuration:
    Target architecture........... %s
    Hardware model................ %s
    Application binary interface.. %s
    Endianness.................... %s
    PIC generation supported...... %B
    OS and development env........ %s
    C compiler.................... %s %s
    C preprocessor................ %s %s
    Assembler..................... %s %s
    Assembler supports CFI........ %B
    Assembler for runtime lib..... %s
    Linker........................ %s %s
    Archiver...................... %s
    Math library.................. %s
    Binaries installed in......... %s
    Shared config installed in.... %s
    Runtime library provided...... %B
    Library files installed in.... %s"
      arch model (Option.get !abi) endianess !pic_supported (Option.get !system)
      !cc !cc_options !cprepro !cprepro_options !casm !casm_options (Option.get !asm_supports_cfi)
      !casmruntime !clinker !clinker_options !archiver !libmath
      !bindir !sharedir !has_runtime_lib !libdir;

    if rellibdir != !libdir then
      printf "
                                   (%s relative to compcert.ini)" rellibdir;

    printf "
    Man pages installed in........ %s
    Standard headers provided..... %B
    Standard headers installed in. %s/include"
      !mandir !has_standard_headers !libdir;

    if !install_coqdev then
      printf "
    Coq development installed in.. %s" !coqdevdir
    else
      printf "
    Coq development will not be installed\n"
  end

(*- #End *)

(*- #End_DEACTIVATED_CODE *)
