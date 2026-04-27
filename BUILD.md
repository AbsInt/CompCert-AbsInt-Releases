# Building with dune

The process of building CompCert with dune is similar to the Makefile based build.
The key advantage is that dune can compile the Rocq proofs and OCaml files for each target architecture in parallel, allowing a quicker feedback loop when ensuring that changes in the proof/code work for all backends.

## How it works
In general, to compile for one architecture the build rules copy all architecture specific files and all shared files into a common build directory, then invoke the Rocq/OCaml compilers.
For example, the rules to compile the Rocq proofs in `theory/dune` copy all Rocq files from the shared directories (`common/`, `backend/`, etc.) and the Rocq files from the architecture specific directory (`aarch64/` or `powerpc` or ...) into `theory/`, and then compile all together.

The `TARGET_ARCH` environment variable is used to control the target architecture of the build by selecting which architecture specific build directory is used. Valid values for the architecture are:
- `aarch64`
- `arm`
- `powerpc`
- `powerpc_vle`
- `riscV`
- `tricore`
- `x86_32`
- `x86_64`

To compile multiple architectures in parallel, we use dune contexts. Each context has the same name as the architecture and it sets the `TARGET_ARCH` environment variable to that name.
There is also the default context which is needed for compatibility with ocamllsp. Normally development should happen in the default context where the env var can be set manually:
```
TARGET_ARCH=powerpc dune build
```

At the moment the configure script (`tools/configure.ml`) is only needed to set the required options to generate a `compcert.ini` file, not for the build of the ccomp/clightgen binaries.

## Limitations
In general the dune build is at the moment less configurable than the Makefile build.

- Some variables that can be set in Makefile.config have no effect, e.g. OCAML_OPT_COMP, OCAML_NATIVE_COMP, COMPFLAGS, LINK_OPT, INSTALL_COQDEV, TIMING, PROFILING etc.
- Overriding Coq flags via COQCOPTS & COQEXTRACTOPTS env variables is not implemented.
  As an alternative, override the corresponding file in `dune-include/`.
- warn-error for compiling OCaml code is always turned on (Makefile disables it if no .git directory exists).
- Disabling warning flags per file for OCaml code not possible atm. The Makefile disables more warnings for extracted Coq code. Instead we disable the union of all disabled flags for all OCaml files.
- Using external Flocq & MenhirLib is not implemented. This would require dynamically changing the dune build rules, e.g. by inserting a `(data_only_dirs flocq MenhirLib)` stanza.

## How to invoke dune

As an analogue to the previous `make all`:
First generate `Makefile.config` by calling `configure.exe`.
```
$ dune exec tools/configure.exe -- <target> [options]
```
Compile `ccomp`, `clightgen`, generate `compcert.ini`, `_CoqProject`, and copy them to the project root for a single target.
This is only possible for the default context, so `TARGET_ARCH` must be set to the desired architecture.
```
$ TARGET_ARCH=<arch> dune build ccomp clightgen _CoqProject
```

The following aliases can always be prefixed with `_build/<arch>` to execute the build only for one architecture.

To compile ccomp/clightgen for all architectures in parallel.
```
$ dune build @compile-ccomp @compile-clightgen
$ dune build @_build/<arch>/compile-ccomp @_build/<arch>/compile-clightgen
```

To compile just the Rocq proofs for all architectures in parallel.
```
$ dune build @proof
$ dune build @_build/<arch>/proof
```

To do the extraction for all architectures in parallel/only for `<arch>`.
```
$ dune build @extraction
$ dune build @_build/<arch>/extraction
```

To check for leftover commands, check for admit commands, run `coqchk`.
```
$ dune build @check-leftovers @check-admitted @check-proof
$ dune build @_build/<arch>/check-leftovers @_build/<arch>/check-admitted @_build/<arch>/check-proof
```

## Makefile wrapper

The `Makefile.dune` wrapper is used to implement shortcuts for certain commands.
Also it saves any generated files (`ccomp`, `clightgen`, etc.) in `out/<arch>/` to use for later.

As an analogue to the previous `make all`:
Compile `ccomp`, `clightgen`, generate `compcert.ini`, `_CoqProject`, and copy them to the project root for a single target. Also compile `runtime/libcompcert.a` for the target.
Or call without argument to get prompted with the list of predefined targets.
```
$ make -f Makefile.dune <target>
$ make -f Makefile.dune
```

Compile everything (but don't place any binaries in the project root) for all architectures in parallel.
```
$ make -f Makefile.dune all
```

Corresponding goals for `proof`, `check-admitted`, `check-leftovers` & `check-proof` also exist.

## dev script

The `./dev` script implements similar shortcuts for dune invokations.
Also it saves any generated files (`ccomp`, `clightgen`, etc.) in `out/<arch>/` to use for later.

As an analogue to the previous `make all`:
Compile `ccomp`, `clightgen`, generate `compcert.ini`, `_CoqProject`, and copy them to the project root for a single target. Also compile `runtime/libcompcert.a` for the target.
Or call without argument to get prompted with the list of predefined targets.
```
$ ./dev <target>
$ ./dev
```

Compile everything (but don't place any binaries in the project root) for all architectures in parallel.
```
$ ./dev all
```

Corresponding commands for `proof`, `check-admitted`, `check-leftovers` & `check-proof` also exist.
