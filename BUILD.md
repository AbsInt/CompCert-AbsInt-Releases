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
Dune always has a dafault context. For single-architecture builds we generate a `dune-workspace` file that defines TARGET_ARCH in the default context to that architecture.
For multi-architecture builds we generate a `dune-workspace` file where `powerpc` is the default context.

## Limitations
In general, the dune build is at the moment less configurable than the Makefile build.

- Some variables that can be set in Makefile.config have no effect, e.g. OCAML_OPT_COMP, OCAML_NATIVE_COMP, COMPFLAGS, LINK_OPT, INSTALL_COQDEV, TIMING, PROFILING etc.
- Overriding Coq flags via COQCOPTS & COQEXTRACTOPTS env variables is not implemented.
  As an alternative, customize the corresponding file in `dune-include/`.
- warn-error for compiling OCaml code is always turned on (Makefile disables it if no .git directory exists).
- Disabling warning flags per file for OCaml code not possible atm. The Makefile disables more warnings for extracted Coq code. Instead we disable the union of all disabled flags for all OCaml files.
- Using external Flocq & MenhirLib is not implemented. This would require dynamically changing the dune build rules, e.g. by inserting a `(data_only_dirs flocq MenhirLib)` stanza.

## How to invoke dune


To configure a build for one architecture, run the `configure` script with a target (e.g. `ppc-eabi`).
```
$ ./configure <target> [options]
```

To configure a build for all architectures in parallel, run the `configure` script with the special `all` target.
(This is only for development and most options are not needed/don't have an effect.)
```
$ ./configure all
```

Then build everything with:
```
$ dune build
```

The following aliases implement common operations.
They require you to have run the `configure` script before in order to generate the proper `dune-workspace` file, defining either a single or multiple build contexts.

### Compile ccomp/clightgen binary
This does not place the binaries in the root folder.
```
$ dune build @compile-ccomp @compile-clightgen
```

### Compile just the Rocq proofs
```
$ dune build @proof
```

### Run the extraction
```
$ dune build @extraction
```

### Check for leftover commands, check for admit commands, run `coqchk`
```
$ dune build @check-leftovers @check-admitted @check-proof
```

## dev script (Recommended)

The `./dev` script implements similar shortcuts for dune invocations.
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

# VSCode specific settings
- Install "OCaml Platform" (ocamllabs.ocaml-platform) & "VsRocq" (rocq-prover.vsrocq) extensions.
- Set `"ocaml.server.args": ["--fallback-read-dot-merlin"]` in workspace settings.
