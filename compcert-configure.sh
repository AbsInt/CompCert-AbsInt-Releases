#!/usr/bin/env bash

set -euo pipefail

scriptdir=$(dirname $(realpath $0))
envdir=$(dirname $scriptdir)
libdir=${scriptdir}/runtime
usage='Usage: compcert-configure [-help|--help] [target]

Supported targets are:
    ppc
    e5500
    ppc-diab
    ppcvle-diab
    arm
    x86_32
    x86_64
    rv32
    rv64
    aarch64
    tricore
'

function compcert_configure () {
    echo "Changing to $scriptdir..."
    pushd $scriptdir

    result=""
    toolprefix=""

    while : ; do
        case ${1:-} in
            "")
                break;;
            -help|--help)
                echo "$usage" 1>&2; exit 0;;
            -*)
                echo "Error: unknown option '$1'." 1>&2
                echo "$usage" 1>&2
                exit 2;;
            *)
                if test -n "$result"; then echo "$usage" 1>&2; exit 2; fi
                result="$1";;
        esac
        shift
    done

    supported_targets="ppc e5500 ppc-diab ppcvle-diab arm x86_32 x86_64 rv32 rv64 aarch64 tricore"

    # interactively get target using fzf
    if test -z "$result"; then
        result=$(for val in $supported_targets; do echo $val; done | fzf)
    fi

    case "$result" in
        ppc)
            build_context="ppc"
            config_target="ppc-eabi"
            toolprefix="${envdir}/gcc/ppc/bin/powerpc-unknown-eabi-";;
        e5500)
            build_context="ppc"
            config_target="e5500-linux"
            toolprefix="${envdir}/gcc/ppc/bin/powerpc-unknown-linux-gnu-";;
        # toolprefix for ppc-diab variants was not configured in the original script. 
        # a.d. TODO should we set toolprefix to the windriver binaries?
        ppc-diab)
            build_context="ppc"
            config_target="ppc-eabi-diab";;
        ppcvle-diab)
            build_context="ppc_vle"
            config_target="ppcvle-eabi-diab";;
        arm)
            build_context="arm"
            config_target="armv7a-linux"
            toolprefix="${envdir}/gcc/arm/bin/arm-multilib-linux-uclibcgnueabi-";;
        aarch64)
            build_context="aarch64"
            config_target="aarch64-linux"
            toolprefix="${envdir}/gcc/aarch64/bin/aarch64-unknown-linux-uclibc-";;
        x86_32)
            build_context="x86_32"
            config_target="x86_32-linux"
            toolprefix="${envdir}/gcc/x86-32/bin/i686-pc-linux-gnu-";;
        x86_64)
            build_context="x86_64"
            config_target="x86_64-linux"
            toolprefix="${envdir}/gcc/x86-64/bin/x86_64-unknown-linux-gnu-";;
        rv32)
            build_context="riscV"
            config_target="rv32-linux"
            toolprefix="${envdir}/gcc/riscv/bin/riscv32-unknown-linux-gnu-";;
        rv64)
            build_context="riscV"
            config_target="rv64-linux"
            toolprefix="${envdir}/gcc/riscv/bin/riscv64-unknown-linux-gnu-";;
        tricore)
            build_context="tricore"
            config_target="tricore-eabi"
            toolprefix="${envdir}/tricore/bin/tricore-elf-";;
        *)
            echo "$usage"
            return 2;;
    esac

    # Generate Makefile.config for selected target triple.
    dune exec -- tools/configure.exe "$config_target" -toolprefix "$toolprefix" -libdir "$libdir"

    # This is from the old compcert_devel script to set a concrete PPC model to test programs with windiss.
    if test "$config_target" = "ppcvle-eabi-diab"; then
        echo "Patching Makefile.config for ppc-vle."
        sed -i "s@CASMRUNTIME=das -Xalign-value@CASMRUNTIME=das -Xalign-value -tPPCE200Z420N3VEG:windiss@g" Makefile.config
        sed -i "s@_OPTIONS=@_OPTIONS=-tPPCE200Z420N3VEG:windiss @g" Makefile.config
    fi

    # Remove files from previous build.
    outdir="out/$result"
    rm -rf $outdir

    # Build ccomp & clightgen binaries, compcert.ini for target & _CoqProject for IDE.
    dune build @_build/${build_context}/ccomp @_build/${build_context}/clightgen _build/${build_context}/compcert.ini _build/${build_context}/_CoqProject

    # Since dune's install functionality does not work for us we copy the ccomp & clightgen binaries and compcert.ini manually.
    # If we can get `dune install` to work with multiple contexts in the future, this can be removed.
    mkdir -p $outdir
    cp _build/${build_context}/extraction/compcert/Driver.exe ${outdir}/ccomp
    cp _build/${build_context}/extraction/clightgen/ExportDriver.exe ${outdir}/clightgen
    cp _build/${build_context}/compcert.ini ${outdir}/compcert.ini

    # Copy Coq project file to be used by an IDE.
    cp _build/${build_context}/_CoqProject _CoqProject
}

compcert_configure "$@"
