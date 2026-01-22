(lang dune 3.16)
(using coq 0.9)
; FIXME only needed if ./cparser/dune menhir stanza works
;(using menhir 3.0)
; necessary due to (dir) target in ./doc/dune
(using directory-targets 0.1)

(name compcert)

; We do not define any Opam packages here for two reasons.
; 1. From our tests the dune install command did not work together with using multiple build contexts, which we use to build the program for multiple architectures.
;    So we continue to handle all the installation of files out of the correct _build/<platform> tree by ourselves.
; 2. There is an open bug on the dune issue tracker (https://github.com/ocaml/dune/issues/8099) which we also run into with packages.
;    dune build -p compcert,MenhirLib,Flocq fails because the coq.extraction stanza for clightgen is also used in the dependency calculation.
;    So we cannot even compile the compcert package if we define it.
