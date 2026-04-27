(lang dune 3.17)
(using coq 0.10)
; Necessary due to (dir) target in ./doc/dune
(using directory-targets 0.1)

(name compcert)

; We do not define any Opam packages here due to an open bug on the dune issue tracker (https://github.com/ocaml/dune/issues/8099).
;  dune build -p compcert,MenhirLib,Flocq fails because the coq.extraction stanza for clightgen is also used in the dependency calculation.
;  So we cannot even compile the compcert package if we define it.
