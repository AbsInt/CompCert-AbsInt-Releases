(lang dune 3.17)
(using coq 0.10)
; Necessary due to (dir) target in ./doc/dune
(using directory-targets 0.1)

(name compcert)

; Disable the /workspace_root rewriting because it breaks ocamldebug.
(map_workspace_root false)

; Disable name mangling to use simple module name in ocamldebug.
(wrapped_executables false)
