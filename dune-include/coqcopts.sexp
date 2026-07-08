; Notes on silenced Coq warnings:
;
; unused-pattern-matching-variable:
;    warning introduced in 8.13
;    the code rewrite that avoids the warning is not desirable
; deprecated-since-8.19
; deprecated-since-8.20
;    renamings performed in Coq's standard library;
;    using the new names would break compatibility with earlier Coq versions.
; deprecated-since-9.1
;    renamings performed in Coq's standard library;
;    using the new names would break compatibility with earlier Coq versions.
; deprecated-since-9.2
;    renamings performed in Coq's standard library;
;    using the new names would break compatibility with earlier Coq versions.
; register-all
;    the scheme all command is only available in 9.2
; deprecated-from-Coq
;    Rocq wants "From Stdlib Require" while Coq wants "From Coq Require".
( "-q"
  -w -unused-pattern-matching-variable
  -w -deprecated-since-8.19
  -w -deprecated-since-8.20
  -w -deprecated-since-9.1
  -w -deprecated-since-9.2
  -w -register-all
  -w -deprecated-from-Coq)
