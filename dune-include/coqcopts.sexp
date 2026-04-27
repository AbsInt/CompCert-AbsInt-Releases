; Notes on silenced Coq warnings:
;
; unused-pattern-matching-variable:
;    warning introduced in 8.13
;    the code rewrite that avoids the warning is not desirable
; deprecated-since-8.19
; deprecated-since-8.20
;    renamings performed in Coq's standard library;
;    using the new names would break compatibility with earlier Coq versions.
; deprecated-from-Coq
;    Rocq wants "From Stdlib Require" while Coq wants "From Coq Require".
("-w" -unused-pattern-matching-variable
  -w -deprecated-since-8.19
  -w -deprecated-since-8.20
  -w -deprecated-from-Coq)
