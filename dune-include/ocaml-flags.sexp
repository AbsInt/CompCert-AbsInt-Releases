(
; Add COMPFLAGS as in Makefile.
 "-bin-annot" -g -strict-sequence -safe-string
; Turn warnings into errors always
 -warn-error +a
; FIXME: until we can set flags per module, disable the union of all disabled warnings from the Makefile build.
 -w +a
; Warnings that should be turned off for handwritten code.
 -w -fragile-match
 -w -missing-record-field-pattern
 -w -unused-var-strict
 -w -missing-mli
; Warnings that should additionally be turned off for Menhir generated code.
 -w -ambiguous-name
; Warnings that should additionally be turned off for extracted Coq code.
 -w -ignored-extra-argument
 -w -unused-value-declaration
 -w -unused-open
 -w -unused-type-declaration
 -w -unused-rec-flag
 -w -ambiguous-name
 -w -open-shadow-identifier
 -w -open-shadow-label-constructor
 -w -unreachable-case
 -w -unused-module
 -w -unused-functor-parameter
)
