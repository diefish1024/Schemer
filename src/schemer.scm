;;; schemer.scm
;;; A compiler for a subset of Scheme targeting x86-64.
;;;
;;; This file is loaded by the generated test.scm after match.scm,
;;; helpers.scm, fmts.pretty and driver.scm.  Each pass named in the
;;; (compiler-passes ...) list for the current assignment must be
;;; defined here as a top-level procedure.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; a1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; verify-scheme
;;; Syntax checking is deferred to later assignments (see docs/notice.md),
;;; so the verifier is the identity pass for now.
(define verify-scheme (lambda (program) program))

;;; generate-x86-64
;;; Program   -> (begin Statement+)
;;; Statement -> (set! Var int64)
;;;            | (set! Var Var)
;;;            | (set! Var (Binop Var int32))
;;;            | (set! Var (Binop Var Var))
;;; The LHS of the set! and the first operand of the Binop are the same
;;; register, matching the two-operand x86-64 instruction forms.
(define-who generate-x86-64
  (define binop->inst
    (lambda (op)
      (case op
        [(+) 'addq]
        [(-) 'subq]
        [(*) 'imulq]
        [else (format-error who "unexpected binop ~s" op)])))
  (define Statement
    (lambda (st)
      (match st
        [(set! ,v1 (,binop ,v2 ,t)) (guard (memq binop '(+ - *)))
         (emit (binop->inst binop) t v1)]
        [(set! ,v1 ,t)
         (emit 'movq t v1)]
        [,x (format-error who "invalid Statement ~s" x)])))
  (lambda (program)
    (match program
      [(begin ,stmt* ...)
       (emit-program (for-each Statement stmt*))]
      [,x (format-error who "invalid Program ~s" x)])))
