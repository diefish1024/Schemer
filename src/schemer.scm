;;; schemer.scm
;;; A compiler for a subset of Scheme targeting x86-64.
;;;
;;; This file is loaded by the generated test.scm after match.scm,
;;; helpers.scm, fmts.pretty and driver.scm.  Each pass named in the
;;; (compiler-passes ...) list for the current assignment must be
;;; defined here as a top-level procedure.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; verify-scheme
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Syntax checking is deferred to a15's parse-scheme (see docs/notice.md),
;;; so the verifier is the identity pass.
(define verify-scheme (lambda (program) program))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; expose-frame-var  (a2)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Replace each frame variable fvN with a displacement operand
;;; #<disp rbp 8N>.  Frames are 8-byte words, so fvi lives at offset 8i
;;; off the frame pointer (rbp).
(define-who expose-frame-var
  (define Var
    (lambda (v)
      (if (frame-var? v)
          (make-disp-opnd frame-pointer-register (* 8 (frame-var->index v)))
          v)))
  (define Effect
    (lambda (ef)
      (match ef
        [(set! ,v (,binop ,t1 ,t2))
         `(set! ,(Var v) (,binop ,(Var t1) ,(Var t2)))]
        [(set! ,v ,t) `(set! ,(Var v) ,(Var t))]
        [,x (format-error who "invalid Effect ~s" x)])))
  (define Tail
    (lambda (tail)
      (match tail
        [(begin ,[Effect -> ef*] ... ,[Tail -> t]) `(begin ,ef* ... ,t)]
        [(,t) `(,(Var t))]
        [,x (format-error who "invalid Tail ~s" x)])))
  (lambda (program)
    (match program
      [(letrec ([,label (lambda () ,[Tail -> t*])] ...) ,[Tail -> t])
       `(letrec ([,label (lambda () ,t*)] ...) ,t)]
      [,x (format-error who "invalid Program ~s" x)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; flatten-program  (a2)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Flatten the nested letrec/begin structure into one (code ...) form:
;;; the letrec body first, then each lambda body prefixed by its label.
;;; Tail calls (Triv) become (jump Triv); begin disappears.
(define-who flatten-program
  (define Tail
    ;; returns a list of statements
    (lambda (tail)
      (match tail
        [(begin ,ef* ... ,t) `(,ef* ... ,@(Tail t))]
        [(,triv) `((jump ,triv))]
        [,x (format-error who "invalid Tail ~s" x)])))
  (lambda (program)
    (match program
      [(letrec ([,label* (lambda () ,tail*)] ...) ,tail)
       `(code
          ,@(Tail tail)
          ,@(apply append
              (map (lambda (l t) (cons l (Tail t))) label* tail*)))]
      [,x (format-error who "invalid Program ~s" x)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; generate-x86-64  (a1 + a2)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Input: (code Statement ...) where a Statement is a label, a jump,
;;; or a set!.  emit-program supplies the surrounding boilerplate.
(define-who generate-x86-64
  (define binop->inst
    (lambda (op)
      (case op
        [(+) 'addq]
        [(-) 'subq]
        [(*) 'imulq]
        [(logand) 'andq]
        [(logor) 'orq]
        [(sra) 'sarq]
        [else (format-error who "unexpected binop ~s" op)])))
  (define Statement
    (lambda (st)
      (match st
        [,lab (guard (label? lab)) (emit-label lab)]
        [(jump ,t) (emit-jump 'jmp t)]
        [(set! ,v (,binop ,t1 ,t2)) (emit (binop->inst binop) t2 v)]
        [(set! ,v ,t) (guard (label? t)) (emit 'leaq t v)]
        [(set! ,v ,t) (emit 'movq t v)]
        [,x (format-error who "invalid Statement ~s" x)])))
  (lambda (program)
    (match program
      [(code ,stmt* ...) (emit-program (for-each Statement stmt*))]
      [,x (format-error who "invalid Program ~s" x)])))
