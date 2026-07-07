;;; schemer.scm
;;; A compiler for a subset of Scheme targeting x86-64.
;;;
;;; This file is loaded by the generated test.scm after match.scm,
;;; helpers.scm, fmts.pretty and driver.scm.  Each pass named in the
;;; (compiler-passes ...) list for the current assignment must be
;;; defined here as a top-level procedure.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; shared helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define relop?
  (lambda (x) (and (memq x '(< <= = >= >)) #t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; verify-scheme
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Syntax checking is deferred to a15's parse-scheme (see docs/notice.md),
;;; so the verifier is the identity pass.
(define verify-scheme (lambda (program) program))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; finalize-locations  (a3)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Each Body is (locate ([uvar Loc]*) Tail).  Replace every uvar in the
;;; Tail with its assigned Loc and drop the locate form.  Because uvars
;;; are unique symbols that never collide with registers, labels, or
;;; operators, a generic substitution over the tree is safe.
(define-who finalize-locations
  (lambda (program)
    (define Body
      (lambda (bd)
        (match bd
          [(locate ([,uvar* ,loc*] ...) ,tail)
           (let ([env (map cons uvar* loc*)])
             (let sub ([x tail])
               (cond
                 [(uvar? x) (cond [(assq x env) => cdr] [else x])]
                 [(pair? x) (cons (sub (car x)) (sub (cdr x)))]
                 [else x])))]
          [,x (format-error who "invalid Body ~s" x)])))
    (match program
      [(letrec ([,label (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label (lambda () ,body*)] ...) ,body)]
      [,x (format-error who "invalid Program ~s" x)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; expose-frame-var  (a2, generalized in a3)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Replace each frame variable fvN with a displacement operand
;;; #<disp rbp 8N>.  Written as a grammar-independent tree walk so it
;;; needs no changes as new forms (if/relop/nop/...) are added.
(define-who expose-frame-var
  (lambda (program)
    (let walk ([x program])
      (cond
        [(frame-var? x)
         (make-disp-opnd frame-pointer-register (* 8 (frame-var->index x)))]
        [(pair? x) (cons (walk (car x)) (walk (cdr x)))]
        [else x]))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; expose-basic-blocks  (a3)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Flatten arbitrarily nested if/begin into basic blocks.  Each helper
;;; returns two values: an expression and a list of new [label (lambda ()
;;; Tail)] bindings that get hoisted into the top-level letrec.  The only
;;; surviving conditional is (if (relop Triv Triv) (clab) (alab)) in tail.
(define-who expose-basic-blocks
  (lambda (program)
    (define Tail
      (lambda (tail)
        (match tail
          [(if ,pred ,ctail ,atail)
           (let-values ([(ct cb*) (Tail ctail)]
                        [(at ab*) (Tail atail)])
             (let ([clab (unique-label 'c)] [alab (unique-label 'a)])
               (let-values ([(pt pb*) (Pred pred clab alab)])
                 (values pt
                   (append pb*
                     `([,clab (lambda () ,ct)]) cb*
                     `([,alab (lambda () ,at)]) ab*)))))]
          [(begin ,ef* ... ,tail)
           (let-values ([(t tb*) (Tail tail)])
             (let-values ([(et eb*) (Effect* ef* t)])
               (values et (append eb* tb*))))]
          [(,triv) (values `(,triv) '())]
          [,x (format-error who "invalid Tail ~s" x)])))
    (define Pred
      (lambda (pr tlab flab)
        (match pr
          [(true) (values `(,tlab) '())]
          [(false) (values `(,flab) '())]
          [(if ,pred ,cpred ,apred)
           (let-values ([(ct cb*) (Pred cpred tlab flab)]
                        [(at ab*) (Pred apred tlab flab)])
             (let ([clab (unique-label 'c)] [alab (unique-label 'a)])
               (let-values ([(pt pb*) (Pred pred clab alab)])
                 (values pt
                   (append pb*
                     `([,clab (lambda () ,ct)]) cb*
                     `([,alab (lambda () ,at)]) ab*)))))]
          [(begin ,ef* ... ,pred)
           (let-values ([(pt pb*) (Pred pred tlab flab)])
             (let-values ([(et eb*) (Effect* ef* pt)])
               (values et (append eb* pb*))))]
          [(,relop ,t1 ,t2) (guard (relop? relop))
           (values `(if (,relop ,t1 ,t2) (,tlab) (,flab)) '())]
          [,x (format-error who "invalid Pred ~s" x)])))
    ;; Effect: given the (already exposed) tail that follows, returns the
    ;; tail that runs this effect then that follow-on tail.
    (define Effect
      (lambda (ef tail)
        (match ef
          [(nop) (values tail '())]
          [(if ,pred ,cef ,aef)
           (let ([jlab (unique-label 'j)])
             (let-values ([(ct cb*) (Effect cef `(,jlab))]
                          [(at ab*) (Effect aef `(,jlab))])
               (let ([clab (unique-label 'c)] [alab (unique-label 'a)])
                 (let-values ([(pt pb*) (Pred pred clab alab)])
                   (values pt
                     (append pb*
                       `([,clab (lambda () ,ct)]) cb*
                       `([,alab (lambda () ,at)]) ab*
                       `([,jlab (lambda () ,tail)])))))))]
          [(begin ,ef* ... ,ef)
           (let-values ([(et eb*) (Effect ef tail)])
             (let-values ([(bt bb*) (Effect* ef* et)])
               (values bt (append bb* eb*))))]
          [(set! ,lhs ,rhs)
           (values (make-begin `((set! ,lhs ,rhs) ,tail)) '())]
          [,x (format-error who "invalid Effect ~s" x)])))
    ;; Effect*: thread a list of effects onto the following tail.
    (define Effect*
      (lambda (ef* tail)
        (if (null? ef*)
            (values tail '())
            (let-values ([(rt rb*) (Effect* (cdr ef*) tail)])
              (let-values ([(t b*) (Effect (car ef*) rt)])
                (values t (append b* rb*)))))))
    (match program
      [(letrec ([,label* (lambda () ,tail*)] ...) ,tail)
       (let-values ([(t tb*) (Tail tail)])
         (let ([binding*
                (apply append
                  (map (lambda (l tl)
                         (let-values ([(bt bb*) (Tail tl)])
                           (cons `[,l (lambda () ,bt)] bb*)))
                       label* tail*))])
           `(letrec ,(append binding* tb*) ,t)))]
      [,x (format-error who "invalid Program ~s" x)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; flatten-program  (a2 + a3)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Flatten into a single (code ...) form.  Conditional jumps use the
;;; label of the *next* letrec binding to avoid redundant jumps.
(define-who flatten-program
  (lambda (program)
    (define Tail
      ;; tail, next-label -> list of statements
      (lambda (tail nlab)
        (match tail
          [(begin ,ef* ... ,t) `(,ef* ... ,@(Tail t nlab))]
          [(if (,relop ,t1 ,t2) (,lab1) (,lab2))
           (cond
             [(eq? lab2 nlab) `((if (,relop ,t1 ,t2) (jump ,lab1)))]
             [(eq? lab1 nlab) `((if (not (,relop ,t1 ,t2)) (jump ,lab2)))]
             [else `((if (,relop ,t1 ,t2) (jump ,lab1)) (jump ,lab2))])]
          [(,triv) (if (eq? triv nlab) '() `((jump ,triv)))]
          [,x (format-error who "invalid Tail ~s" x)])))
    (match program
      [(letrec ([,label* (lambda () ,tail*)] ...) ,tail)
       (let ([body-next (and (pair? label*) (car label*))])
         `(code
            ,@(Tail tail body-next)
            ,@(let loop ([labs label*] [tails tail*])
                (if (null? labs)
                    '()
                    (let ([nlab (and (pair? (cdr labs)) (cadr labs))])
                      (cons (car labs)
                            (append (Tail (car tails) nlab)
                                    (loop (cdr labs) (cdr tails)))))))))]
      [,x (format-error who "invalid Program ~s" x)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; generate-x86-64  (a1 + a2 + a3)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-who generate-x86-64
  (define binop->inst
    (lambda (op)
      (case op
        [(+) 'addq]   [(-) 'subq]  [(*) 'imulq]
        [(logand) 'andq] [(logor) 'orq] [(sra) 'sarq]
        [else (format-error who "unexpected binop ~s" op)])))
  ;; cmpq t2, t1 computes t1 - t2, so the condition code names t1 <relop> t2.
  (define relop->cc
    (lambda (op)
      (case op
        [(=) 'je] [(<) 'jl] [(<=) 'jle] [(>) 'jg] [(>=) 'jge]
        [else (format-error who "unexpected relop ~s" op)])))
  (define relop->cc/not
    (lambda (op)
      (case op
        [(=) 'jne] [(<) 'jge] [(<=) 'jg] [(>) 'jle] [(>=) 'jl]
        [else (format-error who "unexpected relop ~s" op)])))
  (define Statement
    (lambda (st)
      (match st
        [,lab (guard (label? lab)) (emit-label lab)]
        [(jump ,t) (emit-jump 'jmp t)]
        [(if (not (,relop ,t1 ,t2)) (jump ,lab))
         (emit 'cmpq t2 t1)
         (emit-jump (relop->cc/not relop) lab)]
        [(if (,relop ,t1 ,t2) (jump ,lab))
         (emit 'cmpq t2 t1)
         (emit-jump (relop->cc relop) lab)]
        [(set! ,v (,binop ,t1 ,t2)) (emit (binop->inst binop) t2 v)]
        [(set! ,v ,t) (guard (label? t)) (emit 'leaq t v)]
        [(set! ,v ,t) (emit 'movq t v)]
        [,x (format-error who "invalid Statement ~s" x)])))
  (lambda (program)
    (match program
      [(code ,stmt* ...) (emit-program (for-each Statement stmt*))]
      [,x (format-error who "invalid Program ~s" x)])))
