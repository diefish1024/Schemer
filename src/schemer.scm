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

;; keep only the locations we track for liveness: unique vars and registers
;; (frame variables, ints, and labels are ignored).
(define track?
  (lambda (x) (or (uvar? x) (register? x))))

(define list->set
  (lambda (ls) (fold-right (lambda (x s) (if (track? x) (set-cons x s) s)) '() ls)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; verify-scheme
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Syntax checking is deferred to a15's parse-scheme (see docs/notice.md),
;;; so the verifier is the identity pass.
(define verify-scheme (lambda (program) program))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; uncover-register-conflict  (a4)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Backward live analysis over each Body, building a conflict graph that
;;; maps every uvar to the uvars/registers it cannot share a register
;;; with.  Emits (locals (uvar*) (register-conflict conflict-graph Tail)).
(define-who uncover-register-conflict
  (lambda (program)
    (define Body
      (lambda (bd)
        (match bd
          [(locals (,uvar* ...) ,tail)
           (let ([ct (map (lambda (u) (cons u '())) uvar*)])
             ;; add b into a's conflict entry (a must be a uvar)
             (define add-edge!
               (lambda (a b)
                 (let ([e (assq a ct)])
                   (set-cdr! e (set-cons b (cdr e))))))
             ;; record conflicts between lhs (uvar or register) and each
             ;; live location.  A register lhs still conflicts with the live
             ;; uvars (they cannot use that register), even though registers
             ;; keep no conflict list of their own.
             (define record-conflict!
               (lambda (lhs conf*)
                 (for-each
                   (lambda (x)
                     (when (uvar? lhs) (add-edge! lhs x))
                     (when (and (uvar? x) (track? lhs)) (add-edge! x lhs)))
                   conf*)))
             (define rhs-uses
               (lambda (rhs)
                 (if (pair? rhs)
                     (match rhs [(,op ,t1 ,t2) (list->set (list t1 t2))])
                     (list->set (list rhs)))))
             (define Effect*
               (lambda (ef* live)
                 (if (null? ef*)
                     live
                     (Effect (car ef*) (Effect* (cdr ef*) live)))))
             (define Effect
               (lambda (ef live)
                 (match ef
                   [(nop) live]
                   [(if ,p ,c ,a) (Pred p (Effect c live) (Effect a live))]
                   [(begin ,ef* ... ,e) (Effect* ef* (Effect e live))]
                   [(set! ,lhs ,rhs)
                    (let ([live^ (difference live (list lhs))])
                      (record-conflict! lhs
                        (if (and (not (pair? rhs)) (track? rhs))
                            (difference live^ (list rhs)) ; move: no self conflict
                            live^))
                      (union live^ (rhs-uses rhs)))]
                   [,x (format-error who "invalid Effect ~s" x)])))
             (define Pred
               (lambda (pr t-live f-live)
                 (match pr
                   [(true) t-live]
                   [(false) f-live]
                   [(if ,p ,c ,a)
                    (Pred p (Pred c t-live f-live) (Pred a t-live f-live))]
                   [(begin ,ef* ... ,p) (Effect* ef* (Pred p t-live f-live))]
                   [(,relop ,x ,y) (guard (relop? relop))
                    (union (union t-live f-live) (list->set (list x y)))]
                   [,x (format-error who "invalid Pred ~s" x)])))
             (define Tail
               (lambda (t)
                 (match t
                   [(if ,p ,c ,a) (Pred p (Tail c) (Tail a))]
                   [(begin ,ef* ... ,t) (Effect* ef* (Tail t))]
                   [(,triv ,loc* ...) (list->set (cons triv loc*))]
                   [,x (format-error who "invalid Tail ~s" x)])))
             (Tail tail)
             `(locals (,uvar* ...) (register-conflict ,ct ,tail)))]
          [,x (format-error who "invalid Body ~s" x)])))
    (match program
      [(letrec ([,label (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label (lambda () ,body*)] ...) ,body)]
      [,x (format-error who "invalid Program ~s" x)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; assign-registers  (a4)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Optimistic graph-coloring allocator (Briggs).  Repeatedly removes a
;;; low-degree node, colors the rest, then assigns the node a register
;;; not used by its neighbors.  a4 never needs to spill, so failure is an
;;; error.  Produces (locate ([uvar reg]*) Tail).
(define-who assign-registers
  (lambda (program)
    (define k (length registers))
    (define color
      (lambda (uvar* ct)
        (define low-degree
          (lambda (u*)
            (let loop ([ls u*])
              (cond
                [(null? ls) (car u*)]
                [(< (length (cdr (assq (car ls) ct))) k) (car ls)]
                [else (loop (cdr ls))]))))
        (define remove-var
          (lambda (u ct)
            (map (lambda (ent) (cons (car ent) (remq u (cdr ent)))) ct)))
        (define used-regs
          (lambda (conf* assignments)
            (let loop ([c conf*])
              (cond
                [(null? c) '()]
                [(register? (car c)) (set-cons (car c) (loop (cdr c)))]
                [(assq (car c) assignments) =>
                 (lambda (p) (set-cons (cadr p) (loop (cdr c))))]
                [else (loop (cdr c))]))))
        (let rec ([uvar* uvar*] [ct ct])
          (if (null? uvar*)
              '()
              (let* ([u (low-degree uvar*)]
                     [u-conf (cdr (assq u ct))]
                     [assignments (rec (remq u uvar*) (remove-var u ct))]
                     [avail (difference registers (used-regs u-conf assignments))])
                (if (null? avail)
                    assignments
                    (cons (list u (car avail)) assignments)))))))
    (define Body
      (lambda (bd)
        (match bd
          [(locals (,uvar* ...) (register-conflict ,ct ,tail))
           (let ([env (color uvar* ct)])
             (unless (= (length env) (length uvar*))
               (format-error who "not enough registers (spilling needed)"))
             `(locate ,env ,tail))]
          [,x (format-error who "invalid Body ~s" x)])))
    (match program
      [(letrec ([,label (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label (lambda () ,body*)] ...) ,body)]
      [,x (format-error who "invalid Program ~s" x)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; discard-call-live  (a4)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Drop the Loc* live list attached to each tail call; only Tail context
;;; needs traversal since calls appear only there.
(define-who discard-call-live
  (lambda (program)
    (define Tail
      (lambda (t)
        (match t
          [(if ,pred ,[Tail -> c] ,[Tail -> a]) `(if ,pred ,c ,a)]
          [(begin ,ef* ... ,[Tail -> t]) `(begin ,ef* ... ,t)]
          [(,triv ,loc* ...) `(,triv)]
          [,x (format-error who "invalid Tail ~s" x)])))
    (define Body
      (lambda (bd)
        (match bd
          [(locate ,binding ,[Tail -> t]) `(locate ,binding ,t)]
          [,x (format-error who "invalid Body ~s" x)])))
    (match program
      [(letrec ([,label (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label (lambda () ,body*)] ...) ,body)]
      [,x (format-error who "invalid Program ~s" x)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; finalize-locations  (a3)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Each Body is (locate ([uvar Loc]*) Tail).  Replace every uvar in the
;;; Tail with its assigned Loc and drop the locate form.
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
;;; #<disp rbp 8N>, as a grammar-independent tree walk.
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
;;; Flatten nested if/begin into basic blocks.  Helpers return (values
;;; expr new-bindings); the only surviving conditional is
;;; (if (relop Triv Triv) (clab) (alab)) in tail position.
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
  ;; cmpq t2, t1 computes t1 - t2, so the cc names t1 <relop> t2.
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
