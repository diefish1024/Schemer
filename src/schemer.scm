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

(define int?
  (lambda (x) (and (integer? x) (exact? x))))

;; Backward live analysis that builds a conflict graph.  loc? selects the
;; fixed locations to track alongside uvars: register? for register
;; conflicts, frame-var? for frame conflicts.  Returns an assoc list
;; mapping each uvar to the uvars/locations it conflicts with.
(define build-conflict-graph
  (lambda (uvar* tail loc?)
    (define track? (lambda (x) (or (uvar? x) (loc? x))))
    (define ->set
      (lambda (ls) (fold-right (lambda (x s) (if (track? x) (set-cons x s) s)) '() ls)))
    (define ct (map (lambda (u) (cons u '())) uvar*))
    (define add-edge!
      (lambda (a b)                       ; add b into a's list (a is a uvar)
        (let ([e (assq a ct)]) (set-cdr! e (set-cons b (cdr e))))))
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
            (match rhs [(,op ,t1 ,t2) (->set (list t1 t2))])
            (->set (list rhs)))))
    (define Effect*
      (lambda (ef* live)
        (if (null? ef*) live (Effect (car ef*) (Effect* (cdr ef*) live)))))
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
          [,x (format-error 'uncover-conflict "invalid Effect ~s" x)])))
    (define Pred
      (lambda (pr t-live f-live)
        (match pr
          [(true) t-live]
          [(false) f-live]
          [(if ,p ,c ,a) (Pred p (Pred c t-live f-live) (Pred a t-live f-live))]
          [(begin ,ef* ... ,p) (Effect* ef* (Pred p t-live f-live))]
          [(,relop ,x ,y) (guard (relop? relop))
           (union (union t-live f-live) (->set (list x y)))]
          [,x (format-error 'uncover-conflict "invalid Pred ~s" x)])))
    (define Tail
      (lambda (t)
        (match t
          [(if ,p ,c ,a) (Pred p (Tail c) (Tail a))]
          [(begin ,ef* ... ,t) (Effect* ef* (Tail t))]
          [(,triv ,loc* ...) (->set (cons triv loc*))]
          [,x (format-error 'uncover-conflict "invalid Tail ~s" x)])))
    (Tail tail)
    ct))

;; Structured substitution of locations for uvars over a Tail, turning
;; any resulting self-move (set! x x) into (nop).  Used by both
;; finalize-frame-locations (frame homes) and finalize-locations (all).
(define subst-tail
  (lambda (env tail)
    (define v (lambda (x) (cond [(assq x env) => cdr] [else x])))
    (define Effect
      (lambda (ef)
        (match ef
          [(nop) '(nop)]
          [(set! ,var (,op ,t1 ,t2)) `(set! ,(v var) (,op ,(v t1) ,(v t2)))]
          [(set! ,var ,t)
           (let ([var^ (v var)] [t^ (v t)])
             (if (equal? var^ t^) '(nop) `(set! ,var^ ,t^)))]
          [(if ,p ,c ,a) `(if ,(Pred p) ,(Effect c) ,(Effect a))]
          [(begin ,ef* ... ,e) (make-begin `(,@(map Effect ef*) ,(Effect e)))])))
    (define Pred
      (lambda (pr)
        (match pr
          [(true) '(true)]
          [(false) '(false)]
          [(,relop ,t1 ,t2) (guard (relop? relop)) `(,relop ,(v t1) ,(v t2))]
          [(if ,p ,c ,a) `(if ,(Pred p) ,(Pred c) ,(Pred a))]
          [(begin ,ef* ... ,p) (make-begin `(,@(map Effect ef*) ,(Pred p)))])))
    (define Tail
      (lambda (t)
        (match t
          [(if ,p ,c ,a) `(if ,(Pred p) ,(Tail c) ,(Tail a))]
          [(begin ,ef* ... ,t) (make-begin `(,@(map Effect ef*) ,(Tail t)))]
          [(,triv ,loc* ...) `(,(v triv) ,@(map v loc*))])))
    (Tail tail)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; verify-scheme
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define verify-scheme (lambda (program) program))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; uncover-frame-conflict  (a5)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Like register conflicts, but tracks frame variables instead of
;;; registers (all locals pessimistically assumed frame-bound).
(define-who uncover-frame-conflict
  (lambda (program)
    (define Body
      (lambda (bd)
        (match bd
          [(locals (,uvar* ...) ,tail)
           `(locals (,uvar* ...)
              (frame-conflict ,(build-conflict-graph uvar* tail frame-var?) ,tail))]
          [,x (format-error who "invalid Body ~s" x)])))
    (match program
      [(letrec ([,label (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label (lambda () ,body*)] ...) ,body)]
      [,x (format-error who "invalid Program ~s" x)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; introduce-allocation-forms  (a5)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Wrap each body with empty ulocals and locate forms so later iterations
;;; have a uniform shape to work with.
(define-who introduce-allocation-forms
  (lambda (program)
    (define Body
      (lambda (bd)
        (match bd
          [(locals (,uvar* ...) (frame-conflict ,fcg ,tail))
           `(locals (,uvar* ...)
              (ulocals ()
                (locate ()
                  (frame-conflict ,fcg ,tail))))]
          [,x (format-error who "invalid Body ~s" x)])))
    (match program
      [(letrec ([,label (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label (lambda () ,body*)] ...) ,body)]
      [,x (format-error who "invalid Program ~s" x)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; select-instructions  (a5)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Rewrite the code so it obeys x86-64 constraints, introducing
;;; unspillable temporaries (added to ulocals) where registers are
;;; required.  uvars are assumed to be register-homed; frame vars are
;;; memory operands.
(define-who select-instructions
  (lambda (program)
    (define Body
      (lambda (bd)
        (match bd
          [(locate ,home ,tail) bd]     ; complete body, reproduce
          [(locals (,local* ...)
             (ulocals (,ulocal* ...)
               (locate (,fh* ...)
                 (frame-conflict ,fcg ,tail))))
           (let ([new-u* '()])
             (define new-u
               (lambda ()
                 (let ([u (unique-name 't)]) (set! new-u* (cons u new-u*)) u)))
             (define mem? frame-var?)
             (define commutative? (lambda (op) (memq op '(+ * logand logor))))
             (define invert
               (lambda (op) (case op [(<) '>] [(>) '<] [(<=) '>=] [(>=) '<=] [(=) '=])))
             ;; movq triv -> var
             (define select-move
               (lambda (var triv)
                 (if (and (mem? var)
                          (or (mem? triv)
                              (and (int? triv) (not (int32? triv)))
                              (label? triv)))
                     (let ([u (new-u)])
                       (make-begin (list `(set! ,u ,triv) `(set! ,var ,u))))
                     `(set! ,var ,triv))))
             ;; produce (set! var (op var t2)) obeying operand constraints
             (define fix-operand
               (lambda (var op t2)
                 (if (or (and (mem? var) (mem? t2))
                         (and (int? t2) (not (int32? t2)) (not (eq? op 'sra)))
                         (label? t2))
                     (let ([u (new-u)])
                       (make-begin
                         (list `(set! ,u ,t2) `(set! ,var (,op ,var ,u)))))
                     `(set! ,var (,op ,var ,t2)))))
             ;; imulq requires a register destination
             (define fix-second
               (lambda (var op t2)
                 (if (and (eq? op '*) (mem? var))
                     (let ([u (new-u)])
                       (make-begin
                         (list `(set! ,u ,var) (fix-operand u op t2) `(set! ,var ,u))))
                     (fix-operand var op t2))))
             (define select-binop
               (lambda (var op t1 t2)
                 (cond
                   [(eq? t1 var) (fix-second var op t2)]
                   [(and (commutative? op) (eq? t2 var)) (fix-second var op t1)]
                   [(eq? t2 var)                 ; non-commutative, t2 is var
                    (let ([u (new-u)])
                      (make-begin
                        (list (select-move u t1) (fix-second u op t2) (select-move var u))))]
                   [else
                    (make-begin (list (select-move var t1) (fix-second var op t2)))])))
             (define select-relop
               (lambda (op t1 t2)
                 (cond
                   ;; cmpq's first operand (t1 here) cannot be an immediate
                   [(and (int? t1) (not (int? t2))) (select-relop (invert op) t2 t1)]
                   [(int? t1)
                    (let ([u (new-u)])
                      (make-begin (list `(set! ,u ,t1) (select-relop op u t2))))]
                   [(or (and (mem? t1) (mem? t2))
                        (and (int? t2) (not (int32? t2)))
                        (label? t2))
                    (let ([u (new-u)])
                      (make-begin (list `(set! ,u ,t2) `(,op ,t1 ,u))))]
                   [else `(,op ,t1 ,t2)])))
             (define Effect
               (lambda (ef)
                 (match ef
                   [(nop) '(nop)]
                   [(set! ,var (,op ,t1 ,t2)) (select-binop var op t1 t2)]
                   [(set! ,var ,t) (select-move var t)]
                   [(if ,p ,c ,a) `(if ,(Pred p) ,(Effect c) ,(Effect a))]
                   [(begin ,ef* ... ,e) (make-begin `(,@(map Effect ef*) ,(Effect e)))])))
             (define Pred
               (lambda (pr)
                 (match pr
                   [(true) '(true)]
                   [(false) '(false)]
                   [(if ,p ,c ,a) `(if ,(Pred p) ,(Pred c) ,(Pred a))]
                   [(begin ,ef* ... ,p) (make-begin `(,@(map Effect ef*) ,(Pred p)))]
                   [(,relop ,t1 ,t2) (guard (relop? relop)) (select-relop relop t1 t2)])))
             (define Tail
               (lambda (t)
                 (match t
                   [(if ,p ,c ,a) `(if ,(Pred p) ,(Tail c) ,(Tail a))]
                   [(begin ,ef* ... ,tl) (make-begin `(,@(map Effect ef*) ,(Tail tl)))]
                   [(,triv ,loc* ...) `(,triv ,@loc*)])))
             (let ([tail^ (Tail tail)])
               `(locals (,local* ...)
                  (ulocals (,@new-u* ,@ulocal*)
                    (locate (,fh* ...)
                      (frame-conflict ,fcg ,tail^))))))]
          [,x (format-error who "invalid Body ~s" x)])))
    (match program
      [(letrec ([,label (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label (lambda () ,body*)] ...) ,body)]
      [,x (format-error who "invalid Program ~s" x)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; uncover-register-conflict  (a4, extended in a5)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-who uncover-register-conflict
  (lambda (program)
    (define Body
      (lambda (bd)
        (match bd
          [(locate ,home ,tail) bd]     ; complete body, reproduce
          [(locals (,local* ...)
             (ulocals (,ulocal* ...)
               (locate (,fh* ...)
                 (frame-conflict ,fcg ,tail))))
           (let ([ct (build-conflict-graph (append local* ulocal*) tail register?)])
             `(locals (,local* ...)
                (ulocals (,ulocal* ...)
                  (locate (,fh* ...)
                    (frame-conflict ,fcg
                      (register-conflict ,ct ,tail))))))]
          [,x (format-error who "invalid Body ~s" x)])))
    (match program
      [(letrec ([,label (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label (lambda () ,body*)] ...) ,body)]
      [,x (format-error who "invalid Program ~s" x)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; assign-registers  (a4, extended in a5 with spilling)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-who assign-registers
  (lambda (program)
    (define k (length registers))
    ;; returns (values assignments spills); unspillables must get a register
    (define color
      (lambda (spillable* unspillable* ct)
        (define spillable? (lambda (u) (memq u spillable*)))
        (define remove-var
          (lambda (u ct) (map (lambda (e) (cons (car e) (remq u (cdr e)))) ct)))
        (define used
          (lambda (conf assignments)
            (fold-right
              (lambda (x acc)
                (cond
                  [(register? x) (set-cons x acc)]
                  [(assq x assignments) => (lambda (p) (set-cons (cadr p) acc))]
                  [else acc]))
              '() conf)))
        (define pick
          (lambda (uvar* ct)
            (or (find (lambda (u) (< (length (cdr (assq u ct))) k)) uvar*)
                (find spillable? uvar*)
                (car uvar*))))
        (let rec ([uvar* (append unspillable* spillable*)] [ct ct])
          (if (null? uvar*)
              (values '() '())
              (let* ([u (pick uvar* ct)]
                     [u-conf (cdr (assq u ct))])
                (let-values ([(assignments spills) (rec (remq u uvar*) (remove-var u ct))])
                  (let ([avail (difference registers (used u-conf assignments))])
                    (cond
                      [(pair? avail) (values (cons (list u (car avail)) assignments) spills)]
                      [(spillable? u) (values assignments (cons u spills))]
                      [else (format-error who "no register for unspillable ~s" u)]))))))))
    (define Body
      (lambda (bd)
        (match bd
          [(locate ,home ,tail) bd]     ; complete body, reproduce
          [(locals (,local* ...)
             (ulocals (,ulocal* ...)
               (locate (,fh* ...)
                 (frame-conflict ,fcg
                   (register-conflict ,rcg ,tail)))))
           (let-values ([(assignments spills) (color local* ulocal* rcg)])
             (if (null? spills)
                 `(locate ,(append fh* assignments) ,tail)
                 `(locals ,(difference local* spills)
                    (ulocals (,ulocal* ...)
                      (spills ,spills
                        (locate (,fh* ...)
                          (frame-conflict ,fcg ,tail)))))))]
          [,x (format-error who "invalid Body ~s" x)])))
    (match program
      [(letrec ([,label (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label (lambda () ,body*)] ...) ,body)]
      [,x (format-error who "invalid Program ~s" x)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; assign-frame  (a5)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Give each spilled variable a frame home compatible with the frame
;;; conflict graph and the homes already assigned this run.
(define-who assign-frame
  (lambda (program)
    (define first-free
      (lambda (used)
        (let loop ([i 0])
          (let ([fv (index->frame-var i)])
            (if (memq fv used) (loop (+ i 1)) fv)))))
    (define assign-spills
      (lambda (spill* fcg home*)
        (if (null? spill* )
            home*
            (let* ([x (car spill*)]
                   [conf (cond [(assq x fcg) => cdr] [else '()])]
                   [used (fold-right
                           (lambda (c acc)
                             (cond
                               [(frame-var? c) (set-cons c acc)]
                               [(assq c home*) => (lambda (p) (set-cons (cadr p) acc))]
                               [else acc]))
                           '() conf)])
              (assign-spills (cdr spill*) fcg
                (cons (list x (first-free used)) home*))))))
    (define Body
      (lambda (bd)
        (match bd
          [(locate ,home ,tail) bd]     ; complete body, reproduce
          [(locals (,local* ...)
             (ulocals (,ulocal* ...)
               (spills (,spill* ...)
                 (locate (,fh* ...)
                   (frame-conflict ,fcg ,tail)))))
           `(locals (,local* ...)
              (ulocals (,ulocal* ...)
                (locate ,(assign-spills spill* fcg fh*)
                  (frame-conflict ,fcg ,tail))))]
          [,x (format-error who "invalid Body ~s" x)])))
    (match program
      [(letrec ([,label (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label (lambda () ,body*)] ...) ,body)]
      [,x (format-error who "invalid Program ~s" x)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; finalize-frame-locations  (a5)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Substitute frame-allocated uvars with their frame vars, keeping the
;;; locate form (its homes are needed by the next iteration).
(define-who finalize-frame-locations
  (lambda (program)
    (define frame-env
      (lambda (home*)
        (fold-right
          (lambda (b acc) (if (frame-var? (cadr b)) (cons (cons (car b) (cadr b)) acc) acc))
          '() home*)))
    (define Body
      (lambda (bd)
        (match bd
          [(locals ,l (ulocals ,u (locate (,home* ...) (frame-conflict ,fcg ,tail))))
           `(locals ,l (ulocals ,u
              (locate (,home* ...)
                (frame-conflict ,fcg ,(subst-tail (frame-env home*) tail)))))]
          [(locate (,home* ...) ,tail)
           `(locate (,home* ...) ,(subst-tail (frame-env home*) tail))]
          [,x (format-error who "invalid Body ~s" x)])))
    (match program
      [(letrec ([,label (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label (lambda () ,body*)] ...) ,body)]
      [,x (format-error who "invalid Program ~s" x)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; discard-call-live  (a4)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
;;; finalize-locations  (a3, extended in a5 with self-move -> nop)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-who finalize-locations
  (lambda (program)
    (define Body
      (lambda (bd)
        (match bd
          [(locate ([,uvar* ,loc*] ...) ,tail)
           (subst-tail (map cons uvar* loc*) tail)]
          [,x (format-error who "invalid Body ~s" x)])))
    (match program
      [(letrec ([,label (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label (lambda () ,body*)] ...) ,body)]
      [,x (format-error who "invalid Program ~s" x)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; expose-frame-var  (a2, generalized in a3)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
