;;; alloc.scm
;;; Register and frame allocation cluster (a4 + a5).
;;;
;;; The a5 pipeline runs these under an (iterate ...) loop:
;;;   uncover-frame-conflict  introduce-allocation-forms
;;;   (iterate select-instructions uncover-register-conflict assign-registers
;;;            (break when everybody-home?) assign-frame finalize-frame-locations)
;;;   discard-call-live  finalize-locations

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
