;;; frontend.scm
;;; Front-end passes that lower the higher-level UIL toward the register/
;;; frame allocation cluster.  Added incrementally from a6 onward:
;;;   a6: remove-complex-opera*  flatten-set!  impose-calling-conventions

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; remove-complex-opera*  (a6)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Make the operands of primitive and procedure calls trivial: each
;;; nontrivial Value operand is hoisted into a fresh local bound by a
;;; preceding set!.  The fresh uvars are added to the enclosing locals.
(define-who remove-complex-opera*
  (lambda (program)
    (define Body
      (lambda (bd)
        (match bd
          [(locals (,local* ...) ,tail)
           (let ([new* '()])
             (define new-local
               (lambda ()
                 (let ([u (unique-name 't)]) (set! new* (cons u new*)) u)))
             ;; Trivialize a Value: returns (values triv effect*) where
             ;; effect* are the set!s that must run first.
             (define Triv
               (lambda (v)
                 (match v
                   [,x (guard (triv? x)) (values x '())]
                   [,other
                    (let ([u (new-local)])
                      (values u (list `(set! ,u ,(Value other)))))])))
             (define Triv*
               (lambda (v*)
                 (let loop ([v* v*] [t* '()] [ef* '()])
                   (if (null? v*)
                       (values (reverse t*) ef*)
                       (let-values ([(t e*) (Triv (car v*))])
                         (loop (cdr v*) (cons t t*) (append ef* e*)))))))
             ;; Value in a context where a begin can surround it.
             (define Value
               (lambda (v)
                 (match v
                   [,x (guard (triv? x)) x]
                   [(if ,[Pred -> p] ,[Value -> c] ,[Value -> a]) `(if ,p ,c ,a)]
                   [(begin ,[Effect -> ef*] ... ,[Value -> v])
                    (make-begin `(,@ef* ,v))]
                   [(alloc ,v)
                    (let-values ([(t* ef*) (Triv* (list v))])
                      (make-begin `(,@ef* (alloc ,@t*))))]
                   [(mref ,v1 ,v2)
                    (let-values ([(t* ef*) (Triv* (list v1 v2))])
                      (make-begin `(,@ef* (mref ,@t*))))]
                   [(,binop ,v1 ,v2) (guard (binop? binop))
                    (let-values ([(t* ef*) (Triv* (list v1 v2))])
                      (make-begin `(,@ef* (,binop ,@t*))))]
                   [(,rator ,rand* ...)
                    (let-values ([(t* ef*) (Triv* (cons rator rand*))])
                      (make-begin `(,@ef* (,@t*))))])))
             (define Effect
               (lambda (ef)
                 (match ef
                   [(nop) '(nop)]
                   [(set! ,uvar ,[Value -> v]) `(set! ,uvar ,v)]
                   [(mset! ,v1 ,v2 ,v3)
                    (let-values ([(t* ef*) (Triv* (list v1 v2 v3))])
                      (make-begin `(,@ef* (mset! ,@t*))))]
                   [(if ,[Pred -> p] ,[Effect -> c] ,[Effect -> a]) `(if ,p ,c ,a)]
                   [(begin ,[Effect -> ef*] ... ,[Effect -> e])
                    (make-begin `(,@ef* ,e))]
                   [(,rator ,rand* ...)              ; nontail call in effect
                    (let-values ([(t* ef*) (Triv* (cons rator rand*))])
                      (make-begin `(,@ef* (,@t*))))])))
             (define Pred
               (lambda (pr)
                 (match pr
                   [(true) '(true)]
                   [(false) '(false)]
                   [(if ,[Pred -> p] ,[Pred -> c] ,[Pred -> a]) `(if ,p ,c ,a)]
                   [(begin ,[Effect -> ef*] ... ,[Pred -> p])
                    (make-begin `(,@ef* ,p))]
                   [(,relop ,v1 ,v2) (guard (relop? relop))
                    (let-values ([(t* ef*) (Triv* (list v1 v2))])
                      (make-begin `(,@ef* (,relop ,@t*))))])))
             (define Tail
               (lambda (t)
                 (match t
                   [,x (guard (triv? x)) x]
                   [(if ,[Pred -> p] ,[Tail -> c] ,[Tail -> a]) `(if ,p ,c ,a)]
                   [(begin ,[Effect -> ef*] ... ,[Tail -> t])
                    (make-begin `(,@ef* ,t))]
                   [(alloc ,v)
                    (let-values ([(t* ef*) (Triv* (list v))])
                      (make-begin `(,@ef* (alloc ,@t*))))]
                   [(mref ,v1 ,v2)
                    (let-values ([(t* ef*) (Triv* (list v1 v2))])
                      (make-begin `(,@ef* (mref ,@t*))))]
                   [(,binop ,v1 ,v2) (guard (binop? binop))
                    (let-values ([(t* ef*) (Triv* (list v1 v2))])
                      (make-begin `(,@ef* (,binop ,@t*))))]
                   [(,rator ,rand* ...)
                    (let-values ([(t* ef*) (Triv* (cons rator rand*))])
                      (make-begin `(,@ef* (,@t*))))])))
             (let ([tail^ (Tail tail)])
               `(locals (,@new* ,@local*) ,tail^)))]
          [,x (format-error who "invalid Body ~s" x)])))
    (match program
      [(letrec ([,label (lambda (,fml* ...) ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label (lambda (,fml* ...) ,body*)] ...) ,body)]
      [,x (format-error who "invalid Program ~s" x)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; flatten-set!  (a6)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Push set! inside the if/begin on its right-hand side so that every
;;; set! ends with a Triv or primitive call.
(define-who flatten-set!
  (lambda (program)
    ;; Produce an Effect that assigns rhs (possibly if/begin) into var.
    (define Set
      (lambda (var rhs)
        (match rhs
          [(begin ,[Effect -> ef*] ... ,v) (make-begin `(,@ef* ,(Set var v)))]
          [(if ,[Pred -> p] ,c ,a) `(if ,p ,(Set var c) ,(Set var a))]
          [,triv `(set! ,var ,triv)])))
    (define Effect
      (lambda (ef)
        (match ef
          [(nop) '(nop)]
          [(set! ,var ,rhs) (Set var rhs)]
          [(if ,[Pred -> p] ,[Effect -> c] ,[Effect -> a]) `(if ,p ,c ,a)]
          [(begin ,[Effect -> ef*] ... ,[Effect -> e]) (make-begin `(,@ef* ,e))]
          [(,rator ,rand* ...) `(,rator ,rand* ...)])))  ; nontail call
    (define Pred
      (lambda (pr)
        (match pr
          [(true) '(true)]
          [(false) '(false)]
          [(,relop ,t1 ,t2) (guard (relop? relop)) `(,relop ,t1 ,t2)]
          [(if ,[Pred -> p] ,[Pred -> c] ,[Pred -> a]) `(if ,p ,c ,a)]
          [(begin ,[Effect -> ef*] ... ,[Pred -> p]) (make-begin `(,@ef* ,p))])))
    (define Tail
      (lambda (t)
        (match t
          [(if ,[Pred -> p] ,[Tail -> c] ,[Tail -> a]) `(if ,p ,c ,a)]
          [(begin ,[Effect -> ef*] ... ,[Tail -> t]) (make-begin `(,@ef* ,t))]
          [,other other])))            ; Triv, (binop ..), or (rator ..)
    (define Body
      (lambda (bd)
        (match bd
          [(locals (,local* ...) ,[Tail -> tail]) `(locals (,local* ...) ,tail)]
          [,x (format-error who "invalid Body ~s" x)])))
    (match program
      [(letrec ([,label (lambda (,fml* ...) ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label (lambda (,fml* ...) ,body*)] ...) ,body)]
      [,x (format-error who "invalid Program ~s" x)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; impose-calling-conventions  (a6)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Realize the calling conventions: formal parameters become locals
;;; initialized from parameter registers / frame vars; procedure and
;;; primitive-call tails become an assignment to the return-value
;;; register followed by a jump to the return point; call operands get
;;; assigned into argument locations.  Output is the input language of
;;; uncover-frame-conflict.
(define-who impose-calling-conventions
  (lambda (program)
    (define fp frame-pointer-register)
    (define rv return-value-register)
    (define ra return-address-register)
    (define ap allocation-pointer-register)
    ;; nth-arg-locations: registers first, then fv0, fv1, ...
    (define arg-locations
      (lambda (n)
        (let loop ([i 0] [regs parameter-registers] [acc '()])
          (cond
            [(= i n) (reverse acc)]
            [(pair? regs) (loop (+ i 1) (cdr regs) (cons (car regs) acc))]
            [else (loop (+ i 1) '()
                    (cons (index->frame-var (- i (length parameter-registers))) acc))]))))
    ;; separate the frame-var argument sets before the register ones, so
    ;; the parameter registers have the shortest live ranges.
    (define frame-first
      (lambda (sets locs)
        (let loop ([sets sets] [locs locs] [f '()] [r '()])
          (if (null? sets)
              (append (reverse f) (reverse r))
              (if (frame-var? (car locs))
                  (loop (cdr sets) (cdr locs) (cons (car sets) f) r)
                  (loop (cdr sets) (cdr locs) f (cons (car sets) r)))))))
    (define Body
      (lambda (bd fml*)
        (match bd
          [(locals (,local* ...) ,tail)
           (let ([rp (unique-name 'rp)] [nf* '()] [new-local* '()])
             (define new-nfv
               (lambda ()
                 (let ([u (unique-name 'nfv)])
                   (set! new-local* (cons u new-local*)) u)))
             ;; A tail call: return address is the enclosing body's rp.
             (define Tail-call
               (lambda (rator rand*)
                 (let* ([locs (arg-locations (length rand*))]
                        [set-args (frame-first
                                    (map (lambda (loc r) `(set! ,loc ,r)) locs rand*)
                                    locs)])
                   (make-begin
                     `(,@set-args
                       (set! ,ra ,rp)
                       (,rator ,fp ,ra ,ap ,@locs))))))
             ;; A nontail call: wrap a return-point.  Frame args go into
             ;; fresh new-frame variables (assign-new-frame places them).
             (define Nontail-call
               (lambda (rator rand*)
                 (let* ([n (length rand*)]
                        [nreg (length parameter-registers)]
                        [reg-locs (list-head parameter-registers (min n nreg))]
                        [nfv* (map (lambda (_) (new-nfv))
                                   (make-list (max 0 (- n nreg))))]
                        [locs (append reg-locs nfv*)]
                        [rp-lab (unique-label 'rp)]
                        ;; frame (new-frame) sets first, then register sets
                        [set-frame (map (lambda (v r) `(set! ,v ,r))
                                        nfv* (list-tail rand* (min n nreg)))]
                        [set-reg (map (lambda (v r) `(set! ,v ,r))
                                      reg-locs (list-head rand* (min n nreg)))])
                   (set! nf* (cons nfv* nf*))
                   `(return-point ,rp-lab
                      ,(make-begin
                         `(,@set-frame
                           ,@set-reg
                           (set! ,ra ,rp-lab)
                           (,rator ,fp ,ra ,ap ,@locs)))))))
             (define Tail
               (lambda (t)
                 (match t
                   [(if ,[Pred -> p] ,[Tail -> c] ,[Tail -> a]) `(if ,p ,c ,a)]
                   [(begin ,[Effect -> ef*] ... ,[Tail -> t]) (make-begin `(,@ef* ,t))]
                   [(alloc ,v)
                    (make-begin `((set! ,rv (alloc ,v)) (,rp ,fp ,rv)))]
                   [(mref ,t1 ,t2)
                    (make-begin `((set! ,rv (mref ,t1 ,t2)) (,rp ,fp ,rv)))]
                   [(,binop ,x ,y) (guard (binop? binop))
                    (make-begin `((set! ,rv (,binop ,x ,y)) (,rp ,fp ,rv)))]
                   [,triv (guard (triv? triv))
                    (make-begin `((set! ,rv ,triv) (,rp ,fp ,rv)))]
                   [(,rator ,rand* ...) (Tail-call rator rand*)])))
             (define Effect
               (lambda (ef)
                 (match ef
                   [(nop) '(nop)]
                   [(mset! ,t1 ,t2 ,t3) `(mset! ,t1 ,t2 ,t3)]
                   [(set! ,var (alloc ,v)) `(set! ,var (alloc ,v))]
                   [(set! ,var (mref ,t1 ,t2)) `(set! ,var (mref ,t1 ,t2))]
                   [(set! ,var (,binop ,x ,y)) (guard (binop? binop))
                    `(set! ,var (,binop ,x ,y))]
                   [(set! ,var (,rator ,rand* ...))       ; nontail call, keep value
                    (make-begin
                      `(,(Nontail-call rator rand*)
                        (set! ,var ,rv)))]
                   [(set! ,var ,rhs) `(set! ,var ,rhs)]
                   [(if ,[Pred -> p] ,[Effect -> c] ,[Effect -> a]) `(if ,p ,c ,a)]
                   [(begin ,[Effect -> ef*] ... ,[Effect -> e]) (make-begin `(,@ef* ,e))]
                   [(,rator ,rand* ...) (Nontail-call rator rand*)])))
             (define Pred
               (lambda (pr)
                 (match pr
                   [(true) '(true)]
                   [(false) '(false)]
                   [(,relop ,t1 ,t2) (guard (relop? relop)) `(,relop ,t1 ,t2)]
                   [(if ,[Pred -> p] ,[Pred -> c] ,[Pred -> a]) `(if ,p ,c ,a)]
                   [(begin ,[Effect -> ef*] ... ,[Pred -> p]) (make-begin `(,@ef* ,p))])))
             ;; initialize formal params from their incoming locations
             (let* ([locs (arg-locations (length fml*))]
                    [set-params (map (lambda (x loc) `(set! ,x ,loc)) fml* locs)]
                    [tail^ (Tail tail)])
               `(locals (,rp ,@new-local* ,@fml* ,@local*)
                  (new-frames ,(reverse nf*)
                    ,(make-begin
                       `((set! ,rp ,ra)
                         ,@set-params
                         ,tail^))))))]
          [,x (format-error who "invalid Body ~s" x)])))
    (match program
      [(letrec ([,label (lambda (,fml** ...) ,body*)] ...) ,body)
       (let ([body^* (map Body body* fml**)])
         `(letrec ([,label (lambda () ,body^*)] ...)
            ,(Body body '())))]
      [,x (format-error who "invalid Program ~s" x)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; expose-allocation-pointer  (a8)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Turn each allocation into an explicit bump of the allocation-pointer
;;; register: (set! x (alloc n)) => (begin (set! x ap) (set! ap (+ ap n))).
;;; A grammar-independent tree walk suffices; by this point alloc only
;;; appears as the right-hand side of a set!.
(define-who expose-allocation-pointer
  (lambda (program)
    (define ap allocation-pointer-register)
    (let walk ([x program])
      (match x
        [(set! ,var (alloc ,n))
         `(begin (set! ,var ,ap) (set! ,ap (+ ,ap ,n)))]
        [(,[walk -> a] . ,[walk -> d]) (cons a d)]
        [,atom atom]))))
