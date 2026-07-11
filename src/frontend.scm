;;; frontend.scm
;;; Front-end passes that lower the higher-level UIL toward the register/
;;; frame allocation cluster.  Added incrementally from a6 onward:
;;;   a6:  remove-complex-opera*  flatten-set!  impose-calling-conventions
;;;   a9:  uncover-locals  remove-let  (the first language-dependent passes)
;;;   a10: specify-representation  (Scheme datatypes/prims -> UIL ptrs)
;;;   a11: lift-letrec  normalize-context  (letrec anywhere; context split)
;;;   a12: uncover-free  convert-closures  introduce-procedure-primitives

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; uncover-free  (a12)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Wrap each lambda body in (free (uvar*) body), listing the variables
;;; that occur free in it.  Expr returns (values expr^ free*); the free
;;; set of a lambda body (minus its formals) is what gets recorded, and
;;; the procedure name stays free in its own body (recursion) because it
;;; is only removed at the enclosing letrec.
(define-who uncover-free
  (lambda (program)
    (define Expr
      (lambda (e)
        (match e
          [,u (guard (uvar? u)) (values u (list u))]
          [(quote ,i) (values `(quote ,i) '())]
          [(if ,[Expr -> p pf] ,[Expr -> c cf] ,[Expr -> a af])
           (values `(if ,p ,c ,a) (union pf cf af))]
          [(begin ,[Expr -> e* ef*] ... ,[Expr -> t tf])
           (values (make-begin `(,@e* ,t)) (apply union tf ef*))]
          [(let ([,u* ,[Expr -> r* rf*]] ...) ,[Expr -> body bf])
           (values `(let ([,u* ,r*] ...) ,body)
                   (union (apply union rf*) (difference bf u*)))]
          [(letrec ([,name* (lambda (,fml** ...) ,[Expr -> lbody* lbf*])] ...)
             ,[Expr -> body bf])
           ;; each lambda records its own free set (body free minus formals)
           (let* ([lfree* (map difference lbf* fml**)]
                  [lam* (map (lambda (fml lfree lbody)
                               `(lambda ,fml (free ,lfree ,lbody)))
                             fml** lfree* lbody*)]
                  ;; free of the whole letrec: bodies' + body's free, minus names
                  [all (difference (apply union bf lfree*) name*)])
             (values `(letrec ([,name* ,lam*] ...) ,body) all))]
          [(,p ,[Expr -> a* af*] ...) (guard (prim? p))
           (values `(,p ,@a*) (apply union '() af*))]
          [(,[Expr -> rator rf] ,[Expr -> rand* randf*] ...)
           (values `(,rator ,@rand*) (apply union rf randf*))])))
    (let-values ([(e _) (Expr program)]) e)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; convert-closures  (a12)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Turn each letrec-bound procedure into an explicit closure.  Each
;;; lambda gains a leading closure-pointer parameter cp; (free f*) becomes
;;; (bind-free (cp f*)); the letrec body is wrapped in (closures ([name
;;; label free*] ...) body); every call passes the operator as its own
;;; first argument.  letrec names become labels.
(define-who convert-closures
  (lambda (program)
    (define Expr
      (lambda (e)
        (match e
          [,u (guard (uvar? u)) u]
          [(quote ,i) `(quote ,i)]
          [(if ,[Expr -> p] ,[Expr -> c] ,[Expr -> a]) `(if ,p ,c ,a)]
          [(begin ,[Expr -> e*] ... ,[Expr -> t]) (make-begin `(,@e* ,t))]
          [(let ([,u* ,[Expr -> r*]] ...) ,[Expr -> body])
           `(let ([,u* ,r*] ...) ,body)]
          [(letrec ([,name* (lambda (,fml** ...)
                              (free (,free** ...) ,[Expr -> lbody*]))] ...)
             ,[Expr -> body])
           (let ([label* (map unique-label name*)]
                 [cp* (map (lambda (_) (unique-name 'cp)) name*)])
             `(letrec ([,label* (lambda (,cp* ,fml** ...)
                                  (bind-free (,cp* ,free** ...) ,lbody*))] ...)
                (closures ([,name* ,label* ,free** ...] ...) ,body)))]
          [(,p ,[Expr -> a*] ...) (guard (prim? p)) `(,p ,@a*)]
          ;; a procedure call passes the operator as its own first
          ;; argument.  A non-variable operator must be evaluated once, so
          ;; bind it to a temp rather than duplicating the expression.
          [(,[Expr -> rator] ,[Expr -> rand*] ...)
           (if (uvar? rator)
               `(,rator ,rator ,@rand*)
               (let ([t (unique-name 'tmp)])
                 `(let ([,t ,rator]) (,t ,t ,@rand*))))])))
    (Expr program)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; introduce-procedure-primitives  (a12)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Make closure operations explicit.  Free-variable references inside a
;;; procedure become (procedure-ref cp n); (closures ...) becomes
;;; make-procedure allocations followed by procedure-set! fills; a call
;;; wraps its operator in (procedure-code op) unless it is already a
;;; label.  bind-free is dropped after recording the cp->free mapping.
(define-who introduce-procedure-primitives
  (lambda (program)
    ;; index of free var f within cp's free list -> (procedure-ref cp n)
    (define ref-of
      (lambda (cp free*)
        (lambda (f)
          (let loop ([f* free*] [n 0])
            (cond
              [(null? f*) f]                     ; not free here: leave as is
              [(eq? (car f*) f) `(procedure-ref ,cp (quote ,n))]
              [else (loop (cdr f*) (+ n 1))])))))
    (define Expr
      (lambda (ref)
        (lambda (e)
          (match e
            [,u (guard (uvar? u)) (ref u)]
            [,l (guard (label? l)) l]
            [(quote ,i) `(quote ,i)]
            [(if ,[(Expr ref) -> p] ,[(Expr ref) -> c] ,[(Expr ref) -> a])
             `(if ,p ,c ,a)]
            [(begin ,[(Expr ref) -> e*] ... ,[(Expr ref) -> t])
             (make-begin `(,@e* ,t))]
            [(let ([,u* ,[(Expr ref) -> r*]] ...) ,[(Expr ref) -> body])
             `(let ([,u* ,r*] ...) ,body)]
            [(letrec ([,label* (lambda (,cp* ,fml** ...)
                                 (bind-free (,cp2* ,free** ...) ,lbody*))] ...)
               ,[(Expr ref) -> body])
             (let ([lam* (map (lambda (cp fml free lbody)
                                `(lambda (,cp ,@fml)
                                   ,((Expr (ref-of cp free)) lbody)))
                              cp* fml** free** lbody*)])
               `(letrec ([,label* ,lam*] ...) ,body))]
            [(closures ([,name* ,clabel* ,cfree** ...] ...) ,[(Expr ref) -> body])
             ;; allocate each closure, then fill in its free-var slots
             (let ([bind* (map (lambda (name clabel free*)
                                 `[,name (make-procedure ,clabel
                                           (quote ,(length free*)))])
                               name* clabel* cfree**)]
                   [set*
                     (apply append
                       (map (lambda (name free*)
                              (let loop ([f* free*] [n 0] [acc '()])
                                (if (null? f*)
                                    (reverse acc)
                                    (loop (cdr f*) (+ n 1)
                                      (cons `(procedure-set! ,name (quote ,n)
                                               ,(ref (car f*)))
                                            acc)))))
                            name* cfree**))])
               `(let ,bind* ,(make-begin `(,@set* ,body))))]
            [(,p ,[(Expr ref) -> a*] ...) (guard (prim? p)) `(,p ,@a*)]
            ;; a call: (op op args...) -> ((procedure-code op) op args...)
            ;; unless op is a label already (it never is at this point)
            [(,[(Expr ref) -> rator] ,[(Expr ref) -> rand*] ...)
             (if (label? rator)
                 `(,rator ,@rand*)
                 `((procedure-code ,rator) ,@rand*))]))))
    ((Expr (lambda (u) u)) program)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; lift-letrec  (a11)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; letrec may now appear anywhere.  Since labels are globally unique and
;;; lambdas have no free uvars, we can hoist every letrec's bindings into
;;; a single top-level letrec and drop the internal letrec forms.  One
;;; grammar-independent walk collects bindings (recurring into each
;;; lambda body and rhs) and returns the letrec-free expression.
(define-who lift-letrec
  (lambda (program)
    (define binding* '())
    (define lift
      (lambda (x)
        (match x
          [(letrec ([,label (lambda (,fml* ...) ,[lift -> body*])] ...) ,[lift -> e])
           (for-each
             (lambda (l f b) (set! binding* (cons `[,l (lambda ,f ,b)] binding*)))
             label fml* body*)
           e]
          [(,[lift -> a] . ,[lift -> d]) (cons a d)]
          [,atom atom])))
    (let ([e (lift program)])
      `(letrec ,(reverse binding*) ,e))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; normalize-context  (a11)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Every expr may appear in value / predicate / effect context on input;
;;; split them so each prim call and constant lands only where it is
;;; legal, matching the a10 source grammar.  Three mutually-recursive
;;; handlers, one per context.
(define-who normalize-context
  (lambda (program)
    (define make-nopless-begin
      (lambda (x*)
        (let ([x* (remove '(nop) x*)])
          (if (null? x*) '(nop) (make-begin x*)))))
    (define Value
      (lambda (e)
        (match e
          [,lbl (guard (label? lbl)) lbl]
          [,u (guard (uvar? u)) u]
          [(quote ,i) `(quote ,i)]
          [(if ,[Pred -> p] ,[Value -> c] ,[Value -> a]) `(if ,p ,c ,a)]
          [(begin ,[Effect -> e*] ... ,[Value -> v]) (make-nopless-begin `(,@e* ,v))]
          [(let ([,u* ,[Value -> r*]] ...) ,[Value -> body])
           `(let ([,u* ,r*] ...) ,body)]
          [(,p ,[Value -> a*] ...) (guard (value-prim? p)) `(,p ,@a*)]
          ;; a predicate prim in value context: compute its boolean
          [(,p ,a* ...) (guard (pred-prim? p))
           `(if ,(Pred e) (quote #t) (quote #f))]
          ;; an effect prim in value context: run it, yield void
          [(,p ,a* ...) (guard (effect-prim? p)) (make-begin (list (Effect e) '(void)))]
          [(,[Value -> rator] ,[Value -> rand*] ...) `(,rator ,@rand*)])))
    (define Pred
      (lambda (e)
        (match e
          [,lbl (guard (label? lbl)) `(if (eq? ,lbl (quote #f)) (false) (true))]
          [,u (guard (uvar? u)) `(if (eq? ,u (quote #f)) (false) (true))]
          [(quote ,i) (if (eq? i #f) '(false) '(true))]
          [(if ,[Pred -> p] ,[Pred -> c] ,[Pred -> a]) `(if ,p ,c ,a)]
          [(begin ,[Effect -> e*] ... ,[Pred -> p]) (make-nopless-begin `(,@e* ,p))]
          [(let ([,u* ,[Value -> r*]] ...) ,[Pred -> body])
           `(let ([,u* ,r*] ...) ,body)]
          [(,p ,[Value -> a*] ...) (guard (pred-prim? p)) `(,p ,@a*)]
          ;; a value prim or a call in predicate context: test for #f
          [,other `(if (eq? ,(Value other) (quote #f)) (false) (true))])))
    (define Effect
      (lambda (e)
        (match e
          [,lbl (guard (label? lbl)) '(nop)]
          [,u (guard (uvar? u)) '(nop)]
          [(quote ,i) '(nop)]
          [(if ,[Pred -> p] ,[Effect -> c] ,[Effect -> a]) `(if ,p ,c ,a)]
          [(begin ,[Effect -> e*] ... ,[Effect -> e]) (make-nopless-begin `(,@e* ,e))]
          [(let ([,u* ,[Value -> r*]] ...) ,[Effect -> body])
           `(let ([,u* ,r*] ...) ,body)]
          [(,p ,[Value -> a*] ...) (guard (effect-prim? p)) `(,p ,@a*)]
          ;; value/pred prim in effect context: drop the call, keep the
          ;; operands' effects (each processed in effect context).
          [(,p ,a* ...) (guard (or (value-prim? p) (pred-prim? p)))
           (make-nopless-begin (map Effect a*))]
          [(,[Value -> rator] ,[Value -> rand*] ...) `(,rator ,@rand*)])))
    (match program
      [(letrec ([,label (lambda (,fml* ...) ,[Value -> body*])] ...) ,[Value -> body])
       `(letrec ([,label (lambda (,fml* ...) ,body*)] ...) ,body)]
      [,x (format-error who "invalid Program ~s" x)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; specify-representation  (a10)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Convert Scheme datatypes to their tagged ptr integers and Scheme
;;; primitives to UIL primitives (alloc / mref / mset! / binops).  All
;;; tag/mask/disp constants come from helpers.scm -- never hard-coded --
;;; so alternative tag assignments keep working.  Runs before
;;; uncover-locals, so freshly introduced lets need no special handling.
(define-who specify-representation
  (lambda (program)
    ;; byte offsets from a tagged ptr to each field
    (define offset-car (- disp-car tag-pair))
    (define offset-cdr (- disp-cdr tag-pair))
    (define offset-vector-length (- disp-vector-length tag-vector))
    (define offset-vector-data (- disp-vector-data tag-vector))
    (define offset-procedure-code (- disp-procedure-code tag-procedure))
    (define offset-procedure-data (- disp-procedure-data tag-procedure))
    ;; a quoted/immediate constant, already specified, is a bare integer
    (define Immediate
      (lambda (i)
        (cond
          [(eq? i #t) $true]
          [(eq? i #f) $false]
          [(null? i) $nil]
          [(and (integer? i) (exact? i)) (ash i shift-fixnum)]
          [else (format-error who "invalid immediate ~s" i)])))
    ;; add a (possibly constant) byte index to a base offset, folding at
    ;; compile time when the index is a specified constant (a number).
    (define idx+
      (lambda (base idx)
        (if (number? idx) (+ base idx) `(+ ,base ,idx))))
    ;; (* 8a 8b) must yield 8ab, so one operand is shifted back down by
    ;; shift-fixnum -- at compile time when that operand is constant.
    (define mult
      (lambda (x y)
        (cond
          [(number? x) `(* ,(sra x shift-fixnum) ,y)]
          [(number? y) `(* ,x ,(sra y shift-fixnum))]
          [else `(* ,x (sra ,y ,shift-fixnum))])))
    (define cons-form
      (lambda (a d)
        (let ([tc (unique-name 'tmp)] [td (unique-name 'tmp)]
              [tp (unique-name 'tmp)])
          `(let ([,tc ,a] [,td ,d])
             (let ([,tp (+ (alloc ,size-pair) ,tag-pair)])
               (begin
                 (mset! ,tp ,offset-car ,tc)
                 (mset! ,tp ,offset-cdr ,td)
                 ,tp))))))
    (define make-vector-form
      (lambda (size)
        (let ([tp (unique-name 'tmp)])
          (if (number? size)
              `(let ([,tp (+ (alloc ,(+ disp-vector-data size)) ,tag-vector)])
                 (begin (mset! ,tp ,offset-vector-length ,size) ,tp))
              (let ([ts (unique-name 'tmp)])
                `(let ([,ts ,size])
                   (let ([,tp (+ (alloc (+ ,disp-vector-data ,ts)) ,tag-vector)])
                     (begin (mset! ,tp ,offset-vector-length ,ts) ,tp))))))))
    ;; a closure: code slot at offset-procedure-code, then n free-var
    ;; slots.  The count n arrives as a specified fixnum ptr (8n bytes).
    (define make-procedure-form
      (lambda (label n)
        (let ([tp (unique-name 'tmp)])
          `(let ([,tp (+ (alloc ,(+ disp-procedure-data n)) ,tag-procedure)])
             (begin (mset! ,tp ,offset-procedure-code ,label) ,tp)))))
    (define value-prim
      (lambda (p a*)
        (case p
          [(+ -) `(,p ,(car a*) ,(cadr a*))]
          [(*) (mult (car a*) (cadr a*))]
          [(car) `(mref ,(car a*) ,offset-car)]
          [(cdr) `(mref ,(car a*) ,offset-cdr)]
          [(cons) (cons-form (car a*) (cadr a*))]
          [(make-vector) (make-vector-form (car a*))]
          [(vector-length) `(mref ,(car a*) ,offset-vector-length)]
          [(vector-ref) `(mref ,(car a*) ,(idx+ offset-vector-data (cadr a*)))]
          [(void) $void]
          [(make-procedure) (make-procedure-form (car a*) (cadr a*))]
          [(procedure-code) `(mref ,(car a*) ,offset-procedure-code)]
          [(procedure-ref)
           `(mref ,(car a*) ,(idx+ offset-procedure-data (cadr a*)))])))
    (define pred-prim
      (lambda (p a*)
        (case p
          [(< <= = >= >) `(,p ,(car a*) ,(cadr a*))]
          [(eq?) `(= ,(car a*) ,(cadr a*))]
          [(null?) `(= ,(car a*) ,$nil)]
          [(pair?) `(= (logand ,(car a*) ,mask-pair) ,tag-pair)]
          [(vector?) `(= (logand ,(car a*) ,mask-vector) ,tag-vector)]
          [(fixnum?) `(= (logand ,(car a*) ,mask-fixnum) ,tag-fixnum)]
          [(boolean?) `(= (logand ,(car a*) ,mask-boolean) ,tag-boolean)]
          [(procedure?) `(= (logand ,(car a*) ,mask-procedure) ,tag-procedure)])))
    (define effect-prim
      (lambda (p a*)
        (case p
          [(set-car!) `(mset! ,(car a*) ,offset-car ,(cadr a*))]
          [(set-cdr!) `(mset! ,(car a*) ,offset-cdr ,(cadr a*))]
          [(vector-set!)
           `(mset! ,(car a*) ,(idx+ offset-vector-data (cadr a*)) ,(caddr a*))]
          [(procedure-set!)
           `(mset! ,(car a*) ,(idx+ offset-procedure-data (cadr a*)) ,(caddr a*))])))
    (define Value
      (lambda (v)
        (match v
          [(quote ,i) (Immediate i)]
          [,lbl (guard (label? lbl)) lbl]
          [,u (guard (uvar? u)) u]
          [(if ,[Pred -> p] ,[Value -> c] ,[Value -> a]) `(if ,p ,c ,a)]
          [(begin ,[Effect -> e*] ... ,[Value -> v]) (make-begin `(,@e* ,v))]
          [(let ([,u* ,[Value -> r*]] ...) ,[Value -> body])
           `(let ([,u* ,r*] ...) ,body)]
          [(,p ,[Value -> a*] ...) (guard (value-prim? p)) (value-prim p a*)]
          [(,[Value -> rator] ,[Value -> rand*] ...) `(,rator ,@rand*)])))
    (define Pred
      (lambda (pr)
        (match pr
          [(true) '(true)]
          [(false) '(false)]
          [(if ,[Pred -> p] ,[Pred -> c] ,[Pred -> a]) `(if ,p ,c ,a)]
          [(begin ,[Effect -> e*] ... ,[Pred -> p]) (make-begin `(,@e* ,p))]
          [(let ([,u* ,[Value -> r*]] ...) ,[Pred -> body])
           `(let ([,u* ,r*] ...) ,body)]
          [(,p ,[Value -> a*] ...) (guard (pred-prim? p)) (pred-prim p a*)])))
    (define Effect
      (lambda (ef)
        (match ef
          [(nop) '(nop)]
          [(if ,[Pred -> p] ,[Effect -> c] ,[Effect -> a]) `(if ,p ,c ,a)]
          [(begin ,[Effect -> e*] ... ,[Effect -> e]) (make-begin `(,@e* ,e))]
          [(let ([,u* ,[Value -> r*]] ...) ,[Effect -> body])
           `(let ([,u* ,r*] ...) ,body)]
          [(,p ,[Value -> a*] ...) (guard (effect-prim? p)) (effect-prim p a*)]
          [(,[Value -> rator] ,[Value -> rand*] ...) `(,rator ,@rand*)])))
    (match program
      [(letrec ([,label (lambda (,fml* ...) ,[Value -> body*])] ...) ,[Value -> body])
       `(letrec ([,label (lambda (,fml* ...) ,body*)] ...) ,body)]
      [,x (format-error who "invalid Program ~s" x)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; uncover-locals  (a9)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The source language binds locals with let instead of a locals form.
;;; Collect every let-bound uvar in each lambda/letrec body and wrap the
;;; body in (locals (uvar*) Tail).  Lambda parameters are not locals, so
;;; only let left-hand sides are gathered.  Since bodies contain no
;;; nested lambdas, a single grammar-independent walk suffices.
(define-who uncover-locals
  (lambda (program)
    (define collect
      (lambda (x)
        (match x
          [(let ([,u* ,[collect -> r*]] ...) ,[collect -> b])
           (union u* (fold-right union b r*))]
          [(,[collect -> a] . ,[collect -> d]) (union a d)]
          [,atom '()])))
    (define Body (lambda (body) `(locals ,(collect body) ,body)))
    (match program
      [(letrec ([,label (lambda (,fml* ...) ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label (lambda (,fml* ...) ,body*)] ...) ,body)]
      [,x (format-error who "invalid Program ~s" x)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; remove-let  (a9)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Replace each let with set!s over its now-declared locals:
;;;   (let ([x e] ...) body) => (begin (set! x e) ... body)
;;; A begin is legal in every context a let could appear (Tail, Pred,
;;; Effect, Value), so a uniform tree walk handles them all; make-begin
;;; keeps the result flat.
(define-who remove-let
  (lambda (program)
    (define rem
      (lambda (x)
        (match x
          [(let ([,u* ,[rem -> e*]] ...) ,[rem -> body])
           (make-begin `(,@(map (lambda (u e) `(set! ,u ,e)) u* e*) ,body))]
          [(,[rem -> a] . ,[rem -> d]) (cons a d)]
          [,atom atom])))
    (rem program)))

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
