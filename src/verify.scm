;;; verify.scm
;;; Front-end verification / parsing.

;;; parse-scheme  (a15)
;;; Replaces verify-scheme: recognizes the full source language, rejects
;;; everything else, and lowers to the a14 source language.
;;;   - syntax + arity checking, unbound-variable detection
;;;   - all variables renamed to unique variables; shadowing of other
;;;     variables, keywords, and primitive names follows Scheme rules
;;;     (no reserved names), via an environment mapping each symbol to a
;;;     var / keyword / prim entry
;;;   - unquoted constants become quoted; datums checked well-formed
;;;     with every fixnum in range
;;;   - implicit-begin bodies, one-armed if, and, or, not expanded away
(define-who parse-scheme
  (lambda (program)
    (define fixnum?
      (lambda (x) (and (integer? x) (exact? x) (fixnum-range? x))))
    (define constant?
      (lambda (x) (or (memq x '(#t #f ())) (fixnum? x))))
    (define datum?
      (lambda (x)
        (or (constant? x)
            (and (pair? x) (datum? (car x)) (datum? (cdr x)))
            (and (vector? x) (andmap datum? (vector->list x))))))
    ;; env entry: (sym . (var . uvar)) | (sym . (keyword . action))
    ;;          | (sym . (prim . arity))
    (define entry-kind cadr)
    (define entry-info cddr)
    (define check-names!
      (lambda (v* x)
        (unless (andmap symbol? v*) (error who "invalid bound name in ~s" x))
        (let loop ([v* v*])
          (unless (null? v*)
            (when (memq (car v*) (cdr v*))
              (error who "duplicate binding of ~s in ~s" (car v*) x))
            (loop (cdr v*))))))
    (define extend                      ; bind v* to fresh uvars
      (lambda (env v*)
        (let ([u* (map unique-name v*)])
          (values u* (append (map (lambda (v u) `(,v var . ,u)) v* u*) env)))))
    (define Body                        ; implicit begin
      (lambda (env e e*)
        (make-begin (map (Expr env) (cons e e*)))))
    (define Expr
      (lambda (env)
        (lambda (x)
          (match x
            [,c (guard (constant? c)) `(quote ,c)]
            [,v (guard (symbol? v))
             (let ([e (assq v env)])
               (unless (and e (eq? (entry-kind e) 'var))
                 (error who "unbound or misplaced identifier ~s" v))
               (entry-info e))]
            [(,h . ,rest) (guard (symbol? h))
             (let ([e (assq h env)])
               (cond
                 [(not e) (error who "unbound variable ~s" h)]
                 [(eq? (entry-kind e) 'keyword) ((entry-info e) env x)]
                 [(eq? (entry-kind e) 'prim) (Prim env x (entry-info e))]
                 [else (App env x)]))]
            [(,h . ,rest) (App env x)]
            [,x (error who "invalid Expr ~s" x)]))))
    (define App
      (lambda (env x)
        (match x
          [(,[(Expr env) -> rator] ,[(Expr env) -> rand*] ...)
           `(,rator ,@rand*)]
          [,x (error who "invalid application ~s" x)])))
    (define Prim
      (lambda (env x arity)
        (match x
          [(,p ,rand* ...)
           (unless (= (length rand*) arity)
             (error who "wrong number of arguments in ~s" x))
           (let ([rand* (map (Expr env) rand*)])
             (if (eq? p 'not)
                 `(if ,(car rand*) (quote #f) (quote #t))
                 `(,p ,@rand*)))]
          [,x (error who "invalid Expr ~s" x)])))
    (define keyword-quote
      (lambda (env x)
        (match x
          [(quote ,d)
           (unless (datum? d) (error who "invalid datum ~s" d))
           `(quote ,d)]
          [,x (error who "invalid Expr ~s" x)])))
    (define keyword-if
      (lambda (env x)
        (match x
          [(if ,[(Expr env) -> p] ,[(Expr env) -> c]) `(if ,p ,c (void))]
          [(if ,[(Expr env) -> p] ,[(Expr env) -> c] ,[(Expr env) -> a])
           `(if ,p ,c ,a)]
          [,x (error who "invalid Expr ~s" x)])))
    (define keyword-and
      (lambda (env x)
        (match x
          [(and ,[(Expr env) -> e*] ...)
           (if (null? e*)
               '(quote #t)
               (let f ([e* e*])
                 (if (null? (cdr e*))
                     (car e*)
                     `(if ,(car e*) ,(f (cdr e*)) (quote #f)))))]
          [,x (error who "invalid Expr ~s" x)])))
    (define keyword-or
      (lambda (env x)
        (match x
          [(or ,[(Expr env) -> e*] ...)
           (if (null? e*)
               '(quote #f)
               (let f ([e* e*])
                 (if (null? (cdr e*))
                     (car e*)
                     (let ([t (unique-name 't)])
                       `(let ([,t ,(car e*)])
                          (if ,t ,t ,(f (cdr e*))))))))]
          [,x (error who "invalid Expr ~s" x)])))
    (define keyword-begin
      (lambda (env x)
        (match x
          [(begin ,e ,e* ...) (Body env e e*)]
          [,x (error who "invalid Expr ~s" x)])))
    (define keyword-lambda
      (lambda (env x)
        (match x
          [(lambda (,fml* ...) ,e ,e* ...)
           (check-names! fml* x)
           (let-values ([(u* env) (extend env fml*)])
             `(lambda ,u* ,(Body env e e*)))]
          [,x (error who "invalid Expr ~s" x)])))
    (define keyword-let
      (lambda (env x)
        (match x
          [(let ([,v* ,[(Expr env) -> r*]] ...) ,e ,e* ...)
           (check-names! v* x)
           (let-values ([(u* env) (extend env v*)])
             `(let ,(map (lambda (u r) `[,u ,r]) u* r*) ,(Body env e e*)))]
          [,x (error who "invalid Expr ~s" x)])))
    (define keyword-letrec
      (lambda (env x)
        (match x
          [(letrec ([,v* ,r*] ...) ,e ,e* ...)
           (check-names! v* x)
           (let-values ([(u* env) (extend env v*)])
             ;; letrec right-hand sides are in the scope of the bindings
             `(letrec ,(map (lambda (u r) `[,u ,((Expr env) r)]) u* r*)
                ,(Body env e e*)))]
          [,x (error who "invalid Expr ~s" x)])))
    (define keyword-set!
      (lambda (env x)
        (match x
          [(set! ,v ,[(Expr env) -> e])
           (let ([entry (and (symbol? v) (assq v env))])
             (unless (and entry (eq? (entry-kind entry) 'var))
               (error who "invalid set! target in ~s" x))
             `(set! ,(entry-info entry) ,e))]
          [,x (error who "invalid Expr ~s" x)])))
    (define initial-env
      `((quote keyword . ,keyword-quote)
        (if keyword . ,keyword-if)
        (and keyword . ,keyword-and)
        (or keyword . ,keyword-or)
        (begin keyword . ,keyword-begin)
        (lambda keyword . ,keyword-lambda)
        (let keyword . ,keyword-let)
        (letrec keyword . ,keyword-letrec)
        (set! keyword . ,keyword-set!)
        (+ prim . 2) (- prim . 2) (* prim . 2)
        (< prim . 2) (<= prim . 2) (= prim . 2) (>= prim . 2) (> prim . 2)
        (boolean? prim . 1) (fixnum? prim . 1) (null? prim . 1)
        (pair? prim . 1) (vector? prim . 1) (procedure? prim . 1)
        (eq? prim . 2) (not prim . 1)
        (cons prim . 2) (car prim . 1) (cdr prim . 1)
        (set-car! prim . 2) (set-cdr! prim . 2)
        (make-vector prim . 1) (vector-length prim . 1)
        (vector-ref prim . 2) (vector-set! prim . 3)
        (void prim . 0)))
    ((Expr initial-env) program)))

;;; verify-uil  (a8)
;;; Checks that the language-dependent front end produced well-formed UIL.
;;; Following the notice, we keep it an identity pass for now.
(define verify-uil (lambda (program) program))
