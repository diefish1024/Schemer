;;; codegen.scm
;;; Back end: lower the intermediate language down to x86-64.
;;;   expose-frame-var  expose-basic-blocks  flatten-program  generate-x86-64

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; expose-frame-var  (a2/a3, made flow-sensitive in a7)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Replace each frame variable fvN with a displacement operand
;;; #<disp rbp (8N - off)>.  Because a7 bumps the frame pointer around
;;; nontail calls, we track the running byte offset `off` by which rbp
;;; has been advanced and subtract it from each frame-var displacement.
(define-who expose-frame-var
  (lambda (program)
    (define fp frame-pointer-register)
    (define fv->disp
      (lambda (x off)
        (if (frame-var? x)
            (make-disp-opnd fp (- (ash (frame-var->index x) align-shift) off))
            x)))
    ;; Triv / operand rewrite (no fp change): plain substitution.
    (define Triv (lambda (x off) (fv->disp x off)))
    (define Effect
      (lambda (ef off)
        (match ef
          [(nop) (values '(nop) off)]
          [(set! ,v (,op ,t1 ,t2)) (guard (eq? v fp) (memq op '(+ -)) (int? t2))
           ;; frame-pointer adjustment: shift the running offset
           (values `(set! ,fp (,op ,fp ,t2))
                   (if (eq? op '+) (+ off t2) (- off t2)))]
          [(set! ,v (,op ,t1 ,t2))
           (values `(set! ,(fv->disp v off) (,op ,(fv->disp t1 off) ,(fv->disp t2 off))) off)]
          [(set! ,v ,t) (values `(set! ,(fv->disp v off) ,(fv->disp t off)) off)]
          [(return-point ,rp-lab ,tail)
           (let-values ([(t o^) (Tail tail off)])
             (values `(return-point ,rp-lab ,t) o^))]
          [(if ,p ,c ,a)
           (let-values ([(p^ po) (Pred p off)])
             (let-values ([(c^ co) (Effect c po)] [(a^ ao) (Effect a po)])
               (values `(if ,p^ ,c^ ,a^) co)))]
          [(begin ,ef* ... ,e)
           (let-values ([(ef*^ o^) (Effect* ef* off)])
             (let-values ([(e^ o^^) (Effect e o^)])
               (values (make-begin `(,@ef*^ ,e^)) o^^)))])))
    (define Effect*
      (lambda (ef* off)
        (if (null? ef*)
            (values '() off)
            (let-values ([(e^ o^) (Effect (car ef*) off)])
              (let-values ([(rest o^^) (Effect* (cdr ef*) o^)])
                (values (cons e^ rest) o^^))))))
    (define Pred
      (lambda (pr off)
        (match pr
          [(true) (values '(true) off)]
          [(false) (values '(false) off)]
          [(,relop ,t1 ,t2) (guard (relop? relop))
           (values `(,relop ,(fv->disp t1 off) ,(fv->disp t2 off)) off)]
          [(if ,p ,c ,a)
           (let-values ([(p^ po) (Pred p off)])
             (let-values ([(c^ co) (Pred c po)] [(a^ ao) (Pred a po)])
               (values `(if ,p^ ,c^ ,a^) co)))]
          [(begin ,ef* ... ,p)
           (let-values ([(ef*^ o^) (Effect* ef* off)])
             (let-values ([(p^ o^^) (Pred p o^)])
               (values (make-begin `(,@ef*^ ,p^)) o^^)))])))
    (define Tail
      (lambda (t off)
        (match t
          [(if ,p ,c ,a)
           (let-values ([(p^ po) (Pred p off)])
             (let-values ([(c^ co) (Tail c po)] [(a^ ao) (Tail a po)])
               (values `(if ,p^ ,c^ ,a^) co)))]
          [(begin ,ef* ... ,t)
           (let-values ([(ef*^ o^) (Effect* ef* off)])
             (let-values ([(t^ o^^) (Tail t o^)])
               (values (make-begin `(,@ef*^ ,t^)) o^^)))]
          [(,triv ,loc* ...)
           (values `(,(fv->disp triv off) ,@(map (lambda (l) (fv->disp l off)) loc*)) off)])))
    (match program
      [(letrec ([,label (lambda () ,tail*)] ...) ,tail)
       (let ([tail*^ (map (lambda (t) (let-values ([(t^ o) (Tail t 0)]) t^)) tail*)]
             [tail^ (let-values ([(t^ o) (Tail tail 0)]) t^)])
         `(letrec ([,label (lambda () ,tail*^)] ...) ,tail^))]
      [,x (format-error who "invalid Program ~s" x)])))

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
          [(return-point ,rp-lab ,rp-tail)
           ;; the code after the call continues at rp-lab; the inner tail
           ;; ends in the callee jump.
           (let-values ([(rt rb*) (Tail rp-tail)])
             (values rt (append rb* `([,rp-lab (lambda () ,tail)]))))]
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
