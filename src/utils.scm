;;; utils.scm
;;; Compiler-wide helpers shared across passes.  (lib/helpers.scm holds
;;; the course-provided helpers; this file holds our own.)

(define relop?
  (lambda (x) (and (memq x '(< <= = >= >)) #t)))

(define int?
  (lambda (x) (and (integer? x) (exact? x))))

(define binop?
  (lambda (x) (and (memq x '(+ - * logand logor sra)) #t)))

;; A Triv in the source UIL: uvar, int, label, or an already-assigned
;; location (register / frame-var).  Used by the a6+ front-end passes.
(define triv?
  (lambda (x)
    (or (uvar? x) (int? x) (label? x) (register? x) (frame-var? x))))

;; Backward live analysis that builds a conflict graph.  loc? selects the
;; fixed locations to track alongside uvars: register? for register
;; conflicts, frame-var? for frame conflicts.  Returns an assoc list
;; mapping each uvar to the uvars/locations it conflicts with.
(define build-conflict-graph
  (lambda (uvar* tail loc? . opt)
    (define call-live! (and (pair? opt) (car opt)))
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
    ;; Optional hook: called with the set of locations live *after* a
    ;; return-point, so callers can accumulate call-live info.
    (define call-live-hook (if (procedure? call-live!) call-live! (lambda (l) (void))))
    (define Effect
      (lambda (ef live)
        (match ef
          [(nop) live]
          [(if ,p ,c ,a) (Pred p (Effect c live) (Effect a live))]
          [(begin ,ef* ... ,e) (Effect* ef* (Effect e live))]
          [(return-point ,rp-lab ,tail)
           (call-live-hook live)
           ;; the inner tail's live-out is `live` (call-live), which flows
           ;; around the call to the return point
           (Tail tail live)]
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
    ;; base is the live-out set (empty for a real tail, call-live for the
    ;; inner tail of a return-point).
    (define Tail
      (lambda (t base)
        (match t
          [(if ,p ,c ,a) (Pred p (Tail c base) (Tail a base))]
          [(begin ,ef* ... ,t) (Effect* ef* (Tail t base))]
          [(,triv ,loc* ...) (union base (->set (cons triv loc*)))]
          [,x (format-error 'uncover-conflict "invalid Tail ~s" x)])))
    (Tail tail '())
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
          [(begin ,ef* ... ,e) (make-begin `(,@(map Effect ef*) ,(Effect e)))]
          [(return-point ,rp-lab ,tail) `(return-point ,rp-lab ,(Tail tail))])))
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
