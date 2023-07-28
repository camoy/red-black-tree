#lang racket

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; insert

(define (insert t x)
  (define (ins t)
    (match t
      [(E) (todo (R (E) x (E)))]
      [(N k a y b)
       (cond
         [(< x y) (=<< balance (<$$> (λ (a) (N k a y b)) (ins a)))]
         [(> x y) (=<< balance (<$$> (λ (b) (N k a y b)) (ins b)))]
         [else    (done t)])]))
  (blacken (from-result (ins t))))

(define (balance t)
  (match t
    [(or (B (R a x (R b y c)) z d)
         (B (R (R a x b) y c) z d)
         (B a x (R (R b y c) z d))
         (B a x (R b y (R c z d))))
     (todo (R (B a x b) y (B c z d)))]
    [(B _ _ _) (done t)]
    [_         (todo t)]))

(define (blacken t)
  (match t
    [(R a x b) (B a x b)]
    [_         t]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; delete

(define (delete t x)
  (define (del t)
    (match-define (N k a y b) t)
    (cond
      [(< x y) (=<< del-left  (<$$> (λ (a) (N k a y b)) (del a)))]
      [(> x y) (=<< del-right (<$$> (λ (b) (N k a y b)) (del b)))]
      [else    (del-root t)]))
  (from-result (del t)))

(define (del-root t)
  (match t
    [(B a y (E)) (blacken* a)]
    [(R a y (E)) (done a)]
    [(N k a y b)
     (define m (box false))
     (=<< del-right (<$$> (λ (b) (N k a (unbox m) b)) (del-min b m)))]))

(define (del-min t m)
  (match t
    [(B (E) y b) (set-box! m y) (blacken* b)]
    [(R (E) y b) (set-box! m y) (done b)]
    [(N k a y b)
     (=<< del-left (<$$> (λ (a) (N k a y b)) (del-min a m)))]))

(define (del-left t)
  (match t
    [(N k a y (R c z d))
     (<$$> (λ (a) (B a z d)) (del-left (R a y c)))]
    [(N k a y (B c z d))
     (balance* (N k a y (R c z d)))]))

(define (del-right t)
  (match t
    [(N k (R a x b) y c)
     (<$$> (λ (b) (B a x b)) (del-right (R b y c)))]
    [(N k (B a x b) y c)
     (balance* (N k (R a x b) y c))]))

(define (balance* t)
  (match t
    [(or (N k (R a x (R b y c)) z d)
         (N k (R (R a x b) y c) z d)
         (N k a x (R (R b y c) z d))
         (N k a x (R b y (R c z d))))
     (done (N k (B a x b) y (B c z d)))]
    [_ (blacken* t)]))

(define (blacken* t)
  (match t
    [(R a x b) (done (B a x b))]
    [_         (todo t)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; monad

(define-syntax-rule (todo x)
  (values true x))


(define-syntax-rule (done x)
  (values false x))

(define-syntax-rule (from-result x)
  (let-values ([(_ y) x])
    y))

(define-syntax-rule (<$$> f x)
  (let-values ([(a d) x])
    (values a (f d))))

(define-syntax-rule (=<< f x)
  (let-values ([(ax dx) x])
    (if ax (f dx) (values ax dx))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; data

(struct E ())
(struct N (color left value right))

(define-syntax-rule (define-color name)
  (begin
    (define-for-syntax (transf stx)
      (syntax-case stx ()
        [(_ a x b) #'(N 'name a x b)]))
    (define-match-expander name transf transf)))

(define-color R)
(define-color B)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; test

(module+ test
  (require rackunit)

  ;; constants

  (define NUM-ELEM-EXP 19)
  (define TEST-ITERS 1000)

  ;; functions

  (define (member? t x)
    (match t
      [(E) false]
      [(N k a y b)
       (cond
         [(< x y) (member? a x)]
         [(> x y) (member? b x)]
         [else    true])]))

  (define (tree->set t)
    (match t
      [(N k a x b) (set-union (tree->set a) (set x) (tree->set b))]
      [(E)         (set)]))

  ;; `red-black-tree?` predicate and generator

  (define (sort-invariant? t)
    (let go ([t t] [low #f] [high #f])
      (match t
        [(N k a x b)
         (and (low . implies . (< low x))
              (high . implies . (< x high))
              (go a low x)
              (go b x high))]
        [(E) true])))

  (define red-invariant?
    (flat-murec-contract
     ([red/black? red? black?]
      [red? (struct/c N 'R black? integer? black?)]
      [black? E? (struct/c N 'B red/black? integer? red/black?)])
     red/black?))

  (define (black-invariant? t)
    (let/ec return
      (let go ([t t])
        (match t
          [(N k a x b)
           (define a* (go a))
           (define b* (go b))
           (cond
             [(not (= a* b*)) (return false)]
             [(eq? (N-color t) 'R) a*]
             [else (+ a* 1)])]
          [(E) 1]))))

  (define red-black-tree?
    (and/c red-invariant?
           black-invariant?
           sort-invariant?))

  ;; test runners

  (define (chk-set insert delete #:iterations [iters TEST-ITERS])
    (for ([k (in-range iters)])
      (define random-ints
        (contract-random-generate (listof exact-integer?)))
      (define init-tree (chk-insert insert random-ints))
      (chk-delete delete random-ints init-tree)))

  (define (chk-insert insert random-ints)
    (for/fold ([s (set)]
               [t (E)]
               #:result t)
              ([x (in-list random-ints)])
      (define s* (set-add s x))
      (define t* (insert t x))
      (check-true (red-black-tree? t*))
      (check-true (set=? s* (tree->set t*)))
      (values s* t*)))

  (define (chk-delete delete random-ints init-tree)
    (define random-set (list->set random-ints))
    (for/fold ([s random-set]
               [t init-tree])
              ([x (in-set random-set)])
      (define s* (set-remove s x))
      (define t* (delete t x))
      (check-true (red-black-tree? t*))
      (check-true (set=? s* (tree->set t*)))
      (values s* t*)))

  (chk-set insert delete))
