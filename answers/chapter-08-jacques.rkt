#lang pie

(claim +
  (-> Nat Nat
    Nat))

(claim step-+
  (-> Nat
    Nat))
(define step-+
  (lambda (j)
    (add1 j)))

(define +
  (lambda (n j)
    (iter-Nat n
      j
      step-+)))

;; ============================================================================
;; ## Exercise 1
;;
;; Define a function called `zero+n=n` that states and proves that
;; `0+n = n` for all Nat `n`.

(claim zero+n=n
  (Pi ((n Nat))
    (= Nat (+ zero n) n)))
(define zero+n=n
  (lambda (n)
    (same n)))
'ex-one
(zero+n=n 2)
(zero+n=n 0)

;; ============================================================================
;; ## Exercise 2
;;
;; Define a function called `a=b->a+n=b+n` that states and proves that
;; `a = b` implies `a+n = b+n` for all Nats `a`, `b`, `n`.
;; (claim mot-a=b->a+n=b+n
;;   (-> Nat Nat Nat
;;     U))
;; (define mot-a=b->a+n=b+n
;;   (lambda (a b n)
;;     (-> (= Nat a b)
;;       (= Nat (+ a n) (+ b n)))))
;; (claim base-a=b->a+n=b+n
;;   (Pi ((a Nat)
;;        (b Nat))
;;     (-> (= Nat a b)
;;       (= Nat (+ a zero) (+ b zero)))))
;; (define base-a=b->a+n=b+n
;;   (lambda (a b)
;;     (lambda (eqab)
;;       (cong eqab
;;         (+ zero)
;;
;;         ))))
;; (same (+ a b)))))

;; is this even correct?
(claim a=b->a+n=b+n
  (Pi ((a Nat)
       (b Nat)
       (n Nat))
    (-> (= Nat a b)
      (= Nat (+ n a) (+ n b)))))
(define a=b->a+n=b+n
  (lambda (a b n a=b)
    (cong a=b (+ n))
    ))
'ex-two
;; is this even correct?
(a=b->a+n=b+n 1 1 0 (same 1))

;; ============================================================================
;; ## Exercise 3
;;
;; Define a function called `plus-assoc` that states and proves that
;; `+` is associative.
;;
;; ```pie
;; (claim plus-assoc
;;  (Pi ((n Nat) (m Nat) (k Nat))
;;    (= Nat (+ k (+ n m)) (+ (+ k n) m))))
;; ```

(claim mot-plus-assoc
  (-> Nat Nat Nat
    U))
(define mot-plus-assoc
  (lambda (n m k)
    (= Nat (+ k (+ n m)) (+ (+ k n) m))))

(claim base-plus-assoc
  (Pi ((n Nat)
       (m Nat))
    (= Nat (+ zero (+ n m)) (+ (+ zero n) m))))
(define base-plus-assoc
  (lambda (n m)
    (same (+ n m))))

(claim step-plus-assoc
  (Pi ((n Nat)
       (m Nat)
       (k-1 Nat))
    (->
    (= Nat (+ k-1 (+ n m)) (+ (+ k-1 n) m))
      (= Nat (add1 (+ k-1 (+ n m))) (add1 (+ (+ k-1 n) m)))
      )))

(define step-plus-assoc
  (lambda (n m k-1)
    (lambda (plus-assoc-k-1)
      (cong plus-assoc-k-1  (+ 1)))))


(claim plus-assoc
  (Pi ((n Nat)
       (m Nat)
       (k Nat))
    (= Nat (+ k (+ n m)) (+ (+ k n) m))))
(define plus-assoc
  (lambda (n m k)
    (ind-Nat k
      (mot-plus-assoc n m)
      (base-plus-assoc n m)
      (step-plus-assoc n m)
      )))
'ex-three
(plus-assoc 1 2 0)
(plus-assoc 1 2 1)
