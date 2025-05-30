#lang pie

(claim + (-> Nat Nat Nat))
(define +
  (lambda (m n)
    (iter-Nat n
      m
      (lambda (n-1) (add1 n-1)) )))

(claim n+zero=n (Pi ((n Nat)) (= Nat (+ n 0) n)))
(define n+zero=n
  (lambda (n)
    (same n) ))

(claim zero+n=n (Pi ((n Nat)) (= Nat (+ 0 n) n)))
(define zero+n=n
  (lambda (n)
    (ind-Nat n
      (lambda (n) (= Nat (+ 0 n) n))
      (same 0)
      (lambda (n-1 prev)
        (cong prev (the (-> Nat Nat) (lambda (x) (add1 x)))) ))))


(claim a=b->a+n=b+n (Pi ((a Nat) (b Nat) (n Nat)) (-> (= Nat a b) (= Nat (+ a n) (+ b n)))))
(define a=b->a+n=b+n
  (lambda (a b n eq)
    (cong eq (the (-> Nat Nat) (lambda (x) (+ x n)))) ))

(claim plus-assoc-type (Pi ((n Nat) (m Nat) (k Nat)) U))
(define plus-assoc-type (lambda (n m k) (= Nat (+ n (+ m k)) (+ (+ n m) k))))
(claim plus-assoc (Pi ((n Nat) (m Nat) (k Nat)) (plus-assoc-type n m k)))
(define plus-assoc
  (lambda (n m k)
    (ind-Nat k
      (plus-assoc-type n m)
      (same (+ n m))
      (lambda (k-1 prev) ; prev asserts that (n + (m + k-1) = (n + m) + k-1
        (cong prev (the (-> Nat Nat) (lambda (x) (add1 x)))) ))))
        