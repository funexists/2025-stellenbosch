Hi Walter. Here are the exercises for yesterday with the definition of symm at the end.

#lang pie

(claim same-cons
  (Pi ((t U) (x t) (as (List t)) (bs (List t)))
    (-> (= (List t) as bs)
        (= (List t) (:: x as) (:: x bs)))))

(define same-cons
  (lambda (t x as bs as=bs)
    (replace as=bs
      (lambda (k) (= (List t) (:: x as) (:: x k)))
      (same (:: x as)) )))

(claim same-lists
  (Pi ((t U) (e1 t) (e2 t) (l1 (List t)) (l2 (List t)))
    (-> (= (List t) l1 l2) (= t e1 e2)
        (= (List t) (:: e1 l1) (:: e2 l2)))))

(define same-lists
  (lambda (t e1 e2 l1 l2 l1=l2 e1=e2)
    (replace e1=e2
      (lambda (e) (= (List t) (:: e1 l1) (:: e l2)))
      (same-cons t e1 l1 l2 l1=l2) )))


(claim + (-> Nat Nat Nat))
(define +
  (lambda (m n)
    (iter-Nat n
      m
      (lambda (n-1) (add1 n-1)) )))

(claim inc (-> Nat Nat))
(define inc
  (lambda (x) (add1 x)) )

(claim zero+n=n (Pi ((n Nat)) (= Nat (+ 0 n) n)))
(define zero+n=n
  (lambda (n)
    (ind-Nat n
      (lambda (n) (= Nat (+ 0 n) n))
      (same 0)
      (lambda (n-1 prev)
        (cong prev inc) ))))

(claim n+1+m=n+m+1 (Pi ((n Nat) (m Nat)) (= Nat (+ (add1 n) m) (add1 (+ n m)))))
(define n+1+m=n+m+1
  (lambda (n m)
    (ind-Nat m
      (lambda (k) (= Nat (+ (add1 n) k) (add1 (+ n k))))
      (same (add1 n))
      (lambda (m-1 prev) ; prev asserts that (n+1)+m-1 = (n+m-1)+1
        (cong prev inc) ))))

(claim plus-comm
 (Pi ((n Nat) (m Nat))
   (= Nat (+ n m) (+ m n))))

(define plus-comm
  (lambda (n m)
    (ind-Nat n
      (lambda (k) (= Nat (+ k m) (+ m k)))
      (zero+n=n m)
      (lambda (n-1 prev) ; prev asserts that n-1 + m = m + n-1 ; then (cong prev inc) gives (n-1+m)+1 = m+n-1+1.
        (trans (n+1+m=n+m+1 n-1 m) (cong prev inc)) ))))
(claim trans2 (Pi ((t U) (x t) (y t) (z t)) (-> (= t x y) (= t y z) (= t x z))))
(define trans2
  (lambda (t x y z x=y y=z)
    (replace y=z
      (lambda (w) (= t x w))
      x=y)))

(claim symm2 (Pi ((t U) (x t) (y t)) (-> (= t x y) (= t y x))))
(define symm2
  (lambda (t x y eq)
    (replace eq
      (lambda (z) (= t z x))
      (same x) )))