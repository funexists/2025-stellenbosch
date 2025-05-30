#lang pie

(claim zip-type (Pi ((A U) (B U) (n Nat)) U))
(define zip-type
  (lambda (A B n) (-> (Vec A n) (Vec B n) (Vec (Pair A B) n))) )
(claim zip
  (Pi ((A U) (B U) (n Nat)) (zip-type A B n)) )
(define zip
  (lambda (A B n)
    (ind-Nat n
      (zip-type A B)
      (lambda (empty1 empty2) vecnil)
      (the (Pi ((n-1 Nat)) (-> (zip-type A B n-1) (zip-type A B (add1 n-1))))
        (lambda (n-1 prev)
          (lambda (xs ys) (vec:: (cons (head xs) (head ys)) (prev (tail xs)(tail ys)))) )) )))
;; The advantage of doing the induction step /before/ taking xs and ys as input seems to be that we let
;; PIE know that the n in the types of xs and ys is the particular n that is nonzero, so that we can use head

(claim + (-> Nat Nat Nat))
(define +
  (lambda (m n)
    (iter-Nat n
      m
      (lambda (n-1) (add1 n-1)) ))) ; it's not possible to curry constructors apparently
(claim append-type (Pi ((A U) (m Nat) (n Nat)) U))
(define append-type
  (lambda (A m n) (-> (Vec A n) (Vec A (+ m n)))) )
(claim append
  (Pi ((A U) (m Nat) (n Nat)) (-> (Vec A m) (append-type A m n))) )
(define append
  (lambda (A m n xs)
    (ind-Nat n
      (append-type A m)
      (lambda (empty) xs)
      (the (Pi ((n-1 Nat)) (-> (append-type A m n-1) (append-type A m (add1 n-1))))
        (lambda (n-1 prev)
          (lambda (ys) (vec:: (head ys) (prev (tail ys)))) )) )))
;; This concatenates the lists in the reverse order, but good enough

(claim drop-last-k-type (Pi ((A U) (n Nat) (k Nat)) U))
(define drop-last-k-type (lambda (A n k) (-> (Vec A (+ k n)) (Vec A n))))
(claim drop-last-k (Pi ((A U) (n Nat) (k Nat)) (drop-last-k-type A n k)))
(define drop-last-k
  (lambda (A n k)
    (ind-Nat n
      (lambda (n) (drop-last-k-type A n k))
      (lambda (xs) vecnil)
      (lambda (n-1 prev)
        (lambda (xs) (vec:: (head xs) (prev (tail xs)))) ) )))