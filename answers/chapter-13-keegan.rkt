#lang pie

(claim step-+
  (-> Nat Nat Nat))
(define step-+
  (lambda (_ n-1) (add1 n-1)))

(claim +
  (-> Nat Nat Nat))
(define +
  (lambda (n m)
    (rec-Nat n
      m
      step-+)))

(claim double
  (-> Nat 
    Nat))
(define double
  (lambda (n)
    (iter-Nat n
      0
      (+ 2))))

(claim Even
  (-> Nat U))
(define Even
  (lambda (n)
    (Sigma ((half Nat))
      (= Nat n (double half)))))

; Exercise 1
(claim even-n-or-n+1
  (Pi ((n Nat))
    (Either (Even n) (Even (add1 n)))))
(define even-n-or-n+1
  (lambda (n)
    (ind-Nat n
      (lambda (n) (Either (Even n) (Even (add1 n))))
      (left (cons 0 (same 0)))
      (lambda (n ih) 
        (ind-Either ih
          (lambda (_) (Either (Even (add1 n)) (Even (add1 (add1 n)))))
          (lambda (en) 
            (right (cons (add1 (car en)) (cong (cdr en) (+ 2)))))
          (lambda (en+1) 
            (left en+1)))))))