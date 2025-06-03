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

(claim unzip
(Pi ((A U) (B U) (n Nat))
    (-> (Vec (Pair A B) n)
        (Pair (Vec A n) (Vec B n)))))
(define unzip
  (lambda (A B n es)
    (ind-Vec n es
      (lambda (n _) (Pair (Vec A n) (Vec B n)))
      (cons vecnil vecnil)
      (lambda (_ ab _ asbs) 
        (cons (vec:: (car ab) (car asbs)) (vec:: (cdr ab) (cdr asbs)))))))
