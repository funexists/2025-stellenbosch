#lang pie

;; ==========
;; Exercise 1
(claim elim-Pair
  (Pi ((A U)
       (D U)
       (X U))
    ( -> ( Pair A D)
         (-> A D
           X)
       X)))
(define elim-Pair
  (lambda (A D X)
    (lambda (p f)
      (f (car p) (cdr p)))))


(claim kar
  (Pi ((A U)
       (B U))
    (-> (Pair A B)
      A)))
(define kar
  (lambda (A B)
    (lambda (p)
      (elim-Pair
        A B
        A
        p
        (lambda (a d) a)))))

(claim kdr
  (Pi ((A U)
       (B U))
    (-> (Pair A B)
      B)))
(define kdr
  (lambda (A B)
    (lambda (p)
      (elim-Pair
        A B
        B
        p
        (lambda (a d) d)))))

(check-same Nat ((kar Nat Nat) (the (Pair Nat Nat) (cons 1 2))) 1)
(check-same Nat ((kdr Nat Nat) (the (Pair Nat Nat) (cons 1 2))) 2)
(check-same Nat ((kar Nat Atom) (cons 1 'Pie)) 1)
(check-same Atom ((kar Atom Nat) (the (Pair Atom Nat) (cons 'Cherry 2))) 'Cherry)

;; ==========
;; Exercise 2

(claim compose
       (Pi ((A U)
            (B U)
            (C U))
           (-> (-> A B)
               (-> B C)
               (-> A C))))
(define compose
  (lambda (A B C)
    (lambda (ab bc)
      (lambda (a)
        (bc (ab a))))))


(check-same Nat ((compose Nat Atom Nat (lambda (a) 'pie) (lambda (b) 5)) 1) 5)

(claim add2
       (-> Nat Nat))
(define add2
    (compose Nat Nat Nat 
         (lambda (a)
           (add1 a)) 
         (lambda (b)
           (add1 b))))

(check-same Nat (add2 0) 2)
(check-same Nat (add2 1) 3)
