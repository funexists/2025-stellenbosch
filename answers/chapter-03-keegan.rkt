#lang pie

; Exercise 1
(claim at-least-two?
  (-> Nat Atom))
(define at-least-two?
  (lambda (n)
    (which-Nat n
      'no
      (lambda (n-1)
        (which-Nat n-1
          'no
          (lambda (_) 'yes))))))

; Exercise 2
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

; Exercise 3
(claim *
  (-> Nat Nat Nat))
(define *
  (lambda (m n)
    (iter-Nat n
      zero
      (lambda (n-1) (+ m n-1)))))

(claim exp
  (-> Nat Nat Nat))
(define exp
  (lambda (m n)
    (iter-Nat n
      1
      (lambda (n-1) (* m n-1)))))

; Exercise 4
(claim dec
  (-> Nat Nat))
(define dec
  (lambda (n) 
    (which-Nat n
      zero
      (lambda (n-1) n-1))))

(claim - 
  (-> Nat Nat Nat))
(define -
  (lambda (n m)
    (iter-Nat m
      n
      dec)))

(claim max
  (-> Nat Nat Nat))
(define max
  (lambda (m n) (+ m (- n m))))

; Exercise 6
(claim step-fact
  (-> Nat Nat
    Nat))
(define step-fact
  (lambda (n-1 almost)
    (* (add1 n-1) almost)))

(claim fact
  (-> Nat
    Nat))
(define fact
  (lambda (n)
    (rec-Nat n
      1
      step-fact)))