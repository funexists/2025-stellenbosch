#lang pie

(claim at-least-two? (-> Nat Atom))
(define at-least-two?
  (lambda (n)
    (which-Nat n
      'nil
      (lambda (n-1)
        (which-Nat n-1
          'nil
          (lambda (n-2) 't))))))

(claim step-+ (-> Nat Nat Nat))
(define step-+
  (lambda (n-1 sum-n-1)
    (add1 sum-n-1)))

(claim + (-> Nat Nat Nat))
(define +
  (lambda (n j)
    (rec-Nat n
      j
      step-+)))

(claim * (-> Nat Nat Nat))
(define *
  (lambda (n j)
    (iter-Nat n
      0
      (+ j))))

(claim exp (-> Nat Nat Nat))
(define exp
  (lambda (a b)
    (iter-Nat b
      1
      (* a))))

(check-same Nat (exp 5 2) 25)

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