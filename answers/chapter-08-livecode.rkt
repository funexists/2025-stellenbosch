#lang pie

(claim +
  (-> Nat Nat Nat))

(define +
  (lambda (x y)
    (rec-Nat x
      y
      (lambda (x-1 almost)
        (add1 almost)))))

; Define a function called a=b->a+n=b+n that states and proves
; that a = b implies a+n = b+n for all Nats a, b, n.

(claim thatthing
  (Pi ((a Nat) (b Nat) (n Nat))
    (-> (= Nat a b) (= Nat (+ a n) (+ b n)))))

(claim mot-thatthing
  (Pi ((a Nat) (b Nat) (n Nat)) U))

(define mot-thatthing
  (lambda (a b n)
    (= Nat (+ a n) (+ b n))))

(claim step-thatthing
  (Pi ((a Nat) (b Nat) (n-1 Nat))
    (->
      (= Nat (+ a n-1) (+ b n-1))
      (= Nat (+ a (add1 n-1)) (+ b (add1 n-1)))
      )))

;(claim step-thatthing-
 ; (Pi ((a Nat) (b Nat) (n-1 Nat))
  ;  (->
   ;   (= Nat (+ a n-1) (+ b n-1))
     ; (= Nat (+ a (add1 n-1)) (+ b (add1 n-1)))
    ;  )))
;(define step-thatthing-
 ; (lambda (a b n ih)
  ;  (cong ih (the (-> Nat Nat) (lambda (x) (+ x 1))))))

;(define step-thatthing
 ; (lambda (a b n ih)
  ;  (cong ih (+ 1))))

;(define thatthing
 ; (lambda (a b n a=b)
  ;  (ind-Nat n
   ;   (mot-thatthing a b)
    ;  a=b
     ; (step-thatthing a b)
      ;)))

(define thatthing
  (lambda (a b n a=b)
    (cong a=b (the (-> Nat Nat) (lambda (x) (+ x n))))))