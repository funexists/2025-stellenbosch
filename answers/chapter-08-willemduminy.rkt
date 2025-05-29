#lang pie

;-------------------------------------------------------------------------------
; From previous chapters and exercises

(claim step+ (-> Nat Nat Nat))
(define step+ (λ(_n-1 +n-1) (add1 +n-1)))
(claim + (-> Nat Nat Nat))
(define + (λ(a b) (rec-Nat a b step+)))

(check-same Nat (+ 2 4) (+ 4 2))

(claim predecessor (-> Nat Nat))
(define predecessor (λ(n) (which-Nat n 0 (λ(n-1) n-1))))
(claim - (-> Nat Nat Nat))
(define - (λ(a b) (rec-Nat b a (λ(b-1 a-b-1) (predecessor a-b-1)))))

;-------------------------------------------------------------------------------
; From chapter 8

(claim incr (-> Nat Nat))
(define incr
  (λ(n)
    (iter-Nat n
      1
      (+ 1))))

(claim +1=add1
  (Pi((n Nat))
    (= Nat (+ 1 n) (add1 n))))
(define +1=add1
  (λ(n) (same (add1 n))))

; proposition: `incr(n) = (add1(n))`

; mot follows from proposition
(claim mot-incr=add1 (-> Nat U))
(define mot-incr=add1
  (λ(n) (= Nat (incr n) (add1 n))))

(claim base-incr=add1 (mot-incr=add1 zero))
(define base-incr=add1 (same (add1 zero)))

; if incr(n) = add1(n)
; then add1(incr(n)) = add1(add1(n)`
(claim step-incr=add1
  (Pi((n Nat))
    (->
           (= Nat (incr n) (add1 n))
      (= Nat (add1 (incr n)) (add1 (add1 n)))
      )))

; if incr(n-1) = add1(n-1)
; then incr(n) = add1 (n)
(define step-incr=add1
  (λ(_n-1)
    (λ (fn-1) (cong fn-1 (+ 1)))))

(claim incr=add1
  (Pi ((n Nat))
    (= Nat (incr n) (add1 n))))
(define incr=add1
  (λ(n)
    (ind-Nat n
      mot-incr=add1
      base-incr=add1
      step-incr=add1
      )))


;-------------------------------------------------------------------------------
; Exercise 8.1
; ------------
; Define a function called zero+n=n that states and proves that 0+n = n
; for all Nat n.

; proposition: +(0 n) = n
; motive follows from proposition
(claim mot-z+n=n (-> Nat U))
(define mot-z+n=n
  (λ(n) (= Nat (+ zero n) n)))

; base: 0 + 0 = 0
(claim base-z+n=n (mot-z+n=n zero))
(define base-z+n=n
  (same zero))

; if 0 + n = n
; then
;   0 + n+1 = n+1
;   1 + n = n
(claim step-z+n=n
  (Pi((n Nat))
    (-> (= Nat (+ zero n) n)
      (= Nat (add1 n) (add1 n)))))
(define step-z+n=n
  (λ(_n-1)
    (λ(fn-1) (cong fn-1 (+ 1)))))

(claim zero+n=n
  (Pi((n Nat)) (= Nat (+ zero n) n)))
(define zero+n=n
  (λ(n)
    (ind-Nat n mot-z+n=n base-z+n=n step-z+n=n)))

;-------------------------------------------------------------------------------
; Exercise 8.2
; ------------
; Define a function called a=b->a+n=b+n that states and proves that a = b
; implies a+n = b+n for all Nats a, b, n.

; a = b => (n + a) = (n + b)
(claim a=b->a+n=b+n
  (Pi((a Nat) (b Nat) (n Nat))
    (->
           (= Nat a b)
      (= Nat (+ n a) (+ n b)))))
(define a=b->a+n=b+n
  (λ(_a _b n)
    (λ(fn-1) (cong fn-1 (+ n)))))

;-------------------------------------------------------------------------------
; Exercise 8.3
; -----------
; Define a function called plus-assoc that states and proves that + is
; associative.

(claim plus-assoc
  (Pi ((n Nat) (m Nat) (k Nat))
    (= Nat (+ k (+ n m)) (+ (+ k n) m))))
(define plus-assoc
  (λ(n m k)
    (ind-Nat k
      ; proposition:  k + (n + m) =  (k + n) + m
      (λ(k) (= Nat (+ k (+ n m)) (+ (+ k n) m)))
      ; 0 + (n + m) = (0 + n) + m
      (same (+ n m))
      ;        k+1 + (n + m) =     (k+1 + n) + m
      ; => 1 + (k + (n + m)) = 1 + (k + n) + m
      (λ(_k-1 fk-1) (cong fk-1 (+ 1)))
      )))


