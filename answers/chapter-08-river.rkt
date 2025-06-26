#lang pie

; ----------------------------------------------------------------------------------------------------
(claim sub1 (-> Nat Nat)) ; subtract 1 from the argument
(define sub1 (lambda (a) (which-Nat a 0 (the (-> Nat Nat) (lambda (n-1) n-1)))))
(claim - (-> Nat Nat Nat))
(define - (lambda (a b) (iter-Nat b a sub1)))

(claim min (-> Nat Nat Nat))
(define min (lambda (a b) (which-Nat (- a b) a (lambda (_) b))))
(claim max (-> Nat Nat Nat))
(define max (lambda (a b) (which-Nat (- a b) b (lambda (_) a))))
; ----------------------------------------------------------------------------------------------------

; Definition of addition
; ------------------------------
(claim step-+ (-> Nat Nat Nat))
(define step-+ (lambda (_ almost-answer) (add1 almost-answer)))

; Add b to a
(claim + (-> Nat Nat Nat))

(define + (lambda (a b) (rec-Nat b a (the (-> Nat Nat Nat) (lambda (i a+i-1) (add1 a+i-1))))))
; ------------------------------

; ## Exercise 1

; Define a function called `zero+n=n` that states and proves that
; `0+n = n` for all Nat `n`.

; Motive
(claim typeof_zero+k=k (Pi ((k Nat)) U))
(define typeof_zero+k=k (lambda (k) (= Nat (+ zero k) k)))

; Base case
(claim zero+zero=zero (typeof_zero+k=k zero))
(define zero+zero=zero (same zero))

; Inductive step (map proof for n-1 to proof for n)
; -------------------------------
;       XXX: induction isn't necessary: (thanks to Keegan for explaining why)
;       -------------------------------
;       (claim keegans-zero+n=n (Pi ((n Nat)) (= Nat (+ zero n) n)))
;       (define keegans-zero+n=n (lambda (n) (same n)))
;       -------------------------------

; helper function
; -------------------------------
(claim plus1 (-> Nat Nat))
(define plus1 (lambda (x) (+ x 1)))
; -------------------------------

(claim step-zero+n=n (Pi ((n-1 Nat)) (-> (typeof_zero+k=k n-1) (typeof_zero+k=k (add1 n-1)))))
(define step-zero+n=n
        (lambda (n-1) ; let k = n-1
                (lambda (zero+n-1=n-1) (cong zero+n-1=n-1 plus1))))
(claim zero+n=n (Pi ((n Nat)) (typeof_zero+k=k n)))
(define zero+n=n (lambda (n) (ind-Nat n typeof_zero+k=k zero+zero=zero step-zero+n=n)))
; -------------------------------

; ## Exercise 2

; Define a function called `a=b->a+n=b+n` that states and proves that
; `a = b` implies `a+n = b+n` for all Nats `a`, `b`, `n`.

(claim a=b->a+n=b+n (Pi ((a Nat) (b Nat) (n Nat)) (-> (= Nat a b) (= Nat (+ a n) (+ b n)))))

; helper
; -------------------------------
(claim add (Pi ((k Nat)) (-> Nat Nat)))
(define add (lambda (k) (lambda (x) (+ x k))))
; -------------------------------

(define a=b->a+n=b+n (lambda (a b n) (lambda (a=b) (cong a=b (add n)))))

; ## Exercise 3

; Define a function called `plus-assoc` that states and proves that
; `+` is associative.

; ```
(claim plus-assoc (Pi ((n Nat) (m Nat) (k Nat)) (= Nat (+ k (+ n m)) (+ (+ k n) m))))
; ```

(claim typeof_plus-assoc (Pi ((n Nat) (m Nat) (k Nat)) U))
(define typeof_plus-assoc (lambda (n m k) (= Nat (+ k (+ n m)) (+ (+ k n) m))))

(define plus-assoc
        (lambda (n m k)
                (ind-Nat m
                         (lambda (m) (typeof_plus-assoc n m k)) ; motive
                         (same (+ k n)) ; base
                         (lambda (m-1 plus-assoc-m-1)
                                 (cong plus-assoc-m-1 (add 1))) ; step
                         )))
