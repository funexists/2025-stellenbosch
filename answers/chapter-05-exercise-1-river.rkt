#lang pie

(claim step-+ (-> Nat Nat
                  Nat))
 (define step-+
   (lambda (i sum-n-1)
     (add1 sum-n-1)))

(claim + (-> Nat Nat
             Nat))
 (define +
   (lambda (n j)
     (rec-Nat n
       j
       step-+)))

(check-same Nat 30 (+ 23 7))

; Define a function called `sum-List` that takes one `List Nat` argument and
; evaluates to a Nat, the sum of the Nats in the list.

(claim sum-List (-> (List Nat) Nat))
(define sum-List (lambda (lst) (rec-List lst zero (lambda (c-lst.head c-lst.tail sum-c-lst.tail) (+ c-lst.head sum-c-lst.tail)))))

(claim range (-> Nat (List Nat)))
(define range (lambda (n) (rec-Nat n (the (List Nat) nil) (lambda (i lst) (:: i lst)))))

(range 4)

(check-same Nat 6 (sum-List (range 4)))