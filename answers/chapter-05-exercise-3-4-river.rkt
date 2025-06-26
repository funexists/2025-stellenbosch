#lang pie

; Define a function called filter-list which takes (in addition to the type
; argument for the list element) one `(-> E Nat)` argument representing a
; predicate and one `(List E)` argument.

; The function evaluates to a `(List E)` consisting of elements from the list
; argument where the predicate is true.

; Consider the predicate to be false for an element if it evaluates to zero,
; and true otherwise.

(claim filter-list (Pi ((E U)) (-> (-> E Nat) (List E) (List E))))

(define filter-list (lambda (E) (lambda (pred lst) (rec-List lst (the (List E) nil) (lambda (x xs filtered-xs) (which-Nat (pred x) filtered-xs (lambda (y) (:: x filtered-xs))))))))

; ----------------------------------------------------------------------------------------------------
(claim nat-id (-> Nat
                  Nat))
(define nat-id (lambda (x) x))

(claim sub1 (-> Nat
                Nat)) ; subtract 1 from the argument
(define sub1 (lambda (a) (which-Nat a 0 nat-id)))

; subtract a from b

(claim - (-> Nat Nat
               Nat))

(define - (lambda (a b) (iter-Nat a b sub1)))

(claim not (-> Nat Nat))
(define not (lambda (x) (which-Nat x 1 (lambda (_) zero))))
; ---------------------------------------------------------------------------------------------------- 

(claim ge? (-> Nat Nat Nat))

(define ge? (lambda (a b) (not (- a b)))) ; b - a is zero if a >= b, so negate the result to get the truth value

(claim list123 (List Nat))
(define list123 (:: 1 (:: 2 (:: 3 nil))))

(filter-list Nat (lambda (x) (ge? x 2)) list123) ; keep elements >= 2
(filter-list Nat (lambda (x) (ge? 2 x)) list123) ; keep elements <= 2

; Exercise 4

; Define a function called `sort-List-Nat` which takes one `(List Nat)` argument
; and evaluates to a `(List Nat)` consisting of the elements from the list
; argument sorted in ascending order.

(claim sort-List-Nat (-> (List Nat) (List Nat)))
(define sort-List-Nat (lambda (lst) (rec-List lst lst (lambda (x xs partly-sorted) (:: (filter-list Nat (lambda (y) (ge? x y)) partly-sorted) (filter-list Nat (lambda (y) (not (ge? x y))) partly-sorted))))))
