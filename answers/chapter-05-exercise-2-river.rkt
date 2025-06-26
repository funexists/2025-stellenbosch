#lang pie

; Define a function called maybe-last which takes (in addition to the type
; argument for the list element) one (`List E`) argument and one `E` argument and
; evaluates to an `E` with value of either the last element in the list, or the
; value of the second argument if the list is empty.

(claim maybe-last (Pi ((E U)) (-> (List E) E E)))

(define maybe-last (lambda (E) (lambda (lst default)
  (rec-List lst
    default
    (lambda (x xs maybe-last-xs)
      (rec-List xs
        x
        (lambda (y ys maybe-last-ys) maybe-last-xs)))))))

(check-same Nat 1 (maybe-last Nat (the (List Nat) (:: 2 (:: 1 nil))) 0))
(check-same Nat 1 (maybe-last Nat (the (List Nat) nil) 1))