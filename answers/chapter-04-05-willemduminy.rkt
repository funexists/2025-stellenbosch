#lang pie
;-------------------------------------------------------------------------------
; Exercise 4.1
; ------------
; Extend the definitions of `kar` and `kdr` (frame 4.42) so they work with
; arbitrary Pairs (instead of just for `Pair Nat Nat` from frame 4.42)
;
; Answer
; ------
; The idea of Pi is explained on page 100
; Using the pattern on page 98 (for flip) 

(claim kar
  ( Pi((A U) (B U))
     (-> (Pair A B) A)))
(define kar
  (λ(A B)
    (λ(p)
      (car p))))

(check-same Nat ((kar Nat Nat) (cons 10 9)) 10)

(claim kdr
  ( Pi((A U) (B U))
     (-> (Pair A B) B)))
(define kdr
  (λ(A B)
    (λ(p)
      (cdr p))))

(check-same Nat ((kdr Nat Nat) (cons 10 9)) 9)
(check-same Nat (kdr Nat Nat (cons 10 9)) 9)

;-------------------------------------------------------------------------------
; Exercise 4.2
; ----------
; Define a function called compose that takes (in addition to the type
; arguments A, B, C) an argument of type `(-> A B)` and an argument of
; type `(-> B C)` that and evaluates to a value of type `(-> A C)`, the function
; composition of the arguments.
;
; Answer
; ------

; compose f g makes a new function h: A -> C
; where f: B -> C and g: A -> B
; such that h(.) = f(g(.))
(claim compose
  (Pi((A U)(B U)(C U))
    (-> (-> B C) (-> A B) (-> A C))))
(define compose
  (λ(A B C)
    (λ(f g) (λ(c) (f (g c))))))

; Using predecessor as an example.
(claim pred (-> Nat Nat))
(define pred (λ(n) (which-Nat n 0 (λ(n-1) n-1))))

(claim pred2 (-> Nat Nat))
(define pred2 ((compose Nat Nat Nat) pred pred))

(check-same Nat (pred2 9) 7)

;-------------------------------------------------------------------------------
; from previous work:
(claim predecessor (-> Nat Nat))
(define predecessor (λ(n) (which-Nat n 0 (λ(n-1) n-1))))
(check-same Nat (predecessor 10) 9)
(check-same Nat (predecessor 0) 0)
; (- a b) = If (a > b) then (a - b) else zero
(claim - (-> Nat Nat Nat))
(define -
  (λ(a b)
    (rec-Nat b a (λ(b-1 a-b-1) (predecessor a-b-1)))))
;-------------------------------------------------------------------------------
; Chapter 5 book functions
; ------------------------

; `append a b` makes a new list such that the elements of `b` is appended to `a`.
(claim append (Pi((E U)) (-> (List E) (List E) (List E))))
(claim step-append (Pi((E U)) (-> E (List E) (List E) (List E))))

(define step-append
  (λ(E)
    (λ(h _t a-t) (:: h a-t))))
(define append (λ(E) (λ(a b) (rec-List a b (step-append E)))))

(check-same (List Nat) (append Nat (:: 1 nil) (:: 2 nil)) (:: 1 (:: 2 nil)))

; `snoc a e` makes a new list from `a` where `e` is placed on the back of `a`.
(claim snoc (Pi((E U)) (-> (List E) E (List E))))
(define snoc
  (λ(E)
    (λ(a e) (append E a (:: e nil)))))

(check-same (List Nat) (snoc Nat (:: 1 nil) 2) (:: 1 (:: 2 nil)))

; `reverse a` makes a new list where the elements of `a` are reversed
(claim reverse (Pi((E U)) (-> (List E) (List E))))
(claim step-reverse (Pi((E U)) (-> E (List E) (List E) (List E))))
(define step-reverse
  (λ(E)
    (λ(h t a-t) (snoc E a-t h))))
(define reverse
  (λ(E)
    (λ(a) (rec-List a (the (List E) nil) (step-reverse E)))))

(check-same (List Nat) (reverse Nat (:: 1 (:: 2 nil))) (:: 2 (:: 1 nil)))

; `length a` return the number of elements in the list `a`
(claim length (Pi ((E U)) (-> (List E) Nat)))
(define length
  (λ(E)
    (λ(a) (rec-List a zero (λ(e t a-t) (add1 a-t))))))
(check-same Nat (length Nat (:: 1 (:: 2 (:: 3 nil)))) 3 )
(check-same Nat (length Nat (:: 1 nil)) 1 )


;-------------------------------------------------------------------------------
; Exercise 5.1
; ------------
; Define a function called sum-List that takes one List Nat argument and
; evaluates to a Nat, the sum of the Nats in the list.
;
; Answer
; ------
; rec-List is defined on page 116

; + from ex 3.2
(claim step+ (-> Nat Nat Nat))
(claim + (-> Nat Nat Nat))
(define step+
  (λ(dim-n-1 a-n-1)
    (add1 a-n-1)))
(define +
  (λ(a b) (rec-Nat a b step+)))

(claim sum-List (-> (List Nat) Nat))
(claim step-sum-List (-> Nat (List Nat) Nat Nat))
(define step-sum-List
  (λ(h dim-t a-t)
    (+ h a-t)))

(define sum-List
  (λ(lst)
    (rec-List lst 0 step-sum-List)))

(check-same Nat (sum-List (:: 2 (:: 3 nil))) 5)

;-------------------------------------------------------------------------------
; Exercise 5.2
; ------------
; Define a function called maybe-last which takes (in addition to the type
; argument for the list element) one (List E) argument and one E argument and
; evaluates to an E with value of either the last element in the list, or the
; value of the second argument if the list is empty.
;
; Answer
; ------
; I take here an approach that follows from `reverse` defined on
; page 125.
; The idea is to pick the first element from the reversed list.

; `maybe-first a d` extracts the first element from `a` if it is not empty
; else it returns `d`
(claim maybe-first (Pi ((E U)) (-> (List E) E E)))
(define maybe-first
  (λ(E)
    (λ(a d) (rec-List a d (λ(e _rest _a-rest) e)))))

(check-same Nat (maybe-first Nat (:: 1 (:: 2 (:: 3 nil))) zero) 1)

; `maybe-last a d` extracts the last element from `a` if it is not empty
; else it returns `d`
(claim maybe-last (Pi ((E U)) (-> (List E) E E)))
(define maybe-last
  (λ(E)
    (λ(a d) (maybe-first E (reverse E a) d)))) 
      
(check-same Nat (maybe-last Nat (:: 1 (:: 2 (:: 3 nil))) zero) 3)

;-------------------------------------------------------------------------------
; Exercise 5.3
; ------------
; Define a function called filter-list which takes (in addition to the type
; argument for the list element) one (-> E Nat) argument representing a
; predicate and one (List E) argument.
; The function evaluates to a (List E) consisting of elements from the list argument
; where the predicate is true.
; Consider the predicate to be false for an element if it evaluates to zero,
; and true otherwise.
;
; Answer
; ------

(claim filter-List (Pi((E U)) (-> (-> E Nat) (List E) (List E))))
(claim step-filter (Pi((E U)) (-> (-> E Nat) E (List E) (List E) (List E))))
(define step-filter
  (λ(E)
    (λ(pred e rest a-rest)
      (which-Nat (pred e)
        a-rest
        (λ(_n) (:: e a-rest))))))  
(define filter-List
  (λ(E)
    (λ(pred a) (rec-List a (the (List E) nil) (step-filter E pred)))))

; example - discard none
(check-same (List Nat) (filter-List Nat (λ(e) 1) (:: 1 (:: 2 (:: 3 nil)))) (:: 1 (:: 2 (:: 3 nil))))
; example - discard all
(check-same (List Nat) (filter-List Nat (λ(e) zero) (:: 1 (:: 2 (:: 3 nil)))) nil)
; example - discard zero
(check-same (List Nat) (filter-List Nat (λ(e) e) (:: 1 (:: 0 (:: 3 nil)))) (:: 1 (:: 3 nil)))


;-------------------------------------------------------------------------------
; Exercise 5.4
; ------------
; Define a function called sort-List-Nat which takes one (List Nat) argument
; and evaluates to a (List Nat) consisting of the elements from the list argument
; sorted in ascending order.
;
; Answer
; ------
; Implementing quicksort here with a partition function that uses the `filter-List`
; function above and the `-` function from a previous exercise

(claim List-Pair U)
(define List-Pair (Pair (List Nat) (List Nat)))

; if a > b then (gt a b) > 0
; a - b > 0
(claim gt (-> Nat Nat Nat))
(define gt (λ(a b) (- a b)))

(check-same Nat (gt 10 3) 7)
(check-same Nat (gt 10 10) 0)
(check-same Nat (gt 1 10) 0)

; if a <= b then (lt a b) > 0
; (b+1) - a > 0
(claim leq (-> Nat Nat Nat))
(define leq (λ(a b) (- (add1 b) a)))

(check-same Nat (leq 10 3) 0)
(check-same Nat (leq 10 10) 1)
(check-same Nat (leq 1 10) 10)

; `partition e a` splits the list `a` into a pair of lists (x y) such that the
; elements in `x` are less than `e` and the rest are in `y`
(claim partition (-> Nat (List Nat) List-Pair))
(define partition
  (λ(c a) (cons (filter-List Nat (gt c) a) (filter-List Nat (leq c) a))))   

(check-same (List Nat) (cdr (partition 2 (:: 3 (:: 2 (:: 1 nil))))) (:: 3 (:: 2 nil)))
(check-same (List Nat) (car (partition 2 (:: 3 (:: 2 (:: 1 nil))))) (:: 1 nil))

(claim part-add (-> Nat List-Pair List-Pair))
(define part-add
  (λ(e p) (cons (car p) (:: e (cdr p)))))

(claim merge-p (-> List-Pair (List Nat)))
(define merge-p
  (λ(p) (the (List Nat) (append Nat (car p) (cdr p)))))

(claim step-q (-> Nat (List Nat) List-Pair List-Pair))
(define step-q
  (λ(h _t a-t) (part-add h (partition h (merge-p a-t)))))

(claim q-sort (-> (List Nat) List-Pair))
(define q-sort
  (λ(lst)
    (rec-List lst (the List-Pair (cons nil nil)) step-q)))

(claim sort-List-Nat (-> (List Nat) (List Nat)))
(define sort-List-Nat
  (λ(lst) (merge-p (q-sort lst))))

(check-same (List Nat) (sort-List-Nat (:: 3 (:: 2 (:: 1 nil)))) (:: 1 (:: 2 (:: 3 nil))))
(check-same (List Nat) (sort-List-Nat (:: 2 (:: 3 (:: 1 nil)))) (:: 1 (:: 2 (:: 3 nil))))
(check-same (List Nat) (sort-List-Nat (:: 1 (:: 2 (:: 3 nil)))) (:: 1 (:: 2 (:: 3 nil))))
(check-same (List Nat) (sort-List-Nat (:: 2 (:: 3 (:: 5 (:: 9 nil))))) (:: 2 (:: 3 (:: 5 (:: 9 nil)))))
(check-same (List Nat) (sort-List-Nat (:: 1 (:: 1 (:: 1 nil)))) (:: 1 (:: 1 (:: 1 nil))))

