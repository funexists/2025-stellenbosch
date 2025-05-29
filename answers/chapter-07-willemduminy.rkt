#lang pie
; https://github.com/funexists/2025-stellenbosch/blob/main/Chapter7.md
;-------------------------------------------------------------------------------
; Sample data for tests
(claim vec-nats (Vec Nat 3))
(define vec-nats (vec:: 10 (vec:: 20 (vec:: 30 vecnil))))
(claim vec-nats-2 (Vec Nat 3))
(define vec-nats-2 (vec:: 1 (vec:: 2 (vec:: 3 vecnil))))

; Functions from the book

; drop last
; f(a::nil) = nil
; f(h::t) = h::f(t)

(claim mot-drop-last (-> U Nat U))
(define mot-drop-last
  (λ (E n) (-> (Vec E (add1 n)) (Vec E n))))

(claim base-drop-last (Pi ((E U)) (mot-drop-last E zero)))
(define base-drop-last (λ(_E) (λ(_h::nil) vecnil)))

(claim step-drop-last
  (Pi ((E U) (n-1 Nat))
    (-> (mot-drop-last E n-1) (mot-drop-last E (add1 n-1)))))
(define step-drop-last
  (λ(_E _n-1 fn-1)
    (λ(v)
      (vec:: (head v) (fn-1 (tail v)))
      )))

(claim drop-last
  (Pi ((E U) (n Nat)) (-> (Vec E (add1 n)) (Vec E n))))
(define drop-last
  (λ(E n)
    (ind-Nat n
      (mot-drop-last E)
      (base-drop-last E)
      (step-drop-last E))))

; (drop-last Nat 2 vec-nats)

; Functions from previous exercises

(claim step+ (-> Nat Nat Nat))
(define step+
  (λ(_n-1 a-n-1)
    (add1 a-n-1)))

(claim + (-> Nat Nat Nat))
(define +
  (λ(a b) (rec-Nat a b step+)))

(claim predecessor (-> Nat Nat))
(define predecessor (λ(n) (which-Nat n 0 (λ(n-1) n-1))))

(claim - (-> Nat Nat Nat))
(define - (λ(a b) (rec-Nat b a (λ(b-1 a-b-1) (predecessor a-b-1)))))


;-------------------------------------------------------------------------------
; Exercise 7.0
; ------------
; Define a function called zip that takes an argument of type (Vec A n) and
; a second argument of type (Vec B n) and evaluates to a value of type
; (Vec (Pair A B) n), the result of zipping the first and second arguments.

; Answer
; -----

; The idea is that we have a function f(a,b) -> v
; f(nil,nil) = nil
; f(a::b,c::d) = (a,c)::f(b,d)

(claim VecPair (-> U U Nat U))
(define VecPair (λ(A B n) (Vec (Pair A B) n)))

; Note: In a way the motive describes the full function

(claim mot-zip (-> U U Nat U))
(define mot-zip (λ(A B n) (-> (Vec A n) (Vec B n) (VecPair A B n))))

; The base can now be defined in terms of the motive

(claim base-zip
  (Pi ((A U) (B U))
    (mot-zip A B zero)))
(define base-zip
  (λ(_A _B)
    (λ(_va _vb) vecnil)))

(claim step-zip
  (Pi ((A U) (B U) (n-1 Nat))
    (-> (mot-zip A B n-1) (mot-zip A B (add1 n-1)))))

(define step-zip
  (λ(_A _B _n-1 fn-1)
    (λ(va vb)
      (vec::
        (cons (head va) (head vb))
        (fn-1 (tail va) (tail vb))))))

(claim zip
  (Pi((A U) (B U)(n Nat))
    (-> (Vec A n) (Vec B n) (VecPair A B n))))

(define zip
  (λ(A B n)
    (ind-Nat n
      (mot-zip A B)
      (base-zip A B)
      (step-zip A B))))


(check-same (Vec (Pair Nat Nat) 3)
  (zip Nat Nat 3 vec-nats vec-nats)
  (vec:: (cons 10 10) (vec:: (cons 20 20) (vec:: (cons 30 30) vecnil))))

;-------------------------------------------------------------------------------
; Exercise 7.1
; ------------
; Define a function called append that takes an argument of type (Vec E m) and
; an argument of type (Vec E n) and evaluates to a value of type (Vec (+ m n)),
; the result of appending the elements of the second argument to the end of
; the first.


; Answer
; ------
; Define prepend(a,b)
; Then append(a,b) = prepend(b,a)
; it reverses the arguments of prepend

; For prepend:
; f(a, nil) = a
; f(a,b::c) = b::f(a,c)

(claim mot-prepend (-> U Nat Nat U))
(define mot-prepend
  (λ(E m n)
    (-> (Vec E m) (Vec E n) (Vec E (+ n m)))))

(claim base-prepend
  (Pi ((E U) (m Nat))
    (mot-prepend E m zero)))
(define base-prepend
  (λ(_E _m)
    (λ(vm _vn) vm)))

(claim step-prepend
  (Pi((E U) (m Nat) (n-1 Nat))
    (-> (mot-prepend E m n-1) (mot-prepend E m (add1 n-1)))))

(define step-prepend
  (λ(_E _m _n-1 fn-1)
    (λ(vm vn)
      (vec:: (head vn) (fn-1 vm (tail vn))))))

(claim prepend
  (Pi((E U) (m Nat) (n Nat))
    (-> (Vec E m) (Vec E n) (Vec E (+ n m)))))

(define prepend
  (λ(E m n)
    (ind-Nat n
      (mot-prepend E m)
      (base-prepend E m)
      (step-prepend E m))))

(claim append
  (Pi((E U) (m Nat) (n Nat))
    (-> (Vec E m) (Vec E n) (Vec E (+ m n)))))
(define append
  (λ(E m n va vb) (prepend E n m vb va)))

(check-same (Vec Nat 6)
  (append Nat 3 3 vec-nats vec-nats-2)
  (vec:: 10 (vec:: 20 (vec:: 30 (vec:: 1 (vec:: 2 (vec:: 3 vecnil)))))))

;-------------------------------------------------------------------------------
; Exercise 7.2
; ------------
; Define a function called drop-last-k that takes an argument of type (Vec E ?)
; and evaluates to a value of type (Vec E ?), the result of dropping the last
; k elements from the first argument.
; NB: The type of the function should guarantee that we can't drop more
; elements than there are in the first argument.
;
; Answer
; ------
; f(0, a) = a
; f(n+1,a) = f(n,drop-last(a))
; where drop-last is in the book p 161

(claim mot-drop (-> U Nat Nat U))
(define mot-drop
  (λ(E n k)
    (-> (Vec E (+ k n)) (Vec E n))))

(claim base-drop (Pi ((E U) (n Nat)) (mot-drop E n zero)))
(define base-drop
  (λ(_E _n)
    (λ(v) v)))

(claim step-drop
  (Pi ((E U) (n Nat) (k-1 Nat))
    (-> (mot-drop E n k-1) (mot-drop E n (add1 k-1)))))
(define step-drop
  (λ(E n k-1 fk-1)
    (λ(v)
      (fk-1 (drop-last E (+ k-1 n) v)))))

(claim drop-last-k
  (Pi ((E U) (n Nat) (k Nat))
    (-> (Vec E (+ k n)) (Vec E n))))

; drops last k items from from vector with (n+k) elements
; we pass in both n and k as arguments to guarantee the
; drop condition
(define drop-last-k
  (λ(E n k)
    (ind-Nat k
      (mot-drop E n)
      (base-drop E n)
      (step-drop E n))))

(check-same (Vec Nat 1)
  (drop-last-k Nat 1 2 vec-nats)
  (vec:: 10 vecnil))
