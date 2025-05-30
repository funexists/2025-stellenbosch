#lang pie

;; We were told to come up with an exercise. I showed that if a type t has decidable equality, so does List t.

(claim Dec (-> U U))
(define Dec
  (lambda (t)
    (Either t (-> t Absurd)) ))

(claim DecEq (-> U U))
(define DecEq
  (lambda (t)
    (Pi ((x t) (y t)) (Dec (= t x y))) ))

(claim zero-consequence (Pi ((n Nat)) U))
(define zero-consequence
  (lambda (m)
    (which-Nat m
      Trivial
      (lambda (_) Absurd) )))

(claim zero-not-add1 (Pi ((n Nat)) (-> (= Nat zero (add1 n)) Absurd)))
(define zero-not-add1
  (lambda (n 0=n+1)
    (replace 0=n+1
      (lambda (k) (zero-consequence k))
      sole )))

(claim length (Pi ((t U)) (-> (List t) Nat)))
(define length
  (lambda (t xs)
    (rec-List xs
      0
      (lambda (x xs prev) (add1 prev)) )))

(claim empty-not-nonempty (Pi ((t U) (y t) (ys (List t))) (-> (= (List t) nil (:: y ys)) Absurd)))
(define empty-not-nonempty
  (lambda (t y ys eq)
    (zero-not-add1 (length t ys) (cong eq (length t))) ))

;(claim head-nonempty (Pi ((t U) (xs (List t))) (-> (Sigma ((n Nat)) (= Nat (length t xs) (add1 n))) t)))
;(define head-nonempty
;  (lambda (t xs)
;    (ind-List xs
;      (lambda (xs) (-> (Sigma ((n Nat)) (= Nat (length t xs) (add1 n))) t))
;      (lambda (not-empty)
;        (ind-Absurd
;          (zero-not-add1 (car not-empty) (cdr not-empty))
;          t ))
;      (lambda (x xs _ not-empty) x) )))

;(claim tail-nonempty (Pi ((t U) (xs (List t))) (-> (Sigma ((n Nat)) (= Nat (length t xs) (add1 n))) (List t))))
;(define tail-nonempty
;  (lambda (t xs)
;    (ind-List xs
;      (lambda (xs) (-> (Sigma ((n Nat)) (= Nat (length t xs) (add1 n))) (List t)))
;      (lambda (not-empty)
;        (ind-Absurd
;          (zero-not-add1 (car not-empty) (cdr not-empty))
;          (List t) ))
;      (lambda (x xs _ not-empty) xs) )))

;(claim list-to-vec (Pi ((t U) (xs (List t))) (Vec t (length t xs))))
;(define list-to-vec
;  (lambda (t xs)
;    (ind-List xs
;      (lambda (xs) (Vec t (length t xs)))
;      vecnil
;      (lambda (x xs prev) (vec:: x prev)) )))
;; TODO TODO: How do you do (cong xs=ys list-to-vec)? What should the type be?

;; The following three functions are based on how the book proved decidable equality for Nat.
(claim =consequence-list (Pi ((t U)) (-> (List t) (List t) U)))
(define =consequence-list
  (lambda (t xs ys)
    (rec-List xs
      (rec-List ys
        Trivial
        (lambda (y ys _) Absurd) )
      (lambda (x xs _)
        (rec-List ys
          Absurd
          (lambda (y ys _)
            (Pair (= t x y) (= (List t) xs ys)) ))) )))

(claim =consequence-list-same (Pi ((t U) (xs (List t))) (=consequence-list t xs xs)))
(define =consequence-list-same
  (lambda (t xs)
    (ind-List xs
      (lambda (xs) (=consequence-list t xs xs))
      sole
      (lambda (x xs _) (cons (same x) (same xs))) )))

(claim use-List (Pi ((t U) (xs (List t)) (ys (List t))) (-> (= (List t) xs ys) (=consequence-list t xs ys))))
(define use-List
  (lambda (t xs ys xs=ys)
    (replace xs=ys
      (lambda (zs) (=consequence-list t xs zs))
      (=consequence-list-same t xs) )))

;; TODO: Is there any easier approach? <-- I think ind-= (not mentioned in the book) might be helpful? I thought so at first, but not I'm not so sure.
(claim equal-lists-equal-heads (Pi ((t U) (x t) (xs (List t)) (y t) (ys (List t))) (-> (= (List t) (:: x xs) (:: y ys)) (= t x y))))
(define equal-lists-equal-heads
  (lambda (t x xs y ys xxs=yys)
    (car (use-List t (:: x xs) (:: y ys) xxs=yys)) ))

(claim equal-lists-equal-tails (Pi ((t U) (x t) (xs (List t)) (y t) (ys (List t))) (-> (= (List t) (:: x xs) (:: y ys)) (= (List t) xs ys))))
(define equal-lists-equal-tails
  (lambda (t x xs y ys xxs=yys)
    (cdr (use-List t (:: x xs) (:: y ys) xxs=yys)) ))

(claim equal-head-and-tail-equal-lists (Pi ((t U) (x t) (xs (List t)) (y t) (ys (List t))) (-> (= t x y) (= (List t) xs ys) (= (List t) (:: x xs) (:: y ys)))))
(define equal-head-and-tail-equal-lists
  (lambda (t x xs y ys x=y xs=ys)
    (replace x=y
      (lambda (z) (= (List t) (:: x xs) (:: z ys)))
      (cong xs=ys (the (-> (List t) (List t)) (lambda (zs) (:: x zs)))) ) ))

(claim list-preseves-dec-eq (Pi ((t U)) (-> (DecEq t) (DecEq (List t)))))
(define list-preseves-dec-eq
  (lambda (t dec-elt xs)
    (ind-List xs
      (lambda (xs) (Pi ((ys (List t))) (Dec (= (List t) xs ys))))
      (lambda (ys)
        (ind-List ys
          (lambda (ys) (Dec (= (List t) nil ys)))
          (left (same nil))
          (lambda (y ys _) (right (empty-not-nonempty t y ys))) ))
      (lambda (x xs prev ys) ; (prev zs) says if xs equals zs or not
        (ind-List ys
          (lambda (ys) (Dec (= (List t) (:: x xs) ys)))
          (right (lambda (eq) (empty-not-nonempty t x xs (symm eq))))
          (lambda (y ys _)
            (ind-Either (prev ys)
              (lambda (_) (Dec (= (List t) (:: x xs) (:: y ys))))
              (lambda (xs=ys)
                (ind-Either (dec-elt x y)
                  (lambda (_) (Dec (= (List t) (:: x xs) (:: y ys))))
                  (lambda (x=y) (left (equal-head-and-tail-equal-lists t x xs y ys x=y xs=ys)))
                  (lambda (x!=y) (right (lambda (xxs=yys) (x!=y (equal-lists-equal-heads t x xs y ys xxs=yys))))) ))
              (lambda (xs!=ys) (right (lambda (xxs=yys) (xs!=ys (equal-lists-equal-tails t x xs y ys xxs=yys))))) )) )) ) ))

; This shows Trivial has decidable equality
(claim trivial-dec (DecEq Trivial))
(define trivial-dec
  (lambda (x y)
    (left (same sole)) ))

;; (List Trivial) is essentially Nat
(claim list-trivial-dec (DecEq (List Trivial)))
(define list-trivial-dec (list-preseves-dec-eq Trivial trivial-dec))

;; TODO: If I have time I can show Nat is iso to (List Trivial) and transport the proof of decidable equality along the isomorphism. <-- Too much work.
