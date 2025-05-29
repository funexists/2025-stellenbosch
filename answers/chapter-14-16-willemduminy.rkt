
#lang pie
;-------------------------------------------------------------------------------
; From previous chapters

;-------------------------------------------------------------------------------
; Chapter 14

(claim Maybe (-> U U))
(define Maybe
  (λ(X) (Either X Trivial)))

(claim nothing (∏((E U)) (Maybe E)))
(define nothing (λ(_E) (right sole)))

(claim just
  (∏((E U))
    (-> E (Maybe E))
    )
  )
(define just (λ(_E e) (left e)))

(claim maybe-head
  (∏ ((E U)) (-> (List E) (Maybe E))))
(define maybe-head
  (λ(E l)
    (ind-List l
      (λ(_) (Maybe E))
      (nothing E)
      (λ(h _l-1 _head-l-1)
        (just E h)
        )
      )
    )
  )

(claim maybe-tail
  (∏ ((E U)) (-> (List E) (Maybe (List E)))))
(define maybe-tail
  (λ(E l)
    (ind-List l
      (λ(_) (Maybe (List E)))
      (nothing (List E))
      (λ(_h l-1 _tail-l-1)
        (just (List E) l-1)
        )
      )
    )
  )

(claim list-ref
  (∏((E U))
    (-> Nat (List E) (Maybe E))))
(define list-ref
  (λ(E i)
    (rec-Nat i
      (maybe-head E)
      (λ(_i-1 ref-fn-i-1 l-1)
        (ind-Either (maybe-tail E l-1)
          (λ(_) (Maybe E))
          (λ(tail-l-1) (ref-fn-i-1 tail-l-1))
          (λ(_empty) (nothing E))
          )
        )
      )
    )
  )

; creates a right skewed binary tree of depth n
(claim Fin (-> Nat U))
(define Fin
  (λ(n)
    (iter-Nat n
      Absurd
      Maybe
      )
    )
  )

(claim fzero (∏((n Nat)) (Fin (add1 n))))
(define fzero (λ(n) (nothing (Fin n))))

(claim fadd1 (∏((n Nat)) (-> (Fin n) (Fin (add1 n)))))
(define fadd1
  (λ(n fin-n)
    (just (Fin n) fin-n)
    )
  )

; Note vec-ref does not produce a maybe
(claim vec-ref
  (∏((E U) (l Nat))
    (-> (Fin l) (Vec E l) E)))
(define vec-ref
  (λ(E l)
    (ind-Nat l
      (λ(k) (-> (Fin k) (Vec E k) E))
      (λ(no-val _empty-vec) (ind-Absurd no-val E))
      (λ(_l-1 vec-ref-l-1 fin-l-1 vec-l-1)
        (ind-Either fin-l-1
          (λ(_) E)
          ; smaller tree with tail
          (λ(k) (vec-ref-l-1 k (tail vec-l-1)))
          ; empty tree - take head
          (λ(_trivial) (head vec-l-1))
          )
        )
      )
    )
  )

;-------------------------------------------------------------------------------
; Chapter 15

; 0 = 0 -> Trivial
; else a != b -> Absurd
; else a = b
(claim =consequence (-> Nat Nat U))
(define =consequence
  (λ(a b)
    (which-Nat a
      (which-Nat b
        Trivial
        (λ(_) Absurd
          )
        )
      (λ(a-1)
        (which-Nat b
          Absurd
          (λ(b-1) (= Nat a-1 b-1))
          )
        )
      )
    )
  )

(claim =consequence-same (∏((n Nat)) (=consequence n n)))
(define =consequence-same
  (λ(n)
    (ind-Nat n
      (λ(k) (=consequence k k))
      sole
      (λ(n-1 _a-n-1)
        (same n-1)
        )
      )
    )
  )

(claim use-Nat= (∏((a Nat) (b Nat))
                  (-> (= Nat a b) (=consequence a b))))
(define use-Nat=
  (λ(a _b a=b)
    (replace a=b
      (λ(k) (=consequence a k))
      (=consequence-same a))
    ))

; for all n 0 = 1 + n is absurd
(claim zero-not-add1
  (∏((n Nat)) (-> (= Nat zero (add1 n)) Absurd)))
(define zero-not-add1
  (λ(n)
    (use-Nat= zero (add1 n))
    )
  )

(claim doughnut-absurdity
  (-> (= Nat 0 6) (= Atom 'one 'two)))
(define doughnut-absurdity
  (λ(0=6)
    (ind-Absurd
      (zero-not-add1 5 0=6)
      (= Atom 'one 'two)
      )
    ))


;-------------------------------------------------------------------------------
; From previous exercises

(claim step+ (-> Nat Nat Nat))
(define step+ (λ(_n-1 +n-1) (add1 +n-1)))
(claim + (-> Nat Nat Nat))
(define + (λ(a b) (rec-Nat a b step+)))

(claim step* (-> Nat Nat Nat Nat))
(define step*
  (λ(j _n-1 a-n-1) (+ j a-n-1)))

(claim * (-> Nat Nat Nat))
(define *(λ(n b) (rec-Nat n 0 (step* b))))

; The ^ eliminator
(claim step^ (-> Nat Nat Nat Nat))
(define step^
  (λ(a _n-1 a-n-1)
    (* a-n-1 a)))

;-------------------------------------------------------------------------------
; Exercise

; Define a function that takes two Nat arguments.
; It evaluates to the exponentiation, a^b, of the two passed arguments.
;
; Consider the variant where 0^0 does not have a Nat value

; no special case: 0^0 = 1
(claim weak^ (-> Nat Nat Nat))
(define weak^
  (λ(a n)
    (rec-Nat n
      1
      (λ(_n-1 a^n-1)
        (* a^n-1 a)
        )
      )
    )
  )

(check-same Nat (weak^ 0 0) 1)

; using maybe
(claim maybe^ (-> Nat Nat (Maybe Nat)))
(define maybe^
  (λ(a n)
    (which-Nat n
      ; n = 0
      (which-Nat a
        (nothing Nat)
        (λ(_) (just Nat 1))
        )
      ; n > 0
      (λ(_n-1)
        (just Nat (weak^ a n))
        )
      )
    )
  )

(check-same (Maybe Nat) (maybe^ 2 3) (left 8))
(check-same (Maybe Nat) (maybe^ 3 0) (left 1))
(check-same (Maybe Nat) (maybe^ 0 3) (left 0))
(check-same (Maybe Nat) (maybe^ 0 0) (right sole))
