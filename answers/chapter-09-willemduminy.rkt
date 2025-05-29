#lang pie

;-------------------------------------------------------------------------------
; From previous chapters and exercises

(claim step+ (-> Nat Nat Nat))
(define step+ (λ(_n-1 +n-1) (add1 +n-1)))
(claim + (-> Nat Nat Nat))
(define + (λ(a b) (rec-Nat a b step+)))

(claim incr (-> Nat Nat))
(define incr (λ(n) (iter-Nat n 1 (+ 1))))

(claim mot-incr=add1 (-> Nat U))
(define mot-incr=add1
  (λ(n) (= Nat (incr n) (add1 n))))

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
; From Chapter 9
(claim step-incr=add1-r
  (Pi((n Nat))
    (-> (= Nat (incr n) (add1 n))
      (= Nat (add1 (incr n)) (add1 (add1 n)))
      )))

(define step-incr=add1-r
  (λ(n-1)
    (λ (fn-1)
      (replace
        fn-1
        (λ(k) (= Nat (add1 (incr n-1)) (add1 k)))
        (same (incr (add1 n-1)))
        )
      )))

(claim double (-> Nat Nat))
(claim twice (-> Nat Nat))
(define double
  (λ(n)  (iter-Nat n
           zero
           (λ(a-n-1) (+ 2 a-n-1))
           )))
(define twice
  (λ(n) (+ n n)))

;add1(n + m) = n + add1(m)
(claim add1+=+add1
  (Pi ((n Nat) (m Nat))
    (= Nat (add1 (+ n m)) (+ n (add1 m)))))

(define add1+=+add1
  (λ(n m)
    (ind-Nat n
      ; proposition
      (λ(k) (= Nat (add1 (+ k m)) (+ k (add1 m))))
      ; add1(0 + m) = (add1 1) + m
      (same (add1 m))
      (λ(_n-1 fn-1) (cong fn-1 (+ 1)))
      )))

(claim twice=double
  (Pi ((n Nat))
    (= Nat (twice n) (double n))))

(claim mot-step-t=d (-> Nat Nat U))
(define mot-step-t=d
  (λ(n-1)
    (λ(k) (= Nat (add1 k) (+ 2 (double n-1))))
    )
  )

(claim mot-t=d (-> Nat U))
(define mot-t=d
  (λ(n) (= Nat (twice n) (double n))))

(claim step-t=d (Pi((n Nat)) (-> (mot-t=d n) (mot-t=d (add1 n)))))
(define step-t=d
  (λ(n-1 fn-1)
    ; 2 +
    (replace
      ; add1(n-1 + n-1) = add1(n-1) + n-1
      (add1+=+add1 n-1 n-1)
      ; find k, add1(k) = (2 + double(n-1))
      (mot-step-t=d n-1)
      ; 2 + twice(n-1) = 2 + double(n-1)
      (cong fn-1 (+ 2))
      )
    )
  )

(define twice=double
  (λ(n)
    (ind-Nat n
      ; proposition
      mot-t=d
      ; twice 0 = double 0
      (same zero)
      step-t=d
      )
    )
  )

;-------------------------------------------------------------------------------
; Exercise 9.1
; ------------
; Define a function called same-cons that states and proves that if you cons the
; same value to the front of two equal Lists then the resulting Lists are also
; equal, using replace, because this can also be done with `cong`, but we are
; trying to practice chapter 9's replace.

(claim same-cons
  (Pi ((E U) (x E) (as (List E)) (bs (List E)))
    (-> (= (List E) as bs)
      (= (List E) (:: x as) (:: x bs)))))

(define same-cons
  (λ(E x a _b)
    (λ(a=b)
      (replace
        a=b
        ; a --> b
        (λ(l) (= (List E) (:: x a) (:: x l)))
        ; = (:: x a) (:: x a)
        (same (:: x a))
        )
      )
    )
  )

;-------------------------------------------------------------------------------
; Exercise 9.2
; ------------
; Define a function called same-lists that states and proves that if two
; values, e1 and e2, are equal and two lists, l1 and l2 are equal then
; the two lists, (:: e1 l1) and (:: e2 l2) are also equal.
;

(claim same-lists
  (Pi ((E U) (e1 E) (e2 E) (l1 (List E)) (l2 (List E)))
    (-> (= (List E) l1 l2) (= E e1 e2)
      (= (List E) (:: e1 l1) (:: e2 l2)))))

(define same-lists
  (λ(E e1 _e2 l1 l2)
    (λ(l1=l2 e1=e2)
      (replace
        e1=e2
        (λ(k) (= (List E) (:: e1 l1) (:: k l2)))
        ; = (:: e1 l1) (:: e1 l2)
        (replace
          l1=l2
          ; l1 --> l2
          (λ(k)
            (= (List E) (:: e1 l1) (:: e1 k)))
          ; = (:: e1 l1) (:: e1 l1)
          (same (:: e1 l1))
          )
        )
      )
    )
  )

;-------------------------------------------------------------------------------
; Exercise 9.3
; Define a function called plus-comm that states and proves that + is commutative

(claim mot-pc (-> Nat Nat U))
(define mot-pc
  (λ(n m)
    (= Nat (+ n m) (+ m n))
    )
  )

; = (+ n 0) n
(claim base-pc (Pi((n Nat)) (mot-pc n zero)))
(define base-pc
  (λ(n)
    (ind-Nat
      n
      (λ(k) (= Nat (+ k 0) k))
      (same zero)
      (λ(_n-1 fn-1) (cong fn-1 (+ 1)))
      )
    )
  )

; n + add1(m) = add1(m) + n
(claim step-pc (Pi((n Nat) (m Nat)) (-> (mot-pc n m) (mot-pc n (add1 m)))))
(define step-pc
  (λ(n m)
    (λ(n+m=m+n)
      ; n + add1(m) = add1(m) + n
      (replace
        ; add1(n + m) = n + add1(m)
        (add1+=+add1 n m)
        ; uses add1(m + n) = add1(m) + n -- definition of +
        (λ(k) (= Nat k (+ (add1 m) n)))
        ; add1(n + m) = add1 (m + n)
        (cong n+m=m+n (+ 1))
        )
      )
    )
  )

(claim plus-comm
  (Pi ((n Nat) (m Nat))
    (= Nat (+ n m) (+ m n))))

(define plus-comm
  (λ(n m)
    (ind-Nat m
      (mot-pc n)
      (base-pc n)
      (step-pc n)
      )
    )
  )
