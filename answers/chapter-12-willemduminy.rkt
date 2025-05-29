#lang pie
;-------------------------------------------------------------------------------
; From previous chapters

(claim step+ (-> Nat Nat Nat))
(define step+ (λ(_n-1 +n-1) (add1 +n-1)))
(claim + (-> Nat Nat Nat))
(define + (λ(a b) (rec-Nat a b step+)))


; 2 * n
(claim double (-> Nat Nat))
(define double
  (λ(n)  (iter-Nat n
           zero
           (λ(double-n-1) (+ 2 double-n-1)))))

; n + n
(claim twice (-> Nat Nat))
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

; n+n = 2*n
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


; k + (n + m) = (k + n) + m
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

; n + (m + k) = (n + m) + k
(claim plus-assoc-b
  (Pi ((n Nat) (m Nat) (k Nat))
    (= Nat (+ n (+ m k)) (+ (+ n m) k))))
(define plus-assoc-b
  (λ(n m k)
    (plus-assoc m k n)))

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

; n + m = n + m
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
;-------------------------------------------------------------------------------
; From chapter 12

; Σ h n = 2 * h
(claim Even (-> Nat U))
(define Even
  (λ(n) (Σ ((even-half Nat)) (= Nat n (double even-half))))
  )

; (the (Even 10) (cons 5 (same 10)) )

(claim +two=even
  (∏((n Nat))
    (-> (Even n) (Even (+ 2 n)))
    )
  )

; Conceptual:
;  A: Even(n)                .. given
;  B:      Σ h n = 2*h       .. from A
;  C:  Σ h 2 + n = 2 + (2*h) ..add 2 on each side of B
;  D: Σ h1 2 + n = 2*h1      ..C From B: h1 = 1 + h
;  E Even(2 + n) .. from D
(define +two=even
  (λ(_n even-n)
    ; Σ h (2 + n) = h
    (cons
      (add1 (car even-n))
      ; 2 + n = 2 + double(car even-n)
      (cong
        (cdr even-n)
        (+ 2)
        )
      )
    )
  )

; Σ k n = 1 + 2 * k
(claim Odd (-> Nat U))
(define Odd
  (λ(n) (Σ((odd-half Nat)) (= Nat n (add1 (double odd-half)))))
  )

(claim add1-even->odd
  (∏((n Nat))
    (-> (Even n)
      (Odd (add1 n))
      )
    )
  )

; Conceptual
; A: Even(n)   .. given
; B:     Σ h n = 2*h     .. from A
; C: Σ h 1 + n = 1 + 2*h .. +1 on each side of B
; D: Odd(1+n)
(define add1-even->odd
  (λ(_n even-n)
    (cons
      ; h
      (car even-n)
      ; 1 + n = 1 + 2 * h
      (cong
        (cdr even-n)
        (+ 1)
        )
      )
    )
  )

(claim add1-odd->even
  (∏((n Nat))
    (-> (Odd n)
      (Even (add1 n))
      )
    )
  )

; Conceptual
; A: Odd(n) .. Given
; B: Σ k n = 1 + 2 * k
; C: Σ k 1 + 1 = 2 + 2 k .. +1 on sides of B
; D: Σ k1 1 + n = 2 * k1 .. from B k1 = 1 + k
; E: Even(n+1)
(define add1-odd->even
  (λ(_n odd-n)
    ; Σ k 1 + n = 2 * k
    (cons (add1 (car odd-n))
      (cong (cdr odd-n) (+ 1))
      )
    )
  )
;-------------------------------------------------------------------------------
; Exercise 12.1
; Define a function called sumOfTwoEvensIsEven that states and proves that the
; sum of two Even Nats is Even.

(claim Even-Twice (-> Nat U))
(define Even-Twice
  (λ(n) (Σ ((even-half Nat)) (= Nat n (twice even-half))))
  )

(claim even->even-twice
  (∏((n Nat)) (-> (Even n) (Even-Twice n))))

; Conceptual
; A: Σ k n = double n
; B: double n = twice n .. Book twice=double
; C: Σ k n = twice n .. B into A
; E: Even-Twice
(define even->even-twice
  (λ(n even-n)
    ; Σ k n = k + k
    (cons
      (car even-n)
      (replace
        ; 2 * k = k + k
        (symm
          ; k + k = 2 * k
          (twice=double (car even-n))
          )
        ; n = 2 * k -> n = s
        (λ(s) (= Nat n s))
        ; n = 2 * k
        (cdr even-n)
        )
      )
    )
  )

; 2(n+1) = 2 + 2n
(claim double+1=2+double
  (∏((n Nat))
    (= Nat
       (double (add1 n))
       (+ 2 (double n))
       )
    )
  )

(define double+1=2+double
  (λ(n)
    (ind-Nat n
      (λ(n)
        (= Nat
          (double (add1 n))
          (+ 2 (double n))
          )
        )
      (same 2)
      (λ(_n-1 a-n-1)
        (cong a-n-1 (+ 2))
        )
      )
    )
  )


(claim 2a+2b=2$a+b
  (∏((a Nat) (b Nat))
    (= Nat
       (+ (double a) (double b))
       (double (+ a b)))))

; Conceptual
; A: (a + b) + (a + b) = 2 (a + b)  .. Twice=double
; B: ((a + b) + a) + b = (a + b) + (a + b) .. Assoc
; C: ((a + b) + a) + b = 2 (a + b)  .. Trans A into B
; D: (a + b) + a = a + (a + b) .. Commute
; E: (a + (a + b)) + b = 2 (a + b) .. Replace D into C
; F: (a + a) + b = a + (a + b) .. Assoc
; G: ((a + a) + b) + b = 2 (a + b)  .. Replace F into E
; H: a + a = 2 a .. Twice = double
; I: (2a + b) + b = 2 (a + b)  .. H into G
; J: (2a + b) + b = 2a + (b + b)
; K: 2a + (b + b) = 2(a + b)  .. J into I
; L: b + b = 2b
; M: 2a + 2b = 2 (a + b) ... L into K
(define 2a+2b=2$a+b
  (λ(a b)
    ;M: 2a + 2b = 2 (a + b)
    (replace
      ; b + b = 2b
      (twice=double b)
      (λ(s) (= Nat (+ (double a) s) (double (+ a b))))
      ; 2a + (b + b) = 2(a + b)
      (trans
        ; 2a + (b + b) = (2a + b) + b
        (plus-assoc-b (double a) b b)
        ; (2a + b) + b = 2 (a + b)
        (replace
          ; a + a = 2a
          (twice=double a)
          (λ(s) (= Nat (+ (+ s b) b) (double (+ a b))))
          ; G: ((a + a) + b) + b = 2 (a + b)
          (replace
            ; a + (a + b) = (a + a) + b
            (plus-assoc-b a a b)
            (λ(s) (= Nat (+ s b) (double (+ a b))))
            ; E: (a + (a + b)) + b = 2 (a + b)
            (replace
              ; (a + b) + a = a + (+ a b)
              (plus-comm (+ a b) a)
              (λ(s) (= Nat (+ s b) (double (+ a b))))
              ; C: ((a + b) + a) + b = 2 (a + b)
              (trans
                ; ((a + b) + a) + b = (a + b) + (a + b)
                (symm
                  ; (a + b) + (a + b) = ((a + b) + a) + b
                  (plus-assoc-b (+ a b) a b)
                  )
                ; A: (a + b) + (a + b) = 2(a + b)
                (twice=double (+ a b))
                )
              )
            )
          )
        )
      )
    )
  )

(claim sumOfTwoEvensIsEven
  (∏((a Nat) (b Nat))
    (-> (Even a) (Even b) (Even (+ a b)))))

; Conceptual
; A: 2k1 + 2k2 = 2 (k1 + k2) .. Shown above
; B: b = 2k2 .. Given
; C: a + b = a + 2k2  .. From B prefix a +
; D: a = 2k1 .. Given
; E: a + b = 2k1 + 2k2 .. D into C
; F: a + b  2 (k1 + k2)  .. A into E
(define sumOfTwoEvensIsEven
  (λ(a b even-a even-b)
    ; F: a + b = 2 (k1 + k2)
    (cons
      ; k3 = k1 + k2
      (+ (car even-a) (car even-b))
      (trans
        ; E: a + b = 2k1 + 2k2
        (replace
          ; a = 2k1
          (cdr even-a)
          (λ(s) (= Nat
                  (+ a b)
                  (+ s
                    (double (car even-b)))
                  )
            )
          ; C: a + b = a + 2k2
          (cong
            ; B: b = 2k2
            (cdr even-b)
            (+ a))
          )
        ; A: 2k1 + 2k2 = 2 (k1 + k2)
        (2a+2b=2$a+b (car even-a) (car even-b))
        )
      )
    )
  )

;-------------------------------------------------------------------------------
; Exercise 12.2
; Define a function called sumOfTwoOddsIsEven that states and proves that the
; sum of two Odd Nats is Even.

(claim 1+2a$1+2b=2$a+b+1
  (∏((a Nat) (b Nat))
    (= Nat
       (+ (+ 1 (double a)) (+ 1 (double b)))
       (double (+ a (+ b 1)))
       )
    )
  )

(claim lhs (-> Nat Nat Nat))
(define lhs
  (λ(a b) (+ (+ 1 (double a)) (+ 1 (double b)))))


(define 1+2a$1+2b=2$a+b+1
  (λ(a b)
    ; lhs = 2 (a + (b + 1))
    (replace
      ; 2a + 2(b + 1) = 2 (a + (b + 1))
      (2a+2b=2$a+b a (+ b 1))
      (λ(s) (= Nat (lhs a b)
              s
              ))
      ; lhs = 2a + 2(b + 1)
      (replace
        ; 2b + 2 = 2(b + 1)
        (2a+2b=2$a+b b 1)
        (λ(s) (= Nat (lhs a b)
                (+ (double a) s)
                ))
        ; lhs = 2a + (2b + 2)
        (replace
          ; 2 + 2b = 2b + 2
          (plus-comm 2 (double b))
          (λ(s) (= Nat (lhs a b)
                  (+ (double a) s)
                  ))

          ; lhs = 2a + (1 + (1 + 2 b)
          ;     = 2a + (2 + 2b)
          (replace
            ; (2a + 1) + (1 + 2b) =  2a + (1 + (1 + 2 b)
            (symm (plus-assoc-b (double a) 1 (+ 1 (double b))))
            (λ(s) (= Nat (lhs a b) s))
            ; lhs = (2a + 1) + (1 + 2b)
            (replace
              ; 1 + 2a = 2a + 1
              (plus-comm 1 (double a))
              (λ(s) (= Nat (lhs a b)
                      (+ s (+ 1 (double b)))
                      ))
              ; (1 + 2a) + (1 + 2b) = (1 + 2a) + (1 + 2b)
              (same (lhs a b))
              )
            )
          )
        )
      )
    )
  )

(claim sumOfTwoOddsIsEven
  (∏ ((a Nat) (b Nat))
    (-> (Odd a) (Odd b) (Even (+ a b)))))

(define sumOfTwoOddsIsEven
  (λ(a b odd-a odd-b)
    (cons
      (+ (car odd-a) (+ (car odd-b) 1))
      ; a + b = double (a + (b + 1))
      (replace
        (1+2a$1+2b=2$a+b+1 (car odd-a) (car odd-b))
        (λ(s) (= Nat
                (+ a b)
                s
                )
          )
        (replace
          ; a = 1 + 2k1
          (cdr odd-a)
          (λ(s) (= Nat
                  (+ a b)
                  (+ s (add1 (double (car odd-b))))
                  )
            )
          ; a + b = a + (1 + 2k2)
          (cong
            (cdr odd-b)
            (+ a))
          )
        )
      )
    )
  )
