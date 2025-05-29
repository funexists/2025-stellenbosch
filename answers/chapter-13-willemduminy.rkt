
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

; Σ h n = 2 * h
(claim Even (-> Nat U))
(define Even
  (λ(n) (Σ ((even-half Nat)) (= Nat n (double even-half))))
  )

;-------------------------------------------------------------------------------
; Exercise 13.1
; Define a function called nOrSuccnIsEven that states and proves that for
; all Nats n, either n is Even or n+1 is Even.

(claim zeroIsEven (Even zero))
(define zeroIsEven
  (cons zero (same zero)))

(claim nOrSuccnIsEven
  (∏((n Nat)) (Either (Even n) (Even (add1 n))))
  )

(claim mot-nOrSIsEven
  (-> Nat U))
(define mot-nOrSIsEven
  (λ(n)
    (Either (Even n) (Even (add1 n)))
    )
  )

(claim base-nOrSIsEven
  (mot-nOrSIsEven zero))
(define base-nOrSIsEven
  (left zeroIsEven)
  )

(claim step-nOrSIsEven
  (∏((n Nat))
    (-> (mot-nOrSIsEven n) (mot-nOrSIsEven (add1 n)))
    )
  )

(define step-nOrSIsEven
  (λ(n-1 a-n-1 )
    (ind-Either a-n-1
      (λ(_) (mot-nOrSIsEven (add1 n-1)))
      (λ(n-1IsEven)
        (right ; Even n
          ; Σ k1 k1 + (1 + n-1) = 1 + (1 + n-1)
          (cons
            ; k1 = 1 + k
            (add1 (car n-1IsEven))
            ; 2 + (k + n-1) = 2 + n-1
            (cong
              ; k + n-1 = n-1
              (cdr n-1IsEven)
              (+ 2)
              )
            )
          )
        )
      (λ(nIsEven)
        (left
          nIsEven
          ))
      )
    )
  )

(define nOrSuccnIsEven
  (λ(n)
    (ind-Nat n
      mot-nOrSIsEven
      base-nOrSIsEven
      step-nOrSIsEven
      )
    )
  )
