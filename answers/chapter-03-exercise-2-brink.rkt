#lang pie
(claim + (-> Nat Nat Nat))

(claim step+ (-> Nat Nat Nat))
(define step+
    (λ (_ n)
      (add1 n)
      )
  )


(define +
  (λ(i j)
    (rec-Nat j
      i
      step+
      )
    )
  )

(check-same Nat (+ 4 5) 9)
