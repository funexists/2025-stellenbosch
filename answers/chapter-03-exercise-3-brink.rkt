#lang pie

(claim + (-> Nat Nat Nat))
(define +
  (λ (i j)
    (rec-Nat j
      i
      (λ (j sum)
        (add1 sum)
      )
    )
  )
)

(check-same Nat (+ 1 1) 2)

(claim step-* (-> Nat Nat Nat Nat))
(define step-*
  (lambda (j j-1 mul)
    (+ j mul)
    ))

(claim * (-> Nat Nat Nat))
(define *
  (lambda (i j)
    (rec-Nat i
      0
      (step-* j)
    )
  )
)


(claim step-^ (-> Nat Nat Nat Nat))
(define step-^
  (lambda (j j-1 pow-1)
    (* j pow-1)
  ))

(claim ^ (-> Nat Nat Nat))
(define ^
  (lambda (i j)
    (rec-Nat j
      1
      (step-^ i)
      )
    )
  )
