#lang pie

;; Exercise 1
'ex-one

(claim at-least-two?
  (-> Nat
    Atom))
(define at-least-two?
  (lambda (n)
    (which-Nat n
      'nil
      (lambda (n-1)
        (which-Nat n-1
          'nil
          (lambda (n-1) 't)
          )
        )
      )
    ))

(at-least-two? 0)
(at-least-two? 1)
(at-least-two? 2)
(at-least-two? 3)


;; Exercise 2
'ex-two

(claim step-+
  (-> Nat Nat Nat
    Nat))
(define step-+
  (lambda (j n-1 +-1)
    (add1 +-1)))

(claim +
  (-> Nat Nat
    Nat))
(define +
  (lambda (i j)
    (rec-Nat i
      j
      (step-+ i)
      )
    ))

(+ 0 1)
(+ 2 8)
(+ 0 0)

;; alt +
;; (claim +
;;   (-> Nat Nat
;;     Nat))
;;
;; (claim step-+
;;   (-> Nat Nat Nat
;;     Nat))
;;
;; (define step-+
;;   (lambda (i n-1 +-1)
;;     (add1 +-1)))
;;
;;
;; (define +
;;   (lambda (a b)
;;     (rec-Nat a
;;       (rec-Nat b
;;         0
;;         (step-+ b))
;;       (step-+ a)
;;       )
;;     )
;;   )

;; Exercise 3
'ex-three
(claim step-*
  (-> Nat Nat Nat
    Nat))
(define step-*
  (lambda (j n-1 *-1)
    (+ j *-1)))

(claim *
  (-> Nat Nat
    Nat))
(define *
  (lambda (i j)
    (rec-Nat i
      0
      (step-* j))))

(claim exp
  (-> Nat Nat
    Nat))

(claim step-exp
  (-> Nat Nat Nat
    Nat))

(define step-exp
  (lambda (i n-1 exp-1)
    (* i exp-1)))

(define exp
  (lambda (i j)
    (rec-Nat j
      (add1 zero)
      (step-exp i)
      )
    )
  )

(exp 2 1)
(exp 2 2)
(exp 2 3)
(exp 2 4)


;; Exercise 4
'ex-four


;; This might be over complicated
(claim min1
  (-> Nat
    Nat))
(define min1
  (lambda (n)
    (which-Nat n
      0
      (lambda (s) s)
      )))

(claim step-min
  (-> Nat Nat Nat
    Nat))
(define step-min
  (lambda (i n-1 min-1)
    (min1 min-1)
    ))

(claim sub
  (-> Nat Nat
    Nat))
(define sub
  (lambda (a b)
    (rec-Nat b
      a
      (step-min a))
    ))
'suba
(sub 7 5)
(sub 0 5)

(claim step-max
  (-> Nat Nat Nat
    Nat))


(claim max
  (-> Nat Nat
    Nat))

(define step-max
  (lambda (i n-1 max-1)
    (add1 max-1)))

(define max
  (lambda (a b)
    (rec-Nat a
      ;; 0
      (sub b a)
      (step-max b)
      )
    )
  )
'maxa
(max 0 0)
(max 1 0)
(max 0 1)
(max 5 10)


;; Exercise 5
'ex-five

;; something in the form of:
;; gcd(a b) x
;;      while b != 0
;;          a, b = b, a rem b
;;      return a
;; I guess first try and get recursive remainder definition.
;; then use that for gcd.
'rem
;; as simple as:
;; rm(0, y) = 0
;; rm(x + 1, y) = (rm(x, y) + 1) · sg(|y − (rm(x, y) + 1)|)

(claim step-rem
  (-> Nat Nat Nat
    Nat))
(define step-rem
  (lambda (j n-1 rem-1)
  ;; oof
    (* (add1 rem-1) (sub j (add1 rem-1)))))

(claim rem
  (-> Nat Nat
    Nat))
(define rem
  (lambda (a b)
    (rec-Nat a
      0
      (step-rem b)
      )
    )
  )
(rem 2 5) ;; 2
(rem 5 2) ;; 1



(claim gcd
  (-> Nat Nat
    Nat))




;; Exercise 6
'ex-six

(claim step-fact
  (-> Nat Nat
    Nat))

(define step-fact
  (lambda (n-1 almost)
    (* (add1 n-1) almost)))

(claim fact
  (-> Nat
    Nat))

(define fact
  (lambda (n)
    (rec-Nat n
      (add1 0) ;; need to have 1 as the base case
      step-fact)))

(fact 0) ;; 1
(fact 1) ;; 1
(fact 2) ;; 2
(fact 3) ;; 6
(fact 4) ;; 42


