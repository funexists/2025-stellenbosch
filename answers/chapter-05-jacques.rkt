#lang pie

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

;; ==========
;; Exercise 1

(claim step-sum-List
  (-> Nat (List Nat) Nat
    Nat))
(define step-sum-List
  (lambda (e es n)
    (+ e n)))

(claim sum-List
  (-> (List Nat)
    Nat))
(define sum-List
  (lambda (es)
    (rec-List es
      0
      step-sum-List)))

(check-same Nat (sum-List (the (List Nat) nil)) 0)
(check-same Nat (sum-List (:: 3 nil)) 3)
(check-same Nat (sum-List (:: 0 (:: 1 (:: 2 (:: 3 nil))))) 6)


;; ==========
;; Exercise 2
(claim step-length
  (Pi ((E U))
    (-> E (List E) Nat
      Nat)))
(define step-length
  (lambda (E)
    (lambda (e es n)
      (add1 n))))
(claim length
  (Pi ((E U))
    (-> (List E)
      Nat)))
(define length
  (lambda (E)
    (lambda (es)
      (rec-List es
        0
        (step-length E)))))



(claim maybe-last
  (Pi ((E U))
    (-> (List E) E
      E)))
(define maybe-last
  (lambda (E)
    (lambda (ls ml)
      (rec-List ls
        ml
        (lambda (ei es n)
          (which-Nat (length E es)
            ei
            (lambda (m) n)))
        ))))

(check-same Atom (maybe-last Atom (:: 'a (:: 'b nil)) 'last) 'b)
(check-same Atom (maybe-last Atom (the (List Atom) nil) 'last) 'last)
(check-same Nat (maybe-last Nat (:: 1 (:: 2 nil)) 10) 2)
(check-same Nat (maybe-last Nat (the (List Nat) nil) 2) 2)


;; ==========
;; Exercise 3
(claim step-filter
  (Pi ((E U))
    (-> (-> E Nat) E (List E) (List E)
      (List E))))
(define step-filter
  (lambda (E)
    (lambda (filter e es n)
      (which-Nat (filter e)
        n
        (lambda (ni) (:: e n))
        ))))



(claim filter-list
  (Pi ((E U))
    (-> (-> E Nat) (List E)
      (List E))))
(define filter-list
  (lambda (E)
    (lambda (filter ls)
      (rec-List ls
        (the (List E) nil)
        (step-filter E filter)
        ))))

;; filter out 0's from a (List Nat)
(check-same (List Nat)
  (filter-list Nat
    (lambda (n)
      (which-Nat n
        0 (lambda (ni) n)))
    (:: 0 (:: 1 (:: 2 (:: 2 (:: 0 (:: 3 (:: 0 nil))))))))
  (:: 1 (:: 2 (:: 2 ( :: 3 nil)))))

;; How do you compare atoms?
(filter-list Atom
  (lambda (n)
    TODO)
  (:: 'pie nil))
;; (:: 'pie (:: 'more (:: 'pie (:: 'and (:: 'pie nil))))))


;; ==========
;; Exercise 4


(claim dec
  (-> Nat
    Nat))
(define dec
  (lambda (n)
    (which-Nat n
      0
      (lambda (s) s))))

(claim -
  (-> Nat Nat
    Nat))
(define -
  (lambda (a b)
    (iter-Nat b
      a
      dec)))

(check-same Nat (- 7 5) 2)
(check-same Nat (- 0 5) 0)


;; Dont ask me to sort 0's
(claim sort-List-Nat
  (-> (List Nat)
    (List Nat)))
(define sort-List-Nat
  (lambda (ln)
    (rec-List ln
      (the (List Nat) nil)
      (lambda (xi xs lres)
        (rec-List lres
          (:: xi nil)
          (lambda (xi2 xs2 lres2)
            (which-Nat (- (add1 xi) xi2)
              (:: xi lres)
              (lambda (n-1)
                (:: xi2 lres2)
                ))))))))
(check-same (List Nat) (sort-List-Nat (:: 2 (:: 1 (:: 0 nil))))
  (:: 0 (:: 1 (:: 2 nil))))

(check-same (List Nat) (sort-List-Nat (:: 2 (:: 2 (:: 2 nil))))
  (:: 2 (:: 2 (:: 2 nil))))

(check-same (List Nat) (sort-List-Nat (:: 0 (:: 1 (:: 2 nil))))
  (:: 0 (:: 1 (:: 2 nil))))

(check-same (List Nat) (sort-List-Nat (:: 0 (:: 1 (:: 0 nil))))
  (:: 0 (:: 0 (:: 1 nil))))

(check-same (List Nat) (sort-List-Nat (:: 1 (:: 0 nil)))
  (:: 0 (:: 1 nil)))

(check-same (List Nat) (sort-List-Nat (:: 0 (:: 0 (:: 1 (:: 0 nil)))))
  (:: 0 (:: 0 (:: 0 (:: 1 nil)))))

(check-same (List Nat) (sort-List-Nat (:: 2 (:: 2 (:: 1 nil))))
  (:: 2 (:: 2 (:: 1 nil))))

(check-same (List Nat) (sort-List-Nat (:: 5 (:: 4 (:: 3 nil))))
  (:: 3 (:: 4 (:: 5 nil))))


(claim kons
  (-> (List Nat) Nat
    (List Nat)))
(define kons
  (lambda (le a)
    (:: a le)))
;; (kons (:: 1 (:: 0 nil)) 1)

(claim snok
  (-> (List Nat) Nat
    (List Nat)))
(define snok
  (lambda (le a)
    (rec-List le
      (:: a nil)
      (lambda (e es eres)
        (:: e eres)
        ))))
;; (snok (:: 1 (:: 0 nil)) 1)
