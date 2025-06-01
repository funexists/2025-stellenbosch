;; ============================================================================
;; ## Exercise 1
;;
;; Define a function called `same-cons` that states and proves that
;; if you `cons` the same value to the front of two equal Lists then
;; the resulting Lists are also equal,
;; using `replace`, because this can also be done with cong,
;; but we are trying to practice chapter 9's `replace`.
;;

(claim mot-same-cons
  (Pi ((t U)
       (x t)
       (as (List t)))
    (-> (List t)
      U)))
(define mot-same-cons
  (lambda (t x as k)
    (= (List t) (:: x as) (:: x k))))

(claim base-same-cons
  (Pi ((t U)
       (x t)
       (as (List t)))
    (= (List t) (:: x as) (:: x as))))
(define base-same-cons
  (lambda (t x as)
    (same (:: x as))))

(claim same-cons
  (Pi ((t U)
       (x t)
       (as (List t))
       (bs (List t)))
    (-> (= (List t) as bs)
      (= (List t) (:: x as) (:: x bs)))))
(define same-cons
  (lambda (t x as bs)
    (lambda (same-cons-r)
      (replace same-cons-r
        (mot-same-cons t x as)
        (base-same-cons t x as)
        ))))