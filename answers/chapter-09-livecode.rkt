#lang pie

(claim same-cons
  (Pi ((t U) (x t) (as (List t)) (bs (List t)))
    (-> (= (List t) as bs)
        (= (List t) (:: x as) (:: x bs)))))

; The Law of replace for Pie
; If target is an
;  (= X from to),
; mot is an
;  (-> X U),
; and base is a
;  base = (mot from)
; then
;  (replace target mot base)
; is a
;  (mot to).

(define same-cons
  (lambda (t x as bs as=bs)
    ; mot to = (= (List t) (:: x as) (:: x bs))
    (replace
      as=bs
      (lambda (xs) (= (List t) (:: x as) (:: x xs)))
      ; (= (List t) (:: x as) (:: x as))
      (same (:: x as)))))
      











(claim same-lists
  (Pi ((t U) (e1 t) (e2 t) (l1 (List t)) (l2 (List t)))
    (-> (= (List t) l1 l2) (= t e1 e2)
        (= (List t) (:: e1 l1) (:: e2 l2)))))

(define same-lists
  (lambda (t e1 e2 l1 l2 l1=l2 e1=e2)
    ; mot to = (= (List t) (:: e1 l1) (:: e2 l2))
    (replace e1=e2
      (lambda (x) (= (List t) (:: e1 l1) (:: x l2)))
      (same-cons t e1 l1 l2 l1=l2)
      )))

