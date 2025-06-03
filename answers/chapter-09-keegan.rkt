#lang pie

; Exercise 1
(claim same-cons
  (Pi ((t U) (x t) (as (List t)) (bs (List t)))
    (-> (= (List t) as bs)
        (= (List t) (:: x as) (:: x bs)))))
(define same-cons
  (lambda (t x as _bs as=bs)
    (replace as=bs
      (lambda (k) (= (List t) (:: x as) (:: x k)))
      (same (:: x as)))))

; Exercise 2
(claim same-lists
  (Pi ((t U) (e1 t) (e2 t) (l1 (List t)) (l2 (List t)))
    (-> (= (List t) l1 l2) (= t e1 e2)
        (= (List t) (:: e1 l1) (:: e2 l2)))))
(define same-lists
  (lambda (t e1 _e2 l1 l2 l1=l2 e1=e2)
    (replace e1=e2
      (lambda (k) (= (List t) (:: e1 l1) (:: k l2)))
      (same-cons t e1 l1 l2 l1=l2))))

(claim step-+
  (-> Nat Nat Nat))
(define step-+
  (lambda (_ n-1) (add1 n-1)))

(claim +
  (-> Nat Nat Nat))
(define +
  (lambda (n m)
    (rec-Nat n
      m
      step-+)))

(claim n+zero=n
  (Pi ((n Nat)) (= Nat (+ n 0) n)))
(define n+zero=n
  (lambda (n)
    (ind-Nat n
      (lambda (n) (= Nat (+ n 0) n))
      (same zero)
      (lambda (_ ih)
        (cong ih (+ 1))))))

(claim add1-+=+-add1
  (Pi ((a Nat) (b Nat)) 
    (= Nat (add1 (+ a b)) (+ a (add1 b)) )))
(define add1-+=+-add1
  (lambda (a b)
    (ind-Nat a
      (lambda (a) (= Nat (add1 (+ a b)) (+ a (add1 b))))
      (same (add1 b))
      (lambda (_ ih)
        (cong ih (+ 1))))))

; Exercise 3
(claim a+b=b+a
  (Pi ((a Nat) (b Nat))
    (= Nat (+ a b) (+ b a))))
(define a+b=b+a
  (lambda (a b)
    (ind-Nat a
      (lambda (a) (= Nat (+ a b) (+ b a)))
      (symm (n+zero=n b))
      (lambda (a ih)
        (replace (add1-+=+-add1 b a)
          (lambda (k) (= Nat (add1 (+ a b)) k))
          (cong ih (+ 1)))))))
      ; (lambda (a ih)
      ;   (replace (symm ih)
      ;     (lambda (k) (= Nat (add1 k) (+ b (add1 a))))
      ;     (add1-+=+-add1 b a))))))


; (define a+b=b+a
;   (lambda (a b)
;     (ind-Nat a
;       (lambda (a) (= Nat (+ a b) (+ b a)))
;       (symm (n+zero=n b))
;       (lambda (a ih)
;         (trans (cong ih (+ 1)) (add1-+=+-add1 b a))))))

; Exercise 4
(claim *
  (-> Nat Nat Nat))
(define *
  (lambda (m n)
    (iter-Nat m
      zero
      (lambda (m-1) (+ n m-1)))))

(claim plus-assoc
 (Pi ((x Nat) (y Nat) (z Nat))
   (= Nat (+ x (+ y z)) (+ (+ x y) z))))
(define plus-assoc
  (lambda (x y z)
    (ind-Nat x
      (lambda (x) (= Nat (+ x (+ y z)) (+ (+ x y) z)))
      (same (+ y z))
      (lambda (_ ih) 
        (cong ih (+ 1))))))

(claim mul-distrib-right
  (Pi ((x Nat) (y Nat) (z Nat))
    (= Nat (* (+ x y) z) (+ (* x z) (* y z)))))
(define mul-distrib-right
  (lambda (x y z)
    (ind-Nat x
      (lambda (x) (= Nat (* (+ x y) z) (+ (* x z) (* y z))))
      (same (* y z))
      (lambda (x ih) (trans (cong ih (+ z)) (plus-assoc z (* x z) (* y z)))))))

(claim mul-assoc
  (Pi ((x Nat) (y Nat) (z Nat))
    (= Nat (* x (* y z)) (* (* x y) z))))
(define mul-assoc
  (lambda (x y z)
    (ind-Nat x
      (lambda (x) (= Nat (* x (* y z)) (* (* x y) z)))
      (same zero)
      (lambda (x ih) (trans (cong ih (+ (* y z))) (symm (mul-distrib-right y (* x y) z)))))))