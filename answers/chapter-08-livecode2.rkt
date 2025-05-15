#lang pie

(claim +
  (-> Nat Nat Nat))

(define +
  (lambda (x y)
    (rec-Nat y
      x
      (lambda (y-1 almost)
        (add1 almost)))))

(claim plus-assoc
 (Pi ((x Nat) (y Nat) (zzz Nat))
   (= Nat (+ x (+ y zzz)) (+ (+ x y) zzz))))

(claim mot-plus-assoc
  (-> Nat Nat Nat U))

(define mot-plus-assoc
  (lambda (x y zzz)
    (= Nat (+ x (+ y zzz)) (+ (+ x y) zzz))))

(claim base-plus-assoc
  (Pi ((x Nat) (y Nat))
  (mot-plus-assoc x y 0)))

(define base-plus-assoc
  ; (= Nat (+ x (+ y 0)) (+ (+ x y) 0)
  (lambda (x y)
    (same (+ x y))))

(claim step-plus-assoc
  (Pi ((x Nat) (y Nat) (zz Nat))
    (->
     (= Nat (+ x (+ y zz)) (+ (+ x y) zz))
     (= Nat (add1 (+ x (+ y zz))) (add1 (+ (+ x y) zz)))
     )))

; (= Nat (+ x (+ y (add1 zz))) (+ (+ x y) (add1 zz)))
; (= Nat (+ x (add1 (+ y zz))) (add1 (+ (+ x y) zz)))
; (= Nat (add1 (+ x (+ y zz))) (add1 (+ (+ x y) zz)))

(define step-plus-assoc
  (lambda (x y zz ih)
  ;  (cong ih (the (-> Nat Nat) (lambda (x) (+ x 1))))))
    (cong ih (+ 1))))


(define plus-assoc
  (lambda (x y zzz)
    (ind-Nat zzz
      (mot-plus-assoc x y)
      (base-plus-assoc x y)
      (step-plus-assoc x y))))
