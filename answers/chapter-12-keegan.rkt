#lang pie

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

(claim double
  (-> Nat 
    Nat))
(define double
  (lambda (n)
    (iter-Nat n
      0
      (+ 2))))

(claim +double=double+
  (Pi ((m Nat) (n Nat))
    (= Nat (+ (double m) (double n)) (double (+ m n)))))
(define +double=double+
  (lambda (m n)
    (ind-Nat m
      (lambda (m) (= Nat (+ (double m) (double n)) (double (+ m n))))
      (same (double n))
      (lambda (_ ih) 
        (cong ih (+ 2))))))

(claim Even
  (-> Nat U))
(define Even
  (lambda (n)
    (Sigma ((half Nat))
      (= Nat n (double half)))))

; Exercise 1
(claim e+e=e
  (Pi ((m Nat) (n Nat))
    (-> (Even m) (Even n)
      (Even (+ m n)))))
(define e+e=e
  (lambda (m _ em en)
    (cons (+ (car em) (car en)) 
      (trans 
        (trans 
          ; m + n = m + (double n/2) 
          (cong (cdr en) (+ m))
          ; m + (double n/2) = (double m/2) + (double n/2)
          (cong (cdr em) (the (-> Nat Nat) (lambda (m) (+ m (double (car en)))))))
        ; (double m/2) + (double n/2) = double (m/2 + n/2)
        (+double=double+ (car em) (car en))))))

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

(claim Odd
  (-> Nat U))
(define Odd
  (lambda (n)
    (Sigma ((haf Nat))
      (= Nat n (add1 (double haf))))))

(claim o+o=e
  (Pi ((m Nat) (n Nat))
    (-> (Odd m) (Odd n)
      (Even (+ m n)))))
(define o+o=e
  (lambda (m _ om on)
    (cons (add1 (+ (car om) (car on))) 
      (trans
        (trans 
          (trans
            ; m + n = m + add1 (double n/2)
            (cong (cdr on) (+ m))
            ; m + add1 (double n/2) = add1 (m + double n/2)
            (symm (add1-+=+-add1 m (double (car on)))))
          ; add1 (m + double n/2) = add1 (add1 (double m/2 + double n/2))
          (cong (cong (cdr om) (the (-> Nat Nat) (lambda (m) (+ m (double (car on)))))) (+ 1)))
        ; add1 (add1 (double m/2 + double n/2)) = add1 (add1 (double (m/2 + n/2))) 
        (cong (+double=double+ (car om) (car on)) (+ 2))))))