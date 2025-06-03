#lang pie

; Exercise 1
(claim mot-zip
  (-> U U Nat U))
(define mot-zip
  (lambda (A B n)
  (->
    (Vec A n)
    (Vec B n)
    (Vec (Pair A B) n))))

(claim base-zip
  (Pi ((A U) (B U))
    (-> 
      (Vec A zero) 
      (Vec B zero) 
      (Vec (Pair A B) zero))))
(define base-zip
  (lambda (_ _ _ _) vecnil))

(claim step-zip
  (Pi ((A U) (B U) (n Nat))
    (-> 
      (mot-zip A B n)
      (mot-zip A B (add1 n)))))
(define step-zip
  (lambda (_ _ _ zip-n) 
    (lambda (v1 v2)
      (vec:: 
        (cons (head v1) (head v2)) 
        (zip-n (tail v1) (tail v2))))))

(claim zip
  (Pi ((A U) (B U) (n Nat)) 
      (-> (Vec A n) (Vec B n) (Vec (Pair A B) n))))
(define zip
  (lambda (A B n)
    (ind-Nat n
      (mot-zip A B)
      (base-zip A B)
      (step-zip A B))))

(check-same (Vec (Pair Nat Atom) 2)
    (vec:: (cons 1 'a) (vec:: (cons 2 'b) vecnil))
    (zip Nat Atom 2
        (vec:: 1 (vec:: 2 vecnil))
        (vec:: 'a (vec:: 'b vecnil))))

; Exercise 2
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

(claim mot-append
  (-> U Nat Nat U))
(define mot-append
  (lambda (E n m)
    (-> (Vec E m) (Vec E n) (Vec E (+ m n)))))

(claim base-append
  (Pi ((E U) (n Nat))
    (mot-append E n zero)))
(define base-append
  (lambda (_ _) 
    (lambda (_ ns) ns)))

(claim step-append
  (Pi ((E U) (n Nat) (m Nat))
    (-> 
      (mot-append E n m)
      (mot-append E n (add1 m)))))
(define step-append
  (lambda (_ _ _ step-m) 
    (lambda (ms ns) (vec:: (head ms) (step-m (tail ms) ns)))))

(claim append
  (Pi ((E U) (m Nat) (n Nat))
    (-> (Vec E m) (Vec E n) (Vec E (+ m n)))))
(define append
  (lambda (E m n)
    (ind-Nat m
      (mot-append E n)
      (base-append E n)
      (step-append E n))))

(check-same (Vec Nat 3)
    (vec:: 1 (vec:: 2 (vec:: 3 vecnil)))
    (append Nat 1 2 (vec:: 1 vecnil) (vec:: 2 (vec:: 3 vecnil))))

(check-same (Vec Nat 3)
    (vec:: 3 (vec:: 2 (vec:: 1 vecnil)))
    (append Nat 2 1 (vec:: 3 (vec:: 2 vecnil)) (vec:: 1 vecnil)))

; Exercise 3
(claim mot-drop-last-k
  (-> U Nat Nat U))
(define mot-drop-last-k
  (lambda (E k n)
    (-> (Vec E (+ n k)) (Vec E n))))

(claim base-drop-last-k
  (Pi ((E U) (k Nat))
    (mot-drop-last-k E k zero)))
(define base-drop-last-k
  (lambda (_ _ _) vecnil))

(claim step-drop-last-k
  (Pi ((E U) (k Nat) (n Nat))
    (-> (mot-drop-last-k E k n)
        (mot-drop-last-k E k (add1 n)))))
(define step-drop-last-k
  (lambda (_ _ _ step-n) 
    (lambda (nks) (vec:: (head nks) (step-n (tail nks))))))

(claim drop-last-k
  (Pi ((E U) (n Nat) (k Nat))
    (-> (Vec E (+ n k)) (Vec E n))))
(define drop-last-k
  (lambda (E n k)
    (ind-Nat n
      (mot-drop-last-k E k)
      (base-drop-last-k E k)
      (step-drop-last-k E k))))

(check-same (Vec Atom 3)
    (vec:: 'a (vec:: 'b (vec:: 'c vecnil)))
    (drop-last-k Atom 3 2
        (vec:: 'a (vec:: 'b (vec:: 'c (vec:: 'd (vec:: 'e vecnil)))))))

(check-same (Vec Atom 0)
    vecnil
    (drop-last-k Atom 0 5
        (vec:: 'a (vec:: 'b (vec:: 'c (vec:: 'd (vec:: 'e vecnil)))))))

(check-same (Vec Atom 5)
    (vec:: 'a (vec:: 'b (vec:: 'c (vec:: 'd (vec:: 'e vecnil)))))
    (drop-last-k Atom 5 0
        (vec:: 'a (vec:: 'b (vec:: 'c (vec:: 'd (vec:: 'e vecnil)))))))