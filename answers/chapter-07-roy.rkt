#lang pie
(claim +
  (-> Nat Nat
      Nat))
(define +
  (lambda (j n)
    (iter-Nat n
      j
      (lambda (+n-1)
        (add1 +n-1)))))

(claim mot-zip
  (-> U U Nat
      U))
(define mot-zip
  (lambda (A B n)
    (-> (Vec A n) (Vec B n)
        (Vec (Pair A B) n))))

(claim base-zip
  (Pi ((A U)
       (B U))
    (-> (Vec A 0) (Vec B 0)
        (Vec (Pair A B) 0))))
(define base-zip
  (lambda (A B)
    (lambda (as bs)
      vecnil)))

(claim step-zip
  (Pi ((A U)
       (B U)
       (k-1 Nat))
    (-> (mot-zip A B k-1)
        (mot-zip A B (add1 k-1)))))
(define step-zip
  (lambda (A B k)
    (lambda (zip-k-1)
      (lambda (as bs)
        (vec:: (cons (head as) (head bs)) (zip-k-1 (tail as) (tail bs)))))))

(claim zip
  (Pi ((A U)
       (B U)
       (n Nat))
    (-> (Vec A n) (Vec B n)
        (Vec (Pair A B) n))))
(define zip
  (lambda (A B n)
    (ind-Nat n
      (mot-zip A B)
      (base-zip A B)
      (step-zip A B))))

(check-same (Vec (Pair Atom Nat) 0) (zip Atom Nat 0 vecnil vecnil) vecnil)
(check-same (Vec (Pair Atom Nat) 1)
  (zip Atom Nat 1 (vec:: 'a vecnil) (vec:: 1 vecnil))
  (vec:: (cons 'a 1) vecnil))
(check-same (Vec (Pair Atom Nat) 2)
  (zip Atom Nat 2 (vec:: 'a (vec:: 'b vecnil)) (vec:: 1 (vec:: 46 vecnil)))
  (vec:: (cons 'a 1) (vec:: (cons 'b 46) vecnil)))

(claim mot-append
  (-> U Nat Nat
      U))
(define mot-append
  (lambda (E n m)
    (-> (Vec E m) (Vec E n)
        (Vec E (+ n m)))))

(claim base-append
  (Pi ((E U)
       (n Nat))
    (-> (Vec E 0) (Vec E n)
        (Vec E n))))
(define base-append
  (lambda (E n)
    (lambda (_ bs)
      bs)))

(claim step-append
  (Pi ((E U)
       (n Nat)
       (k-1 Nat))
    (-> (mot-append E n k-1)
        (mot-append E n (add1 k-1)))))
(define step-append
  (lambda (E n k)
    (lambda (append-k-1)
      (lambda (as bs)
        (vec:: (head as) (append-k-1 (tail as) bs))))))

(claim append
  (Pi ((E U)
       (m Nat)
       (n Nat))
    (-> (Vec E m) (Vec E n)
        (Vec E (+ n m)))))
(define append
  (lambda (E m n)
    (ind-Nat m
      (mot-append E n)
      (base-append E n)
      (step-append E n))))

(check-same (Vec Atom 0) (append Atom 0 0 vecnil vecnil) vecnil)
(check-same (Vec Atom 1)
  (append Atom 0 1 vecnil (vec:: 'a vecnil))
  (vec:: 'a vecnil))
(check-same (Vec Atom 1)
  (append Atom 1 0 (vec:: 'a vecnil) vecnil)
  (vec:: 'a vecnil))
(check-same (Vec Atom 2)
  (append Atom 1 1 (vec:: 'a vecnil) (vec:: 'b vecnil))
  (vec:: 'a (vec:: 'b vecnil)))

(claim mot-drop-last-k
  (-> U Nat Nat
      U))
(define mot-drop-last-k
  (lambda (E k n-k)
    (-> (Vec E (+ k n-k))
        (Vec E n-k))))
  
(claim base-drop-last-k
  (Pi ((E U)
       (k Nat))
    (-> (Vec E k)
        (Vec E 0))))
(define base-drop-last-k
  (lambda (E k)
    (lambda (_)
      vecnil)))

(claim step-drop-last-k
  (Pi ((E U)
       (k Nat)
       (j-k-1 Nat))
    (-> (mot-drop-last-k E k j-k-1)
        (mot-drop-last-k E k (add1 j-k-1)))))
(define step-drop-last-k
  (lambda (E k j-k-1)
    (lambda (drop-last-k-j-k-1)
      (lambda (es)
        (vec:: (head es) (drop-last-k-j-k-1 (tail es)))))))

(claim drop-last-k
  (Pi ((E U)
       (k Nat)
       (n-k Nat))
    (-> (Vec E (+ k n-k))
        (Vec E n-k))))
(define drop-last-k
  (lambda (E k n-k)
    (ind-Nat n-k
      (mot-drop-last-k E k)
      (base-drop-last-k E k)
      (step-drop-last-k E k))))

(check-same (Vec Atom 0) (drop-last-k Atom 0 0 vecnil) vecnil)
(check-same (Vec Atom 1)
  (drop-last-k Atom 0 1 (vec:: 'a vecnil))
  (vec:: 'a vecnil))
(check-same (Vec Atom 0)
  (drop-last-k Atom 1 0 (vec:: 'a vecnil))
  vecnil)
(check-same (Vec Atom 1)
  (drop-last-k Atom 1 1 (vec:: 'a (vec:: 'b vecnil)))
  (vec:: 'a vecnil))
(check-same (Vec Atom 0)
  (drop-last-k Atom 2 0 (vec:: 'a (vec:: 'b vecnil)))
  vecnil)
(check-same (Vec Atom 2)
  (drop-last-k Atom 2 2 (vec:: 'a (vec:: 'b (vec:: 'c (vec:: 'd vecnil)))))
  (vec:: 'a (vec:: 'b vecnil)))
(check-same (Vec Atom 1)
  (drop-last-k Atom 4 0 (vec:: 'a (vec:: 'b (vec:: 'c vecnil))))
  vecnil)