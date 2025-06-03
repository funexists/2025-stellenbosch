#lang pie

; Exercise 1
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

(claim foldr
  (Pi ((A U) (B U)) (-> (-> A B B) B (List A) B)))
(define foldr
  (lambda (_ _)
    (lambda (f a xs)
      (rec-List xs
        a
        (lambda (y _ fold-ys) 
          (f y fold-ys))))))

(claim sum-list
  (-> (List Nat) Nat))
(define sum-list
  (foldr Nat Nat + 0))

; Exercise 2
(claim maybe-last 
  (Pi ((E U)) 
    (-> (List E) E E)))
(define maybe-last
  (lambda (_)
    (lambda (xs default)
      (rec-List xs
        default
        (lambda (y ys last-ys)
          (rec-List ys
            y
            (lambda (_ _ _) last-ys)))))))

; Exercise 3
(claim step-filter
  (Pi ((E U)) 
    (-> 
      (-> E Nat) E (List E) (List E) 
      (List E))))
(define step-filter
  (lambda (_)
    (lambda (pred e _ filter-es)
      (which-Nat (pred e)
        filter-es
        (lambda (_) (:: e filter-es))))))

(claim filter-list
  (Pi ((E U)) 
      (-> 
        (-> E Nat) (List E) 
        (List E))))
(define filter-list
  (lambda (E)
    (lambda (pred es)
      (rec-List es
        (the (List E) nil)
        (step-filter E pred)))))

; Exercise 4
(claim dec
  (-> Nat Nat))
(define dec
  (lambda (n) 
    (which-Nat n
      zero
      (lambda (n-1) n-1))))

(claim - 
  (-> Nat Nat Nat))
(define -
  (lambda (n m)
    (iter-Nat m
      n
      dec)))

(claim insert-sorted
  (-> Nat (List Nat) (List Nat)))
(define insert-sorted
  (lambda (x ns)
    (rec-List ns
      (:: x nil)
      (lambda (y ys insert-ys)
        (which-Nat (- x y) 
          (:: x (:: y ys))
          (lambda (_) (:: y insert-ys)))))))

(claim sort-list-Nat
  (-> (List Nat) (List Nat)))
(define sort-list-Nat (foldr Nat (List Nat) insert-sorted nil))
