#lang pie

(claim +
  (-> Nat Nat
      Nat))
(define +
  (lambda (j n)
    (rec-Nat n
      j
      (lambda (n-1 +n-1)
        (add1 +n-1)))))


(claim elim-Pair
  (Pi ((A U)
       (D U)
       (X U))
    (-> (Pair A D)
        (-> A D
            X)
        X)))

(define elim-Pair
  (lambda (A D X)
    (lambda (p f)
      (f (car p) (cdr p)))))

(claim kar
  (Pi ((C U))
    (-> (Pair C C)
       C)))

(define kar
  (lambda (C)
    (lambda (p)
      (elim-Pair
        C C
        C
        p
        (lambda (a d)
          a)))))

(claim kdr
  (Pi ((C U))
    (-> (Pair C C)
       C)))

(define kdr
  (lambda (C)
    (lambda (p)
      (elim-Pair
        C C
        C
        p
        (lambda (a d)
          d)))))

(claim compose
  (Pi ((A U)
       (B U)
       (C U))
    (-> (-> A B) (-> B C)
        (-> A C))))

(define compose
  (lambda (A B C)
    (lambda (f g)
      (lambda (x)
        (g (f x))))))

(claim add-One
  (-> Nat
      Nat))

(define add-One
  (lambda (n)
    (add1 n)))

; Chapter 5

(claim sum-List
  (-> (List Nat)
      Nat))

(define sum-List
  (lambda (ns)
    (rec-List ns
      0
      (lambda (n _ sum)
        (+ n sum)))))

(claim which-List
  (Pi ((C U)
       (X U))
    (-> (List C) X (-> (List C) X)
        X)))

(define which-List
  (lambda (C X)
    (lambda (cs if-nil f)
      (rec-List cs
        if-nil
        (lambda (_ bs _)
          (f bs))))))

(claim maybe-Last
  (Pi ((C U))
    (-> (List C) C
        C)))

(define maybe-Last
  (lambda (C)
    (lambda (cs if-empty)
      (rec-List cs
        if-empty
        (lambda (c before last)
          (which-List
            C C
            before
            c
            (lambda (_)
              last))))))) 
          
(claim filter-List
  (Pi ((E U))
    (-> (List E) (-> E Nat)
        (List E))))

(define filter-List
  (lambda (E)
    (lambda (es pred)
      (rec-List es
        (the (List E) nil)
        (lambda (current _ so-far)
          (which-Nat (pred current)
            so-far
            (lambda (_)
              (:: current so-far))))))))

(claim dec
  (-> Nat
      Nat))
(define dec
  (lambda (n)
    (which-Nat n
      0
      (lambda (n-1)
        n-1))))

(claim nat-Minus
  (-> Nat Nat
      Nat))
(define nat-Minus
  (lambda (j n)
    (rec-Nat n
      j
      (lambda (n-1 +n-1)
        (dec +n-1)))))

(claim insert-Sorted-Last-Step
  (-> Nat (Pair (List Nat) Nat)
      (List Nat)))
(define insert-Sorted-Last-Step
  (lambda (inserted p)
    (which-Nat (cdr p)
      (:: inserted (car p))
      (lambda (_)
        (car p)))))
      

(claim insert-Sorted
  (-> (List Nat) Nat
       (List Nat)))
(define insert-Sorted
  (lambda (ns a)
    (insert-Sorted-Last-Step a (rec-List ns
      (the (Pair (List Nat) Nat) (cons nil 0))
      (lambda (current _ so-far)
        (which-Nat (cdr so-far)
          (which-Nat (nat-Minus a current)
            (the (Pair (List Nat) Nat) (cons (:: current (car so-far)) 0))
            (lambda (_)
              (cons (:: current (:: a (car so-far))) 1)))
          (lambda (_)
            (cons (:: current (car so-far)) 1)))))
      
      )))
      
(claim insertion-Sort
  (-> (List Nat)
      (List Nat)))
(define insertion-Sort
  (lambda (ns)
    (rec-List ns
      (the (List Nat) nil)
      (lambda (current _ so-far)
        (insert-Sorted so-far current)))))

(check-same (List Nat) (insertion-Sort nil) nil)
(check-same (List Nat) (insertion-Sort (:: 1 nil)) (:: 1 nil))
(check-same (List Nat) (insertion-Sort (:: 1 (:: 2 nil))) (:: 1 (:: 2 nil)))
(check-same (List Nat) (insertion-Sort (:: 2 (:: 1 nil))) (:: 1 (:: 2 nil)))
(check-same (List Nat) (insertion-Sort (:: 1 (:: 2 (:: 3 nil)))) (:: 1 (:: 2 (:: 3 nil))))
(check-same (List Nat) (insertion-Sort (:: 3 (:: 2 (:: 1 nil)))) (:: 1 (:: 2 (:: 3 nil))))
(check-same (List Nat) (insertion-Sort (:: 1 (:: 2 (:: 1 nil)))) (:: 1 (:: 1 (:: 2 nil))))

        
      