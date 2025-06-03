#lang pie

(claim elim-Pair
  (Pi ((A U) 
       (D U) 
       (X U)) 
   (-> (Pair A D) 
       (-> A D X) 
       X)))
(define elim-Pair
  (lambda (_ _ _ p f)
    (f (car p) (cdr p))))

; Exercise 1
(claim kar 
  (Pi ((A U) (D U)) (-> (Pair A D) A)))
(define kar
  (lambda (A D p)
    (elim-Pair A D A p (lambda (a _) a))))

(claim kdr 
  (Pi ((A U) (D U)) (-> (Pair A D) D)))
(define kdr
  (lambda (A D p)
    (elim-Pair A D D p (lambda (_ d) d))))

; Exercise 2
(claim compose
  (Pi ((A U) (B U) (C U)) 
   (-> (-> A B) 
       (-> B C) 
       (-> A C))))
(define compose
  (lambda (_ _ _ f g)
    (lambda (a) (g (f a)))))