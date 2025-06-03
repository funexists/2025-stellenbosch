#lang pie

(claim +
  (-> Nat Nat
      Nat))
(define +
  (lambda (n j)
    (iter-Nat n
      j
      (lambda (+n-1)
        (add1 +n-1)))))

(claim n+0=n
  (Pi ((n Nat))
    (= Nat (+ n 0) n)))
(define n+0=n
  (lambda (n)
    (ind-Nat n
      (lambda (k)
        (= Nat (+ k 0) k))
      (same 0)
      (lambda (n-1 n-1+0=n-1)
        (cong n-1+0=n-1 (+ 1))))))


;Exercise 1
(claim same-cons
  (Pi ((t U) (x t) (as (List t)) (bs (List t)))
    (-> (= (List t) as bs)
        (= (List t) (:: x as) (:: x bs)))))

(define same-cons
  (lambda (t x as bs as=bs)
    (replace as=bs
      (lambda (ys)
        (= (List t)
          (:: x as)
          (:: x ys)))
      (same (:: x as)))))

;Exercise 2
(claim same-lists
  (Pi ((t U) (e1 t) (e2 t) (l1 (List t)) (l2 (List t)))
    (-> (= (List t) l1 l2) (= t e1 e2)
        (= (List t) (:: e1 l1) (:: e2 l2)))))

(define same-lists
  (lambda (t e1 e2 l1 l2 l1=l2 e1=e2)
    (replace e1=e2
      (lambda (e)
        (= (List t)
          (:: e1 l1)
          (:: e l2)))
      (same-cons t e1 l1 l2 l1=l2))))
          
;Execise 3
(claim add1+=+add1
  (Pi ((n Nat)
       (j Nat))
    (= Nat (add1 (+ n j)) (+ n (add1 j)))))

(define add1+=+add1
  (lambda (n j)
    (ind-Nat n
      (lambda (k)
        (= Nat (add1 (+ k j)) (+ k (add1 j))))
      (same (add1 j))
      (lambda (n-1)
        (lambda (add1+=+add1n-1)
          (cong add1+=+add1n-1 (+ 1)))))))

(claim mot-plus-com
  (-> Nat Nat U))
(define mot-plus-com
  (lambda (m k)
    (= Nat (+ k m) (+ m k))))

(claim mot-step-plus-com
  (-> Nat Nat Nat U))
(define mot-step-plus-com
  (lambda (m n-1 k)
    (= Nat (+ (add1 n-1) m) k)))

(claim step-plus-com
  (Pi ((m Nat) (n Nat))
    (-> (mot-plus-com m n)
        (mot-plus-com m (add1 n)))))
(define step-plus-com
  (lambda (m n-1)
    (lambda (plus-com-n-1)
      (replace (add1+=+add1 m n-1)
        (mot-step-plus-com m n-1)
        (cong plus-com-n-1 (+ 1)))))) 
        
  

(claim plus-comm
 (Pi ((n Nat) (m Nat))
   (= Nat (+ n m) (+ m n))))
(define plus-comm
  (lambda (n m)
    (ind-Nat n
      (mot-plus-com m)
      (replace (symm (n+0=n m))
        (lambda (j)
          (= Nat (+ 0 m) j))
        (same m))   
      (step-plus-com m))))


