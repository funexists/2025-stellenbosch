#lang pie

(claim +
  (-> Nat Nat Nat))
(define +
  (lambda (x y)
    (rec-Nat x
      y
      (lambda (_ y+x-1)
        (add1 y+x-1)))))

(claim length
  (Pi ((E U))
    (-> (List E) Nat)))
(define length
  (lambda (_)
    (lambda (list)
      (rec-List list
        0
        (lambda (_ _ n-1)
          (add1 n-1))))))

(claim append
  (Pi ((E U))
    (-> (List E) (List E) (List E))))
(define append
  (lambda (_)
    (lambda (l1 l2)
      (rec-List l1
        l2
        (lambda (e _ es:l2)
          (:: e es:l2))))))

; Exercise 1
(claim list-length-append-dist
  (Pi ((E U) (l1 (List E)) (l2 (List E)))
    (= Nat (length E (append E l1 l2)) (+ (length E l1) (length E l2)))))
(define list-length-append-dist
  (lambda (E l1 l2)
    (ind-List l1
      (lambda (l1) (= Nat (length E (append E l1 l2)) (+ (length E l1) (length E l2))))
      (same (length E l2))
      (lambda (_ _ ih) 
        (cong ih (+ 1))))))

; Exercise 2
(claim <=
  (-> Nat Nat
      U))
(define <=
  (λ (a b)
    (Σ ((k Nat))
       (= Nat (+ k a) b))))

; Exercise 2.1
(claim 1<=2
  (<= 1 2))
(define 1<=2
  (cons 1 (same 2)))

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

(claim a+1<=b->a<=b
  (Pi ((a Nat) (b Nat))
    (-> (<= (+ 1 a) b)
        (<= a b))))
(define a+1<=b->a<=b
  (lambda (a _b a+1<=b)
    (cons 
      (add1 (car a+1<=b)) 
      (trans 
        (add1-+=+-add1 (car a+1<=b) a) 
        (cdr a+1<=b)))))

; Exercise 2.2
(claim <=-simplify
  (Pi ((a Nat) (b Nat) (n Nat))
    (-> (<= (+ n a) b)
      (<= a b))))
(define <=-simplify
  (lambda (a b n)
    (ind-Nat n
      (lambda (n) (-> (<= (+ n a) b) (<= a b)))
      (lambda (0+a<=b) 0+a<=b)
      (lambda (n ih n+1+a<=b) 
        (ih (a+1<=b->a<=b (+ n a) b n+1+a<=b))))))

(claim plus-assoc
 (Pi ((n Nat) (m Nat) (k Nat))
   (= Nat (+ n (+ m k)) (+ (+ n m) k))))
(define plus-assoc
  (lambda (n m k)
    (ind-Nat n
      (lambda (n) (= Nat (+ n (+ m k)) (+ (+ n m) k)))
      (same (+ m k))
      (lambda (_ ih) 
        (cong ih (+ 1))))))

; Exercise 2.3
(claim <=-trans
  (Pi ((a Nat) (b Nat) (c Nat))
    (-> (<= a b)
        (<= b c)
        (<= a c))))
(define <=-trans
  (lambda (a _b c a<=b b<=c) 
    (cons 
      (+ (car b<=c) (car a<=b)) 
      (trans 
        (symm (plus-assoc (car b<=c) (car a<=b) a)) 
        (replace (symm (cdr a<=b))
          (lambda (b) (= Nat (+ (car b<=c) b) c))
          (cdr b<=c))))))

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

(claim length-filter-cons
  (Pi ((E U) (e E) (l (List E)) (pred (-> E Nat)))
    (<= (length E (filter-list E pred (:: e l))) (add1 (length E (filter-list E pred l))))))
(define length-filter-cons
  (lambda (E e l pred)
    (ind-Nat (pred e)
      (lambda (n) 
        (<= 
          (length E (which-Nat n (filter-list E pred l) (lambda (_) (:: e (filter-list E pred l))))) 
          (add1 (length E (filter-list E pred l)))))
      (cons 1 (same (+ 1 (length E (filter-list E pred l))))) 
      (lambda (_ _) 
        (cons 0 (same (add1 (length E (filter-list E pred l)))))))))

(claim <=->add1<=
  (Pi ((x Nat)
       (y Nat))
    (->
      (<= x y)
      (<= (add1 x) (add1 y)))))
(define <=->add1<=
  (lambda (x y)
    (lambda (x<=y)
      (cons
        (car x<=y)
        (replace (add1-+=+-add1 (car x<=y) x)
          (lambda (x) (= Nat x (add1 y)))
          (cong (cdr x<=y) (+ 1)))))))

; Exercise 3
(claim length-filter-list
  (Pi ((E U) (l (List E)) (pred (-> E Nat)))
    (<= (length E (filter-list E pred l)) (length E l))))
(define length-filter-list
  (lambda (E l pred)
    (ind-List l
      (lambda (l) (<= (length E (filter-list E pred l)) (length E l)))
      (cons 0 (same 0))
      (lambda (e es ih)
        (<=-trans
          (length E (filter-list E pred (:: e es))) 
          (add1 (length E (filter-list E pred es))) 
          (add1 (length E es))
          (length-filter-cons E e es pred)
          (<=->add1<= (length E (filter-list E pred es)) (length E es) ih))))))