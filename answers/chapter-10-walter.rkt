#lang pie

(claim +
  (-> Nat Nat Nat))

(define +
  (lambda (x y)
    (rec-Nat x
      y
      (lambda (_ y+x-1)
        (add1 y+x-1)))))

(claim n+zero=n
  (Pi ((n Nat)) (= Nat (+ n 0) n)))

(define n+zero=n
  (lambda (n)
    (ind-Nat n
      (lambda (n) (= Nat (+ n 0) n))
      (same 0)
      (lambda (n-1 ih) (cong ih (+ 1))))))

(claim a+b+1==a+1+b
  (Pi ((a Nat) (b Nat))
    (= Nat
       (+ a (add1 b))
       (+ (add1 a) b))))

(claim mot-a+b+1==a+1+b
  (Pi ((a Nat) (b Nat))
    U))

(define mot-a+b+1==a+1+b
  (lambda (b a)
    (= Nat
      (+ a (add1 b))
       (+ (add1 a) b))))

(claim base-a+b+1==a+1+b
  (Pi ((b Nat))
    (= Nat
       (+ zero (add1 b))
       (+ (add1 zero) b))))

(define base-a+b+1==a+1+b
  (lambda (b)
    (same (add1 b))))

(claim step-a+b+1==a+1+b
  (Pi ((b Nat) (a-1 Nat))
    (-> (= Nat
          (+ a-1 (add1 b))
          (+ (add1 a-1) b))
        (= Nat
          (+ (add1 a-1) (add1 b))
          (+ (add1 (add1 a-1)) b)))))

(define step-a+b+1==a+1+b
  (lambda (b a)
    (lambda (a-1+b+1==a-1+1+b)
      (cong a-1+b+1==a-1+1+b (+ 1)))))

(define a+b+1==a+1+b
  (lambda (a b)
    (ind-Nat a
      (mot-a+b+1==a+1+b b)
      (base-a+b+1==a+1+b b)
      (step-a+b+1==a+1+b b))))

(claim <=
       (-> Nat Nat
           U))

(define <=
  (λ (a b)
    (Σ ([k Nat])
       (= Nat (+ k a) b))))

(claim 2<=3
  (<= 2 3))

(define 2<=3
  (cons 1
  (same 3))
)

(claim 3<=4
  (= Nat 3 3))

(define 3<=4
  (cdr 2<=3)
)

(claim zero<=n
 (Pi ((n Nat)) (<= 0 n)))

(define zero<=n
  (lambda (n)
   (cons n (n+zero=n n))))

(claim add1a<=b->a<=b
  (Pi ((a Nat) (b Nat))
    (-> (<= (add1 a) b) (<= a b))))

(define add1a<=b->a<=b
  (lambda (a b add1a<=b)
    (ind-Nat a
      (lambda (n) (<= n b))
      (zero<=n b)
      (lambda (n-1 ih) TODO))))



(claim <=-simplify
       (Π ([a Nat]
           [b Nat]
           [n Nat])
          (-> (<= (+ n a) b)
              (<= a b))))


(define <=-simplify
  (lambda (a b n)
    (ind-Nat n
      (lambda (n)
        (->
          (<= (+ n a) b)
          (<= a b)))
      (lambda (zero+a<=b)
        zero+a<=b)
      (lambda (n-1 ih)
       ; ih : (-> (<= (+ n-1 a) b) (<= a b)))
       ; want : (-> (<= (+ (add1 n-1) a) b) (<= a b)))
        (lambda (n+a<=b)
          TODO))
          
    )
  )
)
        