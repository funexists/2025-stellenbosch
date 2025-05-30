#lang pie

(claim + (-> Nat Nat Nat))
(define +
  (lambda (n m)
    (iter-Nat n m (lambda (n) (add1 n))) ))

(claim double (-> Nat Nat))
(define double
  (lambda (n)
    (iter-Nat n 0 (+ 2)) ))

(claim Even (-> Nat U))
(define Even
  (lambda (n)
    (Sigma ((half Nat)) (= Nat n (double half))) ))

(claim double-distrib (Pi ((n Nat) (m Nat)) (= Nat (double (+ n m)) (+ (double n) (double m)))))
(define double-distrib
  (lambda (n m)
    (ind-Nat n
      (lambda (n) (= Nat (double (+ n m)) (+ (double n) (double m))))
      (same (double m))
      (lambda (n prev) ;; prev says double(n + m) = double(n) + double(m)
        (cong prev (+ 2)) ) )))

(claim sumOfTwoEvensIsEven (Pi ((n Nat) (m Nat)) (-> (Even n) (Even m) (Even (+ n m)))))
(define sumOfTwoEvensIsEven
  (lambda (n m n-even m-even)
    (cons (+ (car n-even) (car m-even))
      ; Now we want n+m = double (half-n + half-m)
      (replace (symm (cdr n-even)) ; double half-n = n
        (lambda (x) (= Nat (+ x m) (double (+ (car n-even) (car m-even)))))
        (replace (symm (cdr m-even)) ; double half-m = m
          (lambda (y) (= Nat (+ (double (car n-even)) y) (double (+ (car n-even) (car m-even)))))
          (symm (double-distrib (car n-even) (car m-even))) ))) )) ; (double half-n) + (double half-m) = double (half-n + half-m)

(claim Odd (-> Nat U))
(define Odd
  (lambda (n)
    (Sigma ((haf Nat)) (= Nat n (add1 (double haf)))) ))

(claim 1+n+m=n+1+m (Pi ((n Nat) (m Nat)) (= Nat (+ (add1 n) m) (+ n (add1 m)))))
(define 1+n+m=n+1+m
  (lambda (n m)
    (ind-Nat n
      (lambda (n) (= Nat (+ (add1 n) m) (+ n (add1 m))))
      (same (add1 m))
      (lambda (n prev) (cong prev (+ 1))))))

(claim sumOfTwoOddsIsEven (Pi ((n Nat) (m Nat)) (-> (Odd n) (Odd m) (Even (+ n m)))))
(define sumOfTwoOddsIsEven
  (lambda (n m n-odd m-odd)
    (cons (add1 (+ (car n-odd) (car m-odd)))
      ; Now we want n+m = 2 + double (haf-n + haf-m)
      (replace (symm (cdr n-odd)) ; 1 + double haf-n = n
        (lambda (x) (= Nat (+ x m) (+ 2 (double (+ (car n-odd) (car m-odd))))))
        (replace (symm (cdr m-odd)) ; 1 + double haf-m = m
          (lambda (y) (= Nat (+ (add1 (double (car n-odd))) y) (+ 2 (double (+ (car n-odd) (car m-odd))))))
          (trans (cong (symm (1+n+m=n+1+m (double (car n-odd)) (double (car m-odd)))) (+ 1)) ; 1 + (double(haf-n) + 1+double(haf-m)) = 1 + (1+double(haf-n) + double(haf-m))
            (cong (symm (double-distrib (car n-odd) (car m-odd))) (+ 2)) ))) ))) ; 2 + (double(haf-n) + double(haf-m)) = 2 + double(haf-n + haf-m)

; --------------------------------------------

(claim nOrSuccnIsEven (Pi ((n Nat)) (Either (Even n) (Even (add1 n)))))
(define nOrSuccnIsEven
  (lambda (n)
    (ind-Nat n
      (lambda (n) (Either (Even n) (Even (add1 n))))
      (left (cons 0 (same 0)))
      (lambda (n prev)
        (ind-Either prev
          (lambda (e) (Either (Even (add1 n)) (Even (+ 2 n))))
          (lambda (lt) (right (cons (add1 (car lt)) (cong (cdr lt) (+ 2)) )))
          (lambda (rt) (left rt))
          ))) ))

; -------------------------------------------- [From last week]

(claim plus-assoc-type (Pi ((n Nat) (m Nat) (k Nat)) U))
(define plus-assoc-type (lambda (n m k) (= Nat (+ n (+ m k)) (+ (+ n m) k))))
(claim plus-assoc (Pi ((n Nat) (m Nat) (k Nat)) (plus-assoc-type n m k)))
(define plus-assoc
  (lambda (n m k)
    (ind-Nat n
      (lambda (n) (plus-assoc-type n m k))
      (same (+ m k))
      (lambda (n prev) ; prev asserts that (n + (m + k) = (n + m) + k
        (cong prev (the (-> Nat Nat) (lambda (x) (add1 x)))) ))))

(claim length (Pi ((t U)) (-> (List t) Nat)))
(define length
  (lambda (t xs)
    (rec-List xs
      0
      (lambda (x xs n) (add1 n)) )))

(claim append (Pi ((t U)) (-> (List t) (List t) (List t))))
(define append
  (lambda (t xs ys)
    (rec-List xs
      ys
      (lambda (x xs prev) (:: x prev)) )))

(claim list-length-append-dist-type (Pi ((t U) (xs (List t)) (ys (List t))) U))
(define list-length-append-dist-type (lambda (t xs ys) (= Nat (length t (append t xs ys)) (+ (length t xs) (length t ys)))))

(claim list-length-append-dist (Pi ((t U) (xs (List t)) (ys (List t))) (list-length-append-dist-type t xs ys)))
(define list-length-append-dist
  (lambda (t xs ys)
    (ind-List xs
      (lambda (xs) (list-length-append-dist-type t xs ys))
      (same (length t ys))
      (lambda (x xs prev) (cong prev (+ 1))) )))

(claim <= (-> Nat Nat U))
(define <=
  (λ (a b)
    (Σ ([k Nat]) ; [] = ()?
       (= Nat (+ k a) b))))

(claim filter-add (Pi ((t U)) (-> Nat t (List t))))
(define filter-add
  (lambda (t b x)
    (which-Nat b (the (List t) nil) (lambda (_) (:: x nil))) ))

(claim filter-list (Pi ((t U)) (-> (-> t Nat) (List t) (List t))))
(define filter-list
  (lambda (t p xs)
    (rec-List xs
      (the (List t) nil)
      (lambda (x xs prev)
        (append t (filter-add t (p x) x) prev) ) )))

(claim length-filter-add (Pi ((t U) (b Nat) (x t)) (<= (length t (filter-add t b x)) 1)))
(define length-filter-add
  (lambda (t b x)
    (ind-Nat b
      (lambda (b) (<= (length t (filter-add t b x)) 1))
      (cons 1 (same 1))
      (lambda (_ _) (cons 0 (same 1))) )))

(claim length-filter-list
  (Pi ((E U)
       (l (List E))
       (p (-> E Nat)))
       (<= (length E (filter-list E p l))
           (length E l))))

(define length-filter-list
  (lambda (E l p)
    (ind-List l
      (lambda (l) (<= (length E (filter-list E p l)) (length E l)))
      (cons 0 (same 0))
      (lambda (x xs prev) ; prev says \exists k. k + (length (filter p xs)) = (length xs)
        ; Also m + length (filter-add t (p x) x) prev) = 1
        ; And (length (append (filter-add (p x) x) xs)) = (length (filter-add (p x) x)) + (length xs)
        ; Want k + m + (length (append t (filter-add (p x) x) xs)) = 1 + length xs
          ((the (-> (<= (length E (filter-add E (p x) x)) 1) (<= (length E (filter-list E p (:: x xs))) (add1 (length E xs)))) (lambda (add<=1)
             (cons (+ (car prev) (car add<=1))
               (trans
                 (symm (plus-assoc (car prev) (car add<=1) (length E (append E (filter-add E (p x) x) (filter-list E p xs)))))
                 (trans
                   (trans
                     (cong
                       (trans
                         (trans
                           ; m + (length (append (filter-add (p x) x) (filter p xs))) = m + (length (filter-add (p x) x)) + (length (filter p xs))
                           (cong (list-length-append-dist E (filter-add E (p x) x) (filter-list E p xs)) (+ (car add<=1)))
                           (plus-assoc (car add<=1) (length E (filter-add E (p x) x)) (length E (filter-list E p xs))) ) ; assoc
                         (cong (cdr add<=1) (the (-> Nat Nat) (lambda (x) (+ x (length E (filter-list E p xs)))))) )
                       ; At this point we have: m + (length (append (filter-add (p x) x) (filter p xs))) = 1 + (length (filter p xs))
                       (+ (car prev)))
                     (symm (1+n+m=n+1+m (car prev) (length E (filter-list E p xs)))))
                   ; Now we have: k + m+(length (append (filter-add (p x) x) (filter p xs))) = 1+ k+(length (filter p xs))
                   (cong (cdr prev) (+ 1))) )
                 ; This gives: k+m+(length (append (filter-add (p x) x) (filter p xs))) = 1+(length xs)
               ) ))
           (length-filter-add E (p x) x) ) ; value of add<=1
          ))))
;;; (length (append (filter-add (p x) x) (filter p xs))) = (length (filter-add (p x) x)) + (length (filter p xs))             [list-length-append-dist]
;;; m + (length (append (filter-add (p x) x) (filter p xs))) = m + ((length (filter-add (p x) x)) + (length (filter p xs)))   [cong using (car add<=1)]
;;; m + (length (append (filter-add (p x) x) (filter p xs))) = (m + (length (filter-add (p x) x))) + (length (filter p xs))   [assoc]
;;; m + (length (append (filter-add (p x) x) (filter p xs))) = 1 + (length (filter p xs))                                     [using (cdr add<=1)]
;;; k + m+(length (append (filter-add (p x) x) (filter p xs))) = k + 1+(length (filter p xs))                                 [cong using (car prev)]
;;; k + m+(length (append (filter-add (p x) x) (filter p xs))) = 1+ k+(length (filter p xs))                                  [using 1+n+m = n+1+m]
;;; k + m+(length (append (filter-add (p x) x) (filter p xs))) = 1+(length xs)                                                [using (cdr prev)]
;;; k+m + (length (append (filter-add (p x) x) (filter p xs))) = 1+(length xs)                                                [assoc]


; ----------------- [My definition for filter-list agrees with the other one]

(claim filter-list2 (Pi ((t U)) (-> (-> t Nat) (List t) (List t))))
(define filter-list2
  (lambda (t p xs)
    (rec-List xs
      (the (List t) nil)
      (lambda (x xs prev)
        (which-Nat (p x)
          prev
          (lambda (_) (:: x prev)) )) )))

(claim filter-add-same (Pi ((t U) (b Nat) (x t) (xs (List t))) (= (List t) (append t (filter-add t b x) xs) (which-Nat b xs (lambda (_) (:: x xs))))))
(define filter-add-same
  (lambda (t b x xs)
    (ind-Nat b
      (lambda (b) (= (List t) (append t (filter-add t b x) xs) (which-Nat b xs (lambda (_) (:: x xs)))))
      (same xs)
      (lambda (_ _) (same (:: x xs)))
    )))

(claim filter-lists-same (Pi ((t U) (p (-> t Nat)) (xs (List t))) (= (List t) (filter-list t p xs) (filter-list2 t p xs))))
(define filter-lists-same
  (lambda (t p xs)
    (ind-List xs
      (lambda (xs) (= (List t) (filter-list t p xs) (filter-list2 t p xs)))
      (same nil)
      (lambda (x xs prev)
        (replace prev
          (lambda (z) (= (List t) (append t (filter-add t (p x) x) (filter-list t p xs)) (which-Nat (p x) z (lambda (_) (:: x z)))))
          (filter-add-same t (p x) x (filter-list t p xs)) )) )))
