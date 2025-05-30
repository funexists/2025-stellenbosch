#lang pie

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

(claim + (-> Nat Nat Nat))
(define +
  (lambda (n m)
    (iter-Nat n m (lambda (n) (add1 n))) ))

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

(claim 1<=2 (<= 1 2))
(define 1<=2 (cons 1 (same 2)))

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

(claim <=-simplify (Pi ((a Nat) (b Nat) (n Nat)) (-> (<= (+ n a) b) (<= a b))))
(define <=-simplify
  (lambda (a b n given) ; \exists k. k+(n+a) = b
    (cons (+ (car given) n)
      (trans (symm (plus-assoc (car given) n a)) (cdr given))) ))


(claim <=-trans
  (Π ([a Nat]
      [b Nat]
      [c Nat])
    (-> (<= a b)
        (<= b c)
        (<= a c))))
(define <=-trans
  (lambda (a b c a<=b b<=c) ; \exists k. k+a = b ; \exists m. m+b = c
    (cons (+ (car b<=c) (car a<=b))
      (trans (symm (plus-assoc (car b<=c) (car a<=b) a)) ; (m+k) + a = m + (k+a)
          (trans (cong (cdr a<=b) (+ (car b<=c))) ; m + (k+a) = m + b
            (cdr b<=c) )) )))



(claim unzip
      (Π ([A U]
          [B U]
          [n Nat])
         (-> (Vec (Pair A B) n)
             (Pair (Vec A n) (Vec B n)))))

(define unzip
  (lambda (A B n pairs)
    (ind-Vec n pairs
      (lambda (n vec) (Pair (Vec A n) (Vec B n)))
      (cons vecnil vecnil)
      (lambda (n p ps prev)
        (cons (vec:: (car p) (car prev)) (vec:: (cdr p) (cdr prev))) ) )))



;(claim filter-list (Pi ((t U)) (-> (-> t Nat) (List t) (List t))))
;(define filter-list
;  (lambda (t p xs)
;    (rec-List xs
;      (the (List t) nil)
;      (lambda (x xs prev)
;        (which-Nat (p x)
;          prev
;          (lambda (_) (:: x prev)) )) )))

;; NOTE: The inclination is to do the which-Nat on (p x) and then decide on the proof after that,
;;       but we can't covey to PIE that (p x) is really 0 (or whatever) in each branch since that
;;       information isn't fed into the type system. So we need to use ind-Nat
;(define length-filter-list
;  (lambda (E l p)
;    (ind-List l
;      (lambda (l) (<= (length E (filter-list E p l)) (length E l)))
;      (cons 0 (same 0))
;      (lambda (x xs prev)
;        (which-Nat (p x)
;          (the (<= (length E (filter-list E p (:: x xs))) (add1 (length E xs))) TODO ) ; the type (<= (length E (filter-list E p xs)) (add1 (length E xs))) doesn't work
;          (lambda (_) (the (<= (length E (filter-list E p (:: x xs))) (add1 (length E xs))) TODO)) )) ))) ; the type (<= (add1 (length E (filter-list E p xs))) (add1 (length E xs))) doesn't work

(claim filter-add (Pi ((t U)) (-> Nat t (List t))))
(define filter-add
  (lambda (t b x)
    (which-Nat b (the (List t) nil) (lambda (_) (:: x nil))) ))

;; A more modular definition
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
      (lambda (n prev) (cons 0 (same 1))) )))

(claim 1+n+m=n+1+m (Pi ((n Nat) (m Nat)) (= Nat (+ (add1 n) m) (+ n (add1 m)))))
(define 1+n+m=n+1+m
  (lambda (n m)
    (ind-Nat n
      (lambda (n) (= Nat (+ (add1 n) m) (+ n (add1 m))))
      (same (add1 m))
      (lambda (n prev) (cong prev (+ 1))))))

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
