
#lang pie
;-------------------------------------------------------------------------------
; From previous chapters

(claim length (Pi ((E U)) (-> (List E) Nat)))
(define length
  (λ(_E) (λ(a) (rec-List a zero (λ(_e _t a-length) (add1 a-length))))))

(claim step+ (-> Nat Nat Nat))
(define step+ (λ(_n-1 +n-1) (add1 +n-1)))
(claim + (-> Nat Nat Nat))
(define + (λ(a b) (rec-Nat a b step+)))

(claim append (Pi((E U)) (-> (List E) (List E) (List E))))
(claim step-append (Pi((E U)) (-> E (List E) (List E) (List E))))

(define step-append
  (λ(_E)
    (λ(h _t a-t) (:: h a-t))))
(define append (λ(E) (λ(a b) (rec-List a b (step-append E)))))

; k + (n + m) = (k + n) + m
(claim plus-assoc
  (Pi ((n Nat) (m Nat) (k Nat))
    (= Nat (+ k (+ n m)) (+ (+ k n) m))))
(define plus-assoc
  (λ(n m k)
    (ind-Nat k
      ; proposition:  k + (n + m) =  (k + n) + m
      (λ(k) (= Nat (+ k (+ n m)) (+ (+ k n) m)))
      ; 0 + (n + m) = (0 + n) + m
      (same (+ n m))
      ;        k+1 + (n + m) =     (k+1 + n) + m
      ; => 1 + (k + (n + m)) = 1 + (k + n) + m
      (λ(_k-1 fk-1) (cong fk-1 (+ 1)))
      )))

(claim filter-list (Pi((E U)) (-> (-> E Nat) (List E) (List E))))
(claim step-filter (Pi((E U)) (-> (-> E Nat) E (List E) (List E) (List E))))
(define step-filter
  (λ(_E)
    (λ(pred e _rest a-filter)
      (which-Nat (pred e)
        a-filter
        (λ(_n) (:: e a-filter))))))
(define filter-list
  (λ(E)
    (λ(pred a) (rec-List a (the (List E) nil) (step-filter E pred)))))


(claim predecessor (-> Nat Nat))
(define predecessor (λ(n) (which-Nat n 0 (λ(n-1) n-1))))
(claim - (-> Nat Nat Nat))
(define - (λ(a b) (rec-Nat b a (λ(_b-1 a-b-1) (predecessor a-b-1)))))
;-------------------------------------------------------------------------------
; From chapter 10

(the (Sigma ((x Atom)) (= Atom x x))
  (cons 'one
    (same 'one)))

; there exists an l
(Sigma ((l Nat)) (Vec Atom l))
; for every l
(Pi((l Nat)) (Vec Atom l))

; for every E and l we can convert a list to a Vec
(Pi((E U) (l Nat)) (-> (List E) (Vec E l)))

; Possible statements to map list to vec
; For every E there exists an l such that we can convert a list to a vec
; (Pi((E U)) (Sigma ((l Nat)) (-> (List E) (Vec E l))))
; There exists an l such that for any E we can convert a list to a vec
; (Sigma ((l Nat)) (Pi((E U))  (-> (List E) (Vec E l))))
; For every E map the list to a vector with some l as length
; (Pi((E U)) (-> (List E) (Sigma ((l Nat)) (Vec E l))))

; produce a vec of length l that contains the same element e
(claim replicate (Pi ((E U) (l Nat)) (-> E (Vec E l))))

(define replicate
  (λ(E l e)
    (ind-Nat l
      ; motive
      (λ(n) (Vec E n))
      ; base
      vecnil
      (λ(_l-1 a-l-1)
        (vec:: e a-l-1))
      )
    )
  )

(length Nat nil)

; for every list of E map it to a vector of the same length
(claim list->vec
  (Pi((E U) (lst (List E))) (Vec E (length E lst))))

(define list->vec
  (λ(E lst)
    ; we have dependent type; so we use ind
    (ind-List
      ; target -- induction on lst
      lst
      ; motive -- what we want to get
      (λ(lst) (Vec E (length E lst)))
      ; base -- empty list
      vecnil
      ; step -- h, tail-1 and answer of tail-1 -> answer of tail
      (λ(h _t list-vec-t)
        (vec:: h list-vec-t)
        )
      )
    )
  )

;-------------------------------------------------------------------------------
; Exercise 10.1
; -------------
; Define a function called list-length-append-dist that states and proves that
; if you append two lists, l1 and l2, and then the length of the result is
; equal to the sum of the lengths of l1 and l2.

(claim list-length-append-dist
  (Pi((E U) (l1 (List E)) (l2 (List E)))
    (= Nat (length E (append E l1 l2))
       (+ (length E l1) (length E l2)))))
(define list-length-append-dist
  (λ(E l1 l2)
    (ind-List l1
      (λ(lst)
        (= Nat (length E (append E lst l2)) (+ (length E lst) (length E l2)))
        )
      (same (length E l2))
      (λ(_h _lst-1 a-lst-1)
        (cong a-lst-1 (+ 1))
        )
      )
    )
  )

;-------------------------------------------------------------------------------
; Exercise 10.2
; -------------
; In the following exercises we'll use the function called <= that takes two
; Nat arguments a, b and evaluates to a type representing the proposition that a
; is less than or equal to b.

; Σ k k + a = b
(claim <= (-> Nat Nat U))
; for all a b there is some k such that a+k = b
(define <= (λ (a b) (Σ ([k Nat]) (= Nat (+ k a) b))))

; Exercise 10.2.1
; ---------------
; Using <=, state and prove that 1 is less than or equal to 2.

(claim 1<=2 (<= 1 2))
(define 1<=2 (cons 1 (same 2)))

;-------------------------------------------------------------------------------
; Exercise 10.2.2
; ---------------
; Define a function called <=-simplify to state and prove that for all Nats a,
; b, n we have that n+a <= b implies a <= b
;
; NB: You may need to use plus-assoc that was proved in Exercise 8.3.

; n + a <= b -> a <= b
(claim <=-simplify
  (∏((a Nat) (b Nat) (n Nat))
    (-> (<= (+ n a) b)
      (<= a b)
      )
    )
  )

; Conceptual
; A: Σ k: k + (n + a) = b .. From n + a <= b (given)
; B: k + (n + a) = (k + n) + a .. Associativity of +
; C: Σ k: (k + n) + a = b .. Apply B to A
; D: Σ k1: k1 + a = b .. From C with k1 = k + n
; E: a <= b
(define <=-simplify
  (λ(a _b n n+a<=b)
    ; Σ k1 k1 + a = b; k1 = k + n
    (cons
      (+ (car n+a<=b) n)
      ; (k + n) + a = b
      (trans
        ; (k + n) + a = k + (n + a)
        (symm (plus-assoc n a (car n+a<=b)))
        ; k + (n + a) = b
        (cdr n+a<=b)
        )
      )
    )
  )

;-------------------------------------------------------------------------------
; Exercise 10.2.3
; Define a function called <=-trans that states and proves that <= is transitive.

(claim <=-trans
  (Π ([a Nat]
      [b Nat]
      [c Nat])
    (-> (<= a b)
        (<= b c)
      (<= a c))))

; Conceptual
; A: Σ k1: k1 + a = b  .. Given
; B: Σ k2: k2 + b = c  .. Given
; C: Σ k2: k2 + (k1 + a) = c .. A into B
; D: k1 + a <= c
; E: a <= c  .. <=-simplified
(define <=-trans
  (λ(a _b c a<=b b<=c)
    (<=-simplify a c (car a<=b)
      ; k1 + a <= c
      (cons (car b<=c)
        ; k2 + (k1 + a) = c
        (replace
          ; b = k1 + a
          (symm (cdr a<=b))
          (λ(k) (= Nat (+ (car b<=c) k) c))
          ; k2 + b = c
          (cdr b<=c)
          )
        )
      )
    )
  )

;-------------------------------------------------------------------------------
; Exercise 10.3
; -------------
; Define a function called length-filter-list that states and proves that
; filtering a list (in the sense of filter-list from Exercise 5.3)
; evaluates to a list no longer than the original list.

; length of filtered list <= length of list

(claim length-filter-list
  (Pi ((E U)
       (l (List E))
       (p (-> E Nat)))
    (<= (length E (filter-list E p l))
        (length E l))))

(claim match-count
  (∏((E U))
    (-> (-> E Nat) (List E) Nat))
  )
(define match-count
  (λ(E p l) (length E (filter-list E p l)))
  )


(claim mot-lfl (∏((E U) (_p (-> E Nat))) (-> (List E) U)))
(define mot-lfl
  (λ(E p l)
    (<=
      (match-count E p l)
      (length E l)
      )
    )
  )

(claim base-lfl (∏((E U) (p (-> E Nat))) (mot-lfl E p nil)))
(define base-lfl
  (λ(_E _p)
    (cons zero (same zero))
    )
  )

(claim step-lfl
  (∏((E U) (p (-> E Nat)) (h E) (lst (List E)))
    (->
      (mot-lfl E p lst)
      (mot-lfl E p (:: h lst))
      )
    )
  )

(claim mot-prop:1
  (∏ ((E U))
    (-> (-> E Nat) E U)
    )
  )

(define mot-prop:1
  (λ(E p h) (<= (match-count E p (:: h nil)) 1))
  )

(claim prop:1
  (∏((E U) (p (-> E Nat)) (h E) ) (mot-prop:1 E p h))
  )

(define prop:1
  (λ(E p h)
    TODO
    ; (cons (match-count E p (:: h nil)) (same 1))
    )
  )

(claim mot-prop:2
  (∏ ((E U)) (-> (-> E Nat) E (List E) U))
  )
(define mot-prop:2
  (λ(E p h l)
    (= Nat
      (+ (match-count E p (:: h nil))
        (match-count E p l)
        )
      (match-count E p (:: h l))
      )
    )
  )

(claim prop:2
  (∏((E U) (p (-> E Nat)) (h E) (l (List E)))
    (mot-prop:2 E p h l)
    )
  )
(define prop:2
  (λ(E p h l)
    TODO
    ;    (ind-List l
    ;      (λ(lst) (mot-prop:1 E p h l))
    ;      (same (match-count E p (:: h nil)))
    ;      TODO
    ;      )
    )
  )




; Conceptual
; A: |filter list| <= |list|  .. Given
; B: 1 + |filter hlist| <= 1 + |list|  .. From A
; C: |filter h::list| <= 1 + |filter list|  ..?
; D: |filter h::list| <= 1 + |list| .. Transitive C and B
; E: |filter h::list| <= |h::list| .. Rewrite E
; Conceptual 2
; A: Σ k1: k1 + |filter l| = |l|  .. Given
; B: Σ k2: k2 + |filter l| = k1 + |filter h::l|  .. ?
; C:
(define step-lfl
  (λ(E p h l sfl<=sl)
    ; |filter p h::l|  <= 1 + |l|
    TODO
    ;    (cons (add1 (car sfl<=sl))

    ;     (cong (cdr sfl<=sl) (+ 1))
    ;     )
    )
  )

(define length-filter-list
  (λ(E l p)
    (ind-List l
      ; motive
      (λ(lst) (mot-lfl E p lst))
      (base-lfl E p)
      (step-lfl E p)
      )
    )
  )

; |filter h::list| <= 1 + |filter list|  ..?
; I think I need an observation of |filter list|
; We know
;   if p h then |filter h::list| = 1 + |filter list|
;   else |filter h::list| = |filter list|
; But in Pie - how to I prove cases?
; The only possibility seems to be a which-Nat
; Do we have a type that depends on (p h)?
(claim sfhl<=1+sfl
  (∏ ((E U) (p (-> E Nat)) (h E) (l (List E)))
    (<= (length E (filter-list E p (:: h l)))
        (add1 (length E (filter-list E p l)))
        )
    )
  )
(define sfhl<=1+sfl
  (λ(E p h l)
    TODO
    )
  )


