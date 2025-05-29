#lang pie
;-------------------------------------------------------------------------------
; From previous chapters

(claim step+ (-> Nat Nat Nat))
(define step+ (λ(_n-1 +n-1) (add1 +n-1)))
(claim + (-> Nat Nat Nat))
(define + (λ(a b) (rec-Nat a b step+)))

(claim length (Pi ((E U)) (-> (List E) Nat)))
(define length
  (λ(_E) (λ(a) (rec-List a zero (λ(_e _t a-length) (add1 a-length))))))

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

(claim append (Pi((E U)) (-> (List E) (List E) (List E))))
(claim step-append (Pi((E U)) (-> E (List E) (List E) (List E))))

(define step-append
  (λ(_E)
    (λ(h _t a-t) (:: h a-t))))
(define append (λ(E) (λ(a b) (rec-List a b (step-append E)))))

; `snoc a e` makes a new list from `a` where `e` is placed on the back of `a`.
(claim snoc (Pi((E U)) (-> (List E) E (List E))))
(define snoc
  (λ(E)
    (λ(a e) (append E a (:: e nil)))))


(claim VecPair (-> U U Nat U))
(define VecPair (λ(A B n) (Vec (Pair A B) n)))

(claim mot-zip (-> U U Nat U))
(define mot-zip (λ(A B n) (-> (Vec A n) (Vec B n) (VecPair A B n))))

(claim base-zip
  (Pi ((A U) (B U))
    (mot-zip A B zero)))
(define base-zip
  (λ(_A _B)
    (λ(_va _vb) vecnil)))

(claim step-zip
  (Pi ((A U) (B U) (n-1 Nat))
    (-> (mot-zip A B n-1) (mot-zip A B (add1 n-1)))))

(define step-zip
  (λ(_A _B _n-1 fn-1)
    (λ(va vb)
      (vec::
        (cons (head va) (head vb))
        (fn-1 (tail va) (tail vb))))))

(claim zip
  (Pi((A U) (B U)(n Nat))
    (-> (Vec A n) (Vec B n) (VecPair A B n))))

(define zip
  (λ(A B n)
    (ind-Nat n
      (mot-zip A B)
      (base-zip A B)
      (step-zip A B))))

;-------------------------------------------------------------------------------
; From chapter 11

(claim vec-append
  (∏ ((E U) (l Nat) (j Nat))
    (-> (Vec E l) (Vec E j) (Vec E (+ l j)))
    )
  )

(define vec-append
  (λ(E l j vec-l vec-j)
    (ind-Vec
      ; target
      ; induction on first argument;
      ; why: for + in motive to work?
      l vec-l
      ; motive
      (λ(k _vec-k) (Vec E (+ k j)))
      ; base
      vec-j
      ; step
      (λ(_n-1 h _t vec-append-t)
        ; notice the order we start
        ; we start at the end of the
        ; target list
        (vec:: h vec-append-t)
        )
      )
    )
  )

(claim vec->list
  (∏ ((E U) (l Nat))
    (-> (Vec E l) (List E))))
(define vec->list
  (λ(E l vec-l)
    (ind-Vec
      l vec-l
      (λ(_k _vec_k) (List E))
      nil
      (λ(_n-1 h _t vec-list-t)
        (:: h vec-list-t)
        )
      )
    )
  )

(claim treat-s
  (∏ ((a (List Atom)) (b (List Atom)))
    (-> (= (List Atom) a b)
      (= (List Atom) (:: 'plat a) (:: 'plat b))
      )
    )
  )
(define treat-s
  (λ(_a _b a=b)
    (cong a=b
      (the (-> (List Atom) (List Atom))
        (λ(s)
          (:: 'plat s)
          )
        )
      )
    )
  )

(claim eq-lst->eq-len
  (∏ ((a (List Atom)) (b (List Atom)))
    (->
      (= (List Atom) a b)
      (= Nat (length Atom a) (length Atom b))
      )
    )
  )
(define eq-lst->eq-len
  (λ(_a _b a=b)
    (cong a=b (length Atom))
    )
  )


(claim list->vec->list=
  (∏ ((E U) (lst (List E)))
    (= (List E)
       lst
       (vec->list E (length E lst) (list->vec E lst))
       )
    )
  )
(define list->vec->list=
  (λ(E lst)
    (ind-List
      lst
      (λ(k)
        (= (List E) k (vec->list E (length E k) (list->vec E k))))
      (same nil)
      (λ(h _t lvl=-t)
        (cong lvl=-t
          (the (-> (List E) (List E))
            (λ(s)
              (:: h s)
              )
            )
          )
        )
      )
    )
  )


;-------------------------------------------------------------------------------
; Exercise 11.1
; -------------
; Use ind-Vec to define a function called unzip that unzips a vector of  pairs
; into a pair of vectors

(claim unzip
  (Π ([A U]
      [B U]
      [n Nat])
    (-> (Vec (Pair A B) n)
      (Pair (Vec A n) (Vec B n)))))
(claim mot-unzip
  (Π ([A U] [B U] [n Nat])
    (-> (Vec (Pair A B) n) U)
    )
  )
(define mot-unzip
  (λ(A B n _)
    (Pair (Vec A n) (Vec B n)))
  )

(define unzip
  (λ(A B n vec-n)
    (ind-Vec n vec-n
      (λ(k vec-k) (mot-unzip A B k vec-k))
      (cons vecnil vecnil)
      (λ(n-1 h t unzip-t)
        (cons
          (vec:: (car h) (car unzip-t))
          (vec:: (cdr h) (cdr unzip-t))
          )
        )
      )
    )
  )

(claim vec-nats (Vec Nat 3))
(define vec-nats (vec:: 10 (vec:: 20 (vec:: 30 vecnil))))

(check-same (Pair (Vec Nat 3) (Vec Nat 3))
  (cons vec-nats vec-nats)
  (unzip Nat Nat 3
    (zip Nat Nat 3 vec-nats vec-nats)
    )
  )

