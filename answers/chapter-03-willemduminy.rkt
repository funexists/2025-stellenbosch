#lang pie

; -----------------------------------------------------------------------------
; Exercise 1
; ----------
;
; Define a function called at-least-two? that takes one Nat argument
; and evaluates to an Atom.
; at-least-two? evaluates to 't if the Nat is greater than or equal to 2
; otherwise it evaluates to 'nil.
; Note: The only Nat eliminator you should need in the body of at-least-two?
;       is which-Nat.

; Notes
; -----
; - which-Nat is described on page 48
 
; Answer
; ------
; We observe that at-least-two is 't only for 0 and 1.  
; The approach I take here here is to call which-Nat twice

(claim at-least-two? (-> Nat Atom))
(define at-least-two?
  (λ(n) (which-Nat n
          ; n is the Nat zero
          'f                  
          (λ(n-1)
            (which-Nat n-1
              ; n-1 is the Nat zero 
              'f          
              ; else
              (λ(dim-n-2) 't))))))

(check-same Atom (at-least-two? 0) 'f)
(check-same Atom (at-least-two? 1) 'f)
(check-same Atom (at-least-two? 2) 't)
(check-same Atom (at-least-two? 10) 't)


; -----------------------------------------------------------------------------
; Exercise 2
; ----------
;
; Rewrite the definition of + (in frame 3.27) using the rec-Nat eliminator
; instead of the iter-Nat eliminator.

; Notes
; -----
; - rec-Nat is defined on page 89

; Answer
; ------
; Following the pattern of first defining the step function and then
; the actual function

; How can I identify the step function?
; What about induction:
; If n = 0 then
;   n + b = b ... the base case
; Else let a-n-1 = (n - 1) + b
;   n + b = (n - 1) + (b + 1) 
;         = (n - 1) + b + 1
;         = a-n-1 + 1 ... the step function!

(claim step+ (-> Nat Nat Nat))
(define step+
  (λ(dim-n-1 a-n-1)
    (add1 a-n-1)))

; Returns the sum of two Nats
(claim + (-> Nat Nat Nat))
(define +
  (λ(a b)
    (rec-Nat a
      ; a is zero
      b
      step+)))

(check-same Nat (+ 1 3) 4)
(check-same Nat (+ 0 0) 0)
(check-same Nat (+ 0 2) 2)
(check-same Nat (+ 2 0) 2)

; -----------------------------------------------------------------------------
; Exercise 3
; ----------
;
; Define a function called exp that takes two Nat arguments and evaluates to a
; Nat. exp evaluates to the exponentiation, a^b, of the two passed arguments.
;
; Answer
; ------
; If n = 0
;  a^n = 1 ... base case
; Else let a^(n - 1) = a-n-1
;  a^(n - 1) = a^(n - 1) * a
;      = a-n-1 * a ... step funtion
; This solution needs * function (defined on page 88)
; which needs a + function (ex-2)
;
; Note: this definition has 0^0 = 1,
;       which should strictly be undefined

; The * eliminator
(claim step* (-> Nat Nat Nat Nat))
(define step*
  (λ(j dim-n-1 a-n-1) (+ j a-n-1)))

(claim * (-> Nat Nat Nat))
(define *(λ(n b) (rec-Nat n 0 (step* b)))) 
      
; The ^ eliminator
(claim step^ (-> Nat Nat Nat Nat))
(define step^
  (λ(a dim-n-1 a-n-1)
    (* a-n-1 a)))

(claim ^ (-> Nat Nat Nat))
(define ^ (λ(a n) (rec-Nat n 1 (step^ a))))

(check-same Nat (^ 0 1) 0)
(check-same Nat (^ 0 0) 1)
(check-same Nat (^ 2 4) (^ 4 2))
(check-same Nat (^ 3 2) 9)
(check-same Nat (^ 20 0) 1)    

; -----------------------------------------------------------------------------
; Exercise 4
; ----------
; Define a function called max that takes two Nat arguments and evaluates to a
; Nat. max evaluates to the larger of the two passed arguments.

; Answer
; ------
; Basic idea: define a minus function and use it to get the max
; but minus requires a predecessor function

; pred(n) = if n = 0 then 0 else n - 1
(claim pred (-> Nat Nat))
(define pred (λ(n) (which-Nat n 0 (λ(n-1) n-1))))

(check-same Nat (pred 10) 9)
(check-same Nat (pred 0) 0)

; (- a b) = If (a > b) then (a - b) else zero
(claim - (-> Nat Nat Nat))
; (a - b) = (a - (b - 1)) - 1)
; (a - b) = a-b-1 - 1 
(define -
  (λ(a b)
    (rec-Nat b a
      (λ(b-1 a-b-1) (pred a-b-1)))))  

(check-same Nat (- 4 1) 3)
(check-same Nat (- 7 10) 0)

; (max a b) If (b - a) = 0 then b else a
(claim max (-> Nat Nat Nat))
(define max
  (λ(a b) (which-Nat (- b a) a (λ(dim) b))))

(check-same Nat (max 1 2) 2)
(check-same Nat (max 2 1) 2)
(check-same Nat (max 0 0) 0)
(check-same Nat (max 10 10) 10)


; -----------------------------------------------------------------------------
; Exercise 4
; ----------
; Define a function called gcd that takes two Nat arguments and evaluates to
; a Nat. gcd evaluates to the greatest common divisor of the two
; passed arguments.

; Answer
; ------

; abs-(a b) = |a - b|
(claim abs- (-> Nat Nat Nat))
(define abs-
  (λ(a b) (which-Nat (- a b) (- b a) (λ(dim) (- a b)))))

(check-same Nat (abs- 3 7) 4)
(check-same Nat (abs- 7 3) 4)

; sg from hint paper
(claim sg (-> Nat Nat))
(define sg (λ(n) (which-Nat n 0 (λ(dim) 1))))

; (% a b) is the remainder of a / b when b 
; from hint paper
; %(0,b) = 0 ... base case
; %(a,b) = (rm(a-1,b) + 1) * sg ( |y - (rm(a-1,b) + 1)|)
;          = (rm(a-1,b) + 1) * sg ( abs-(b,(rm(a-1,b) + 1))) ... step
(claim step% (-> Nat Nat Nat Nat))
(define step%
  (λ(b a-1 a-a-1) (* (add1 a-a-1) (sg (abs- b (add1 a-a-1))))))  

(claim % (-> Nat Nat Nat))
(define % (λ(a b) (rec-Nat a 0 (step% b))))

(check-same Nat (% 7 3) 1)
(check-same Nat (% 3 7) 3)
(check-same Nat (% 0 7) 0)
(check-same Nat (% 3 0) 3)

(claim Nat2 U)
(define Nat2 (Pair Nat Nat))

(claim make-p (-> Nat Nat Nat2))
(define make-p (λ(a b) (cons a b)))

; 12, 15
; 15 mod 12, 12
; 3, 12
; n-1: 12 mod 3, 3
; 0, 3
; 3 % 0, 0
; 3, 0
; 0, 3
; 3, 0

; Euclidean algoritm assumes a <= b implies a - b <= 0
; egdc(0 b) = 0 
; egdc(a b) = egdc(b (% a b))
; 
; we implement it to return a pair to faciliate exchange
; answer is the sum of the pair elements
(claim egdc (-> Nat Nat Nat2))
(define egdc
  (λ(a b)
    (rec-Nat a (make-p b a)
      (λ(a-1 a-a-1)
        (make-p (cdr a-a-1) (% (car a-a-1) (cdr a-a-1)))))))

(check-same Nat2 (egdc 5 10) (make-p 5 0))
(check-same Nat2 (egdc 9 12) (make-p 0 3))
(check-same Nat2 (egdc 2 64) (make-p 0 2))
(check-same Nat2 (egdc 2 65) (make-p 1 0))

(claim sum-p (-> Nat2 Nat))
(define sum-p (λ(p) (+ (car p) (cdr p))))

; gdc(a b) uses egdc
(claim gdc (-> Nat Nat Nat))
(define gdc
  (λ(a b) (sum-p (which-Nat (- a b) (egdc a b) (λ(dim) (egdc b a))))))

(check-same Nat (gdc 10 5) 5)
(check-same Nat (gdc 8 12) 4)
(check-same Nat (gdc 12 8) 4)
(check-same Nat (gdc 0 3) 3)
(check-same Nat (gdc 3 0) 3)

; -----------------------------------------------------------------------------
; Exercise 6
; ----------
; Correct the function in frame 73 to not always return 0, but to be factorial


; Answer
; ------
; Multiply and plus comes from ex-3
; The problem is the code is that (fact 0) is 1 not 0.

(claim step-fact
  (-> Nat Nat
    Nat))
(define step-fact
  (lambda (n-1 almost)
    (* (add1 n-1) almost)))
(claim fact
  (-> Nat
    Nat))
(define fact
  (lambda (n)
    (rec-Nat n
      1
      step-fact)))

(check-same Nat (fact 3) 6)
(check-same Nat (fact 0) 1)
