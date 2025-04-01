# Chapter 3 Exercises

## Exercise 1

Define a function called `at-least-two?` that takes one Nat argument and evaluates to an Atom.
`at-least-two?` evaluates to `'t` if the Nat is greater than or equal to 2 otherwise it evaluates to `'nil`.

Note: The only Nat eliminator you should need in the body of `at-least-two?` is `which-Nat`.

## Exercise 2

Rewrite the definition of `+` (in frame 3.27) using the `rec-Nat` eliminator instead of the `iter-Nat` eliminator.

```pie
 (define step-+
   (lambda (sum-n-1)
     (add1 sum-n-1)))

 (define +
   (lambda (n j)
     (iter-Nat n
       j
       step-+)))
```

## Exercise 3

Define a function called `exp` that takes two Nat arguments and evaluates to a Nat. `exp` evaluates to the exponentiation, `a^b`, of the two passed arguments.

## Exercise 4

Define a function called `max` that takes two Nat arguments and evaluates to a Nat. `max` evaluates to the larger of the two passed arguments.

## Exercise 5

Define a function called `gcd` that takes two Nat arguments and evaluates to a
Nat. `gcd` evaluates to the greatest common divisor of the two passed arguments.

<details>
<summary>Hint</summary>
<br>
You might find this resource helpful: https://www.andrew.cmu.edu/user/kk3n/recursionclass/chap2.pdf.
</details>

## Exercise 6

Correct the function in frame 73 to not always return 0, but to be factorial.

```pie
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
      0
      step-fact)))
```
