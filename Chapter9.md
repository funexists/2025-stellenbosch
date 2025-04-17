# Chapter 9 Exercises

Chapter 9's `replace` can be quite hard to grasp.
Previous reading groups have also struggled to understand, see our [discussions here](https://github.com/awalterschulze/the-little-typer-exercises/files/9706444/Gmail.-.Session6.-.2019-02-19_.Summary.pdf).
[Andrew Helwer](https://github.com/ahelwer) has written up a blog post as a [preamble to Chapter 9](https://ahelwer.ca/post/2022-10-13-little-typer-ch9/), that we would recommend reading before reading Chapter 9.

## Exercise 1

Define a function called `same-cons` that states and proves that
if you `cons` the same value to the front of two equal Lists then
the resulting Lists are also equal,
using `replace`, because this can also be done with cong,
but we are trying to practice chapter 9's `replace`.

```pie
(claim same-cons
  (Pi ((t U) (x t) (as (List t)) (bs (List t)))
    (-> (= (List t) as bs)
        (= (List t) (:: x as) (:: x bs)))))
```

## Exercise 2

Define a function called `same-lists` that states and proves that
if two values, `e1` and `e2`, are equal and two lists, `l1` and `l2` are
equal then the two lists, `(:: e1 l1)` and `(:: e2 l2)` are also equal.

```pie
(claim same-lists
  (Pi ((t U) (e1 t) (e2 t) (l1 (List t)) (l2 (List t)))
    (-> (= (List t) l1 l2) (= t e1 e2)
        (= (List t) (:: e1 l1) (:: e2 l2)))))
```

## Exercise 3

Define a function called `plus-comm` that states and proves that
`+` is commutative

```pie
(claim plus-comm
 (Pi ((n Nat) (m Nat))
   (= Nat (+ n m) (+ m n))))
```

Bonus: Write the solution using the [trans](https://docs.racket-lang.org/pie/index.html#%28def._%28%28lib._pie%2Fmain..rkt%29._trans%29%29) elimiator instead of the `replace` eliminator.

## Exercise 4

Implement [trans](https://docs.racket-lang.org/pie/index.html#%28def._%28%28lib._pie%2Fmain..rkt%29._trans%29%29) using replace:

```pie
(claim mytrans (Pi ((t U) (x t) (y t) (z t)) (-> (= t x y) (= t y z) (= t x z))))
```

## Exercise 5

Implement symm using replace:

```pie
(claim mysymm (Pi ((t U) (x t) (y t)) (-> (= t x y) (= t y x))))
```

## Exercise 6 (Advanced)

Define a function called `mul-assoc` that states and proves that `*` is associative.

```
(claim mul-assoc
  (Pi ((x Nat) (y Nat) (z Nat))
    (= Nat (* x (* y z)) (* (* x y) z))))
```

<details>
<summary>Hint</summary>
You need to use the right distributive law of multiplication over addition.

```
(claim mul-distrib-right
  (Pi ((x Nat) (y Nat) (z Nat))
    (= Nat (* (+ x y) z) (+ (* x z) (* y z)))))
```

<details><summary>Hint hint</summary>

To prove `mul-distrib-right` you need to use `plus-assoc` from the chapter 8 exercises.

</details>
</details>