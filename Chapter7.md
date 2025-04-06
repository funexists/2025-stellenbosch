# Chapter 7 Exercises

If you get stuck, reread pages 152 - 157, especially frame 49-52.

## Exercise 1

Define a function called zip that takes an argument of type `(Vec A n)` and a
second argument of type `(Vec B n)` and evaluates to a vlue of type `(Vec (Pair A B) n)`,
the result of zipping the first and second arguments.

## Exercise 2

Define a function called `append` that takes an argument of type `(Vec E m)` and an
argument of type `(Vec E n)` and evaluates to a value of type `(Vec (+ m n))`, the
result of appending the elements of the second argument to the end of the first.

<details>
<summary>Hint 1</summary>
<br>
The order of `m` and `n` in the `+` is very important, since we do not have ways to show that `(+ m n)` = `(+ n m)`, yet.
</details>

<details>
<summary>Hint 2</summary>
<br>
The way `+` is defined is also very important, since we do not have ways to show that different implementations of `+` are the same, yet.
</details>

## Exercise 3

Define a function called `drop-last-k` that takes an argument of type `(Vec E ?)` and
evaluates to a value of type `(Vec E ?)`, the result of dropping the last `k` elements
from the first argument.
NB: The type of the function should guarantee that we can't drop more elements
than there are in the first argument.
