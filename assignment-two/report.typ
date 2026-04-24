#set document(
  title: [Implementing and verifying the Euclidean algorithm in Idris2 and Haskell],
)

#title()
#heading(outlined: false, depth: 2)[(My ID here) - ENGR340 Assignment Two]
#outline()

#pagebreak()

= Objectives
In this report, we aim to implement the Euclidean algorithm in both Haskell and Idris, then verify some properties about each implementation using their respective language's tools. Following this, there will be a discussion comparing the techniques, verification methods, and programming languages used, with references to this exercise for examples and evidence.

= Mathematical specification

== Definition 1: Divisibility
For $a, b in NN$, $a$ _divides_ $b$ if $exists k in NN [k times a = b]$. Symbolically, we may write _"$a$ divides $b$"_ as $a divides b$.

== Definition 2: Common divisor
$d$ is a _common divisor_ of $a$ and $b$ if $d | a and d | b$.

== Definition 3: Euclidean algorithm
We define $gcd : (NN times NN) -> NN$ as
  - $gcd(a, 0) = a$
  - $gcd(a, b) = gcd(b, a mod b)$

== Lemma 1
$d divides a and d divides b -> d divides (a mod b)$

== Proof of Lemma 1
TODO

== Theorem 1 : Correctness
$gcd(a, b) | a and gcd(a,b) divides b$

== Proof of Theorem 1
TODO

== Theorem 2 : Greatest divisor
$d | a and d | b -> d | gcd(a, b)$

== Proof of Theorem 2
TODO

== Theorem 3 : Symmetry
$gcd(a,b) = gcd(b,a)$

== Proof of Theorem 3
TODO

== Theorem 4 : Idempotence
$gcd(a, a) = a$

== Proof of Theorem 4
TODO
