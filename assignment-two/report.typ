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

== Definition 1: Euclidean algorithm
The Euclidean algorithm may be defined recursively over the natural numbers:

$"euc"(a, 0) = a\ "euc"(a, b) = "euc"(b, a mod b)$

== Theroem 1: modulo size
$forall a,b in NN. b != 0 -> b > a mod b$

=== Proof
$a mod b$ is defined as the remainder after fully dividing $a$ by $b$. Let $q$ denote the quotient and $r$ denote the remainder. Thus, $a = q*b+r$. Suppose that $r>=b$. In that case, $exists k. r = k+b$. We may substitute this back into the original equation and rearrange:
$
  a &= q*b+r\
  a &= q*b+b+k\
  a &= (q+1)*b + k
$
We have obtained a new representation of $a$ with a larger quotient, contradicting the assumption that we divided $a$ fully. $arrow.double.r arrow.double.l$

== Theorem 2: termination
$"euc"$ called with any two parameters such that the precondition holds will eventually terminate.

=== Proof
Consider the second argument in the recursive case $"euc"(a,b) = "euc"(b, a mod b)$. By theorem 1, $a mod b < b$. Therefore, the second argument is monotonically decreasing. As it is a natural number, it will eventually reach zero, thus arriving at the base case and terminating the algorithm.

== Theorem 3: correctness
$"euc"(a, b)$ is a common divisor of $a$ and $b$.

=== Proof
The proof is by induction on the number of times $n$ the recursive case was reached in a run of the Euclidean algorithm. By theorem 2, this number always exists.

If $n = 0$, then the recursive case was never reached. The base case of the algorithm is $"euc"(a,0) = a$. $a$ clearly divides both itself and zero. 

Suppose $"euc"$ is correct for $n$ recursive calls, and consider an additional recursive call. That is, $"euc"(b, a mod b) =k$ and $k$ is a common divisor of $b$ and $a mod b$. The new recursive call will be of the shape $"euc"(a, b)$, therefore it is necessary to show that $k$ divides $a$ and $b$. By the induction hypothesis, $k$ divides $b$.

It remains to show that $k$ divides $a$. Denoting $a mod b$ as $r$,
$
  a = q*b+r
$
Then, because $k$ divides $r$ and $b$:
$
  a &= q*(n*k)+(m*k)\
  a &= k*(q*n+m)
$
Thus $k$ divides $a$. $qed$

== Theorem 4: greatest common divisor
If $k$ divides $a$ and $b$, then $k$ divides $"euc"(a, b)$

=== Proof
The proof is again by induction on the number of recursive calls, $n$.

Suppose $n = 0$. Then, only the base case was reached. Thus, $b = 0$ and $"euc"(a,0) = a$. Therefore, it is sufficient to prove that if $k$ divides $a$ and $0$, then $k$ divides $a$. This is trivially true.

Suppose this property holds for $n$ recursive calls, and consider a run of the algorithm with one more recursive call. The additional call will be of the shape $"euc"(a,b) = "euc"(b, a mod b)$. Suppose there is a $k$ which divides $a$ and $b$. Consider $a mod b$ and denote the quotient and remainder as $q$ and $r$ respectively. Because of this:
$
  a &= q*b+r\
  (m*k) &= (q*n*k)+r\
  (m*k)-(q*n*k) &= r\
  k*(m-q*n) &= r
$
Thus, $k$ divides $r$, which denotes $a mod b$. Knowing $k$ divides $b$ and $k$ divides $a mod b$, we may apply the induction hypothesis to conclude that $k$ divides $"euc"(b, a mod b)$ and thus $"euc"(a, b)$. $qed$

= The Idris2 proof

== Unverified implementation
```idris
public export total
modHelp : Nat -> Nat -> Nat -> (b : Nat) -> IsSucc b -> Nat
modHelp k rem a 0 x = absurd x
modHelp k rem 0 (S j) x = rem
modHelp k rem (S i) (S j) x =
  if rem == j
     then modHelp (S k) Z i (S j) ItIsSucc 
     else modHelp k (S rem) i (S j) ItIsSucc

public export total
mod : Nat -> (b : Nat) -> IsSucc b -> Nat
mod = modHelp 0 0

public export partial
euc : Nat -> Nat -> Nat
euc a 0 = a
euc a (S j) = euc (S j) (mod a (S j) ItIsSucc)
```
This is a functional, but unverified implementation of the modulo function and the euclidean algorithm in Idris. The majority of the code is defining `mod` and `modHelp`. The `modHelp` function computes the remainder by tracking it in one of its arguments. Then, on each recursive call, `a` is decremented, and the remainder is incremented unless it is one less than `b`, in which case it is reset to zero. This process continues until `a` is empty, at which point the remainder is returned. We also require `b` to be nonzero, because taking a modulo of zero is not well defined.  

`modHelp` is then wrapped in `mod` to provide a nicer interface without the quotient and remainder accumulator arguments. With this, the euclidean algorithm can be defined as usual, with the addition of a non-zero proof being passed to the mod function.

The first thing we will verify is termination, as the totality checker cannot verify that the current implementation terminates. This is because it verifies totality by checking that the arguments passed to each recursive call are an exact *syntactic* subterm of the current arguments, which is not the case here.

== Termination proof

This is done with well-founded recursion. We would like to argue that the rightmost argument strictly decreases with each call, and thus it must always reach zero.

Although we can intuitively see that $a mod b < b$, we will still need to modify the `modHelp` function to produce this proof alongside the result, so that we may use it in the well-founded implementation to justify making the recursive call.


