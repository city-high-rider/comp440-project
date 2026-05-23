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
We would like to show that the recursive calls of euc are performed on arguments whose size strictly decreases. Since each recursive call replaces b with a mod b, and a mod b < b, repeated recursion must eventually terminate.

Although we can intuitively see that $a mod b < b$, we will still need to modify the `modHelp` function to produce this proof alongside the result, so that we may use it in the well-founded implementation to justify making the recursive call.

```idris
public export total
neqBump : Not (a = b) -> Not (S a = S b)
neqBump f Refl = f Refl

public export total
neqUnbump : Not (S a = S b) -> Not (a = b)
neqUnbump f Refl = f Refl

public export total
lteStrengthen : {a, b : _} -> LTE a b -> Not (a = b) -> LT a b
lteStrengthen {a = 0} {b = 0} LTEZero f = absurd (f Refl)
lteStrengthen {a = 0} {b = (S k)} LTEZero f = LTESucc LTEZero
lteStrengthen {a = (S left)} {b = (S right)} (LTESucc x) f = 
  let
    fRec = neqUnbump f
  in
  LTESucc (lteStrengthen x fRec)

public export total
modHelp : (r : Nat) -> Nat -> (b : Nat) -> IsSucc b -> (LT r b) -> (rem : Nat ** LT rem b)
modHelp r 0 b bnz rltb = (r ** rltb)
modHelp r (S k) 0 bnz rltb = absurd bnz
modHelp r (S k) (S j) bnz rltb =
  case decEq r j of
    (Yes prf) => modHelp 0 k (S j) bnz (LTESucc LTEZero)
    (No contra) =>
      let
        cbump = neqBump contra
        rltbPrime = lteStrengthen rltb cbump
      in
      modHelp (S r) k (S j) bnz rltbPrime
  

public export total
mod : Nat -> (b : Nat) -> IsSucc b -> (rem : Nat ** LT rem b)
mod a 0 bnz = absurd bnz
mod a (S k) bnz = modHelp 0 a (S k) bnz (LTESucc LTEZero)
```

In the previous implementation, we repeatedly decremented the dividend and incremented the remainder, resetting the remainder to zero if it became equal to the modulus. Mechanically, this implementation does the same thing, but it also carries a proof that the current remainder is strictly less than the modulus, augmenting it with each recursive call.

Recall that the modulus is non-zero; that is, it is the successor of some number `S j`. Thus, in the case where we reset the remainder back to zero, it is easy to construct a proof that `Z < S j`. On the other hand, incrementing the remainder requires more steps to justify. Firstly, we have the current proof in scope: `r < (S j)`, which desugars to `S r <= S j`. We also have access to a proof that `r != j`. Thus it follows that `S r != S j`. We may then combine `S r <= S j` with `S r != S j` to conclude that `S r < S j`, hence verifying that the incremented remainder is still strictly smaller than the modulus. These intermediate steps are handled by the `neqBump` and `lteStrengthen` lemmas respectively.

Finally, the `mod` wrapper is also updated to return a proof that the remainder is strictly smaller than the modulus. With this, we can move to rewriting the `euc` implementation using `Control.WellFounded.sizeRec`. Here is its signature:
```
total
sizeRec : Sized a =>
  ((x : a) -> ((y : a) -> Smaller y x -> b) -> b) ->
  a -> b
```
Let us focus on the first argument, namely: `(x : a) -> ((y : a) -> Smaller y x -> b) -> b`. This is a helper function which accepts an `x` and a "recursive oracle," which permits us to call the helper function recursively for any `y`, provided we can prove that `y` is smaller than `x`. The remaining type signature of `sizeRec` indicates that if we can implement such a helper, we may pass in any input and compute the result in a total manner.

Of course, we must first define a "size" for our inputs. Since we are arguing that the second argument passed to `euc` is strictly decreasing between recursive calls, it makes sense to define it like this:
```
public export total
data EucArgPair = MkEPair Nat Nat

Sized EucArgPair where
  size (MkEPair a b) = b
```
Now we have all the pieces to write the helper:
```
public export total
eucHelper : (x : EucArgPair) -> ((y : EucArgPair) -> Smaller y x -> Nat) -> Nat
eucHelper (MkEPair a 0) rec = a
eucHelper (MkEPair a (S k)) rec =
  let
    (nextRight ** isLess) = mod a (S k) ItIsSucc
  in
  rec (MkEPair (S k) nextRight) isLess
```
If the second argument is zero, there is no need to invoke the "recursive oracle," and we simply return `a`, as usual. Otherwise, the second argument must be a successor `S k`. We then compute `a mod (S k)`, obtaining both the remainder and a proof that the remainder is smaller than the modulus. These are unpacked as `nextRight` and `isLess` respectively. With this proof, we can then call the function recursively with the next argument pair, `(S k), nextRight`.

Finally, we can use the helper along with `sizeRec` to get a total `euc` function:
```
public export total
euc : Nat -> Nat -> Nat
euc a b = sizeRec (eucHelper) (MkEPair a b)
```

== Verifying arithmetic properties of the `mod` function
To work on the remaining two theorems, we will need to prove that our `mod` function not only produces a remainder `r` which is properly smaller than the modulus, but also a quotient `q` such that `a = b*q+r`, where `a` and `b` are the dividend and modulus respectively. Here is the updated function:

```idris
public export total
modHelp :
  (q : Nat) ->
  (r : Nat) ->
  (remaining : Nat) ->
  (b : Nat) ->
  IsSucc b ->
  LT r b ->
  (q' : Nat ** r' : Nat ** ( LT r' b, q' * b + r' = q * b + r + remaining))
modHelp q r 0 b bnz rltb = (q ** r ** (rltb, rewrite (plusZeroRightNeutral (plus (mult q b) r)) in Refl))
modHelp q r (S k) 0 bnz rltb = absurd bnz
modHelp q r (S k) (S j) bnz rltb =
  case decEq r j of
       (Yes Refl) =>
          let
            (qrec ** rrec ** (rrltb, prf)) = modHelp (S q) 0 k (S j) bnz (LTESucc LTEZero)
          in
          (qrec ** rrec ** (rrltb,
          rewrite prf in
          rewrite plusZeroRightNeutral (plus r (mult q (S r))) in
          rewrite plusSuccRightSucc (plus r (mult q (S r))) k in
          rewrite plusCommutative r (mult q (S r)) in Refl))
       (No contra) =>
          let
            nextPrf = lteStrengthen rltb (neqBump contra)
            (qrec ** rrec ** (rrltb, prf)) = modHelp q (S r) k (S j) bnz nextPrf
          in
          (qrec ** rrec ** (rrltb,
          rewrite prf in
          rewrite sym (plusSuccRightSucc (mult q (S j)) r) in
          rewrite plusSuccRightSucc (plus (mult q (S j)) r) k in Refl))
```
In this iteration, we have added a parameter `q : Nat` to represent the current quotient. The function behaves in the same way as before, except every time the remainder rolls back to zero, we increment the current quotient. Alongside the `r < b` proof we used to justify termination, we have added an additional proof that `q' * b + r' = q * b + r + remaining`. It states that the final quotient `q'` multiplied by the modulus `b` plus the final remainder `r'` is equal to the initial quotient `q` times the modulus, plus the initial remainder and dividend `remaining`. This is convenient, because this helper function is invoked by `mod`, which will initialise the accumulated quotient `q` and remainder `r` to zero, as well as the dividend to `a`. Thus, substituting these into the return type yields `q' * b + r' = 0*b+0+a`, which simplifies to `q' * b + r' = a`, exactly the statement we wanted. The proof itself is provided easily in the base case, then propagated up and augmented through the recursive calls. This is acomplished with algebraic `rewrite` rules, which, while being somewhat fun to write, are not very interesting to discuss.

Finally, the new `modHelp` function may be wrapped by `mod`, providing a nicer interface:
```idris
public export total
mod : (a : Nat) -> (b : Nat) -> IsSucc b -> (q : Nat ** rem : Nat ** (LT rem b, a=q*b+rem))
mod a 0 bnz = absurd bnz
mod a (S k) bnz =
  let
    (q ** r ** (rltb, prf)) = modHelp 0 0 a (S k) bnz (LTESucc LTEZero)
  in
  (q ** r ** (rltb, sym prf))
```

== Theorem 1 proof
Now we can show that `euc a b` divides both `a` and `b`. On top of the arithmetic proof, there are also necessary structural changes. First, we must define divisibility:
```
Divides : Nat -> Nat -> Type
Divides a b = (k : Nat ** b = k * a)
```
Here we define _"a divides b"_ to mean that there exists some `k` such that `b = a*k`. In order to construct a proof of divisibility, we will need to explicitly provide the witness `k`. Additionally, to tidy up the type signatures, we will define a helper type which encodes the properties we wish to prove about the Euclidean algorithm:
```
public export total
EucProp : EucArgPair -> Type
EucProp (MkEPair l r) = (d : Nat ** (Divides d l, Divides d r))
```
For now, we have limited it to this theorem. The above definition can be read as "The proposition `EucProp` holds for a given `EucArgPair` if there exists a `d` which divides the left (`l`) and right (`r`) arguments." However, this significantly changes the type signature of `euc`: now instead of returning a number, it has to return a value of a dependent type indexed by its inputs:
```
euc : (a : Nat) -> (b : Nat) -> (c : Nat ** (Divides c a, Divides c b))
```
This means that we can no longer use `sizeRec`. Instead, we must move to `sizeInd`, which is a similar, but more powerful function:
```
sizeInd : Sized a =>
  {P : a -> Type} ->
  ((x : a) -> ((y : a) -> Smaller y x -> P y) -> P x) ->
  (z : a) -> P z
```
This is much the same signature as `sizeRec`, but with the addition of a new parameter `P : a -> Type`, which is a dependent type indexed over values of our return type `a`. Another way of looking at this is that `P` is a _proposition_ which declares something about `a`s. In this way, `sizeInd` can be seen as a proof by induction, where `P` is the statement we aim to prove, the "recursive oracle" is the induction hypothesis, and the helper function is the actual proof body. Once we partially apply this to `sizeInd`, the resulting function has type `(z : a) -> P z`, which encodes that `P` holds for any `z` in `a`.

```
public export total
divLem : {a,b,q,r,d : Nat} -> a=q*b+r -> Divides d b -> Divides d r -> Divides d a
divLem prf (k1 ** p1) (k2 ** p2) =
  rewrite prf in
  rewrite p1 in
  rewrite p2 in
  rewrite (multAssociative q k1 d) in
  rewrite sym (multDistributesOverPlusLeft (q*k1) k2 d) in
  (plus (mult q k1) k2 ** Refl)

public export total
data EucArgPair = MkEPair Nat Nat

Sized EucArgPair where
  size (MkEPair a b) = b

public export total
EucProp : EucArgPair -> Type
EucProp (MkEPair l r) = (d : Nat ** (Divides d l, Divides d r))

public export total
eucHelper : (x : EucArgPair) -> ((y : EucArgPair) -> Smaller y x -> EucProp y) -> EucProp x
eucHelper (MkEPair a 0) _ =
  (a **
    ( (1 ** rewrite plusZeroRightNeutral a in Refl)
    , (0 ** Refl)
    ))
eucHelper theseArgs@(MkEPair a (S p)) rec =
  let
    (q ** r ** (rltb, prfArith)) = mod a (S p) ItIsSucc
    (dRec ** (p1, p2)) = rec (MkEPair (S p) r) rltb
    dda : Divides dRec a = divLem prfArith p1 p2
  in
  (dRec ** (dda, p1))

public export total
euc : (a : Nat) -> (b : Nat) -> (c : Nat ** (Divides c a, Divides c b))
euc a b = sizeInd {P = EucProp} (eucHelper) (MkEPair a b)
```

