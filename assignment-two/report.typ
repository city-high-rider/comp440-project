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
This is a problem, because `sizeRec` restricts us to a fixed codomain, but our new return type changes depending on the input pair. Therefore, we will move to the more general `sizeInd`, whose codomain may vary with the recursive argument:
```
sizeInd : Sized a =>
  {P : a -> Type} ->
  ((x : a) -> ((y : a) -> Smaller y x -> P y) -> P x) ->
  (z : a) -> P z
```
This is much the same signature as `sizeRec`, but with the addition of a new parameter `P : a -> Type`, which is a dependent type indexed over values of our input type `a`. Another way of looking at this is that `P` is a _proposition_ which declares something about `a`s. In this way, `sizeInd` can be seen as a proof by induction, where `P` is the statement we aim to prove, the "recursive oracle" is the induction hypothesis, and the helper function is the actual proof body. Once we supply the proposition and the helper function to `sizeInd`, the resulting function has type `(z : a) -> P z`, which encodes that `P` holds for every value `z` of type `a`.

With this change, here are the relevant updated type signatures, as well as the amended body of `euc`:
```
public export total
eucHelper : (x : EucArgPair) -> ((y : EucArgPair) -> Smaller y x -> EucProp y) -> EucProp x

public export total
euc : (a : Nat) -> (b : Nat) -> (c : Nat ** (Divides c a, Divides c b))
euc a b = sizeInd {P = EucProp} (eucHelper) (MkEPair a b)
```
Having upgraded our recursive machinery, we may move to the algebraic part of the proof, starting with the base case. In the base case, the left argument is some natural number `a`, and the right argument is `0`. Substituting this into `EucProp`, we obtain:
```
d : Nat ** (Divides d a, Divides d 0)
```
In other words, when we reach the base case of the Euclidean algorithm, the final call will look like this: `euc a 0`. Here, we are obligated to provide a proof that there is a common divisor of `a` and `0`. Indeed, such a common divisor is `a` itself. Unfolding our definition even more, if we claim that `a` is the common divisor, we are now required to show that `a` divides itself and zero by providing actual quotients `k1` and `k2`:
```
a : Nat ** ((k1 : Nat ** a = k1 * a), (k2 : Nat ** 0 = k2 * a))
```
Here `k1` and `k2` are `1` and `0` respectively. This combined with an additional lemma about addition concludes our base case:
```
public export total
eucHelper : (x : EucArgPair) -> ((y : EucArgPair) -> Smaller y x -> EucProp y) -> EucProp x
eucHelper (MkEPair a 0) _ =
  (a **
    ( (1 ** rewrite plusZeroRightNeutral a in Refl)
    , (0 ** Refl)
    ))
eucHelper (MkEPair a (S p)) rec = ?eucHelper_rhs_1
```
The recursive case proceeds in the same way as before: we compute `a mod b` to obtain a remainder `r` and a proof that `r < b`, then use this proof to make a recursive call through the "oracle." However, now `mod` also gives us a quotient `q` and an arithmetic proof `a = b*q+r`. Furthermore, we cannot just return the value produced by the recursive call anymore: since return types now depend on the function's inputs, and the recursive call had different arguments, it will have a different return type. Namely, we will be returned a proof that there exists a common divisor for the smaller `EucArgPair`:
```
d : Nat ** (Divides d (S p), Divides d r)
-- where (S p) is the second argument in the euclidean algorithm
```
and required to produce a proof for the larger argument pair:
```
d : Nat ** (Divides d a, Divides d (S p))
-- where (S p) is the second argument in the euclidean algorithm
```
Here is the relevant code:
```
eucHelper (MkEPair a (S p)) rec =
  let
    -- Call mod and unpack the results
    (q ** r ** (rltb, prfArith)) = mod a (S p) ItIsSucc

    -- Make the recursive call and unpack its common divisor dRec alongside the divisibility proofs
    (dRec ** (p1, p2)) = rec (MkEPair (S p) r) rltb
  in
  ?eucHelper_rhs_1
```
Looking at all the information we have in scope, we can see that the recursive call already gave us half of the proof, specifically that `dRec` divides `S p`. The only thing we need to show is that `dRec` also divides `a`. We can do this because the arithmetic proof returned by `mod` tells us that `a = (S p)*q + r`, and the proofs obtained from the recursive call tell us that both `S p` and `r` are divisible by `dRec`. Thus, through some algebraic manipulation, it should follow that `dRec` also divides `a`. We can do all of this algebraic manipulation in a separate lemma:
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
```
Again, `rewrite` chains are not easy to read without interactive editing tools, but translated to paper, the above algebraic working would resemble this:
$
a &= q times b+r\
a &= q times (k_1 times d) + r\
a &= q times (k_1 times d) + (k_2 times d)\
a &= (q times k_1) times d + (k_2 times d)\
a &= (q times k_1 + k_2) times d
$
Thus $d$ divides $a$ where the quotient is $q times k_1 + k_2$. And finally, here is the complete `eucHelp` implementation:
```
public export total
eucHelper : (x : EucArgPair) -> ((y : EucArgPair) -> Smaller y x -> EucProp y) -> EucProp x
eucHelper (MkEPair a 0) _ =
  (a **
    ( (1 ** rewrite plusZeroRightNeutral a in Refl)
    , (0 ** Refl)
    ))
eucHelper (MkEPair a (S p)) rec =
  let
    (q ** r ** (rltb, prfArith)) = mod a (S p) ItIsSucc
    (dRec ** (p1, p2)) = rec (MkEPair (S p) r) rltb
    dda : Divides dRec a = divLem prfArith p1 p2
  in
  (dRec ** (dda, p1))
```

== Theorem 2 proof
Now we have shown that the result of the Euclidean algorithm is a common divisor of the two inputs, the only thing left to do is show that it is the _greatest_ common divisor. We did most of the hard work involving `sizeInd`, termination, arithmetic properties of `mod`, and the `EucProp` definitions in the previous parts. This proof will largely build on previous code, with the algebra containing most of the noteworthy details.

First, we must change `EucProp` to also state that `d` is the greatest common divisor. However, instead of working with the `LTE` or `GTE` types, we will define this in terms of divisibility. In order for `d` to be the greatest common divisor, any other divisor must also divide it, which makes the proof substantially nicer.
```
public export total
CommonDiv : Nat -> Nat -> Nat -> Type
CommonDiv d a b = (Divides d a, Divides d b)

public export total
EucProp : EucArgPair -> Type
EucProp (MkEPair l r) =
  (d : Nat ** (CommonDiv d l r, (o : Nat) -> CommonDiv o l r -> Divides o d))
```
First, we move out the statement "`d` is a common divisor of `a` and `b`" to its own top level definition to make the other types more succinct. To encode this theorem formally, we introduced this to `EucProp` 
```
(o : Nat) -> CommonDiv o l r -> Divides o d
```
Which is a function that takes any natural number `o`, a proof that `o` is a common divisor of `l` and `r`, and constructs a proof that `o` is a common divisor of `d`. It can logically be thought of as a "for all" quantifier, because we can pass any `o` to this function. As before, we update the definition of `euc`:
```
euc : (a : Nat) -> (b : Nat) ->
      (c : Nat ** (CommonDiv c a b, (o : Nat) -> CommonDiv o a b -> Divides o c))
euc a b = sizeInd {P = EucProp} (eucHelper) (MkEPair a b)
```
Now, we ought to prove this for the base case, and add it to `eucHelper`. Specifically, we want to show that `a` is the greatest common divisor of `a` and `0`. Unrolling our definitions, the proof becomes straightforward: suppose we have another divisor `o`, which divides `a` and `0`. We are obligated to show that `o` divides `a`. This can be done just by repeating the premises:
```
public export total
eucGcdBaseCase :
  (a : Nat) ->
  (o : Nat) ->
  ( (k : Nat ** a = mult k o)
  , (k : Nat ** 0 = mult k o)
  ) ->
  (k : Nat ** a = mult k o)
eucGcdBaseCase a _ ((k1 ** p1), _) =
  (k1 ** rewrite p1 in Refl)
```
and so that concludes the updated base case of `eucHelper`:
```
eucHelper (MkEPair a 0) _ =
  (a ** 
    (( (1 ** rewrite plusZeroRightNeutral a in Refl)
     , (0 ** Refl))
     , eucGcdBaseCase a)
  )
```
The inductive case remains largely unchanged from before, but we get a new piece of information from the induction hypothesis: `p3`, which is a proof that `dRec` is the greatest common divisor of `S p` and `r`. However, we must also prove that `dRec` is the largest common divisor of `S p` and `a`, which we will mark with a hole for now.
```
eucHelper (MkEPair a (S p)) rec =
  let
    (q ** r ** (rltb, prfArith)) = mod a (S p) ItIsSucc
    (dRec ** ((p1, p2), p3)) = rec (MkEPair (S p) r) rltb
    dda : Divides dRec a = divLem prfArith p1 p2
  in
  (dRec ** ((dda, p1), ?hole))
```
Let's algebraically reason about how we may implement the hole. Suppose we are given `o`, a divisor of `a` and `S p`. We still have the arithmetic proof from `mod`, so let us use that:
$
  a &= q times (S p) + r\
  (k_1 times o) &= q times (S p) + r\
  (k_1 times o) &= q times (k_2 times o) + r\
  (k_1 times o) &= (q times k_2) times o + r\
  (k_1 times o) - (q times k_2) times o &= r\
  (k_1 - q times k_2) times o &= r
$
Thus, `o` divides `r`. We also know `o` divides `S p`, and recall that `p3` from the induction hypothesis tells us that any common divisor of `r` and `S p` also divides `dRec`! Thus, we can conclude our proof. But unfortunately, there is a problem in our algebra: we used subtraction to move everything with `o` to one side and factor it. Because we are working with natural numbers, all subtractions are floored at zero. Introducing subtraction would complicate our algebraic proof immensely, because we would need to reason about whether $q times k_2$ is bigger than $k_1$ or not.

This brings us to the noteworthy algebraic trick of this section: we will need to find a way to get from
$
  (k_1 times o) = (q times k_2) times o + r
$
Or, equivalently, by merging $q$ and $k_2$ into the same constant:
$
  k_1 times o = k_2 times o + r
$
to a constructive proof that `o` divides `r` without using subtraction. We will do this by induction on $k_2$.

*Base case:* $k_2 = 0$. Here we can substitute this into our premise:
$
  k_1 times o &= k_2 times o + r\
  k_1 times o &= 0 times o + r\
  k_1 times o &= 0 + r\
  k_1 times o &= r\
$
And thus it follows that $o$ divides $r$ with $k_1$ as the quotient.

*Inductive case*: Suppose $k_2$ is nonzero, i.e. $k_2 = n + 1$. Our inductive hypothesis is that we can go from a proof that 
$
  k_1 times o = n times o + r
$
to a proof that $o$ divides $r$. To continue, we examine whether or not $k_1$ is zero:

*Case 1:* $k_1 = 0$. We substitute into our premise:
$
  0 times o &= (n + 1) times o + r\
  0 &= (n + 1) times o + r\
$
Observe that here we have two natural numbers summing to zero. Therefore, they must both be zero:
$
  r &= 0\
  "and"\
  (n + 1) times o &= 0\
$
Therefore by transitivity of equality,
$
  r = (n + 1) times o
$
and we can conclude that $o$ divides $r$ with $n + 1$ as the quotient.

*Case 2:* $k_2 != 0$, i.e. $k_2 = m + 1$. Here we again substitute and expand:
$
  (m+1) times o &= (n+1) times o + r\
  o + (m times o) &= (o + n times o) + r\
  o + (m times o) &= o + (n times o + r)\
$
Here, we can use the fact that for any $c$, $f(x) = c + x$ is injective to "cancel out" the $o$:
$
  m times o = n times o + r
$
Now we have reduced the equality to a form where we can apply the induction hypothesis and conclude that $o$ divides $r$.

$qed$

This is the core algebraic logic that we will need to encode in Idris. Once again, `rewrite` chains are not very human readable and writing them involves a gruelling session of repeatedly bouncing syntactic terms back and forth to the type checker, thus I will spare the details of actually encoding this algebra and present the full source code:
```
public export total
sumZeroArgsZero : {a,b : Nat} -> a + b = 0 -> (a = 0, b = 0)
sumZeroArgsZero {a = 0} {b = 0} Refl = (Refl, Refl)
sumZeroArgsZero {a = 0} {b = (S k)} prf impossible
sumZeroArgsZero {a = (S k)} {b = 0} prf impossible
sumZeroArgsZero {a = (S k)} {b = (S j)} prf impossible

public export total
plusConstCancelLeft : (c : Nat) -> (l : Nat) -> (r : Nat) -> c+l = c+r -> l=r 
plusConstCancelLeft 0 l l Refl = Refl
plusConstCancelLeft (S k) l r prf =
  plusConstCancelLeft k l r (injective prf)

public export total
divCancelLem : 
  (k1 : Nat) ->
  (k2 : Nat) ->
  (d : Nat) ->
  (r : Nat) ->
  (k1 * d = k2 * d + r) ->
  Divides d r
divCancelLem k1 0 d r prf = (k1 ** rewrite prf in Refl)
divCancelLem 0 (S n) d r prf =
  let
    (_, rzero) = sumZeroArgsZero (sym prf)
  in
  (0 ** rzero)
divCancelLem (S m) (S n) d r prf =
  let
    prf' : (d+m*d = d+(n*d+r)) = rewrite (plusAssociative d (n*d) r) in prf
  in
  divCancelLem m n d r (rewrite (plusConstCancelLeft d (m*d) (n*d+r) prf') in Refl)

public export total
data EucArgPair = MkEPair Nat Nat

Sized EucArgPair where
  size (MkEPair a b) = b

public export total
CommonDiv : Nat -> Nat -> Nat -> Type
CommonDiv d a b = (Divides d a, Divides d b)

public export total
EucProp : EucArgPair -> Type
EucProp (MkEPair l r) =
  (d : Nat ** (CommonDiv d l r, (o : Nat) -> CommonDiv o l r -> Divides o d))

public export total
eucGcdBaseCase : (a : Nat) -> (o : Nat) -> ((k : Nat ** a = mult k o), (k : Nat ** 0 = mult k o)) -> (k : Nat ** a = mult k o)
eucGcdBaseCase a _ ((k1 ** p1), _) =
  (k1 ** rewrite p1 in Refl)

public export total
eucHelper : (x : EucArgPair) -> ((y : EucArgPair) -> Smaller y x -> EucProp y) -> EucProp x
eucHelper (MkEPair a 0) _ =
  (a ** 
    (( (1 ** rewrite plusZeroRightNeutral a in Refl)
     , (0 ** Refl))
     , eucGcdBaseCase a)
  )
eucHelper (MkEPair a (S p)) rec =
  let
    (q ** r ** (rltb, prfArith)) = mod a (S p) ItIsSucc
    (dRec ** ((p1, p2), p3)) = rec (MkEPair (S p) r) rltb
    dda : Divides dRec a = divLem prfArith p1 p2
  in
  (dRec ** ((dda, p1), \o, ((k1 ** pr1), odivb@(k2 ** pr2)) =>
    let
      prf' : (k1*o = plus (mult q (S p)) r) = sym (rewrite sym prfArith in pr1)
      prf'' : (k1*o = plus (mult q (k2*o)) r) = rewrite sym pr2 in prf'
      prf''' : (k1*o = ((q*k2)*o)+r) = rewrite sym (multAssociative q k2 o) in prf''
    in
    p3 o (odivb, (divCancelLem k1 (q*k2) o r prf'''))
  ))

public export total
euc : (a : Nat) -> (b : Nat) ->
      (c : Nat ** (CommonDiv c a b, (o : Nat) -> CommonDiv o a b -> Divides o c))
euc a b = sizeInd {P = EucProp} (eucHelper) (MkEPair a b)
```

And with that, we have constructively verified the Euclidean algorithm in Idris2.

= Verification in Haskell

Haskell has many things in common with Idris2: both are purely functional programming languages with similar syntax. Both languages aim to have a rich type system, and naturally, this leads to computational code in both languages looking similar.

However, there are a few things that make Haskell unwieldy for encoding propositions in the type system and proving them constructively with functions, like we did in Idris. For starters, Haskell does not enforce totality, meaning that the `bottom` term, defined as follows:
```haskell
bottom :: a
bottom = bottom
```
inhabits every lifted type. As a result, Haskell cannot treat types as constructive proofs in the same way as Idris, because arbitrary types may be inhabited by nonterminating or partial terms. On top of that, `bottom` is not the only construct with this behavior: `error` and `undefined` inhabit every type, and crash the program when they are evaluated.

The other issue is that Haskell does not have support for first-class types or dependent types like Idris does. The separation between types and values is very strict, and often requires you to manually "promote" values into types, and types into kinds. This requires using lots of language extensions (`GADTs`, `DataKinds`, `TypeFamilies`, `PolyKinds`, `TypeApplications` etc.) Using these features enables some lightweight dependent typing, such as length indexed vectors and operations on them, or encoding database schemas / API specs into the type system to enforce their correct use statically. However, as it stands, many of the features we used extensively in the Idris proof are not native to Haskell, and must be emulated with the aforementioned language extensions. Specifically, dependent pairs, rewrite chains, and injectivity proofs all become more cumbersome.

With that being said, emulating our Idris proof in Haskell is still very likely possible. However, I will not do it because it is very awkward and time consuming while simultaneously not introducing anything new to write about. Instead, I will focus on two new tools which see much more use in the Haskell ecosystem: refinement types and property based testing.

== Property based testing and QuickCheck
Property based testing is not formal verification, but it is nonetheless a great tool for finding bugs. Property tests are typically much easier and faster to write than constructive proofs, and they can be defined outside of the module where the actual code you are testing is. This avoids a nasty consequence we saw in our Idris2 verification: at the start, we had a clear and concise implementation of the Euclidean algorithm, but in verifying it we introduced several helper lemmas and filled the core logic with dozens of lines of proof code. It also saves us from having to redefine library functions like `mod` in a simpler way just so we can verify them.

The gist of property based testing is this:
  1. Pick the function you want to test, and, in code, write down a property it should satisfy.
  2. The tester will repeatedly generate inputs and check whether the property holds.
  3. If an input is found for which the property is false, the tester will attempt to "shrink" the input as much as possible to find a minimal counterexample which breaks the property.

Here is our Haskell implementation of the Euclidean algorithm:
```haskell
euc :: Int -> Int -> Int
euc a 0 = a
euc a b = euc b (a `rem` b)
```
and here is a test for the first theorem:
```haskell
divides :: Int -> Int -> Bool
0 `divides` _ = True
a `divides` b = b `rem` a == 0

prop_eucCommonDiv :: Int -> Int -> Bool
prop_eucCommonDiv a b =
  let
    c = euc a b
  in
  (c `divides` a) && (c `divides` b)

main :: IO ()
main = quickCheck prop_eucCommonDiv
```
Running these tests with verbose mode yields the following output:
```
Test suite euclid-gcd-tests: RUNNING...
Running QuickCheck tests...
Passed:  
0
0

Passed: 
0
1

Passed:  
-2
0

Passed:  
-2
-1

Passed:  
3
-4

(rest of cases omitted)

+++ OK, passed 100 tests.
Test suite euclid-gcd-tests: PASS
```

There you can see the process in action; the tester is going and invoking the code with each input pair, then checking that the property holds. Unlike Idris, I made this implementation use integers rather than natural numbers, and the `mod` function from the standard library so that these tests cover cases which our formal proof does not. If we add another test:
```haskell
-- we use the triple equals to provide richer debug information
prop_eucGreatestDiv :: Int -> Int -> Property
prop_eucGreatestDiv a b =
  euc a b === gcd a b
```
(Yes, this is cheating a bit because we are using the known-good `gcd` from the standard library, but you can replace it with a simple brute-force implementation that iterates through the common divisors and finds the maximum)

We can see that QuickCheck has found a very simple set of inputs which break our implementation:
```
*** Failed! Falsified (after 2 tests and 1 shrink):     
0
-1
-1 /= 1
```
which we can quickly fix by taking the absolute value of `a` in the base case, after which all the tests pass:
```haskell
euc a 0 = abs a
```
And if 100 tests for each property aren't convincing enough, we can always tell QuickCheck to run more cases. In principle, because machine integers are finite, verifying every possible input pair (of which there are $2^128$ on a 64-bit computer) would establish correctness for that specific implementation and integer representation. However, this would be computationally infeasible, and unlike the Idris proof, it would provide little insight into _why_ the algorithm is correct.

The important thing here is that these tests took only a minute or two to set up, compared to the three or four hours I spent writing the formal proof. Despite this, we still managed to find a bug involving negative inputs, all without reinventing existing functions or obfuscating the original implementation in rewrite chains, extra proof carrying arguments, lemmas, etc.

And surprisingly, counterexamples to many non-trivial conjectures in number theory have been found with conceptually similar approaches. Examples inculde "Counterexample to Euler's Conjecture on Sums of Like Powers by L. J. Lander and T. R. Parkin" as well as recent computational work on instances of the sum of three cubes problem. More rigorous forms of computer assisted verification also exist in mathematics: the proof of the four color theorem reduced the problem to a very large but finite collection of cases, which were then exhaustively checked by a computer.

== Refinement types and LiquidHaskell
One property of the Haskell implementation that we are yet to test is termination. Unlike our other two properties, testing termination by simply running the program leads to a problem: how can we actually tell that the program is stuck in an infinite loop, and not just taking a long time to finish? In general, this is impossible. In practice, a single function having an execution time of several seconds on a modern computer is eyebrow raising and often indicates non-termination, but is not a proof. Furthermore, in some domains such as scientific computing, execution times are frequently measured in hours.

Thankfully, there is a technique which can formally verify properties of programs in a way that is less invasive and more automated than our constructive Idris proof. In LiquidHaskell, we annotate our functions with _refinement types_, which place logical constraints on ordinary Haskell types. It then combines the code, types, and propositions to produce a set of decidable verification conditions, i.e. predicates which are valid only if the program satisfies the specified properties. Finally, an SMT solver is used to determine whether or not the verification conditions are valid. If they are, the program is marked safe.

This makes LiquidHaskell much more automatic than Idris and removes the need for the explicit construction and manipulation of proofs, which in turn means we do not need to actually modify the implementation to carry them. However, we will still need to provide annotations for LiquidHaskell, and potentially write some helper lemmas. The heavy automation also comes at the cost of less approachable error messages, as they are the direct output of the SMT solver.


