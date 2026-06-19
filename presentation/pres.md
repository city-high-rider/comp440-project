---
marp: true
theme: gaia
paginate: true
style: |
  section {
    padding: 20px 40px;
  }
---
## From Static Typing to Theorem Proving
**ENGR340 Presentation**

---
### Contents
- Describing the shape of data
- Well-typed programs still go wrong
- Encoding invariants in the type system
- Code specifications as types
- Vector `reverse` example and commutativity proof
- Types as propositions, values as evidence, and programs as proofs
- Tactic-based theorem proving
- Property based testing and refinement types

---

**The low level view**
How should the computer interpret binary data?
What CPU instructions should it use?

`01001000 01100101 01111001 00000000`

1. Null-terminated ASCII string: "Hey"
2. Float: 234980.0
3. Signed 32-bit integer: 1214609664
4. `struct Player*`: A memory address which points to six integers and ten characters, all stored contiguously. 

<!--
Eventually, everything must be encoded as binary, and we need to indicate whether the bits store a string, number, or pointer.
-->
---

**Primitives**
Bits grouped into standard, simple shapes
- `i32`: -2,147,483,648 <-> 2,147,483,647
- `u8`: 0 <-> 255
- `bool`: 0 <-> 1
```c
enum Color {Red, Green, Blue};
enum Shape {Square, Circle};

enum Color c = Red;
enum Shape s = Square;
int res = (c == s); // ???
printf("%i", res);
```

<!--
There's still some issues:
- Ranges are huge or tiny
- You have to remember the semantic meaning of things: E.g. `00000000` indicates the absence of data due to an error
- Compiler doesn't care and will gladly let you add, dereference, or cast the raw data in nonsensical ways
- Switch/case exhaustiveness
- Some values are technically valid but semantically nonsensical
- "Trust me, go to this memory location, and you will find exactly 6 ints and 10 chars." If you lie, or if that data got wiped, the program violently crashes.
- Developer has to worry about serialization when writing code
- can represent invalid states
-->
---
```c
enum Status { InFlight, Success, Failure };
typedef struct {
    enum Status status;
    union {
        int errorCode;
        char data[1024];
    }; 
} NetworkRequest;
```
Not every value is semantically valid
```c
NetworkRequest req = {
  .status = (enum Status) 100,
  .data = "what"
};
```
---
...And, with this in mind, we have to write code defensively to prevent problems such as:
 - status and the union going out of sync
```c
NetworkRequest *req = getValidRequest();
//...
if (req->status == Failure) {
  strcpy(req->data, "Fixed it!");
}
//...
return req;
```
---
<style scoped>
pre {
   font-size: 70%;
}
</style>
 - status being set to some int which is not in the enum
```c
NetworkRequest req;
req.status = (enum Status) 100;
strcpy(req.data, "Happy debugging ;)");
```
 - non-exhaustive pattern matching
```c
switch (req.status) {
  case InFlight:
    // ...
    break;
  case Success:
    // ...
    break;
  case Failure:
    // ...
    break;
  default:
    // What goes here??
    break;
}
```
---
 - something writing to the wrong variant and corrupting or leaking the union
```c
// start here...
req.status = Success;
strcpy(req.data, "...Some very sensitive secret data!");
// ...
// Something later on goes wrong, so we flip to failure
req.status = Failure;
// Overwrites only the first 4 bytes of 'data'
// -1 == 0xFFFFFFFF
req.errorCode = -1;
// ...
// System tries to log something
printf("Raw buffer preview: %s\n", &req.data);
// Output: "????ome very sensitive secret data!" 
// The semantic intent was to destroy/overwrite the success state, but the data leaked.
```
---

You can alleviate this with clever use of macros, opaque pointers, constructor functions, or good code hygiene...

some public `network_request.h`:
```c
// Opaque type definition
typedef struct NetworkRequest NetworkRequest;

NetworkRequest* create_success(const char* data);
NetworkRequest* create_failure(int error_code);
void free_request(NetworkRequest* req);

// Forced pattern matching via a callback handler
void match_request(const NetworkRequest* req,
                   void (*on_success)(const char*),
                   void (*on_failure)(int));
```
---
...but you're never guaranteed to be safe
```c
// External code bypassing the API boundary completely
void maliciousOrLazyCode(NetworkRequest* publicReq) {
    struct ILookedAtTheInternalLayout { int status; char data[1024]; };
    struct ILookedAtTheInternalLayout* evil =
      (struct ILookedAtTheInternalLayout*)publicReq;
    evil->status = 999;
}
```
---
**Types are sets of values**

*"Make invalid states unrepresentable"* - Yaron Minsky

Instead of trying to carve our domain types out of big numbers, what if we stopped worrying about memory entirely and focused only on describing the set of "good" values?

To build a set, you only need these things:
1. A set with just one value, often called the unit type
2. "AND"-ing sets together via the Cartesian product
3. "OR"-ing sets together via the disjoint union
4. Descriptive labels for our values, so the compiler and human can tell them apart.

---
(Flavor 1/2: ADTs)

```haskell
-- Pure sum types (This OR That - An enum)
data EyeColor = Blue | Green | Brown

-- Pure product types (This AND That - A struct/record)
data Person = MkPerson Name EyeColor HeightCm

-- Mixed/Tagged sum types (A variant that carries data)
data User = Anonymous | Guest Name | Registered Person

-- Recursion
data JsonValue = JNull | JBool Bool | JNum Double | JArray [JsonValue] | JObject (Map String JsonValue)

-- Parametric polymorphism (generics)
-- 'Maybe' is a type constructor; 'Maybe Person' is a concrete type.
data Maybe a = Just a | Nothing
```
---
Flavor 2/2: Enterprise edition
You can do mostly the same thing using interfaces and classes, with some caveats:
```java
public sealed interface User permits Anonymous, Guest, Registered {}
public record Anonymous() implements User {}
public record Guest(String name) implements User {}
public record Registered(String name, Color eyeColor, LengthCM height) implements User {}

public sealed interface ConsList<T> permits Cons, Nil {}
public record Nil<T>() implements ConsList<T> {}
public record Cons<T>(T value, ConsList<T> rest) implements ConsList<T> {}
```
---
We can now specify the *shape* of our data very precisely. This prevents a lot of the c-style bugs from before, but there's still problems.
```haskell
-- data List a = [] | a : List a

reverse :: List a -> List a
reverse [] = []
reverse (first:rest) = reverse rest ++ [first]
```
The recursion converges towards a base case. Reversing a list twice returns the original list...

---
... until it doesn't
```haskell
main = print . take 10 . reverse . reverse $ [1..]
```
(This type checks, but loops forever, or until you run out of stack space)

---
Programs can also fail by throwing errors or not covering all values
```haskell
head :: List a -> a
head (first:_) = first
head [] = undefined

index :: List a -> Int -> a
index [] _ = undefined
index (first:_) 0 = first
index (_:rest) n = if n > 0 then index rest (n - 1) else undefined

lookup :: (Ord k) => Map k v -> k -> v
```
---
We can solve this with constructs like `Maybe` and `Optional`
```haskell
data Maybe a = Nothing | Just a

head :: List a -> Maybe a
-- If we don't know what to do, we can just return Nothing instead of crashing!
-- Now it's someone else's problem.
head [] = Nothing
head (x:_) = Just x
```
Java starts to show its age here...
```java
// lol
Optional<User> userOpt = null;
// ... somewhere else in the code, this causes a NPE
if (userOpt.isPresent()) {
  doSomething(userOpt.get().getName());
}
```
---
The type signature reflects the possible absence of a value
Good: this forces us to handle errors
```haskell
doSomething :: Int -> IO ()
stringToInt :: String -> Maybe Int

placeOrder :: IO ()
placeOrder = do
  putStrLn "Enter your order quantity here"
  qtyStr <- getLine
  case (stringToInt qtyStr) of
    Nothing -> do
      putStrLn "Invalid, please try again"
      placeOrder
    Just qtyInt -> do
      putStrLn "OK."
      -- We have to check that qtyInt parsed correctly
      -- before we pass it further down the pipeline
      doSomething qtyInt
```
---
Something interesting has happened:

We intially just wanted to model a set and enforce that data was well-formed at compile time. But now we are seeing that the type system can also enforce some lightweight "contracts"

Can we / should we push further in this direction?

---
**Another look at our ADTs:**
```haskell
data List a = Nil | Cons a (List a)
```
`List` is not a type on its own. It has to be a list of *something*, e.g. `List Int` or `List Char`.

`List` is a type *constructor*. We have to pass it a type, and we get a type out

Kind of like a function!

List :: Type -> Type
List a = $\{Nil\} \sqcup (a \times \text{List a})$

(We are taking a set of values `a` and making another set of values)

---

$$
\text{List Bool} = \{Nil\} \sqcup (\{\text{True} \sqcup \text{False}\} \times \text{List Bool})
$$
Some values:
- Nil <-> [] 
- Cons True (Nil) <-> [True]
- Cons False (Nil) <-> [False]
- Cons True (Cons True (Nil)) <-> [True, True]
- Cons True (Cons False (Nil)) <-> [True, False]
...
---
Usually these type constructor "functions" are boring, and we can only pass in other types as arguments.

**What if we removed this restriction?**

```
data Nat = Z | S Nat
```

Vector :: Nat -> Type -> Type
Vector length a = case length of
  Z -> {Nil}
  (S k) -> $a \times \text{Vector k a}$

---

Vector 3 Bool 
 = Bool $\times$ Vector 2 Bool
 = Bool $\times$ Bool $\times$ Vector 1 Bool
 = Bool $\times$ Bool $\times$ Bool $\times$ Vector 0 Bool
 = Bool $\times$ Bool $\times$ Bool $\times$ {Nil}

We have encoded the length of the list (a runtime property) into the type!

---
Some functions with `Vector`
```haskell
append : Vector m a -> Vector n a -> Vector (m + n) a
append Nil v = v
append (Cons x rest) v = Cons x (append rest v)

-- We don't need to cover Nil here!
head : Vector (S k) a -> a
head (Cons x rest) = x

-- No need to handle Nil / cons combo
dotProd : Vector len Int -> Vector len Int -> Int
dotProd Nil Nil = 0
dotProd (Cons x restA) (Cons y restB) = (x*y) + dotProd restA restB
```

---

Each signature is telling you the preconditions and postconditions on the Vector's length.
This is *enforced by the typechecker*, so it is impossible to write a `reverse` implementation that changes the size of the vector:

```haskell
reverse : Vector len a -> Vector len a
```
---
Another fun exercise: Can we write a type constructor that takes an `n` and makes a set of `n` different values?

Fin : Nat -> Type
Fin 0 = {}
Fin (S k) = {FZ} $\sqcup$ {FS x | x $\in$ Fin k}

Fin 1
 = {FZ} $\sqcup$ {FS x | x $\in$ Fin 0}
 = {FZ} $\sqcup$ {FS x | x $\in$ {}}
 = {FZ}
 $\cong$ {0}

---

Fin 2
 = {FZ} $\sqcup$ {FS x | x $\in$ Fin 1}
 = {FZ} $\sqcup$ {FS x | x $\in$ {FZ}}
 = {FZ} $\sqcup$ {FS (FZ)}
 = {FZ, FS (FZ)}
 $\cong$ {0, 1}

---
Fin 3
 = {FZ} $\sqcup$ {FS x | x $\in$ Fin 2}
 = {FZ} $\sqcup$ {FS x | x $\in$ {FZ, FS (FZ)}}
 = {FZ} $\sqcup$ {FS (FZ), FS (FS (FZ))}
 = {FZ, FS (FZ), FS (FS (FZ))}
 $\cong$ {0, 1, 2}

So Fin k $\cong$ {0, 1, 2, ..., k - 1}

```haskell
index : Vector k a -> Fin k -> a
index (Cons first rest) FZ = first
index (Cons first rest) (FS idx) = index rest idx
```
---

**The actual syntax for declaring dependent types is "bottom-up," not "top-down."**

1. The "signature" of the type constructor is still here
```haskell
data Vector : Nat -> Type -> Type where
```

You can think of this as defining a family of different types at once, E.g.
- Vector 0 Bool
- Vector 35 Int
- Vector 3 (Vector 0 Double)
etc. are all distinct types, but have the same "shape"

---
2. We define the common constructors for each `Vector` type, and for each one, determine exactly which `Vector`s it makes.
```haskell
-- The signature from the last slide
data Vector : Nat -> Type -> Type where
  -- Nil doesn't take any arguments, and is in the set of
  -- empty vectors parameterised by any type.
  Nil : Vector 0 a
  -- Cons takes a value of 'a', a vector of length n,
  -- and is in the set of (n+1) long vectors parameterised by 'a'.
  Cons : a -> Vector n a -> Vector (S n) a
```
---

Here is `fin` with this syntax
```haskell
data Fin : Nat -> Type where
  FZ : Fin (S k)
  FS : Fin m -> Fin (S m)
```
Notice that `Fin 0` is a valid type, but there is no constructor that makes a value of `Fin 0`!

This syntax is needed because
 - It is much easier for the compiler to reason about
 - We can assign labels to disjoint unions and pattern-match on them easier

---
**The cost of dependent types**
Assume we already have a good `++` (appending)
```haskell
(++) : Vector n a -> Vector m a -> Vector (n + m) a
```
and try to implement `reverse`
```haskell
reverse : Vector n a -> Vector n a
reverse Nil = Nil
reverse (Cons first rest) = reverse rest ++ (Cons first Nil)
```
---
```
Error: While processing right hand side of reverse. Can't solve constraint between:
  plus len 1
and
  S len.

Test:15:28--15:67
 11 |
 12 | total
 13 | reverse : Vector n a -> Vector n a
 14 | reverse [] = Nil
 15 | reverse (Cons this rest) = (reverse rest) ++ (Cons this Nil)
                                 ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```
During typechecking, the compiler is unable to unify `len + 1` with `S len`

Even though it's obviously the same thing...

---
**Why is it like this?**
The definition of `plus`
```haskell
plus : Nat -> Nat -> Nat
plus Z x = x
plus (S k) x = S (plus k x)
```

To simplify a `plus` call, we have to pattern match on the first argument, so we have to know what it is

---
Looking at the problematic expression:
`(reverse rest) ++ (Cons this Nil)`

Recall appending has the signature
```haskell
append : Vector m a -> Vector n a -> Vector (m + n) a
```

`Cons this Nil` : Vector 1 a
`reverse rest` : Vector m a
Resulting type: `Vector (m + 1) a`

But we do not know if `m` is zero or a successor, so we cannot simplify any further!

---
Therefore, to the type checker, `Vector (m + 1) a` and `Vector (S m) a` are completely different, incompatible types.

But intuitively, we know that `m + 1` and `S m` give the same result. So for any `m`, `Vector (m + 1) a` and `Vector (S m) a` will end up being the same set of values.

Can we communicate this to the type checker?

---
**A proof of equality**
Can we make a type constructor that takes two values, and returns the empty set if they are different, and a nonempty set if they are the same?

```haskell
data EqualNats : Nat -> Nat -> Type where
  Refl : x -> EqualNats x x
```

All of these are now valid types:
 - EqualNats 0 0
 - EqualNats 0 1
 - EqualNats 17 31
 - EqualNats 2 2

But our constructor only lets us build two of the above examples

---

We can make it more general than just natural numbers
```haskell
data Equal : a -> a -> Type where
  Refl : a -> Equal a a
```
If we have a *value* of `Equal x y` it means `x` and `y` are *exactly the same thing*.

Unlike a boolean method like `.equals()`, this is structurally impossible to fake

---

The equality type in the standard library has special powers. If we have a proof that `x = y`, we can get the type checker to replace every `x` in the type with a `y`.

We now need to prove that `a + b = b + a` (commutativity) to finish writing `reverse`.

```haskell
plusComm : (a : Nat) -> (b : Nat) -> a + b = b + a
plusComm 0 b = ?plusComm_rhs_0
plusComm (S k) b = ?plusComm_rhs_1
```

---

We can inspect the holes to see what we are obligated to prove in each case
```
   b : Nat
------------------------------
plusComm_rhs_0 : b = plus b 0
````
```
   k : Nat
   b : Nat
------------------------------
plusComm_rhs_1 : S (plus k b) = plus b (S k)
````
---

```haskell
plusZeroRightNeutral : (rhs : Nat) -> rhs + 0 = rhs
plusZeroRightNeutral 0 = ?plusZeroRightNeutral_rhs_0
plusZeroRightNeutral (S k) = ?plusZeroRightNeutral_rhs_1
```

```
plusZeroRightNeutral_rhs_0 : 0 = 0
```

```
   k : Nat
------------------------------
plusZeroRightNeutral_rhs_1 : S (plus k 0) = S k
```
---

```haskell
plusZeroRightNeutral : (rhs : Nat) -> rhs + 0 = rhs
plusZeroRightNeutral 0 = Refl
plusZeroRightNeutral (S k) =
  let
    rec : (plus k 0 = k) = plusZeroRightNeutral k
  in
  rewrite rec in Refl
```

```haskell
plusComm : (a : Nat) -> (b : Nat) -> a + b = b + a
plusComm 0 b = sym (plusZeroRightNeutral b)
plusComm (S k) b = ?plusComm_rhs_1
```
---

```haskell
plusComm : (a : Nat) -> (b : Nat) -> a + b = b + a
plusComm 0 b = sym (plusZeroRightNeutral b)
plusComm (S k) b = 
  let
    rec : (plus k b = plus b k) = plusComm k b
  in
  rewrite rec in ?plusComm_rhs1
```

```
   k : Nat
   b : Nat
   rec : plus k b = plus b k
------------------------------
plusComm_rhs1 : S (plus b k) = plus b (S k)
```
---
```hs
plusLemma : (left : Nat) -> (right : Nat) -> left + (S right) = S (left + right)
plusLemma 0 0 = ?plusLemma_rhs_2
plusLemma 0 (S k) = ?plusLemma_rhs_3
plusLemma (S k) 0 = ?plusLemma_rhs_4
plusLemma (S k) (S j) = ?plusLemma_rhs_5
```
```
plusLemma_rhs_2 : 1 = 1

   k : Nat
------------------------------
plusLemma_rhs_3 : S (S k) = S (S k)
```

```
   k : Nat
------------------------------
plusLemma_rhs_4 : S (plus k 1) = S (S (plus k 0))
```
---
```hs
plusLemma : (left : Nat) -> (right : Nat) -> left + (S right) = S (left + right)
plusLemma 0 0 = Refl
plusLemma 0 (S k) = Refl
plusLemma (S k) 0 =
  rewrite (plusZeroRightNeutral k) in
  ?plusLemma_rhs_4
plusLemma (S k) (S j) = ?plusLemma_rhs_5
```

```
   k : Nat
------------------------------
plusLemma_rhs_4 : S (plus k 1) = S (S k)
```
---
```hs
plusOneSucc : (x : Nat) -> x + 1 = S x
plusOneSucc 0 = ?plusOneSucc_rhs_0
plusOneSucc (S k) = ?plusOneSucc_rhs_1
```

```
plusOneSucc_rhs_0 : 1 = 1

   k : Nat
------------------------------
plusOneSucc_rhs_1 : S (plus k 1) = S (S k)
```

```hs
plusOneSucc : (x : Nat) -> x + 1 = S x
plusOneSucc 0 = Refl
plusOneSucc (S k) = rewrite (plusOneSucc k) in Refl
```
---
```hs
plusLemma : (left : Nat) -> (right : Nat) -> left + (S right) = S (left + right)
plusLemma 0 0 = Refl
plusLemma 0 (S k) = Refl
plusLemma (S k) 0 =
  rewrite (plusZeroRightNeutral k) in
  rewrite (plusOneSucc k) in
  Refl
plusLemma (S k) (S j) = ?plusLemma_rhs_5
```

```
   k : Nat
   j : Nat
------------------------------
plusLemma_rhs_5 : S (plus k (S (S j))) = S (S (plus k (S j)))
```
If you squint really hard...

---
```hs
plusLemma : (left : Nat) -> (right : Nat) -> left + (S right) = S (left + right)
plusLemma 0 0 = Refl
plusLemma 0 (S k) = Refl
plusLemma (S k) 0 =
  rewrite (plusZeroRightNeutral k) in
  rewrite (plusOneSucc k) in
  Refl
plusLemma (S k) (S j) =
  rewrite (plusLemma k (S j)) in
  Refl
```
---
```hs
plusComm : (a : Nat) -> (b : Nat) -> a + b = b + a
plusComm 0 b = sym (plusZeroRightNeutral b)
plusComm (S k) b = 
  let
    rec : (plus k b = plus b k) = plusComm k b
  in
  rewrite rec in
  rewrite (plusLemma b k) in
  ?plusComm_rhs1
```

```
   k : Nat
   b : Nat
   rec : plus k b = plus b k
------------------------------
plusComm_rhs1 : S (plus b k) = S (plus b k)
```
---
**... Finally!**
```hs
reverse : {n : Nat} -> Vector n a -> Vector n a
reverse {n = 0} [] = Nil
reverse {n = S k} (Cons this rest) = 
  rewrite (plusComm 1 k) in
  (reverse rest) `append` (Cons this Nil)
```

---

**Termination**
*"We can't fake equality"*

```haskell
bad : 0 = 1
bad = bad
```

Typechecks, but loops infinitely when evaluated.
Can be generalised:
```haskell
bad : a
bad = bad
```
---
Check 1: Only allow recursion on *syntactic subterms* of current arguments.
```haskell
isEven : Nat -> Bool
isEven Z = True
isEven (S Z) = False
-- Allowed: k is a subterm of S k
isEven (S k) = not (isEven k)
```
```haskell
collatz : Nat -> Nat
collatz Z = Z
collatz (S Z) = (S Z)
-- Not ok: recursive call is not on a subterm
collatz num = if (isEven num) then collatz (num / 2) else collatz (3*num + 1)
```
---
The idea: every value is finitely big, so by repeatedly taking subterms, we are guaranteed to eventually arrive at a base case.
```haskell
data NatStream : Type where
  Done : NatStream
  More : Nat -> (NatStream -> NatStream)

moreNats : NatStream -> NatStream
moreNats Done = Done
moreNats (More thisNat getTail) = getTail (More (S thisNat) getTail)

nats : NatStream
nats = moreNats (More 0 moreNats)
```
---
**Evaluating `nats`**
nats
  = moreNats (More 0 moreNats)
  = moreNats (More 1 moreNats)
  = moreNats (More 2 moreNats)
  ...

Clearly, not every value is finitely big. There is no recursion, but we end up in an infinite loop

---
Check 2: No negative types

Here is the problem:
```hs
More : Nat -> (NatStream -> NatStream)
````
Specifically, `NatStream` being on the left of an arrow
```hs
(NatStream -> ...)
```

So, we should not allow this in type definitions.

---
**Types as propositions**
Look at the kinds of signatures we have been writing:
```hs
plusZeroRightNeutral : (x : Nat) -> x + 0 = x
plusComm : (a : Nat) -> (b : Nat) -> a + b = b + a
Refl : 1 = 1
```
These look less like types, and more like mathematical statements. 

---
| Type                              | Proposition                                              |
| --------------------------------- | -------------------------------------------------------- |
| Unit / ()                         | True                                                     |
| Void                              | False                                                    |
| Product type / tuple (a,b)        | Conjunction                                              |
| Sum type / Either a b             | Disjunction                                              |
| Function (->)                     | Implication                                              |
| \=                                | Equality                                                 |
| Dependent function (x : a) -> P x | Universal quantification $\forall x \in a. P(x)$        |
| Dependent pair (x : a \*\* P x)   | Existential quantification $\exists x \in a. P(x)$ |

---
```hs
plusComm : (a : Nat) -> (b : Nat) -> a + b = b + a
```
plusComm : $\forall a \in \mathbb{N}. \forall b \in \mathbb{N}. a + b = b + a$

```hs
absurd : Void -> p
```
absurd : $\forall P \in \text{Type}. \bot \implies P$

```hs
-- Not possible to implement
lem : Either p (p -> Void)
```
lem : $\forall P \in \text{Type}. P \lor (P \implies \bot)$

---
We are not limited to just the logical connectives; we can make types that encode more interesting propositions / relations
```haskell
data IsEven : Nat -> Type where
  DoubleOf : (x : Nat) -> IsEven (2*x)
```

```haskell
data LTE : Nat -> Nat -> Type where
  ZLTE : LTE 0 x
  Bump : LTE x y -> LTE (S x) (S y)
```

Doing this is fundamentally a creative exercise: does the type you defined faithfully capture your *intent*?

You cannot formally prove that the encoding is adequate in the system itself.

---
Another encoding of `LTE`
```haskell
data LTE : Nat -> Nat -> Type where
  Sure : (k, x, y : Nat) -> x + k = y -> LTE x y
```
Semantically the same, but completely different types.
The type checker can guarantee that your program matches your specification, but it cannot guarantee that your specification matches your thoughts.

See Tarski's undefinability of truth

---

**Some more sane alternatives**

Property based testing: the same mindset of thinking in properties, but lots of test cases instead of a proof

```hs
dedup :: Eq a => [a] -> [a]
dedup [] = []
dedup [x] = [x]
dedup (x:y:xs)
  | x == y    = dedup (y:xs)
  | otherwise = x : dedup (y:xs)

prop_noDuplicates :: [Int] -> Bool
prop_noDuplicates xs = unique (dedup xs)
  where
    unique []     = True
    unique (y:ys) = not (y `elem` ys) && unique ys
````
---

```bash
cabal test

Running 1 test suites...
Test suite dedup-tests: RUNNING...
Testing uniqueness
*** Failed! Falsified (after 6 tests and 2 shrinks):     
[-5,0,-5]
```

NOT a formal proof, but great at catching edge cases in practice. "Shrinks" try to find the minimal counterexample which breaks the property.

---

Refinement types: Attach logical predicates to existing types, but let an SMT solver try and verify everything.

```hs
{-@ type OrdList a = [a] <{\x v -> x <= v}>@-}

{-@ ups :: OrdList Int @-}
ups :: [Int]
ups = [1, 3, 2]
```

Has the worst error messages known to man (it is just raw SMT output)

---

```
**** LIQUID: UNSAFE ************************************************************
src/Euclid.hs:24:1: error:
    Liquid Type Mismatch
    .
    The inferred type
      VV : GHC.Types.Int
    .
    is not a subtype of the required type
      VV : {VV##1128 : GHC.Types.Int | ?a <= VV##1128}
    .
    in the context
      ?a : GHC.Types.Int
    Constraint id 10
   |
24 | ups = [1, 3, 2]
   | ^^^^^^^^^^^^^^^
```

But it IS a formal proof, and doesn't require a bunch of new types or proof code.

---

```hs
{-@ type OrdList a = [a] <{\x v -> x <= v}>@-}

{-@ insertSort :: (Ord a) => [a] -> OrdList a @-}
insertSort :: Ord a => [a] -> [a]
insertSort = foldr insert []

{-@ insert :: (Ord a) => a -> OrdList a -> OrdList a @-}
insert :: Ord a => a -> [a] -> [a]
insert x [] = [x]
insert x (y:ys)
  | x <= y = x : y : ys
  | otherwise = y : insert x ys
```

```
**** LIQUID: SAFE (10 constraints checked) *************************************
```

---

**Lots of techniques for code correctness, each with tradeoffs**

Simple static typing -> property based testing -> refinement types -> dependent types / proofs

---
