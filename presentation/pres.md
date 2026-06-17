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
**What's the difference?**
**TODO: Move this slide!!**
Classes and interfaces can mimic ADTs, but they are fundamentally different.
An ADT is a potentially *infinite* set of *finite* values. Each value must be inductively constructed up from some base case, so we know all the possible shapes of values and can rip the type open with pattern matching to work with it. This also lets us provide totality guarantees for recursive calls on syntactic subterms. These correspond to algebras.
OO modelling corresponds to a co-algebra, and can support truly infinite values. We do not care about construction, only about what we can *do* with values. This is more flexible, but many mainstream OO languages do not aim to guarantee soundness.

For algebras, we would need to use positivity checking to make sure each value is truly finite, and for co-algebras we need to use prooductivity checking to make sure that the program doesn't randomly loop forever. 




