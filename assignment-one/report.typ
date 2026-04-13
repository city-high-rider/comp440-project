= Verifying a Simple DAG Scheduler

== (TODO: My ID here) - COMP440 Assignment One

#outline()

---

== Aims and Objectives
The objective of this report is to model and prove the termination of a directed acyclic graph (DAG) scheduler in Idris2 and Coq (the precise theorem will be stated at the end of the next section). The proof will then be used as a vehicle to compare both languages by considering their available tooling (specifically interactive editing features, content of the standard library, and package managers), approaches to encoding propositions and proofs, as well as their methods for judging these propositions. Finally, a subjective account of both languages' developer experience will be given.

== Preliminary Models, Definitions, and Proofs

=== Definition 1
A _Scheduler state_ over a finite directed acyclic graph $G = (V, E)$ is comprised of four sets of tasks that are pairwise disjoint and together cover $V$:
  1. The set of finished tasks, $F$
  2. The set of ready tasks, $R$
  3. The set of pending tasks, $P$
  4. The set of running tasks, $D$, which may contain at most one element.

=== Definition 2
A task $t$ is _enabled_ in a scheduler state over a directed acyclic graph $G = (V,E)$ if $t in P and forall d in T [d E t -> d in F]$ 
(The task is pending and all dependencies are finished.)

=== Definition 3
A _step_ is a binary relation on states $S_1 = (P_1, R_1, D_1, F_1), S_2 = (P_2, R_2, D_2, F_2)$ over a directed acyclic graph $G = (V, E)$ which holds iff exactly one of the following conditions are true: 
  + $D_1 = emptyset and exists t in T [t in R_1 and t in D_2]$ (A task is moved from _ready_ to _running_)
  + $D_2 = emptyset and exists t in T [t in D_1 and t in F_2]$ (A task is moved from _running_ to _finished_)
  + $exists t in T [t "is enabled in" S_1 and t in R_2]$ (An enabled task is moved to _ready_)

=== Definition 4
A "trace" between two scheduler states $S_1$ and $S_2$ is a witness of $S_1 "Step"^* S_2$, where $"Step"^*$ is the transitive-reflexive closure of the step relation.

=== Definition 5
A scheduler state $S$ is "terminal" if there does not exist an $S'$ such that $S "Step" S'$ holds.

=== Definition 6
The measure $mu$ of a state $S$ is a function $mu : SS -> NN$ where $mu(S) = |D| + 2|R| +3|P|$

=== Definition 7
A scheduler state over a directed acyclic graph $G = (V, E)$ is _finished_ if $forall t in V [t in F]$

=== Lemma 1
If every node in a directed graph $G = (V,E)$ has an outgoing edge, the graph is cyclic.

==== Proof of lemma 1
Pick any $v in V$. Because each node has an outgoing edge, it is possible to cross $|V|$ edges starting from $v$. Every time you cross an edge to an adjacent node, one of the following is true:
  + You have visited the adjacent node before
  + You have not visited the adjacent node before.
  In the first case, this means there is a cycle. If, after $|V|$ steps, you have not found a cycle, this means you have visited $|V| + 1$ unique nodes, which is not possible. Therefore, the graph is cyclic. $qed$

=== Lemma 2
For a scheduler state $S = (F, P, R, D)$ over a directed acyclic dependency graph $G = (V, E)$, if $P != emptyset and R = emptyset and D = emptyset$ then there is an enabled task in $P$.

==== Proof of lemma 2
The proof is by contradiction. Suppose that we cannot find an enabled task in $P$. This means that each pending task depends on an unfinished task. Since $P, R, D, F$ are pairwise disjoint and cover $V$, and $R$ and $D$ are empty, this means that these unfinished tasks must be in the pending set also. Therefore, each node in the subgraph $G_s = (P, {u->v in E | u in P and v in P})$ must have at least one outgoing edge. By lemma 1, this implies $G_s$ is cyclic. Since $G_s$ is cyclic, $G$ is cyclic. $arrow.r.double arrow.l.double$

=== Theorem 1 (Terminal and finished states)
A state is finished iff it is terminal.

==== Proof of theorem 1
===== $->$ direction (if a state is finished, then it is terminal.)
In a finished state $S$ over $G = (V, E)$, every $t$ in $V$ is in $F$. Since $P, R, D, F$ are pairwise disjoint and cover $V$, this means that the sets $P, R, G$ are all empty. Therefore, no steps are possible, and thus the finished state is terminal.
===== $<-$ direction (if a state is terminal, then it is finished.)
We will do the contrapositive proof: if a state is not finished, then it is not terminal. Consider a non-finished state $S$. Then, one of the following must hold:
  + $D != emptyset$
  + $R != emptyset$
  + $P != emptyset$
If $D != emptyset$, then there is some $e in D$. Therefore, a step to $S' = (F union {e}, R, P, emptyset)$ is possible, and $S$ is non-terminal.
If $R != emptyset and D = emptyset$, then there is some $r in R$. Therefore, a step to $S' = (F, R - {r}, P, {r})$ is possible, thus $S$ is non-terminal.
If $P != emptyset and R = emptyset and D = emptyset$, there is some enabled $p in P$ by lemma 2. Therefore, a step to $S' = (F, {p}, P - {p}, emptyset)$ is possible, thus $S$ is non-terminal. $qed$

=== Lemma 3
$mu(S) = 0$ iff $S$ is finished. 

==== Proof of lemma 3
===== $<-$ direction (if a state is finished, then the measure is zero)
By definition, if $S = (F, P, R, D)$ over $G = (V, E)$ is finished, every task is finished. Because $F, P, R, D$ are pairwise disjoint and cover $V$, $P, R, D$ must all be empty. Therefore, $mu(S) = |D| + 2|R| +3|P| = 0$.
===== $->$ direction (if the measure is zero, then the state is finished)
if $mu(S) = |D| + 2|R| +3|P| = 0$, this means all the cardinalities must be zero, as cardinalities are non-negative. Since $|D| = 0, |R| = 0, |P| = 0$, this means $D = R = P = emptyset$. Because $F, P, R, D$ are pairwise disjoint and cover $V$, this means $forall t in V [t in F]$. Therefore, $S$ is finished. $qed$

=== Lemma 4
If $S_0 "step" S_1$ holds, $mu(S_0) = mu(S_1) + 1$

==== Proof of lemma 4
Since $S_0 "step" S_1$ holds, one of the following must be true:
  + $D_1 = emptyset and exists t in V [t in R_1 and t in D_2]$
  + $D_2 = emptyset and exists t in V [t in D_1 and t in F_2] $
  + $exists t in V [t in R_2 and t "is enabled in" S_1]$
- In case 1, $mu(S_1) - mu(S_0) = 1 + 2*(|R| - 1) + 3|P| - [0 + 2*(|R|) + 3|P|] = -1$ 
- In case 2, $mu(S_1) - mu(S_0) = 0 + 2|R| + 3|P| - [1 + 2|R| + 3|P|] = -1$
- In case 3, $mu(S_1) - mu(S_0) = |D| + 2*(|R| + 1) + 3*(|P| - 1) - [|D| + 2|R| + 3|P|] = -1$
In each case, $mu(S_1) - mu(S_0) = -1$. Therefore, in each case, $mu(S_0) = mu(S_1) + 1 qed$

=== Theorem 2 (Termination)
For every scheduler state $S_0$ there exists a finite trace to a finished state $S$.

==== Proof of theorem 2
The proof is by induction on $mu(S_0)$.
===== Base case
Suppose $mu(S_0) = 1$. By lemma 3, $S_0$ is not finished, and by theorem 1 it is therefore non-terminal. Thus, there exists some $S_1$ such that $S_0 "step" S_1$ holds. By lemma 4, $mu(S_1) = 0$. By lemma 3, $S_1$ must be finished. Therefore, the trace is the step from $S_0$ to $S_1$.
===== Inductive step
Suppose that for every scheduler state whose measure is equal to $n$ there exists a finite trace to a finished state. Suppose that $mu(S_0) = n + 1$. By lemma 3, $S_0$ is not finished, thus by theorem 1, $S_0$ is non-terminal. So, there exists some $S_1$ such that $S_0 "step" S_1$ holds. By lemma 4, $mu(S_1) = n$. By the inductive hypothesis, there is a finite trace $t$ from $S_1$ to a finished state $S$. Therefore, a finite trace from $S_0$ to $S$ is obtained by combining the step from $S_0$ to $S_1$ with $t$. 

We have shown that for every non-terminal scheduler state with an arbitrarily large measure, there is a finite trace to a finished state. Now consider a starting state. It is either terminal, or non-terminal. If it is terminal, then we have a trivial trace to a finished state, that is, itself. If it is non-terminal, then by the induction proof above, we can find a finite trace to a finished state. $qed$ 

== What does it mean for a program to "prove" something?
A particular school of logic called constructivism asserts that to show a proposition is true, you must be able to find evidence to support it; it is not sufficient to assume the proposition does not hold and derive a contradiction.

Thus, under constructivist logic, a proposition holding means that there exists _explicit evidence_ for it, rather than merely the absence of contradiction. Morevoer, the evidence is an object with structure that can be examined and manipulated. Proofs can then be seen as functions which constructively transform valid evidence for one fact into valid evidence for another fact while preserving truth.

Constructivist philosophy makes the relationship between proofs and computer programs much easier to see. Specifically, this connection is called the _Curry-Howard_ correspondence, which shows that propositions correspond to types, and proofs correspond to functions. Thus, a program that typechecks and is implemented in a language with certain constraints (determinism, absence of side effects, a sound type system) can be seen as a proof.  

Since a proposition can be viewed as a type, then it makes sense to also see its evidence as a value of that type. A proposition is considered true precisely when we can construct evidence for it, and there should be no way to construct evidence for a false proposition. Even though that view is simple, it is already a practical mindset to have when encoding propositions as type definitions. For instance, here's how it can help us write a type that encodes a proposition that $a <= b$ for natural numbers in Idris2. In this setting, defining a type is equivalent to defining a proposition, and its constructors define exactly what counts as valid evidence for that proposition.

Here is the complete type definition, followed by a line-by-line explanation:
```idris
data LTE : Nat -> Nat -> Type where
  ZLTEAnything : LTE 0 someNumber
  Bump : LTE a b -> LTE (S a) (S b)
```

Firstly, the proposition "$a$ is less than or equal to $b$" has two free variables which are natural numbers, $a$ and $b$. Therefore, we must define a family of types for all the combinations of two natural numbers:
```idris
data LTE : Nat -> Nat -> Type
```
With this definition, all of the following are now valid _propositions_:
 - `LTE 0 0` ($0 <= 0$)
 - `LTE 51 9` ($51 <= 9$)
 - `LTE 2 10` ($2 <= 10$)
But not all of these propositions are necessarily true. The next step is to define what kind of _evidence_ can witness this proposition, i.e. how proofs of this proposition are constructed. For instance, zero should be less than or equal to any other natural number:
```idris
ZLTEAnything : {someNumber : Nat} -> LTE 0 someNumber
```
Notice that by adding `someNumber` as a parameter to `ZLTEAnything`, we have quantified it as _any_ natural number, because there are absolutely no restrictions to the number we can pass to that constructor. This means that `ZLTEAnything` encodes the rule $forall "someNumber" in NN [0 <= "someNumber"]$.

Next, if we know that $a <= b$, then $(a+1) <= (b+1)$ should be true as well. This gives the second rule/type constructor:
```idris
Bump : {a,b : Nat} -> LTE a b -> LTE (S a) (S b)
```
Or, in first-order logic notation: $forall a in NN. forall b in NN. [a <= b -> (a+1) <= (b+1)]$.

I emphasize that these constructors do not state facts about an existing relation; rather, they define what counts as valid evidence for the relation. Putting both of the constructors together gives the complete definition for the $<=$ proposition. For readability, the explicit quantification of variables will also be omitted, as Idris will automatically add them as implicit arguments for us. Here is the starting definition repeated again.
```idris
data LTE : Nat -> Nat -> Type where
  ZLTEAnything : LTE 0 someNumber
  Bump : LTE a b -> LTE (S a) (S b)
```
Now it's possible to check whether or not the previous three propositions are true by attempting to construct evidence for them with those two rules:
 - `LTE 0 0` ($0 <= 0$) is trivially true. Since the lefthand number is a zero, `ZLTEAnything {someNumber = 0}` is valid evidence for this proposition. 
 - `LTE 51 9` ($51 <= 9$) is false. Observe that the lefthand number is $51$, not zero, meaning that evidence for this must be constructed by applying the `Bump` rule to evidence that $50 <= 8$. Repeating the same reasoning, we may eventually conclude that in order to construct evidence that $51 <= 9$, it is necessary to construct evidence that $42 <= 0$. However, by again analysing the type constructors, we may deduce that this is not possible. There are only two we can apply: `ZLTEAnything`, which is evidence for $0 <= x$, and `Bump`, which is evidence for $S(a) <= S(b)$. The first rule could not be used to prove this, because the left-hand number is $42$, not zero. The second rule could also not be used to prove this, because the right-most number is zero.
 - `LTE 2 10` ($2 <= 10$) is true. Neither the left nor right-hand numbers are zero, so it is necessary to `Bump` a proof that $1 <= 9$. Once again, neither one nor nine are zero, so to get this subproof, it is necessary to `Bump` a proof that $0 <= 8$. This sub-subproof can finally be constructed with the `ZLTEAnything` rule applied to the number eight. Putting this together, the _evidence_ that $2 <= 10$ is `Bump (Bump (ZLTEAnything {someNumber = 8}))`.

Now that we've seen how to encode a proposition as a type, what remains is to see how a program can encode a proof. Can we show that our `LTE` relation is transitive?

The starting point is the _type signature_ of the proof-function. Suppose we have evidence that $a <= b$ and $b <= c$. Can we use that to construct evidence that $a <= c$?
```idris
lteTrans : LTE a b -> LTE b c -> LTE a c
```
This proof can be done with cases. Each piece of evidence was either constructed with `ZLTEAnything` or `Bump`. This makes four combinations:
1. `LTE a b` and `LTE b c` were both constructed with `ZLTEAnything`. This means `a` and `b` are both zero, while `c` is some other number. Therefore, the goal may be updated with this information: now we are trying to provide evidence for `LTE 0 c`, which can be done with `ZLTEAnything {someNumber = c}`.
2. `LTE a b` was constructed with `ZLTEAnything`, while `LTE b c` was constructed with `Bump`. Much like the last case, knowing that the first constructor is `ZLTEAnything` tells us that `a = 0`, which reduces the goal to `LTE 0 c`. Therefore, `ZLTEAnything {someNumber = c}` is sufficient evidence.
3. `LTE a b` was constructed with `Bump`, while `LTE b c` was constructed with `ZLTEAnything`. If this is the case, we gather some information: `a` and `b` are both successors of some natural number, and `b` is zero. This is a contradiction, because `b` cannot both be zero and nonzero at the same time. Therefore, we have no obligation to prove anything in this case, since it's impossible to provide this combination of evidence.
4. `LTE a b` and `LTE b c` were both constructed by `Bump`ing a subproof. Thus, we can gather that:
  - `a = S x` for some `x`
  - `b = S y` for some `y` 
  - `c = S z` for some `z`
  - There is evidence that `LTE x y` and `LTE y z` from the subproofs that were `Bump`ed.
  Here, we can call the proof-function recursively to get evidence that `LTE x z` from the evidence that `LTE x y` and `LTE y z`. Because `x, y, z` are all strictly smaller than `a, b, c`, eventually this function must reach one of its base cases. We may then apply `Bump` to this result to obtain `LTE (S x) (S z)`, which is the goal.

And here is the Idris2 implementation of the function:
```idris
total
lteTrans : LTE a b -> LTE b c -> LTE a c
lteTrans ZLTEAnything _ = ZLTEAnything
lteTrans (Bump subprfA) (Bump subprfB) = Bump (lteTrans subprfA subprfB)
```
There are a few notable things about this function. Firstly, it is substantially more terse than the preceding written proof. Secondly, there is a `total` annotation at the top.

The `total` annotation forces the compiler to verify that the function is _covering_, meaning it should be defined for all inputs, and that it eventually terminates. Termination is a notable property: if a function which computes evidence does not terminate, it means the proof is not sound.

Consider the following function. The type signature can be interpreted as "for any proposition, return evidence of that proposition," and the implementation goes into an endless recursive loop:
```idris
anyProof : {a : Type} -> a
anyProof = anyProof
```
Thus, `anyProof {a = LTE 1 0}` is valid evidence that $1 < 0$ as far as the type checker is concerned, although in practice asking the program to actually _provide_ this evidence will cause it to loop forever. Clearly, this is not desirable, but unfortunately, there is no way to verify whether or not an arbitrary program will terminate. Thus, the totality checker in Idris works conservatively: any program it verifies to be total is actually total, but it will not accept every total program. In particular, all of the following must be true for a function to be verified as total:
1. It is covering
2. Every function the implementation calls is also total
3. In a recursive call, one argument must be _syntactially smaller_. That is, it must be a sub-term of the current argument. 
The totality checker is clever enough that usually, no manual intervention by the programmer is required. However, for proofs that instead use a strictly decreasing measure to justify termination, some more work is required, which will be discussed in more detail at the end of the Idris section.

Secondly, it is worth mentioning why the Idris proof is so terse, as it will provide a bit of context when we later discuss the languages' tooling and compare it to tactic-based theorem proving like Rocq. The compactness mainly comes from the fact that most of the "reasoning" is delegated to the type checker's constraint solving mechanisms rather than being written explicitly in the proof. Recall the written `LTE` transitivity proof from earlier: most of the steps were case analysis on constructors, refinement of type indices, and elimination of contradictory cases. All of this mechanical work is automatically handled in a process called _unification_, which solves equations between types and fills in implicit parameters. This is why we did not need to supply values such as `someNumber`, since the type checker infers them in order to make the expressions type correctly. Finally, termination is also automatically handled by a totality checker, meaning that explicit termination arguments are often unnecessary.

=== Proving that something is not true

It is sometimes necessary to prove that a proposition does _not_ hold. For this, there needs to be a type which represents falsehood, or a contradiction. We have already established that in order to prove a proposition holds, it is necessary to provide direct evidence. Since the false proposition should never be provable, there should be no way to construct any evidence for it at all. Thus, the type representing contradiction / falsehood is remarkably simple: it is merely a type with no constructors:
```idris
data Void
```
As there are no constructors, it is impossible to construct a _value_ of `Void`. Such a type with no values is called _uninhabited_, and any uninhabited type represents a contradiction, since it has no possible evidence. Crucially, there is a total function in the standard library which can provide evidence for any proposition given a value of any uninhabited type, much like the principle of explosion in classical logic:
```
absurd : Uninhabited t => t -> a
```
This function is sound because it can only be applied if a value of an uninhabited type is available, which can only occur in contradictory situations. This raises a natural question: if a value of type `Void` cannot be constructed, how can one ever appear in a program?

The key idea is that such a value can arise from assumptions. When proving that a proposition does not hold, we assume that it does hold, and then show that this leads to a contradiction. This contradiction is represented by a value of type `Void`. In this sense, a value of type Void does not arise from construction, but from demonstrating that a given assumption is impossible. In practice, proofs often require additional lemmas to rule out cases that are syntactically possible but logically impossible. For example, the type checker requires all constructors of a datatype to be handled during pattern matching, even when some branches correspond to uninhabited situations.  Ocasionally, the totality checker will be able to deduce that certain combinations of inputs are impossible, as seen in the `lteTrans` proof, because indices in the types cannot unify. However, this mechanism is still fundamentally syntactic, so in cases where it fails, the programmer must explicitly prove that the case cannot occur and eliminate it using a contradiction.

With the `Void` type, it is now possible to show that a proposition does _not_ hold by providing a function which takes evidence of the proposition and returns a `Void` value. In fact, this is exactly the definition of the `Not` proposition in Idris:
```idris
Not : Type -> Type
Not prop = prop -> Void
```
which matches the classical logic interpretation of negation: to prove $not P$, we assume $P$ and derive a contradiction.

=== Tactic based theorem proving
We can now see how it's possible to state and prove propositions constructively by directly manipulating evidence. We also have an idea about how the unifier verifies such proofs through constraint solving and definitional equality. However, working directly with explicit terms can be unpleasant in practice. Since correctness is only established for fully constructed expressions, proofs often feel like manually building and reshaping complex terms while relying on the type checker to validate each intermediate step. This process does not capture higher level proof structure or intent, which can make proofs difficult to write and understand.

For example, consider the following function:
```idris
||| a number is equal to the sum of its digits mod 3.
total
kCongDigits3 : (d : Decimal n) -> congMod 3 n (sumDigits d)
kCongDigits3 (MostSig digit) = (0 ** rewrite plusZeroRightNeutral (finToNat digit) in Refl)
kCongDigits3 (digit <: rest) = let (h ** prf) = kCongDigits3 rest in
  rewrite prf in
  rewrite multCommutative 10 (sumDigits rest + h*3) in
  rewrite multDistributesOverPlusLeft (sumDigits rest) (h*3) 10 in
  rewrite multRightSuccPlus (sumDigits rest) 9 in
  rewrite sym (plusAssociative (sumDigits rest) ((sumDigits rest) * 9) ((h*3)*10)) in
  rewrite plusAssociative (finToNat digit) (sumDigits rest) ((sumDigits rest)*9 + (h*3)*10) in
  rewrite nestedMultSwap h 3 10 in
  rewrite factor3from9 (sumDigits rest) in
  rewrite sym (multDistributesOverPlusLeft (mult (sumDigits rest) 3) (mult h 10) 3) in
  ((plus (mult (sumDigits rest) 3) (mult h 10)) ** Refl)
```
From the type signature and comment, it's possible to understand what this lemma proves. But, it may not be immediately clear to the reader that this is a proof by induction on the quantity of digits in the decimal representation of the number, or what the underlying algebraic manipulation is actually doing. Rather than using traditional algebraic techniques, writing this proof involved several syntactic rewrites of an expression tree until it was accepted by the type checker.

To solve these problems, tactics provide a higher-level interface for constructing proofs. Rather than explicitly building proof terms, they allow us to work in terms of goals and subgoals. Each tactic incrementally refines the proof state while generating a term that is ultimately checked using the same unification techniques.

=== Classical axioms
TODO: write me!

== Comparing the Idris and Coq proofs
There is quite a bit of code in both proofs, however much of this is taken up by rather mechanical lemmas which are not very interesting to discuss. Here is a map of the source code:
#table(
  columns: 2,
  table.header[*File*][*Notable Contents*],
  [`idris/Elem.idr`], [List membership definition and lemmas.],
  [`idris/All.idr`], [Proof that a proposition holds for all elements in a list.],
  [`idris/Subset.idr`], [Definition of a list being a subset of another list, proof that a proposition holds for an element in a list, some lemmas.],
  [`idris/Task.idr`], [Definition of a task, a DAG, and dependencies of a task.],
  [`idris/Unique.idr`], [Definition of a list with no duplicate elements.],
  [`idris/Remove.idr`], [Definition of removing an item from a list, lemmas about how it interacts with other definitions.],
  [`idris/Trace.idr`], [Definition of scheduler state, step, trace, measure function. Proof of progress and termination theorems.],
  [`coq/terminationProof.v`], [Definition of scheduler state, step, trace, measure. Proof of progress and termination. This is the only Coq file, because unlike Idris, many things were assumed or already defined in the standard library.]
)

There are, however, a few specific parts definitely worth discussing, which I will focus on.

=== Modelling the DAG.
First, a brief note on tasks: they are treated as an opaque type and hold no internal state. It may be helpful to think of them as _task IDs_ instead. The only constraint is that equality of tasks should be decidable. In both implementations, tasks are a type alias for natural numbers.

The approach to modelling the dependency graph in Idris and Coq was very different. In Idris, we tend to prefer simple, recursively defined data types, as they reduce code complexity, particularly when proofs by induction are involved. Moreover, it is desirable to make the graph acyclic by construction rather than model a generic graph and carry an acyclicity proof separately. Therefore, traditional representations of graphs such as adjacency lists and matrices are not ideal. Instead, the DAG is built up by starting with an empty graph and repeatedly adding unique source nodes:
```idris
data DAG : List Task -> Type where
  Empty : DAG []
  AddTask :
    (t : Task) ->
    (deps : List Task) ->
    Not (t `Elem` tasks) ->
    deps `Subset` tasks ->
    DAG tasks ->
    DAG (t :: tasks)
```
In order to enforce that every node is a source, the DAG is indexed over a list of tasks which represents all of the present nodes. The list of nodes which a new source points to (`deps`) is required to be a subset of the task list. The task list also allows us to enforce uniqueness of nodes by requiring that a newly added source is not already there. This representation dramatically simplifies the proof of Lemma 2 (finding an enabled task) as it allows us to reason about the graph inductively by passing a subgraph into a recursive call. Since the subgraph is a syntactic subterm of the original graph, this eliminates the need for complicated measures or termination proofs when working with it, as recursive calls on subterms of an argument is the precise condition the totality checker examines. There is also no need to carry proofs of acyclicity or uniqueness, as they are baked directly into the construction of the graph.

The Coq implementation follows the pen and paper proof more closely. Instead of modelling a graph at all, we assume there is some finite set of tasks and a dependency relation over tasks such that is it acyclic and the set of all tasks is closed under this relation:
```coq
Variable allTasks : list Task.

Variable E : Task -> Task -> Prop.

Definition acyclic :=
    forall t, ~ clos_trans Task E t t.

Hypothesis E_acyclic : acyclic.

Hypothesis E_closed :
    forall d t, E d t -> In t allTasks -> In d allTasks.
```
In contrast to the Idris approach, this representation does not attempt to encode structural invariants such as acyclicity or closure directly into a data type. Instead, these properties are stated separately as logical hypotheses.

These design differences mostly stem from the distinct philosophies of Idris and Coq. Both are capable of theorem proving and general-purpose programming, but they emphasize different aspects. Idris is best viewed as a functional programming language with a sufficiently expressive type system to encode and verify proofs, whereas Coq is primarily designed as a proof assistant, with programming as a secondary concern.

This difference is reflected in how proofs are expressed. In Coq, tactic-based proofs tend to mirror traditional hand-written arguments, which are typically phrased in terms of properties and relations rather than inductively constructed data. Moreover, Coq distinguishes between `Type`s and `Prop`ositions, where values in `Prop` carry no computational content and are erased during extraction. As a result, proofs in Coq are generally not meant to be executed.

Taken together, these factors reduce the incentive to encode invariants directly into data structures, as was done in the Idris implementation. Instead, in Coq it is more natural to represent systems abstractly and state their properties as separate hypotheses. Meanwhile, Idris proofs must remain executable and work directly with syntactic terms, which encourages encoding invariants directly in data types.

=== Proving Lemma 4 (Measure decreases across steps)
I want to highlight this lemma in particular, because unlike all the others, this one is an arithmetic proof. It shows perhaps the strongest contrast between tactic-based and Idris style proofs. It is also a good place to demonstrate the interactive tooling of both languages. Here are both implementations for the case when we enqueue a task:

Idris:
```idris
stepDecreasesMeasure (Enqueue (MkScheduler pending ready running finished _ _ _ _ _ _) readyThis pendingPrf _ _ _ _) =
  rewrite sym (removeShrinkLen {xs = pending, prf = pendingPrf}) in
  rewrite sym (plusSuccRightSucc (length (remove pending pendingPrf)) (plus (length (remove pending pendingPrf)) 0)) in
  rewrite sym (plusSuccRightSucc (length (remove pending pendingPrf)) (S (plus (length (remove pending pendingPrf)) (plus (length (remove pending pendingPrf)) 0)))) in
  rewrite sym (plusSuccRightSucc (length (remove pending pendingPrf)) (plus (length (remove pending pendingPrf)) (plus (length (remove pending pendingPrf)) 0))) in
  rewrite sym (plusSuccRightSucc (plus (length (maybeToList running)) (plus (length ready) (plus (length ready) 0))) (S (S ((plus (length (remove pending pendingPrf)) (plus (length (remove pending pendingPrf)) (plus (length (remove pending pendingPrf)) 0))))))) in
  rewrite sym (plusSuccRightSucc (plus (length (maybeToList running)) (plus (length ready) (plus (length ready) 0))) (S ((plus (length (remove pending pendingPrf)) (plus (length (remove pending pendingPrf)) (plus (length (remove pending pendingPrf)) 0)))))) in
  rewrite sym (plusSuccRightSucc (plus (length (maybeToList running)) (plus (length ready) (plus (length ready) 0))) ((plus (length (remove pending pendingPrf)) (plus (length (remove pending pendingPrf)) (plus (length (remove pending pendingPrf)) 0))))) in
  rewrite sym (plusSuccRightSucc (length ready) (plus (length ready) 0)) in
  rewrite sym (plusSuccRightSucc (length (maybeToList running)) (S (plus (length ready) (plus (length ready) 0)))) in
  rewrite sym (plusSuccRightSucc (length (maybeToList running)) (plus (length ready) (plus (length ready) 0))) in
  Refl
```

Coq:
```coq
- unfold mu. cbn [F R P D].
  pose proof (Nat.add_lt_mono_l) as Hsub.
  repeat rewrite <- Nat.add_assoc.
  symmetry in Hsub.
  apply Hsub with (p := length (D S)).
  simpl (length (t :: R S)).
  rewrite (Nat.mul_succ_r 2 (length (R S))).
  repeat rewrite <- Nat.add_assoc.
  apply Hsub with (p := 2*length(R S)).
  destruct H as [H _].
  pose proof (remove_length_lt Nat.eq_dec (P S) t H) as Hlen.
  apply ltSum in Hlen. destruct Hlen.
  replace (3 * length (P S)) with (3 * (Datatypes.S x + length (remove Nat.eq_dec t (P S)))).
    + rewrite (Nat.mul_add_distr_l 3 (Datatypes.S x) (length (remove Nat.eq_dec t (P S)))).
      pose proof (Nat.add_lt_mono_r) as HsubR.
      symmetry in HsubR.
      apply HsubR with (p := 3 * length (remove Nat.eq_dec t (P S))).
      lia.
    + f_equal. assumption.
```

Neither of these are particularly easy to read without tools. However, observe the difference in structure: the Idris proof is just a sequence of rewrites, explicitly specifying which rule should be applied to which sub-expressions. In contrast, the coq proof uses several different tactics: we tell it to replace certain function calls with their definitions, introduce new proofs in the context, and in cases where the goal has been simplified enough, we can even invoke fully automatic tools like `lia` to complete the rest of the proof. In some places, specific sub-expressions are mentioned just like in the Idris proof, however they are much simpler.

Unlike Idris however, Coq allows the reader to walk through the proof step-by-step, incrementally applying the tactics and observing how the hypotheses and goal change. For example, the goal is initially
```coq
mu
  {|
    F := F S;
    R := t :: R S;
    P := remove Nat.eq_dec t (P S);
    D := D S
  |} < mu S
```
Then, after expanding the definition of `mu` and record field projections with `unfold mu. cbn [F R P D].`, the goal changes:
```coq
length (D S) + 2 * length (t :: R S) + 3 * length (remove Nat.eq_dec t (P S))
<
length (D S) + 2 * length (R S) + 3 * length (P S)
```
This gives the reader a very solid idea of what is happening, and what the next steps might be. In this case, it's immediately clear that `length (D S)` is present on both sides of the inequality, so a next step could be to cancel them out. Indeed, this is precisely what the next four tactics do:
 - Introduce a proof that `p + a < p + b -> a < b` into the list of hypotheses as `Hsub`.
 - use associativity of addition to get the LHS into the correct form, because addition is left-associative by default.
 - Apply `Hsub` with `p := length (D S)`.
Having applied these tactics, the goal is now:
```coq
2 * length (t :: R S) + 3 * length (remove Nat.eq_dec t (P S))
<
2 * length (R S) + 3 * length (P S)
```
Again, the next step is clear. We know by the definition of `length` that `length (t :: R S)` should be equal to `1 + length (R S)`. We can use tactics to conclude this by simplifying `length (t :: R S)`, then distribute the multiplication of 2 over both terms. Afterwards, both sides of the inquality will once again contain identical terms, namely `2 * length (R S)` that we can cancel out. Once again, this is done by the next four tactics. The rest of the proof proceeds in a similar manner, until the goal is simplified to a proof that `2 < 3 * (1 + x)`. At this point, the goal is sufficiently simple that `lia` is able to automatically complete the remainder of the proof.

Now, let's compare this to the Idris proof. Although there is no interactive tooling to step through each rewrite, we may manually remove all the rewrites, replace the function body with a hole, and inspect the type of the hole to see what the initial goal of the proof is:
```
stepDecreasesMeasure (Enqueue (MkScheduler pending ready running finished _ _ _ _ _ _) readyThis pendingPrf _ _ _ _) =
  ?hole
```
This yields the following (note that here `S` is the successor function, not a scheduler state):
```
hole :
plus (plus (length (maybeToList running)) (plus (length ready) (plus (length ready) 0))) (plus (length pending) (plus (length pending) (plus (length pending) 0)))
=
S (plus (plus (length (maybeToList running)) (S (plus (length ready) (S (plus (length ready) 0))))) (plus (length (remove pending pendingPrf)) (plus (length (remove pending pendingPrf)) (plus (length (remove pending pendingPrf)) 0))))
```
Here we can see that the unification process automatically expanded all the functions it could: the measure, the field projections, multiplication, and addition where possible. The expressions are also written in prefix form rather than infix form with explicit brackets. The remaining proof involves applying an equality `length pending = S (length (remove pending pendingPrf))` and bubbling the `S` functions out of the `plus` expressions with `plusSuccRightSucc : (left : Nat) -> (right : Nat) -> S (left + right) = left + S right` before concluding the proof with reflexivity. Most of the volume in the proof is from having to specify what `left` and `right` are at every `plussSuccRightSucc` call, which involves repeating a lot of large expressions.

This is an example of how tactic based proofs can be much easier to read and write. If a reader wants to understand the Coq proof, they may simply walk through it step by step. On the other hand, examining an intermediate step of the Idris proof requires commenting out code, inserting a hole, and inspecting its type. When writing this proof in Coq, it was also much easier to read the goal and judge what the next step should be. We were able to precisely control what got expanded and where, and writing out complicated sub-expressions was usually not necessary to apply tactics.

